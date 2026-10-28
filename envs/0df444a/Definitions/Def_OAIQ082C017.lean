-- Prove2me | Definitions.Def_OAIQ082C017
-- name    : OAIQ082C017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:39:10.516988+00:00
-- url     : https://prove2.me/theorems/c772b584-1243-49d3-b3fa-37fc12d5924a
-- title:
--   Definitions bundle OAIQ082C017 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 538 declarations of OpenAI's Lean: 267 definitions, 3 inductive types or structures, 2 instances and 266 theorems. The definitions and types are `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.Clean`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.Layout`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.Output`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.PhasePrivate`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.Private`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.ProgramLabel`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.clockOutput`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.controlSlots`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.entry`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.headLayout`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.headSlots`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.outputPolynomial`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.outputSlot`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.program`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.resultTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.tailLayout`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.tailSlots`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.Tape`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.bootstrapPorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.bootstrapPrepared`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.capacity`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.clock`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.count`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.countdown`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.current`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.cursor`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.finishPorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.finishTape`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.framed`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.freeInputs`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.frontPorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.frontTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.frontendPrepared`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.initializationPorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.initializationTape`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.output`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.q`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.raw` and 230 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Computation_MachineCanonicalOutput`, `BinPacking_Computation_MachineCeilingPower`, `BinPacking_Computation_MachineCloudPrefix`, `BinPacking_Computation_MachineCloudRank`, `BinPacking_Computation_MachineLazyRows`, `BinPacking_Computation_MachineLazyTableRuntime`, `BinPacking_Computation_MachineOverlayRows`, `BinPacking_Computation_MachineOverlayTable`, `BinPacking_Computation_MachinePaddedOverlayRuntime`, `BinPacking_Computation_MachinePortReindex`, `BinPacking_Computation_MachineRegularDummyRow`, `BinPacking_Computation_MachineRegularExecutionBounds`, `BinPacking_Computation_MachineRegularInternalRow`, `BinPacking_Computation_MachineRegularOwnerProgram`, `BinPacking_Computation_MachineRegularTable`, `BinPacking_Computation_MachineRegularTableRuntime`, `BinPacking_Computation_MachineRegularVertexBlock`, `BinPacking_Computation_MachineUnaryEqualityBit`, `BinPacking_Computation_MachineVertexPadding`, `BinPacking_Computation_PoweringGlobalEnumeration`, `BinPacking_Computation_PoweringMachineRow`, `BinPacking_Computation_PoweringMachineRowBody`, `BinPacking_Computation_PoweringMachineRuntime`, `BinPacking_Computation_PoweringMasterState`, `BinPacking_CookLevin_ProducerFrontStage`, `BinPacking_CookLevin_VerifierFront`, `BinPacking_Information_SourceNonempty`, `BinPacking_PCP_Initialization`, `BinPacking_PCP_PCPSourceHardness`, `BinPacking_PCP_PoweringTableLayout`, `BinPacking_PCP_PoweringTableSemantics`, `BinPacking_PCP_PreprocessingGuarantees`, `BinPacking_PCP_PreprocessingRegularBounds`, `BinPacking_Search_SearchInitializeEncoding`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C010`, `OAIQ082C011` and `OAIQ082C013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C023`, `OAIQ082C024` and `OAIQ082C025`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C010
import Definitions.Def_OAIQ082C011
import Definitions.Def_OAIQ082C013

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringMachineRow
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open BinPackingGames.Foundations.PCP

section Chains

variable {K Λ σ : Type} {N : Nat}

variable [DecidableEq K]

theorem stepAux_readEncodedSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readEncodedSlots src slots next) (ambient, buffer)
        (Function.update tapes src (encodeBits (slots.map bits) ++ suffix)) =
      TM2.stepAux next (ambient, fill slots bits buffer)
        (Function.update tapes src suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readEncodedSlots, encodeBits, fill]
  | cons i slots ih =>
      cases hb : bits i <;>
        simpa only [readEncodedSlots, List.map_cons, encodeBits, encodeBit, hb,
          Bool.false_eq_true, ite_false, ite_true, if_true, List.cons_append,
          List.nil_append, TM2.stepAux, Function.update_self, List.head?_cons,
          Option.getD_some, List.tail_cons, Function.update_idem, Bool.cond_false,
          Bool.cond_true, fill, List.foldl_cons] using
          ih (Function.update buffer i (bits i)) tapes

theorem stepAux_readEncodedAll (src : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (readEncodedSlots src (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes src suffix) := by
  have h := stepAux_readEncodedSlots src (List.ofFn id) next
    state.1 bits state.2 tapes suffix
  have hin : Function.update tapes src
      (encodeBits ((List.ofFn id).map bits) ++ suffix) = tapes := by
    simpa only [List.map_ofFn, Function.comp_id, ← hinput] using
      Function.update_eq_self src tapes
  rw [hin, fill_all] at h
  exact h

theorem stepAux_writeEncodedSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (writeEncodedSlots dst emit slots next) state tapes =
      TM2.stepAux next state
        (Function.update tapes dst
          (encodeBits ((slots.map (emit state)).reverse) ++ tapes dst)) := by
  induction slots generalizing tapes with
  | nil => simp [writeEncodedSlots, encodeBits]
  | cons i slots ih =>
      cases hb : emit state i <;>
        simp only [writeEncodedSlots, TM2.stepAux, hb, Bool.cond_false, Bool.cond_true]
      all_goals rw [ih]
      all_goals simp [Function.update_idem, List.map_cons, List.reverse_cons,
        encodeBits_append, encodeBits, encodeBit, hb, List.append_assoc]

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

variable [DecidableEq K]

theorem stepAux_encodedBlockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockStmt src dst F next) state tapes =
      TM2.stepAux next (state.1, emptyBuffer N)
        (Function.update (Function.update tapes src suffix) dst
          (encodeBits (List.ofFn (F bits)) ++ tapes dst)) := by
  unfold encodedBlockStmt
  rw [stepAux_readEncodedAll src _ state bits tapes suffix hinput,
    stepAux_writeEncodedSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]

theorem stepAux_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockAt src dst F exit) state tapes =
      { l := exit, var := (state.1, emptyBuffer N),
        stk := Function.update (Function.update tapes src suffix) dst
          (encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  rw [encodedBlockAt, stepAux_encodedBlockStmt src dst F _ hne bits suffix state tapes hinput]
  cases exit <;> rfl

end Block

end BinPackingGames.Foundations.Complexity.PoweringMachineRow

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineCanonicalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem cleanupTrace {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (labels : Label (workTapes enumeration output) → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) =
      instruction (workTapes enumeration output) labels none l)
    (base : Tapes K) (ambient : σ) :
    (advance (TM2.step program))^[steps (workTapes enumeration output) base]
      (some ⟨entry (workTapes enumeration output) labels none, (ambient, none), base⟩) =
    some ⟨none, (ambient, none), haltTapes output (base output)⟩ := by
  simpa only [finalRegister_none, finalTapes_workTapes] using
    trace (workTapes enumeration output) labels none program atLabels base ambient none

end BinPackingGames.Foundations.Complexity.MachineDrainMany

namespace BinPackingGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

def instruction (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (labels : Label enumeration output → Λ) :
    Label enumeration output → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .inl l => copyInstruction headerD scratch output (fun q => labels (.inl q))
      (some (labels (.inr (.inl .seed)))) l
  | .inr (.inl l) => copyInstruction headerV scratch output
      (fun q => labels (.inr (.inl q)))
      (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
        (fun q => labels (.inr (.inr q))) none) l
  | .inr (.inr l) => MachineDrainMany.instruction
      (MachineDrainMany.workTapes enumeration output) (fun q => labels (.inr (.inr q))) none l

theorem traceAt (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (hvs : headerV ≠ scratch) (hvo : headerV ≠ output)
    (hds : headerD ≠ scratch) (hdo : headerD ≠ output) (hso : scratch ≠ output)
    (labels : Label enumeration output → Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, target (labels l) =
      instruction enumeration headerV headerD output scratch labels l)
    (base : K → List Bool) (n m : Nat) (suffixV suffixD : List Bool)
    (wordV : base headerV = encodeWord n ++ suffixV)
    (wordD : base headerD = encodeWord m ++ suffixD)
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step target))^[steps enumeration output base n m]
      (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
      some ⟨none, (ambient, none),
        MachineDrainMany.haltTapes output (encodeWords [n, m] ++ base output)⟩ := by
  have hd := MachineUnaryAffineAt.seededAffineTrace headerD scratch output hds hdo hso 1 0
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (.inr (.inl .seed)))) target
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base m suffixD wordD scratchEmpty ambient register
  simp only [Nat.one_mul, Nat.add_zero] at hd
  change (advance (TM2.step target))^[2 * (m + 1) + 1]
    (some ⟨some (labels (.inl .seed)), (ambient, register), base⟩) =
    some ⟨some (labels (.inr (.inl .seed))), (ambient, none), afterD output base m⟩ at hd
  have wordV' : afterD output base m headerV = encodeWord n ++ suffixV := by
    simpa only [afterD, Function.update_of_ne hvo] using wordV
  have scratchEmpty' : afterD output base m scratch = [] := by
    simpa only [afterD, Function.update_of_ne hso] using scratchEmpty
  have hv := MachineUnaryAffineAt.seededAffineTrace headerV scratch output hvs hvo hso 1 0
    (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
    (labels (.inr (.inl .restore)))
    (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
      (fun q => labels (.inr (.inr q))) none)
    target (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
    (atLabels (.inr (.inl .restore))) (afterD output base m) n suffixV
    wordV' scratchEmpty' ambient none
  simp only [Nat.one_mul, Nat.add_zero] at hv
  have copied : Function.update (afterD output base m) output
      (encodeWord n ++ afterD output base m output) = afterHeaders output base n m := by
    simp only [afterD, afterHeaders, Function.update_self, Function.update_idem,
      encodeWords, List.append_nil, List.append_assoc]
  rw [copied] at hv
  have cleaned := MachineDrainMany.cleanupTrace enumeration output
    (fun q => labels (.inr (.inr q))) target (fun l => atLabels (.inr (.inr l)))
    (afterHeaders output base n m) ambient
  rw [afterHeaders_output] at cleaned
  have total := trace_trans _ (trace_trans _ hd hv) cleaned
  simpa only [steps, copySteps] using total

end BinPackingGames.Foundations.Complexity.PoweringMachineFinish

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineUnaryEqualityBit
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineUnaryEqualityBit

open Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

theorem equalityTrace (tape : Fin 6 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit l)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix : List Bool)
    (leftWord : base (tape 0) = encodeWord a ++ leftSuffix)
    (rightWord : base (tape 1) = encodeWord b ++ rightSuffix)
    (leftEmpty : base (tape 2) = []) (rightEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    (advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .seedLeft), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update base (tape 5) (bitEncoding (decide (a = b)) ++ base (tape 5))⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j :=
    fun h => hne (distinct h)
  let midLeft := Function.update base (tape 2) (encodeWord a)
  let midBoth := Function.update midLeft (tape 3) (encodeWord b)
  have leftRun : (advance (TM2.step program))^[copySteps a]
      (some ⟨some (labels .seedLeft), clean ambient, base⟩) =
      some ⟨some (labels .seedRight), clean ambient, midLeft⟩ := by
    simpa only [copySteps, clean, midLeft, Nat.one_mul, Nat.add_zero,
      leftEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 0) (tape 4) (tape 2)
        (hd 0 4 (by decide)) (hd 0 2 (by decide)) (hd 4 2 (by decide)) 1 0
        (labels .seedLeft) (labels .scanLeft) (labels .restoreLeft)
        (some (labels .seedRight)) program (atLabels .seedLeft)
        (atLabels .scanLeft) (atLabels .restoreLeft)
        base a leftSuffix leftWord scratchEmpty (ambient, false, none) none
  have rightSource : midLeft (tape 1) = encodeWord b ++ rightSuffix := by
    simpa [midLeft, hd 1 2 (by decide)] using rightWord
  have scratchAfterLeft : midLeft (tape 4) = [] := by
    simpa [midLeft, hd 4 2 (by decide)] using scratchEmpty
  have rightCopyAfterLeft : midLeft (tape 3) = [] := by
    simpa [midLeft, hd 3 2 (by decide)] using rightEmpty
  have rightRun : (advance (TM2.step program))^[copySteps b]
      (some ⟨some (labels .seedRight), clean ambient, midLeft⟩) =
      some ⟨some (labels .compare), clean ambient, midBoth⟩ := by
    simpa only [copySteps, clean, midBoth, Nat.one_mul, Nat.add_zero,
      rightCopyAfterLeft, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 1) (tape 4) (tape 3)
        (hd 1 4 (by decide)) (hd 1 3 (by decide)) (hd 4 3 (by decide)) 1 0
        (labels .seedRight) (labels .scanRight) (labels .restoreRight)
        (some (labels .compare)) program (atLabels .seedRight)
        (atLabels .scanRight) (atLabels .restoreRight)
        midLeft b rightSuffix rightSource scratchAfterLeft (ambient, false, none) none
  have copyLeftWord : midBoth (tape 2) = encodeWord a := by
    simp [midBoth, midLeft, hd 2 3 (by decide)]
  have copyRightWord : midBoth (tape 3) = encodeWord b := by simp [midBoth]
  have restored : Reduction.MachineTransfer.tapesAt (tape 2) (tape 3) midBoth [] [] = base := by
    funext k
    by_cases hl : k = tape 2
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, midBoth, midLeft,
        hd 2 3 (by decide), leftEmpty]
    · by_cases hr : k = tape 3
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, midBoth, midLeft, rightEmpty]
      · simp [Reduction.MachineTransfer.tapesAt, midBoth, midLeft, hl, hr]
  let back := MachineStateEquiv.program (compareStateEquiv A).symm program
  have atCompare : back (labels .compare) =
      MachineCompare.loop (tape 2) (tape 3) (labels .compare)
        (some (labels .equal)) (some (labels .different)) := by
    change MachineStateEquiv.statement (compareStateEquiv A).symm
      (program (labels .compare)) = _
    rw [atLabels .compare]
    exact MachineStateEquiv.statement_symm_statement (compareStateEquiv A) _
  have backForward : MachineStateEquiv.program (compareStateEquiv A) back = program := by
    funext l
    change MachineStateEquiv.statement (compareStateEquiv A)
      (MachineStateEquiv.statement (compareStateEquiv A).symm (program l)) = program l
    simpa only [Equiv.symm_symm] using
      MachineStateEquiv.statement_symm_statement (compareStateEquiv A).symm (program l)
  have compareRun : (advance (TM2.step program))^[compareSteps a b]
      (some ⟨some (labels .compare), clean ambient, midBoth⟩) =
      some ⟨if a = b then some (labels .equal) else some (labels .different),
        clean ambient, base⟩ := by
    have native := MachineCompare.compareTrace_fromTapes (tape 2) (tape 3)
      (hd 2 3 (by decide)) (labels .compare) (some (labels .equal))
      (some (labels .different)) back atCompare midBoth ambient none none
    rw [copyLeftWord, copyRightWord, restored] at native
    simp only [encodeWord_eq_iff, encodeWord_length] at native
    have transported := MachineStateEquiv.trace (compareStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa [MachineStateEquiv.configuration, compareStateEquiv, clean, compareSteps] using
      transported
  have emitRun : TM2.step program
      ⟨if a = b then some (labels .equal) else some (labels .different),
        clean ambient, base⟩ =
      some ⟨exit, clean ambient,
        Function.update base (tape 5) (bitEncoding (decide (a = b)) ++ base (tape 5))⟩ := by
    by_cases heq : a = b
    · simpa only [heq, ite_true, if_true, decide_true] using
        emit_step (tape 5) true exit program (labels .equal) (atLabels .equal)
          (clean ambient) base
    · simpa only [heq, ite_false, decide_false] using
        emit_step (tape 5) false exit program (labels .different) (atLabels .different)
          (clean ambient) base
  have copied := joinTrace leftRun rightRun
  have compared := joinTrace copied compareRun
  rw [steps, Function.iterate_succ_apply', compared, advance_some]
  exact emitRun

end BinPackingGames.Foundations.Complexity.MachineUnaryEqualityBit

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringMasterState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.PoweringMasterState

open Turing
open MachineFixedBlockMap

section Row

variable {K Λ : Type} [DecidableEq K] {N M : Nat}

def encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master N) :=
  MachineStateEquiv.statement (rowEquiv N).symm
    (PoweringMachineRow.encodedBlockAt src dst F exit)

theorem stepAux_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : Master N) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockAt src dst F exit) state tapes =
      { l := exit, var := clearBuffer state,
        stk := Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  rw [encodedBlockAt, MachineStateEquiv.stepAux_transport_symm, Equiv.symm_symm]
  rw [PoweringMachineRow.stepAux_encodedBlockAt src dst F exit hne bits suffix
    (rowEquiv N state) tapes hinput]
  rfl

theorem step_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Master N))
    (label : Λ) (atLabel : program label = encodedBlockAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : Master N) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program ⟨some label, state, tapes⟩ =
      some ⟨exit, clearBuffer state,
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (F bits)) ++ tapes dst)⟩ := by
  simp only [TM2.step, atLabel, stepAux_encodedBlockAt src dst F exit hne bits suffix state tapes hinput]

def rowAt {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master (PoweringMachineRow.inputSize t S)) :=
  encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit

theorem step_rowAt_clean {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ
      (Master (PoweringMachineRow.inputSize t S)))
    (label : Λ) (atLabel : program label = rowAt (t := t) src dst labelAt exit)
    (hne : src ≠ dst) (bits register : Buffer (PoweringMachineRow.inputSize t S))
    (suffix : List Bool) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program ⟨some label, withBuffer register, tapes⟩ =
      some ⟨exit, clean (PoweringMachineRow.inputSize t S),
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (PoweringMachineRow.rowBlock labelAt bits)) ++
            tapes dst)⟩ := by
  simpa only [rowAt, clearBuffer_withBuffer] using
    step_encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit
      program label atLabel hne bits suffix (withBuffer register) tapes hinput

end Row

end BinPackingGames.Foundations.Complexity.PoweringMasterState

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineCeilingPower
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open BinPackingGames.Foundations.PCP

variable {σ : Type}

theorem paddingOutput_bounds (k : Nat) :
    PreprocessingLevels.boundedLevel k ≤ k ∧
      k ≤ PreprocessingLevels.paddedSize k ∧
      PreprocessingLevels.paddedSize k ≤ ExpanderFamily.growth * (k + 1) := by
  refine ⟨PreprocessingLevels.boundedLevel_le_input k, PreprocessingLevels.le_paddedSize k, ?_⟩
  by_cases hk : k = 0
  · subst k
    simpa using ExpanderFamily.growth_gt_one.le
  · exact (PreprocessingLevels.paddedSize_bounds (Nat.pos_of_ne_zero hk)).2.trans
      (Nat.mul_le_mul_left ExpanderFamily.growth (Nat.le_succ k))

end BinPackingGames.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineCloudRank
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

theorem rankProgram_skip {i : Nat} (hi : i < 4097) :
    rankProgram (σ := σ) (rankSkip i) =
      MachineLookup.discard .work (rankSkip i) (rankSkip (i + 1)) := by
  simp only [rankSkip, dite_eq_left hi, rankProgram]

theorem rowGuard_succ (original work target scratch count fuelSuffix : List Bool)
    (k : Nat) (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (rankProgram (σ := σ))
      ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord (k + 1) ++ fuelSuffix)⟩ =
      some ⟨some .field, ((ambient, flag), none),
        memory original work target scratch count (encodeWord k ++ fuelSuffix)⟩ := by
  change some (TM2.stepAux (rankProgram .row) _ _) = _
  simp [rankProgram, MachineUnaryCounter.guard, TM2.stepAux, encodeWord,
    List.replicate_succ]

theorem rowGuard_zero (original work target scratch count fuelSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step (rankProgram (σ := σ))
      ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ =
      some ⟨some .done, ((ambient, flag), none),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ := rfl

theorem zeroRowsTrace (original work target scratch count fuelSuffix : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[2]
      (some ⟨some .row, ((ambient, flag), register),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, flag), none),
        memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩ := by
  rw [Function.iterate_succ_apply]
  change advance (TM2.step (rankProgram (σ := σ)))
    (TM2.step rankProgram ⟨some .row, ((ambient, flag), register),
      memory original work target scratch count (encodeWord 0 ++ fuelSuffix)⟩) = _
  rw [rowGuard_zero]
  rfl

theorem rankRowTrace (r : Row) (hwidth : r.2.length = 4097) (v k : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rowTime v r]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
          [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) =
      some ⟨some .row, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if r.1 = v then 1 else 0) true ++ count)
          (encodeWord k ++ fuelSuffix)⟩ := by
  have hfield := preservingFieldTrace RankLabel.field RankLabel.restore (rankSkip 0)
    rankProgram rfl rfl original (encodeWords r.2 ++ suffix) targetSuffix count
    (encodeWord k ++ fuelSuffix) r.1 v ambient none
  have hskip := discardFieldsTrace rankSkip (rankProgram (σ := σ)) r.2 0
    (by intro i hi; simpa only [Nat.zero_add] using rankProgram_skip (hwidth ▸ hi))
    original suffix (encodeWord v ++ targetSuffix) []
    (List.replicate (if r.1 = v then 1 else 0) true ++ count)
    (encodeWord k ++ fuelSuffix) ambient false none
  have hnonempty : r.2 ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, rankSkip, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at hskip
  have htime : rowTime v r = (encodeWords r.2).length + (r.1 + min r.1 v + 2) + 1 := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [htime, Function.iterate_succ_apply]
  change (advance (TM2.step (rankProgram (σ := σ))))^[
      (encodeWords r.2).length + (r.1 + min r.1 v + 2)]
    (TM2.step rankProgram ⟨some .row, ((ambient, false), register),
      memory original (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix)
        [] count (encodeWord (k + 1) ++ fuelSuffix)⟩) = _
  rw [rowGuard_succ, Function.iterate_add_apply]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hfield]
  exact hskip

theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097) (v : Nat)
    (original suffix targetSuffix fuelSuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[prefixTime v rs]
      (some ⟨some .row, ((ambient, false), register),
        memory original (encodeWords (rs.flatMap rowWords) ++ suffix)
          (encodeWord v ++ targetSuffix) [] count (encodeWord rs.length ++ fuelSuffix)⟩) =
      some ⟨none, ((ambient, false), none),
        memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (rowsHits v rs) true ++ count) (encodeWord 0 ++ fuelSuffix)⟩ := by
  induction rs generalizing count register with
  | nil =>
      simpa only [prefixTime, List.flatMap_nil, encodeWords, List.nil_append,
        List.length_nil, rowsHits, List.replicate_zero] using
        zeroRowsTrace original suffix (encodeWord v ++ targetSuffix) [] count fuelSuffix
          ambient false register
  | cons r rs ih =>
      have hrow := rankRowTrace r (hwidth r (by simp)) v rs.length original
        (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix fuelSuffix count ambient register
      have hrest := ih (by intro x hx; exact hwidth x (by simp [hx]))
        (List.replicate (if r.1 = v then 1 else 0) true ++ count) none
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc,
        List.length_cons]
      rw [Function.iterate_add_apply, hrow]
      simpa only [rowsHits, ← List.append_assoc, List.replicate_append_replicate,
        Nat.add_comm] using hrest

theorem rankTrace (n m v k : Nat) (rs : List Row) (hk : k ≤ rs.length)
    (hwidth : ∀ r ∈ rs, r.2.length = 4097) (querySuffix count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (rankProgram (σ := σ))))^[rankSteps n m v k rs querySuffix]
      (some ⟨some .queryFirst, ((ambient, false), register),
        memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count []⟩) =
      some ⟨none, ((ambient, false), none),
        memory (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
          (queryWord v k querySuffix) []
          (List.replicate (rowsHits v (rs.take k)) true ++ count)
          (encodeWord 0 ++ querySuffix)⟩ := by
  have hquery := MachineCopy.copyTrace Tape.target Tape.spare Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.queryFirst RankLabel.querySecond
    (some RankLabel.querySkip) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count [])
    rfl (ambient, false) register
  simp only [memory_target, memory_spare, List.append_nil, update_memory_spare] at hquery
  have hquerySkip := MachineLookup.discardTrace Tape.spare RankLabel.querySkip RankLabel.tableFirst
    rankProgram rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count (queryWord v k querySuffix))
    v (encodeWord k ++ querySuffix) rfl (ambient, false) none
  simp only [update_memory_spare] at hquerySkip
  have hcopy := MachineCopy.copyTrace Tape.original Tape.work Tape.scratch
    (by decide) (by decide) (by decide) false RankLabel.tableFirst RankLabel.tableSecond
    (some RankLabel.headerFirst) rankProgram rfl rfl
    (memory (inputWord n m rs) [] (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix)) rfl (ambient, false) none
  simp only [memory_original, memory_work, List.append_nil, update_memory_work] at hcopy
  have hfirst := MachineLookup.discardTrace Tape.work RankLabel.headerFirst RankLabel.headerSecond
    rankProgram rfl
    (memory (inputWord n m rs) (inputWord n m rs) (queryWord v k querySuffix) [] count
      (encodeWord k ++ querySuffix))
    n (encodeWord m ++ encodeWords (rs.flatMap rowWords))
    (inputWord_eq n m rs) (ambient, false) none
  simp only [update_memory_work] at hfirst
  have hsecond := MachineLookup.discardTrace Tape.work RankLabel.headerSecond RankLabel.row
    rankProgram rfl
    (memory (inputWord n m rs) (encodeWord m ++ encodeWords (rs.flatMap rowWords))
      (queryWord v k querySuffix) [] count (encodeWord k ++ querySuffix))
    m (encodeWords (rs.flatMap rowWords)) rfl (ambient, false) none
  simp only [update_memory_work] at hsecond
  have hprefix := prefixTrace (rs.take k)
    (by intro r hr; exact hwidth r (List.mem_of_mem_take hr)) v
    (inputWord n m rs) (encodeWords ((rs.drop k).flatMap rowWords))
    (encodeWord k ++ querySuffix) querySuffix count ambient none
  have htake : (rs.take k).length = k := by
    simp only [List.length_take, Nat.min_eq_left hk]
  rw [htake, ← encoded_rows_split rs k] at hprefix
  rw [show rankSteps n m v k rs querySuffix = prefixTime v (rs.take k) +
      ((m + 1) + ((n + 1) + (2 * ((inputWord n m rs).length + 1) +
        ((v + 1) + 2 * ((queryWord v k querySuffix).length + 1))))) by
      unfold rankSteps; omega,
    Function.iterate_add_apply _ (prefixTime v (rs.take k)),
    Function.iterate_add_apply _ (m + 1), Function.iterate_add_apply _ (n + 1),
    Function.iterate_add_apply _ (2 * ((inputWord n m rs).length + 1)),
    Function.iterate_add_apply _ (v + 1), hquery, hquerySkip, hcopy, hfirst, hsecond]
  exact hprefix

open BinPackingGames.Foundations.PCP

end BinPackingGames.Foundations.Complexity.MachineCloudRank

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularDummyRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachinePaddingRows

open Turing MachineComposition

def extra (d : Nat) (hd : 0 < d) : Control → TM2.Stmt Alphabet (Label d) State
  | .initialize_ => Reduction.MachineSubstitution.pushWord (.inl 2)
      MachineDummyRows.trueBits.reverse
      (.load (fun _ => (((), none), ())) (.goto (fun _ => .inr .guard)))
  | .guard => .pop (.inr ()) (fun _ bit => (((), bit), ()))
      (.branch (fun s => s.1.2.getD false)
        (.load (fun _ => (((), none), ())) (.goto (fun _ => bodyEntry d hd)))
        (.push (.inr ()) (fun _ => false)
          (.load (fun _ => (((), none), ())) .halt)))
  | .bump => .push (.inl 0) (fun _ => true) (.goto (fun _ => .inr .guard))

def program (d : Nat) (hd : 0 < d) : Label d → TM2.Stmt Alphabet (Label d) State :=
  MachineEmbedding.program (some (.inr .bump)) (MachineDummyRows.program d) (extra d hd)

def machine (d : Nat) (hd : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .inl 0
  k₁ := .inl 4
  Γ := Alphabet
  Λ := Label d
  main := .inr .initialize_
  σ := State
  initialState := (((), none), ())
  m := program d hd

end BinPackingGames.Foundations.Complexity.MachinePaddingRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PreprocessingGuarantees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def output (H : BaseTable) (t : GraphTables.Table) : PortTables.Input degree :=
  ⟨vertices t, preprocess H t⟩

end BinPackingGames.Foundations.PCP.PreprocessingTables

namespace BinPackingGames.Foundations.PCP.PreprocessingStageMaps
open PreprocessingRegularTables

def regular (H : BaseTable) (t : GraphTables.Table) : PortTables.Input (internalDegree + 1) :=
  ⟨vertexCount t (PreprocessingRegularTables.padding t), regularize H t⟩

def padding (d : Nat) (input : PortTables.Input d) : PortTables.Input d :=
  ⟨PreprocessingLevels.paddedSize input.1,
    PreprocessingPaddingTables.pad input.2 (PreprocessingLevels.le_paddedSize input.1)⟩

def familyAt (H : BaseTable) (n : Nat) :
    ExpanderTables.Table (PreprocessingLevels.paddedSize n) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize n)
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel n))

def paddedOverlay (H : BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (d + internalDegree) :=
  ⟨PreprocessingLevels.paddedSize input.1,
    PreprocessingOverlayTables.overlay (padding d input).2 (familyAt H input.1)⟩

end BinPackingGames.Foundations.PCP.PreprocessingStageMaps

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineCloudPrefix
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
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

theorem incrementStep (table bound remaining total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .increment, ((ambient, false), register),
        frame table (encodeWord v) [] (encodeWord 0) [] bound remaining total⟩ =
      some ⟨some .guard, ((ambient, false), none),
        frame table (encodeWord (v + 1)) [] [] [] bound remaining total⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord, List.replicate_succ]

theorem guardStep_succ (table bound suffix total : List Bool) (v n : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord (n + 1) ++ suffix) total⟩ =
      some ⟨some (.padding .init), ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord n ++ suffix) total⟩ := by
  simp [TM2.step, program, MachineUnaryCounter.guard, TM2.stepAux, encodeWord,
    List.replicate_succ]

theorem guardStep_zero (table bound suffix total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ =
      some ⟨some .done, ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ := rfl

theorem zeroTrace (table bound suffix total : List Bool) (v : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[2]
      (some ⟨some .guard, ((ambient, false), register),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩) =
      some ⟨none, ((ambient, false), none),
        frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩ := by
  rw [Function.iterate_succ_apply]
  change advance (TM2.step (program (σ := σ)))
    (TM2.step program ⟨some .guard, ((ambient, false), register),
      frame table (encodeWord v) [] [] [] bound (encodeWord 0 ++ suffix) total⟩) = _
  rw [guardStep_zero]
  rfl

theorem sumFrom_list (t : GraphTables.Table) (xs : List (Fin t.vertices)) (v : Nat)
    (hseq : ∀ i (hi : i < xs.length), (xs[i]).val = v + i) :
    sumFrom t v xs.length = (xs.map (PreprocessingRegularTables.padding t)).sum := by
  induction xs generalizing v with
  | nil => simp [sumFrom]
  | cons x xs ih =>
      have hx : x.val = v := by
        simpa only [List.getElem_cons_zero, Nat.add_zero] using! hseq 0 (by simp)
      have hv : v < t.vertices := by simpa only [hx] using x.isLt
      have he : (⟨v, hv⟩ : Fin t.vertices) = x := Fin.ext hx.symm
      have hnext : ∀ i (hi : i < xs.length), (xs[i]).val = v + 1 + i := by
        intro i hi
        have h := hseq (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using h
      simp only [List.length_cons, sumFrom, amount, dite_eq_left hv, he,
        List.map_cons, List.sum_cons]
      rw [ih (v + 1) hnext]
      rfl

theorem sumFrom_eq_offset (t : GraphTables.Table) (b : Nat) (hb : b ≤ t.vertices) :
    sumFrom t 0 b =
      PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) b := by
  have h := sumFrom_list t ((List.finRange t.vertices).take b) 0
    (by intro i hi; simp only [List.getElem_take, List.getElem_finRange, Fin.val_cast,
      Nat.zero_add])
  simpa only [List.length_take, List.length_finRange, Nat.min_eq_left hb,
    PreprocessingPaddingOffsets.offset] using h

theorem initStep (table bound : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step (program (σ := σ))
      ⟨some .init, ((ambient, false), register), frame table [] [] [] [] bound [] []⟩ =
      some ⟨some .copyFirst, ((ambient, false), register),
        frame table (encodeWord 0) [] [] [] bound [] (encodeWord 0)⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

end BinPackingGames.Foundations.Complexity.MachineCloudPrefix

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachinePortReindex
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachinePortReindex

open Turing MachineComposition
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

theorem reindexTrace (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A d))
    (atLabels : ∀ l, program (labels l) = instruction d positive c b tape labels exit l)
    (base : K → List Bool) (j : Nat) (suffix : List Bool)
    (sourceWord : base (tape 0) = encodeWord j ++ suffix)
    (scratchEmpty : base (tape 1) = []) (workEmpty : base (tape 2) = [])
    (quotientEmpty : base (tape 3) = []) (ambient : A) :
    (advance (TM2.step program))^[steps d j]
      (some ⟨some (labels .copySeed), clean d positive ambient, base⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
  have hd (i k : Fin 5) (h : i ≠ k) : tape i ≠ tape k := fun e => h (distinct e)
  let q := j / d
  let r := MachineFixedDivMod.residue d positive j
  let copied := Function.update base (tape 2) (encodeWord j)
  let initialized := frame tape base (encodeWord j) (encodeWord 0)
    (encodeWord 0 ++ base (tape 4))
  let divided := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord 0 ++ base (tape 4))
  let emitted := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord (r.val + b) ++ base (tape 4))
  let computed := frame tape base (encodeWord 0) (encodeWord q)
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  let drained := frame tape base (encodeWord 0) []
    (encodeWord (c * q + (r.val + b)) ++ base (tape 4))
  have copyRun : (advance (TM2.step program))^[2 * (j + 1) + 1]
      (some ⟨some (labels .copySeed), clean d positive ambient, base⟩) =
      some ⟨some (labels .initialize_), clean d positive ambient, copied⟩ := by
    simpa only [clean, copied, Nat.one_mul, Nat.add_zero, workEmpty, List.append_nil] using
      MachineUnaryAffineAt.seededAffineTrace (tape 0) (tape 1) (tape 2)
        (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide)) 1 0
        (labels .copySeed) (labels .copyScan) (labels .copyRestore)
        (some (labels .initialize_)) program (atLabels .copySeed) (atLabels .copyScan)
        (atLabels .copyRestore) base j suffix sourceWord scratchEmpty
        (ambient, MachineFixedDivMod.residue d positive 0) none
  have initRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize_), clean d positive ambient, copied⟩) =
      some ⟨some (labels .divide), clean d positive ambient, initialized⟩ := by
    change some (TM2.stepAux (program (labels .initialize_)) _ _) = _
    rw [atLabels]
    simp [instruction, TM2.stepAux, copied, initialized, frame, MachineCopy.forkTapes,
      hd 3 2 (by decide), hd 4 2 (by decide), hd 4 3 (by decide), quotientEmpty, encodeWord]
  have divisionInput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base j 0 0 [] [] (base (tape 4)) = initialized := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, initialized, frame]
  have divisionOutput : MachineFixedDivMod.unaryTapes (tape 2) (tape 3) (tape 4)
      base 0 q 0 [] [] (base (tape 4)) = divided := by
    simp only [MachineFixedDivMod.unaryTapes, MachineFixedDivMod.tapes,
      List.append_nil, divided, frame]
  have divideRun : (advance (TM2.step program))^[j + 1]
      (some ⟨some (labels .divide), clean d positive ambient, initialized⟩) =
      some ⟨some (labels (.emit r)), ((ambient, r), some false), divided⟩ := by
    have h := MachineFixedDivMod.scanTrace_fromCount d positive (tape 2) (tape 3) (tape 4)
      (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide))
      (labels .divide) (fun a => labels (.emit a)) program (atLabels .divide)
      base j 0 [] [] (base (tape 4)) ambient none
    simpa only [Nat.zero_div, Nat.zero_add, divisionInput, divisionOutput, clean, r, q] using h
  have emitRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels (.emit r)), ((ambient, r), some false), divided⟩) =
      some ⟨some (labels .affineScan), clean d positive ambient, emitted⟩ := by
    change some (TM2.stepAux (program (labels (.emit r))) _ _) = _
    rw [atLabels]
    simp [instruction, emit, stepAux_pushWord, TM2.stepAux, divided, emitted, frame,
      MachineCopy.forkTapes, List.reverse_replicate, encodeWord, List.append_assoc]
  have affineInput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (r.val + b) ++ base (tape 4)) = emitted := by
    have heq : emitted (tape 3) = encodeWord q := by
      simp [emitted, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
    have hempty : emitted (tape 1) = [] := by
      simp [emitted, frame, MachineCopy.forkTapes, hd 1 2 (by decide),
        hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    have hout : emitted (tape 4) = encodeWord (r.val + b) ++ base (tape 4) := by
      simp [emitted, frame, MachineCopy.forkTapes]
    rw [List.append_nil, ← heq, ← hempty, ← hout]
    exact MachineCopy.forkTapes_self _ _ _ _
  have affineOutput : MachineUnaryAffineAt.tapes (tape 3) (tape 1) (tape 4)
      emitted (encodeWord q ++ []) [] (encodeWord (c * q + (r.val + b)) ++ base (tape 4)) =
      computed := by
    funext k
    by_cases h1 : k = tape 1
    · subst k
      simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
        hd 1 2 (by decide), hd 1 3 (by decide), hd 1 4 (by decide), scratchEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
          hd 3 1 (by decide), hd 3 4 (by decide)]
      · by_cases h4 : k = tape 4
        · subst k; simp [MachineUnaryAffineAt.tapes, computed, frame, MachineCopy.forkTapes]
        · simp [MachineUnaryAffineAt.tapes, emitted, computed, frame, MachineCopy.forkTapes,
            h1, h3, h4]
  have affineRun : (advance (TM2.step program))^[2 * (q + 1)]
      (some ⟨some (labels .affineScan), clean d positive ambient, emitted⟩) =
      some ⟨some (labels .drainQuotient), clean d positive ambient, computed⟩ := by
    have h := MachineUnaryAffineAt.affineTrace (tape 3) (tape 1) (tape 4)
      (hd 3 1 (by decide)) (hd 3 4 (by decide)) (hd 1 4 (by decide)) c
      (labels .affineScan) (labels .affineRestore) (some (labels .drainQuotient))
      program (atLabels .affineScan) (atLabels .affineRestore) emitted q (r.val + b)
      [] (base (tape 4)) (ambient, MachineFixedDivMod.residue d positive 0) none
    simpa only [affineInput, affineOutput, clean] using h
  have quotientWord : computed (tape 3) = encodeWord q := by
    simp [computed, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
  have drainOutput : Function.update computed (tape 3) [] = drained := by
    funext k
    by_cases h3 : k = tape 3
    · subst k
      simp [drained, frame, MachineCopy.forkTapes, hd 3 4 (by decide)]
    · by_cases h4 : k = tape 4
      · subst k
        simp [computed, drained, frame, MachineCopy.forkTapes, hd 4 3 (by decide)]
      · simp [computed, drained, frame, MachineCopy.forkTapes, h3, h4]
  have drainRun : (advance (TM2.step program))^[q + 2]
      (some ⟨some (labels .drainQuotient), clean d positive ambient, computed⟩) =
      some ⟨some (labels .finish), clean d positive ambient, drained⟩ := by
    have h := MachineDrain.drainTrace (tape 3) (labels .drainQuotient)
      (some (labels .finish)) program (atLabels .drainQuotient)
      computed (computed (tape 3)) (ambient, MachineFixedDivMod.residue d positive 0) none
    rw [Function.update_eq_self, drainOutput, quotientWord, encodeWord_length] at h
    exact h
  have finishOutput : Function.update drained (tape 2) [] =
      Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4)) := by
    have hv : c * q + (r.val + b) = value d c b j := by
      simp [value, q, r, MachineFixedDivMod.residue, Nat.add_assoc]
    funext k
    by_cases h2 : k = tape 2
    · subst k
      simp [hd 2 4 (by decide), workEmpty]
    · by_cases h3 : k = tape 3
      · subst k
        simp [drained, frame, MachineCopy.forkTapes, hd 3 2 (by decide),
          hd 3 4 (by decide), quotientEmpty]
      · by_cases h4 : k = tape 4
        · subst k
          simp [drained, frame, MachineCopy.forkTapes, hd 4 2 (by decide), hv]
        · simp [drained, frame, MachineCopy.forkTapes, h2, h3, h4]
  have finishRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean d positive ambient, drained⟩) =
      some ⟨exit, clean d positive ambient,
        Function.update base (tape 4) (encodeWord (value d c b j) ++ base (tape 4))⟩ := by
    have hw : drained (tape 2) = encodeWord 0 := by
      simp [drained, frame, MachineCopy.forkTapes, hd 2 3 (by decide), hd 2 4 (by decide)]
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels]
    cases exit <;> simp [instruction, TM2.stepAux, exitAt, hw, encodeWord, finishOutput, clean]
  have total := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace copyRun initRun) divideRun) emitRun) affineRun) drainRun) finishRun
  have hsteps : steps d j =
      (((((2 * (j + 1) + 1) + 1) + (j + 1)) + 1) + 2 * (q + 1)) + (q + 2) + 1 := by
    dsimp [steps, q]
    omega
  rw [hsteps]
  exact total

end BinPackingGames.Foundations.Complexity.MachinePortReindex

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PoweringTableSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

def outputBits {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) : List Bool :=
  GenericGraphTables.tableBits (table input n)

end BinPackingGames.Foundations.PCP.PoweringTables

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringGlobalEnumeration
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRotor

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def instruction (tape : Fin 7 → K) (degree port : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .reverse l => MachineAffineLookup.instruction (tape 1) (reverseTapes tape)
      (4098 * degree) (4098 * port + 3) (fun q => labels (.reverse q))
      (some (labels (.endpoint .seed))) l
  | .endpoint l => MachineAffineLookup.instruction (tape 4) (endpointTapes tape)
      4098 2 (fun q => labels (.endpoint q)) exit l

end BinPackingGames.Foundations.Complexity.PoweringMachineRotor

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRelation

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def instruction (source : K) (tape : Fin 5 → K) (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ) :
    MachineAffineLookup.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineAffineLookup.instruction source tape (4098 * d)
    (4098 * port.val + 4 + position.val) labels exit

end BinPackingGames.Foundations.Complexity.PoweringMachineRelation

namespace BinPackingGames.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def instruction : (t : Nat) → (Tape t → K) → (Fin t → Fin d) →
    (Label t → Λ) → Option Λ → Label t →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, placement, _, labels, exit =>
      copyInstruction (placement (.inr (first 0))) (placement (.inl 4))
        (placement (.inl 5)) labels exit
  | t + 1, placement, ports, labels, exit => fun l =>
      match l with
      | .inl q => PoweringMachineRotor.instruction (placement ∘ rotorRole t) d (ports 0).val
          (fun z => labels (.inl z)) (some (labels (.inr (entry t)))) q
      | .inr q => instruction t (placement ∘ shift t) (fun j => ports j.succ)
          (fun z => labels (.inr z)) exit q

end BinPackingGames.Foundations.Complexity.PoweringMachineWord

namespace BinPackingGames.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop PoweringMasterState

def dropUnit (N : Nat) : (Master N × Unit) ≃ Master N where
  toFun := Prod.fst
  invFun state := (state, ())
  left_inv := by rintro ⟨state, ⟨⟩⟩; rfl
  right_inv := by intro state; rfl

def headerStatement (max N B : Nat) (label : HeaderLabel) :
    TM2.Stmt (fun _ : GlobalTape max => Bool) Label (Master N) :=
  MachineStateEquiv.statement (dropUnit N)
    (castStatement (boolAlphabet_eq max)
      (MachineEmbedding.statement (Λextra := MachineUnaryAffineAt.Label)
        (τ := Unit) none (headerProgram (σ := OtherRegisters N) B label)))

def headerConfiguration {max N : Nat} (extra : ExtraTape max → List Bool)
    (c : TM2.Cfg HeaderAlphabet HeaderLabel (Master N)) :
    TM2.Cfg (fun _ : GlobalTape max => Bool) Label (Master N) :=
  ⟨c.l.map Sum.inl, c.var, mergeTapes c.stk extra⟩

theorem headerConfiguration_eq {max N : Nat} (extra : ExtraTape max → List Bool)
    (c : TM2.Cfg HeaderAlphabet HeaderLabel (Master N)) :
    headerConfiguration extra c =
      MachineStateEquiv.configuration (dropUnit N)
        (castConfiguration (boolAlphabet_eq max)
          (MachineEmbedding.configuration (Λextra := MachineUnaryAffineAt.Label)
            none () extra c)) := by
  cases c with
  | mk label state tapes =>
    simp only [MachineEmbedding.configuration, castConfiguration_mk,
      MachineStateEquiv.configuration, castTapes_embedding, dropUnit,
      Equiv.coe_fn_mk, headerConfiguration]
    cases label <;> rfl

theorem stepAux_headerStatement (max N B : Nat) (label : HeaderLabel)
    (state : Master N) (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) :
    TM2.stepAux (headerStatement max N B label) state (mergeTapes header extra) =
      headerConfiguration extra (TM2.stepAux (headerProgram B label) state header) := by
  rw [headerStatement, MachineStateEquiv.stepAux_transport_symm]
  change MachineStateEquiv.configuration (dropUnit N)
    (TM2.stepAux (castStatement (boolAlphabet_eq max)
      (MachineEmbedding.statement none (headerProgram B label))) (state, ())
      (mergeTapes header extra)) = _
  rw [← castTapes_embedding, stepAux_cast, MachineEmbedding.stepAux_simulation]
  exact (headerConfiguration_eq extra _).symm

def program (max N B : Nat) : Label →
    TM2.Stmt (fun _ : GlobalTape max => Bool) Label (Master N)
  | .inl label => headerStatement max N B label
  | .inr .seed => MachineUnaryAffineAt.seed (.inl .source) 0 (.inr .scan)
  | .inr .scan => MachineUnaryAffineAt.scan
      (commonPlacement max (PoweringMachineTapes.table max))
      (commonPlacement max (PoweringMachineTapes.scratch max))
      (.inl .source) 1 (.inr .scan) (.inr .restore)
  | .inr .restore => Reduction.MachineTransfer.loopAt
      (commonPlacement max (PoweringMachineTapes.scratch max))
      (commonPlacement max (PoweringMachineTapes.table max))
      id false (.inr .restore) (some (.inl .initialize_))

theorem headerStep (max N B : Nat) (extra : ExtraTape max → List Bool)
    (a b : TM2.Cfg HeaderAlphabet HeaderLabel (Master N))
    (run : TM2.step (headerProgram B) a = some b) :
    TM2.step (program max N B) (headerConfiguration extra a) =
      some (headerConfiguration extra b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [TM2.step] at run
    | some label =>
      have hb : TM2.stepAux (headerProgram B label) state tapes = b := Option.some.inj run
      rw [← hb]
      change some (TM2.stepAux (headerStatement max N B label) state
        (mergeTapes tapes extra)) = _
      rw [stepAux_headerStatement]

theorem headerTrace (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (state : Master N) :
    (MachineComposition.advance (TM2.step (program max N B)))^[vertices + 2]
      (some ⟨some (.inl .initialize_), state,
        mergeTapes (initialTapes vertices []) extra⟩) =
      some ⟨none, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩ := by
  exact MachineComposition.liftSuccessfulTrace (TM2.step (headerProgram B))
    (TM2.step (program max N B)) (headerConfiguration extra)
    (headerStep max N B extra) (vertices + 2) _ _
    (PoweringMachineLoop.headerTrace B vertices [] state.1 state.2)

theorem copyFirstTrace (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    (MachineComposition.advance (TM2.step (program max N B)))^[2 * (vertices + 1) + 1]
      (some ⟨some (.inr .seed), state, initialGlobalTapes extra⟩) =
      some ⟨some (.inl .initialize_), (state.1, none),
        mergeTapes (initialTapes vertices []) extra⟩ := by
  have copied := MachineUnaryAffineAt.seededAffineTrace
    (commonPlacement max (PoweringMachineTapes.table max))
    (commonPlacement max (PoweringMachineTapes.scratch max)) (.inl HeaderTape.source)
    (by
      intro heq
      have hroles := commonPlacement_injective max heq
      simp [PoweringMachineTapes.table, PoweringMachineTapes.scratch] at hroles)
    (by simp) (by simp) 1 0 (.inr .seed) (.inr .scan) (.inr .restore)
    (some (.inl .initialize_)) (program max N B) rfl rfl rfl
    (initialGlobalTapes extra) vertices suffix
    (by simpa [initialGlobalTapes, mergeTapes] using input)
    (by simpa [initialGlobalTapes, mergeTapes] using scratch) state.1 state.2
  have handoff : Function.update (initialGlobalTapes extra) (.inl HeaderTape.source)
      (encodeWord (1 * vertices + 0) ++ initialGlobalTapes extra (.inl .source)) =
      mergeTapes (initialTapes vertices []) extra := by
    funext tape
    cases tape with
    | inl field => cases field <;> simp [initialGlobalTapes, mergeTapes, initialTapes]
    | inr field => simp [initialGlobalTapes, mergeTapes]
  rw [handoff] at copied
  exact copied

theorem initializeTrace (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    (MachineComposition.advance (TM2.step (program max N B)))^[3 * vertices + 5]
      (some ⟨some (.inr .seed), state, initialGlobalTapes extra⟩) =
      some ⟨none, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩ := by
  rw [show 3 * vertices + 5 = (vertices + 2) + (2 * (vertices + 1) + 1) by omega,
    Function.iterate_add_apply, copyFirstTrace max N B vertices extra suffix input scratch state]
  exact headerTrace max N B vertices extra (state.1, none)

def initializeInTime (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    StateTransition.EvalsToInTime (TM2.step (program max N B))
      ⟨some (.inr .seed), state, initialGlobalTapes extra⟩
      (some ⟨none, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩)
      (3 * vertices + 5) where
  steps := 3 * vertices + 5
  evals_in_steps := initializeTrace max N B vertices extra suffix input scratch state
  steps_le_m := Nat.le_refl _

def instruction {Λ : Type} (max N B : Nat) (labels : Label → Λ) (exit : Option Λ)
    (label : Label) : TM2.Stmt (fun _ : GlobalTape max => Bool) Λ (Master N) :=
  MachineSubroutine.statement labels exit (program max N B label)

def initializeAtInTime {Λ : Type} (max N B vertices : Nat)
    (labels : Label → Λ) (exit : Option Λ)
    (caller : Λ → TM2.Stmt (fun _ : GlobalTape max => Bool) Λ (Master N))
    (atLabels : ∀ label, caller (labels label) = instruction max N B labels exit label)
    (extra : ExtraTape max → List Bool) (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    StateTransition.EvalsToInTime (TM2.step caller)
      ⟨some (labels (.inr .seed)), state, initialGlobalTapes extra⟩
      (some ⟨exit, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩)
      (3 * vertices + 5) :=
  MachineSubroutine.execution labels exit (program max N B) caller atLabels
    (initializeInTime max N B vertices extra suffix input scratch state)

@[simp] theorem final_extra (max B vertices : Nat) (extra : ExtraTape max → List Bool)
    (tape : ExtraTape max) :
    mergeTapes (finalTapes B vertices []) extra (.inr tape) = extra tape := rfl

end BinPackingGames.Foundations.Complexity.PoweringMachineInitialize

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRelationField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

abbrev State (A : Type) := MachineUnaryEqualityBit.State A

omit [DecidableEq K] in
theorem source_outside_lookup (placement : PoweringMachineTapes.Tape max → K)
    (distinct : Function.Injective placement) :
    ∀ i, placement (.inl 6) ≠ lookupTapes placement i := by
  intro i h
  have heq : PoweringMachineTapes.relationPlacement max 0 = PoweringMachineTapes.relationPlacement max i.succ := by
    simpa [PoweringMachineTapes.leftEndpoint] using distinct h
  have hi := (PoweringMachineTapes.relationPlacement_injective max) heq
  have hv := congrArg Fin.val hi
  simp at hv

def instruction (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ) :
    Label path → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
      path.get (fun z => labels (.inl z)) (some (labels (.inr .seed))) q
  | .inr q => PoweringMachineRelation.instruction (placement (.inl 6)) (lookupTapes placement)
      port (GraphTables.relationIndex (left, right)) (fun z => labels (.inr z)) exit q

theorem afterWord_frame (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (role : Fin 11) (h₂ : role ≠ 2) (h₃ : role ≠ 3) (h₄ : role ≠ 4) (h₆ : role ≠ 6) :
    afterWord placement path lengthBound table vertex base (placement (.inl role)) =
      base (placement (.inl role)) := by
  apply PoweringMachineWord.finalTapes_other
  · intro h; exact h₂ (by simpa [PoweringMachineTapes.query] using distinct h)
  · intro h; exact h₃ (by simpa [PoweringMachineTapes.scan] using distinct h)
  · intro h; exact h₄ (by simpa [PoweringMachineTapes.reverse] using distinct h)
  · intro h; exact h₆ (by simpa [PoweringMachineTapes.leftEndpoint] using distinct h)
  · intro i h
    have heq := distinct h
    simp at heq

theorem finalTapes_frame (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (role : Fin 11) (h₂ : role ≠ 2) (h₃ : role ≠ 3) (h₄ : role ≠ 4)
    (h₆ : role ≠ 6) (h₁₀ : role ≠ 10) :
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl role)) =
      base (placement (.inl role)) := by
  calc
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl role)) =
        afterWord placement path lengthBound table vertex base (placement (.inl role)) := by
      apply MachineAffineLookup.finalTapes_other
      · intro h; exact h₂ (by simpa [lookupTapes, PoweringMachineTapes.query] using distinct h)
      · intro h; exact h₃ (by simpa [lookupTapes, PoweringMachineTapes.scan] using distinct h)
      · intro h; exact h₁₀ (by simpa [lookupTapes, PoweringMachineTapes.rowOutput] using distinct h)
    _ = _ := afterWord_frame placement distinct path lengthBound table vertex base role h₂ h₃ h₄ h₆

end BinPackingGames.Foundations.Complexity.PoweringMachineRelationField

namespace BinPackingGames.Foundations.Complexity.PoweringGlobalEnumeration

open PoweringMachineLoop PoweringMachineInitialize

def headerTapeEquiv : HeaderTape ≃ Fin 4 where
  toFun
    | .source => 0
    | .counter => 1
    | .vertices => 2
    | .darts => 3
  invFun i := if i = 0 then .source else if i = 1 then .counter
    else if i = 2 then .vertices else .darts
  left_inv tape := by cases tape <;> rfl
  right_inv i := by fin_cases i <;> rfl

def extraTapeEquiv (max : Nat) : ExtraTape max ≃ Fin (11 + max + 1) :=
  (Equiv.sumCongr (sharedTapeEquiv max) unitTapeEquiv).trans finSumFinEquiv

def globalTapeEquiv (max : Nat) : GlobalTape max ≃ Fin (4 + (11 + max + 1)) :=
  (Equiv.sumCongr headerTapeEquiv (extraTapeEquiv max)).trans finSumFinEquiv

def enumeration (max : Nat) : Fin (4 + (11 + max + 1)) ≃ GlobalTape max :=
  (globalTapeEquiv max).symm

@[simp] theorem globalTapeEquiv_enumeration (max : Nat) (i : Fin (4 + (11 + max + 1))) :
    globalTapeEquiv max (enumeration max i) = i :=
  (globalTapeEquiv max).apply_symm_apply i

@[simp] theorem enumeration_globalTapeEquiv (max : Nat) (tape : GlobalTape max) :
    enumeration max (globalTapeEquiv max tape) = tape :=
  (globalTapeEquiv max).symm_apply_apply tape

@[simp] theorem source_index (max : Nat) :
    (globalTapeEquiv max (.inl .source)).val = 0 := rfl

@[simp] theorem counter_index (max : Nat) :
    (globalTapeEquiv max (.inl .counter)).val = 1 := rfl

@[simp] theorem vertices_index (max : Nat) :
    (globalTapeEquiv max (.inl .vertices)).val = 2 := rfl

@[simp] theorem darts_index (max : Nat) :
    (globalTapeEquiv max (.inl .darts)).val = 3 := rfl

@[simp] theorem finalOutput_index (max : Nat) :
    (globalTapeEquiv max (finalOutput max)).val = 4 + (11 + max) := rfl

end BinPackingGames.Foundations.Complexity.PoweringGlobalEnumeration

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineLazyRows
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalRow

open Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

def zeroBuffer : Buffer := MachineFixedBlockMap.emptyBuffer 4096

theorem looked_relation (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    looked t e base 3 = encodeWords (relationWords t.rows[e].relation) ++
      (encodeWords (suffixWords t e) ++ base 3) := by
  change MachineLookup.tapes (2 : Tape) 3 4 base
    (encodeWord 0 ++ base 2)
    (encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 3 + 1)) ++ base 3)
    (encodeWord t.rows[e].reverseIndex.val ++ base 4) 3 = _
  rw [MachineLookup.tapes_source _ _ _ (by decide), remaining_relation, encodeWords_append]
  exact List.append_assoc _ _ _

theorem relationCopy_step {K Λ σ : Type} [DecidableEq K]
    (src dst : K) (hne : src ≠ dst) (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : program label = relationCopyAt src dst exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base src = encodeWords (relationWords relation) ++ suffix)
    (ambient : σ) (buffer : Buffer) (register : Option Bool) :
    TM2.step program ⟨some label, ((ambient, buffer), register), base⟩ =
      some ⟨exit, ((ambient, zeroBuffer), register),
        Function.update (Function.update base src suffix) dst
          (encodeWords (relationWords relation) ++ base dst)⟩ := by
  change some (TM2.stepAux (program label) _ base) = _
  rw [code]
  unfold relationCopyAt
  rw [MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (copyStateEquiv σ)
    (TM2.stepAux (PoweringMachineRow.encodedBlockAt src dst (id : Buffer → Buffer) exit)
      ((ambient, register), buffer) base)) = _
  have hinput : base src = PoweringMachineRow.encodeBits
      (List.ofFn (fun i : Fin 4096 => relation[i])) ++ suffix := by
    rw [relationBits_eq_encodedBlock]
    exact input
  rw [PoweringMachineRow.stepAux_encodedBlockAt src dst (id : Buffer → Buffer)
    exit hne (fun i : Fin 4096 => relation[i]) suffix
    ((ambient, register), buffer) base hinput]
  simp only [id_eq, relationBits_eq_encodedBlock, MachineStateEquiv.configuration,
    copyStateEquiv, zeroBuffer]
  rfl

section Execution

variable {Λ σ : Type}

theorem copyTrace (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (t : Table) (e : Fin t.darts) (base : Tape → List Bool) (ambient : σ) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .copyRelation), ((ambient, zeroBuffer), none), looked t e base⟩) =
      some ⟨some (labels .reverseSeed), ((ambient, zeroBuffer), none), copied t e base⟩ := by
  simp only [Function.iterate_one, advance_some]
  have run := relationCopy_step (3 : Tape) 7 (by decide) (labels .copyRelation)
    (some (labels .reverseSeed)) program (code .copyRelation) t.rows[e].relation
    (encodeWords (suffixWords t e) ++ base 3) (looked t e base) (looked_relation t e base)
    ambient zeroBuffer none
  rw [looked_other t e base 7 (by decide) (by decide) (by decide)] at run
  exact run

end Execution

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalRow

namespace BinPackingGames.Foundations.Complexity.MachineLazyRows

open Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

def reindexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State A d)
  | .inl stage => MachinePortReindex.instruction d positive c b
      (tape ∘ addressIndex) (fun stage => labels (.inl stage))
      (some (labels (.inr .relationRead))) stage
  | .inr stage => MachineTableRows.routine (fields tape) (tape 8) (tape 7) (tape 3)
      (fun stage => labels (.inr stage)) exit stage

def reindexRowBits (d c b v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord (MachinePortReindex.value d c b j) ++
    encodeWords (relationWords relation)

def reindexMappedTapes (d c b j : Nat) (tape : Fin 9 → K)
    (base : K → List Bool) : K → List Bool :=
  Function.update base (tape 6) (encodeWord (MachinePortReindex.value d c b j))

def reindexResultTapes (d c b v j : Nat) (relation : RelationTable)
    (tape : Fin 9 → K) (base : K → List Bool) : K → List Bool :=
  Function.update (reindexMappedTapes d c b j tape base) (tape 7)
    (base (tape 7) ++ reindexRowBits d c b v j relation)

def reindexSteps (d c b v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  MachinePortReindex.steps d j + 4 * (reindexRowBits d c b v j relation).length +
    2 * output.length + 9

def rowBits (d v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord (reverseMap d j) ++ encodeWords (relationWords relation)

theorem rowBits_eq_moveRow {n d : Nat} (table : PCP.PortTables.Table n d)
    (v : Fin n) (p : Fin d) :
    rowBits d v.val (PCP.PreprocessingLazyWords.row table v p).reverseIndex.val
        (PCP.PreprocessingLazyWords.row table v p).relation =
      encodeWords (rowWords (moveRow table v p)) := by
  rw [moveRow_words]
  simp [rowBits, encodeWords]

abbrev Buffer := MachineRegularOriginalRow.Buffer
abbrev StreamState (A : Type) (d : Nat) := State (A × Buffer) d

def streamClean (d : Nat) (positive : 0 < d) (ambient : A) : StreamState A d :=
  MachinePortReindex.clean d positive (ambient, MachineRegularOriginalRow.zeroBuffer)

def relationStateEquiv (A : Type) (d : Nat) :
    MachineRegularOriginalRow.State (A × Fin d) ≃ StreamState A d where
  toFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  invFun s := (((s.1.1.1, s.1.2), s.1.1.2), s.2)
  left_inv _ := rfl
  right_inv _ := rfl

def streamRelationCopy (d : Nat) (source destination : K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d) :=
  MachineStateEquiv.statement (relationStateEquiv A d)
    (MachineRegularOriginalRow.relationCopyAt source destination exit)

theorem streamRelationCopy_step (d : Nat) (positive : 0 < d)
    (source destination : K) (different : source ≠ destination)
    (label : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d))
    (code : program label = streamRelationCopy d source destination exit)
    (relation : RelationTable) (suffix : List Bool) (base : K → List Bool)
    (input : base source = encodeWords (relationWords relation) ++ suffix) (ambient : A) :
    TM2.step program ⟨some label, streamClean d positive ambient, base⟩ =
      some ⟨exit, streamClean d positive ambient,
        Function.update (Function.update base source suffix) destination
          (encodeWords (relationWords relation) ++ base destination)⟩ := by
  have hraw := MachineRegularOriginalRow.relationCopy_step source destination different label exit
    (fun _ => MachineRegularOriginalRow.relationCopyAt source destination exit) rfl
    relation suffix base input (ambient, MachineFixedDivMod.residue d positive 0)
    MachineRegularOriginalRow.zeroBuffer none
  have haux := Option.some.inj hraw
  change some (TM2.stepAux (program label) (streamClean d positive ambient) base) = _
  rw [code, streamRelationCopy, MachineStateEquiv.stepAux_transport_symm]
  change some (MachineStateEquiv.configuration (relationStateEquiv A d)
    (TM2.stepAux (MachineRegularOriginalRow.relationCopyAt source destination exit)
      (((ambient, MachineFixedDivMod.residue d positive 0),
        MachineRegularOriginalRow.zeroBuffer), none) base)) = _
  rw [haux]
  rfl

def streamInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : StreamLabel d → Λ) (exit : Option Λ) :
    StreamLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | .tailStart => Hastad.SourceMachine.fieldStart (tape 0) (labels .tailRead)
  | .tailRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 0) (labels .tailRead)
      (some (labels .reverseStart))
  | .reverseStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .reverseRead)
  | .reverseRead => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1) (labels .reverseRead)
      (some (labels .copyRelation))
  | .copyRelation => streamRelationCopy d (tape 9) (tape 2)
      (some (labels (.row (.inl .copySeed))))
  | .row stage => reindexInstruction d positive c b (tape ∘ bodyIndex)
      (fun stage => labels (.row stage)) (some (labels .clearTail)) stage
  | .clearTail => MachineDrain.drain (tape 0) (labels .clearTail) (some (labels .clearOld))
  | .clearOld => MachineDrain.drain (tape 1) (labels .clearOld) (some (labels .clearRelation))
  | .clearRelation => MachineDrain.drain (tape 2) (labels .clearRelation) (some (labels .clearNew))
  | .clearNew => MachineDrain.drain (tape 6) (labels .clearNew) exit

def inputRowBits (v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord j ++ encodeWords (relationWords relation)

def streamRowSteps (d c b v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  (v + 2) + (j + 2) + 1 + reindexSteps d c b v j relation output +
    (v + 2) + (j + 2) + ((encodeWords (relationWords relation)).length + 1) +
    (MachinePortReindex.value d c b j + 2)

def streamResultTapes (d c b v j : Nat) (relation : RelationTable)
    (tape : Fin 10 → K) (base : K → List Bool) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) suffix) (tape 7)
    (base (tape 7) ++ reindexRowBits d c b v j relation)

def vertexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 10 → K)
    (labels : VertexLabel d → Λ) (exit : Option Λ) :
    VertexLabel d → TM2.Stmt (fun _ : K => Bool) Λ (StreamState A d)
  | (i, none) => if i.val < d then .goto fun _ => labels (i, some .tailStart)
      else MachinePortReindex.exitAt exit
  | (i, some stage) => if h : i.val < d then
      streamInstruction d positive c b tape (fun stage => labels (i, some stage))
        (some (labels (⟨i.val + 1, by omega⟩, none))) stage
      else MachinePortReindex.exitAt exit

def recordsInput {n m : Nat} (rows : List (DartRow n m)) : List Bool :=
  rows.flatMap (fun r => inputRowBits r.tail.val r.reverseIndex.val r.relation)

def recordsOutput {n m : Nat} (d c b : Nat) (rows : List (DartRow n m)) : List Bool :=
  rows.flatMap (fun r => reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation)

def streamFrame {n m : Nat} (tape : Fin 10 → K) (base : K → List Bool)
    (rows : List (DartRow n m)) (output : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) (recordsInput rows ++ base (tape 9)))
    (tape 7) output

def vertexSteps {n m : Nat} (d c b : Nat) : List (DartRow n m) → List Bool → Nat
  | [], _ => 1
  | r :: rows, output => 1 + streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output +
      vertexSteps d c b rows
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation)

theorem recordsInput_eq_codec {n m : Nat} (rows : List (DartRow n m)) :
    recordsInput rows = encodeWords (rows.flatMap rowWords) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      simp only [recordsInput, List.flatMap_cons, encodeWords_append,
        MachineTableRows.rowBits_eq, inputRowBits] at ih ⊢
      rw [ih]

theorem streamFrame_afterRow {n m : Nat} (d c b : Nat) (r : DartRow n m)
    (tape : Fin 10 → K) (distinct : Function.Injective tape) (base : K → List Bool)
    (rows : List (DartRow n m)) (output : List Bool) :
    streamResultTapes d c b r.tail.val r.reverseIndex.val r.relation tape
      (streamFrame tape base (r :: rows) output) (recordsInput rows ++ base (tape 9)) =
      streamFrame tape base rows
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) := by
  have h79 : tape 7 ≠ tape 9 := fun h => (by decide : (7 : Fin 10) ≠ 9) (distinct h)
  funext k
  by_cases h7 : k = tape 7
  · subst k
    simp [streamResultTapes, streamFrame]
  · by_cases h9 : k = tape 9
    · subst k
      simp [streamResultTapes, streamFrame, Ne.symm h79]
    · simp [streamResultTapes, streamFrame, h7, h9]

theorem recordsOutput_lazy {n d : Nat} (table : PCP.PortTables.Table n d) (v : Fin n) :
    recordsOutput d (2 * d) d (List.ofFn (PCP.PreprocessingLazyWords.row table v)) =
      encodeWords ((List.ofFn (moveRow table v)).flatMap rowWords) := by
  rw [encodeWords_flatMap]
  simp only [recordsOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  change reindexRowBits d (2 * d) d v.val
      (PCP.PreprocessingLazyWords.row table v p).reverseIndex.val
      (PCP.PreprocessingLazyWords.row table v p).relation =
    encodeWords (rowWords (moveRow table v p))
  have h := rowBits_eq_moveRow table v p
  simpa only [rowBits, reindexRowBits, MachinePortReindex.lazy_value, reverseMap] using h

theorem reindexRowBits_length_le {n m : Nat} (d c b : Nat) (r : DartRow n m) :
    (reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation).length ≤
      rowSizeBound c b n m := by
  have htail := r.tail.isLt.le
  have hvalue := reindexValue_le d c b r
  have hrelation := relationBits_length_le r.relation
  simp only [reindexRowBits, List.length_append, encodeWord_length]
  unfold rowSizeBound
  omega

theorem streamRowSteps_le {n m : Nat} (d c b : Nat) (r : DartRow n m) (output : List Bool) :
    streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output ≤
      rowCostBound c b n m + 2 * output.length := by
  have htail := r.tail.isLt.le
  have hj := r.reverseIndex.isLt.le
  have hdiv := (Nat.div_le_self r.reverseIndex.val d).trans hj
  have hvalue := reindexValue_le d c b r
  have hrelation := relationBits_length_le r.relation
  have hsize := reindexRowBits_length_le d c b r
  unfold streamRowSteps reindexSteps MachinePortReindex.steps rowCostBound
  omega

theorem vertexSteps_le_capacity {n m : Nat} (d c b capacity : Nat)
    (rows : List (DartRow n m)) (output : List Bool)
    (room : output.length + rows.length * rowSizeBound c b n m ≤ capacity) :
    vertexSteps d c b rows output ≤
      rows.length * (rowCostBound c b n m + 2 * capacity + 1) + 1 := by
  induction rows generalizing output with
  | nil => simp [vertexSteps]
  | cons r rows ih =>
      have hsize := reindexRowBits_length_le d c b r
      have hcost := streamRowSteps_le d c b r output
      have hout : output.length ≤ capacity := by omega
      have hroom : (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation).length +
          rows.length * rowSizeBound c b n m ≤ capacity := by
        rw [List.length_append]
        simp only [List.length_cons, Nat.succ_mul] at room
        omega
      have htail := ih
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) hroom
      change 1 + streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output +
        vertexSteps d c b rows
          (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) ≤
        (rows.length + 1) * (rowCostBound c b n m + 2 * capacity + 1) + 1
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem vertexSteps_le {n m : Nat} (d c b : Nat) (rows : List (DartRow n m))
    (output : List Bool) :
    vertexSteps d c b rows output ≤ rows.length * (rowCostBound c b n m +
      2 * (output.length + rows.length * rowSizeBound c b n m) + 1) + 1 :=
  vertexSteps_le_capacity d c b _ rows output (Nat.le_refl _)

end BinPackingGames.Foundations.Complexity.MachineLazyRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineVertexPadding
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineTableSplit

open Turing MachineComposition

def program {σ : Type} : Label → TM2.Stmt (fun _ : Tape => Bool) Label (State σ)
  | .copyFirst => Reduction.MachineTransfer.loopAt 0 2 id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop 2 0 1 false .copySecond (some .startVertices)
  | .startVertices => Hastad.SourceMachine.fieldStart 3 .readVertices
  | .readVertices => Hastad.SourceMachine.fieldLoop 1 3 .readVertices (some .startDarts)
  | .startDarts => Hastad.SourceMachine.fieldStart 4 .readDarts
  | .readDarts => Hastad.SourceMachine.fieldLoop 1 4 .readDarts none

def exactSteps (n m : Nat) (rowsBits : List Bool) : Nat :=
  2 * (encodeWords [n, m] ++ rowsBits).length + n + m + 6

theorem splitTrace {σ : Type} (n m : Nat) (rowsBits : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[exactSteps n m rowsBits]
      (some ⟨some .copyFirst, (ambient, register),
        initialTapes (encodeWords [n, m] ++ rowsBits)⟩) =
      some ⟨none, (ambient, none), resultTapes n m rowsBits⟩ := by
  let word := encodeWords [n, m] ++ rowsBits
  let b₀ := initialTapes word
  let b₁ := tapes word word [] []
  let b₂ := tapes word (encodeWord m ++ rowsBits) (encodeWord n) []
  let b₃ := resultTapes n m rowsBits
  have h₀ : Function.update b₀ (1 : Tape) (b₀ 0 ++ b₀ 1) = b₁ := by
    funext k; fin_cases k <;> simp [b₀, b₁, initialTapes, tapes]
  have h₁ : Hastad.SourceMachine.fieldTapes (1 : Tape) 3 b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ 3) = b₂ := by
    funext k; fin_cases k <;> simp [b₁, b₂, tapes, Hastad.SourceMachine.fieldTapes]
  have h₂ : Hastad.SourceMachine.fieldTapes (1 : Tape) 4 b₂
      rowsBits (encodeWord m ++ b₂ 4) = b₃ := by
    funext k; fin_cases k <;>
      simp [b₂, b₃, resultTapes, tapes, word, Hastad.SourceMachine.fieldTapes]
  have copy := MachineCopy.copyTrace (0 : Tape) 1 2
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program (σ := σ)) rfl rfl b₀ (by simp [b₀, initialTapes, tapes]) ambient register
  rw [h₀] at copy
  have c₀ : (advance (TM2.step (program (σ := σ))))^[2 * (word.length + 1)]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨some .startVertices, (ambient, none), b₁⟩ := by
    simpa only [show b₀ 0 = word by simp [b₀, initialTapes, tapes]] using copy
  have scan₁ := (Hastad.SourceMachine.fieldInTime (1 : Tape) 3 (by decide)
    .startVertices .readVertices (some .startDarts) (program (σ := σ)) rfl rfl
    b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, tapes, word, encodeWords, List.append_assoc]) ambient none).evals_in_steps
  have c₁ : (advance (TM2.step (program (σ := σ))))^[n + 2]
      (some ⟨some .startVertices, (ambient, none), b₁⟩) =
        some ⟨some .startDarts, (ambient, none), b₂⟩ := by
    dsimp only [Hastad.SourceMachine.fieldInTime] at scan₁
    change (advance (TM2.step (program (σ := σ))))^[n + 2]
      (some ⟨some .startVertices, (ambient, none), b₁⟩) =
      some ⟨some .startDarts, (ambient, none),
        Hastad.SourceMachine.fieldTapes (1 : Tape) 3 b₁ (encodeWord m ++ rowsBits)
          (encodeWord n ++ b₁ 3)⟩ at scan₁
    simpa only [h₁] using scan₁
  have scan₂ := (Hastad.SourceMachine.fieldInTime (1 : Tape) 4 (by decide)
    .startDarts .readDarts none (program (σ := σ)) rfl rfl
    b₂ m rowsBits (by simp [b₂, tapes]) ambient none).evals_in_steps
  have c₂ : (advance (TM2.step (program (σ := σ))))^[m + 2]
      (some ⟨some .startDarts, (ambient, none), b₂⟩) =
        some ⟨none, (ambient, none), b₃⟩ := by
    dsimp only [Hastad.SourceMachine.fieldInTime] at scan₂
    change (advance (TM2.step (program (σ := σ))))^[m + 2]
      (some ⟨some .startDarts, (ambient, none), b₂⟩) =
      some ⟨none, (ambient, none),
        Hastad.SourceMachine.fieldTapes (1 : Tape) 4 b₂ rowsBits
          (encodeWord m ++ b₂ 4)⟩ at scan₂
    simpa only [h₂] using scan₂
  have c₀₁ : (advance (TM2.step (program (σ := σ))))^[(n + 2) + 2 * (word.length + 1)]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨some .startDarts, (ambient, none), b₂⟩ := by
    rw [Function.iterate_add_apply, c₀, c₁]
  have c₀₁₂ : (advance (TM2.step (program (σ := σ))))^[(m + 2) +
      ((n + 2) + 2 * (word.length + 1))]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨none, (ambient, none), b₃⟩ := by
    rw [Function.iterate_add_apply, c₀₁, c₂]
  have count : exactSteps n m rowsBits = (m + 2) + ((n + 2) + 2 * (word.length + 1)) := by
    dsimp [exactSteps, word]
    omega
  rw [count]
  exact c₀₁₂

theorem exactSteps_le (n m : Nat) (rowsBits : List Bool) :
    exactSteps n m rowsBits ≤ timePolynomial.eval (encodeWords [n, m] ++ rowsBits).length := by
  rw [timePolynomial_eval]
  simp only [exactSteps, List.length_append, encodeWords_length, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil]
  omega

def rowsBits (table : PCP.GraphTables.Table) : List Bool :=
  encodeWords ((PCP.GraphTables.rowList table).flatMap PCP.GraphTables.rowWords)

theorem tableBits_header_rows (table : PCP.GraphTables.Table) :
    PCP.GraphTables.tableBits table = encodeWords [table.vertices, table.darts] ++ rowsBits table := by
  simp only [PCP.GraphTables.tableBits, PCP.GraphTables.tableWords, encodeWords_append, rowsBits]

theorem tableTrace {σ : Type} (table : PCP.GraphTables.Table) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[exactSteps table.vertices table.darts (rowsBits table)]
      (some ⟨some .copyFirst, (ambient, register), initialTapes (PCP.GraphTables.tableBits table)⟩) =
      some ⟨none, (ambient, none), resultTapes table.vertices table.darts (rowsBits table)⟩ := by
  rw [tableBits_header_rows]
  exact splitTrace table.vertices table.darts (rowsBits table) ambient register

end BinPackingGames.Foundations.Complexity.MachineTableSplit

namespace BinPackingGames.Foundations.Complexity.MachinePaddingTable

open PCP MachinePaddingRows

def initialOutput {n d m : Nat} (table : PortTables.Table n d) : List Bool :=
  encodeWords [m, m * d] ++ PreprocessingPaddingWords.rowsBits table

end BinPackingGames.Foundations.Complexity.MachinePaddingTable

namespace BinPackingGames.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open BinPackingGames.Foundations.PCP
open MachineCloudPadding

def splitTape : MachineTableSplit.Tape → Tape := ![.original, .output, .scratch, .vertex, .edge]
def splitView : Tape → Option MachineTableSplit.Tape
  | .original => some 0
  | .output => some 1
  | .scratch => some 2
  | .vertex => some 3
  | .edge => some 4
  | _ => none

theorem splitView_left (k : MachineTableSplit.Tape) : splitView (splitTape k) = some k := by
  fin_cases k <;> rfl
theorem splitView_right (j : Tape) (k : MachineTableSplit.Tape)
    (h : splitView j = some k) : splitTape k = j := by
  cases j <;> fin_cases k <;> simp_all [splitView, splitTape]

def rowProgram {σ : Type} (d : Nat) (hd : 0 < d) :
    MachinePaddingRows.Label d →
      TM2.Stmt (fun _ : MachinePaddingRows.Tape => Bool) (MachinePaddingRows.Label d) (State σ) :=
  MachineStateEquiv.program (rowStateEquiv σ)
    (MachineStateFrame.frameProgram
      (MachineAlphabetTransport.program rowAlphabet_eq (MachinePaddingRows.program d hd)))

def program {σ : Type} (d : Nat) (hd : 0 < d) : Label d → TM2.Stmt Alphabet (Label d) (State σ)
  | .splitCode l => Placement.statement splitTape Label.splitCode (some (.powerCode .init))
      (MachineTableSplit.program l)
  | .powerCode l => Placement.statement powerTape Label.powerCode (some .dartSeed)
      (MachineCeilingPower.program ExpanderFamily.growth l)
  | .dartSeed => MachineUnaryAffineAt.seed .output 0 .dartScan
  | .dartScan => MachineUnaryAffineAt.scan .power .scratch .output d .dartScan .dartRestore
  | .dartRestore => Reduction.MachineTransfer.loopAt
      .scratch .power id false .dartRestore (some .vertexSeed)
  | .vertexSeed => MachineUnaryAffineAt.seed .output 0 .vertexScan
  | .vertexScan => MachineUnaryAffineAt.scan .power .scratch .output 1 .vertexScan .vertexRestore
  | .vertexRestore => Reduction.MachineTransfer.loopAt
      .scratch .power id false .vertexRestore (some .copyFirst)
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .power .scratch id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .scratch .power .fuel false .copySecond (some (.subtractCode .subtract))
  | .subtractCode l => Placement.statement subtractTape Label.subtractCode
      (some (.rowsCode (.inr .initialize_))) (MachineCloudPadding.program l)
  | .rowsCode l => Placement.statement rowTape Label.rowsCode (some .cleanVertex) (rowProgram d hd l)
  | .cleanVertex => MachineDrain.drain .vertex .cleanVertex (some .cleanEdge)
  | .cleanEdge => MachineDrain.drain .edge .cleanEdge (some .cleanPower)
  | .cleanPower => MachineDrain.drain .power .cleanPower (some .cleanRelation)
  | .cleanRelation => MachineDrain.drain .relation .cleanRelation (some .cleanFuel)
  | .cleanFuel => MachineDrain.drain .fuel .cleanFuel none

theorem tableBits_split {n d : Nat} (t : PortTables.Table n d) :
    PortTables.tableBits t = encodeWords [n, n * d] ++ PreprocessingPaddingWords.rowsBits t := by
  change encodeWords (PortTables.tableWords t) = _
  rw [PortTables.tableWords_eq, encodeWords_append]
  rfl

theorem splitInitialTapes (word : List Bool) :
    Placement.tapes splitView (MachineTableSplit.initialTapes word) (fun _ => []) =
      memory word [] [] [] [] [] [] [] := by
  funext k; cases k <;> simp [Placement.tapes, splitView, MachineTableSplit.initialTapes,
    MachineTableSplit.tapes, memory]

theorem splitResultTapes (n e : Nat) (rows : List Bool) :
    Placement.tapes splitView (MachineTableSplit.resultTapes n e rows) (fun _ => []) =
      memory (encodeWords [n, e] ++ rows) rows (encodeWord n) (encodeWord e) [] [] [] [] := by
  funext k; cases k <;> simp [Placement.tapes, splitView, MachineTableSplit.resultTapes,
    MachineTableSplit.tapes, memory]

theorem splitTrace {σ : Type} {n d : Nat} (hd : 0 < d) (t : PortTables.Table n d)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[MachineTableSplit.exactSteps n (n * d)
      (PreprocessingPaddingWords.rowsBits t)]
      (some ⟨some (.splitCode .copyFirst), ((ambient, false), register),
        memory (PortTables.tableBits t) [] [] [] [] [] [] []⟩) =
      some ⟨some (.powerCode .init), ((ambient, false), none),
        memory (PortTables.tableBits t) (PreprocessingPaddingWords.rowsBits t)
          (encodeWord n) (encodeWord (n * d)) [] [] [] []⟩ := by
  have h := Placement.trace splitTape splitView splitView_left splitView_right
    (Label.splitCode (d := d)) (some (.powerCode .init)) (fun _ => [])
    (MachineTableSplit.program (σ := σ × Bool)) (program d hd) (fun _ => rfl) _ _ _
    (MachineTableSplit.splitTrace n (n * d) (PreprocessingPaddingWords.rowsBits t)
      (ambient, false) register)
  simpa only [Placement.configuration, Placement.label, splitInitialTapes, splitResultTapes,
    ← tableBits_split] using h

theorem powerTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output edge : List Bool) (n : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[MachineCeilingPower.totalTime ExpanderFamily.growth n]
      (some ⟨some (.powerCode .init), ((ambient, false), register),
        memory input output (encodeWord n) edge [] [] [] []⟩) =
      some ⟨some .dartSeed, ((ambient, false), none),
        memory input output (encodeWord n) edge (encodeWord (PreprocessingLevels.paddedSize n))
          (encodeWord (PreprocessingLevels.boundedLevel n)) [] []⟩ := by
  have h := Placement.trace powerTape powerView powerView_left powerView_right
    (Label.powerCode (d := d)) (some .dartSeed) (memory input output [] edge [] [] [] [])
    (MachineCeilingPower.program ExpanderFamily.growth (σ := σ)) (program d hd)
    (fun _ => rfl) _ _ _ (MachineCeilingPower.paddingTrace n ambient register)
  simpa only [Placement.configuration, Placement.label, powerTapes] using h

theorem affineOutputTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (coefficient : Nat) (seed scan restore : Label d) (exit : Option (Label d))
    (atSeed : program (σ := σ) d hd seed = MachineUnaryAffineAt.seed (σ := σ × Bool) .output 0 scan)
    (atScan : program (σ := σ) d hd scan = MachineUnaryAffineAt.scan (σ := σ × Bool) .power .scratch .output
      coefficient scan restore)
    (atRestore : program (σ := σ) d hd restore = Reduction.MachineTransfer.loopAt (σ := σ × Bool)
      .scratch .power id false restore exit)
    (input output vertex edge level fuel relation : List Bool) (m : Nat)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[1 + 2 * (m + 1)]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨exit, ((ambient, false), none),
        memory input (encodeWord (coefficient * m) ++ output) vertex edge
          (encodeWord m) level fuel relation⟩ := by
  have hs : (advance (TM2.step (program d hd)))^[1]
      (some ⟨some seed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level fuel relation⟩) =
      some ⟨some scan, ((ambient, false), register),
        memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation⟩ := by
    change some (TM2.stepAux (program d hd seed) _ _) = _
    rw [atSeed]
    simp [MachineUnaryAffineAt.seed, Reduction.MachineSubstitution.stepAux_pushWord,
      TM2.stepAux, encodeWord, memory]
  let base := memory input output vertex edge (encodeWord m) level fuel relation
  have ht := MachineUnaryAffineAt.affineTrace Tape.power Tape.scratch Tape.output
    (by decide) (by decide) (by decide) coefficient scan restore exit (program d hd)
    atScan atRestore base m 0 [] output (ambient, false) register
  have hstart : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord 0 ++ output) =
      memory input (encodeWord 0 ++ output) vertex edge (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  have hfinish : MachineUnaryAffineAt.tapes Tape.power Tape.scratch Tape.output base
      (encodeWord m ++ []) [] (encodeWord (coefficient * m + 0) ++ output) =
      memory input (encodeWord (coefficient * m) ++ output) vertex edge
        (encodeWord m) level fuel relation := by
    funext k
    cases k <;> simp [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, base, memory]
  rw [hstart, hfinish] at ht
  exact appendTrace _ hs ht

theorem headersTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output vertex edge level : List Bool) (m : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[4 * (m + 1) + 2]
      (some ⟨some .dartSeed, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level [] []⟩) =
      some ⟨some .copyFirst, ((ambient, false), none),
        memory input (encodeWords [m, m * d] ++ output) vertex edge (encodeWord m) level [] []⟩ := by
  have h₁ := affineOutputTrace d hd d .dartSeed .dartScan .dartRestore (some .vertexSeed)
    rfl rfl rfl input output vertex edge level [] [] m ambient register
  have h₂ := affineOutputTrace d hd 1 .vertexSeed .vertexScan .vertexRestore (some .copyFirst)
    rfl rfl rfl input (encodeWord (d * m) ++ output) vertex edge level [] [] m ambient none
  have h := appendTrace _ h₁ h₂
  simpa only [Nat.one_mul, Nat.mul_comm d m, encodeWords, List.append_nil, List.append_assoc,
    show (1 + 2 * (m + 1)) + (1 + 2 * (m + 1)) = 4 * (m + 1) + 2 by omega] using h

theorem copyPowerTrace {σ : Type} (d : Nat) (hd : 0 < d)
    (input output vertex edge level : List Bool) (m : Nat) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program d hd)))^[2 * (m + 2)]
      (some ⟨some .copyFirst, ((ambient, false), register),
        memory input output vertex edge (encodeWord m) level [] []⟩) =
      some ⟨some (.subtractCode .subtract), ((ambient, false), none),
        memory input output vertex edge (encodeWord m) level (encodeWord m) []⟩ := by
  have h := MachineCopy.copyTrace Tape.power Tape.fuel Tape.scratch
    (by decide) (by decide) (by decide) false (Label.copyFirst (d := d)) .copySecond
    (some (.subtractCode .subtract)) (program d hd) rfl rfl
    (memory input output vertex edge (encodeWord m) level [] []) rfl (ambient, false) register
  simpa only [memory, encodeWord_length, List.append_nil, update_fuel] using h

def otherTime {n d : Nat} (t : PortTables.Table n d) : Nat :=
  MachineTableSplit.exactSteps n (n * d) (PreprocessingPaddingWords.rowsBits t) +
    MachineCeilingPower.totalTime ExpanderFamily.growth n +
    (4 * (PreprocessingLevels.paddedSize n + 1) + 2) +
    (2 * (PreprocessingLevels.paddedSize n + 2)) + (2 * n + 2) +
    cleanupTime d (PreprocessingLevels.paddedSize n)

theorem rows_length_le {n d : Nat} (t : PortTables.Table n d) :
    (PreprocessingPaddingWords.rowsBits t).length ≤ (PortTables.tableBits t).length := by
  rw [tableBits_split, List.length_append]
  omega

theorem power_length_bound {n d : Nat} (t : PortTables.Table n d) :
    PreprocessingLevels.paddedSize n ≤ ExpanderFamily.growth * ((PortTables.tableBits t).length + 1) :=
  (MachineCeilingPower.paddingOutput_bounds n).2.2.trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (PortTables.vertices_le_tableBits_length t) 1))

theorem initialOutput_length {n d m : Nat} (t : PortTables.Table n d) :
    (MachinePaddingTable.initialOutput (m := m) t).length =
      m + m * d + 2 + (PreprocessingPaddingWords.rowsBits t).length := by
  simp only [MachinePaddingTable.initialOutput, List.length_append, encodeWords_length,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  omega

theorem intermediate_bound {n d : Nat} (t : PortTables.Table n d) :
    MachinePaddingBounds.inputSize n (n * d) (PreprocessingLevels.paddedSize n - n)
      (MachinePaddingTable.initialOutput (m := PreprocessingLevels.paddedSize n) t) ≤
      (intermediatePolynomial d).eval (PortTables.tableBits t).length := by
  have hn := PortTables.vertices_le_tableBits_length t
  have he := darts_length_le t
  have hr := rows_length_le t
  have hm := power_length_bound t
  have hs := Nat.sub_le (PreprocessingLevels.paddedSize n) n
  have hmul := Nat.mul_le_mul_left (d + 2) hm
  simp only [MachinePaddingBounds.inputSize, encodeWord_length, initialOutput_length,
    intermediatePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, intermediateCoefficient]
  nlinarith

theorem otherTime_le {n d : Nat} (t : PortTables.Table n d) :
    otherTime t ≤ (otherPolynomial d).eval (PortTables.tableBits t).length := by
  have hs := MachineTableSplit.exactSteps_le n (n * d) (PreprocessingPaddingWords.rowsBits t)
  rw [← tableBits_split, MachineTableSplit.timePolynomial_eval] at hs
  have hc := MachineCeilingPower.totalTime_le ExpanderFamily.growth n
  have hn := PortTables.vertices_le_tableBits_length t
  have hm := power_length_bound t
  have hsq := Nat.mul_le_mul_left (ExpanderFamily.growth + 8)
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2)
  have hmul := Nat.mul_le_mul_left (d + 8) hm
  simp only [otherPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold otherTime cleanupTime
  unfold MachineCeilingPower.timeBound at hc
  nlinarith

end BinPackingGames.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineLazyTable

open Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

abbrev State (d : Nat) := MachineLazyRows.StreamState Unit d

def clean (d : Nat) (positive : 0 < d) : State d :=
  MachineLazyRows.streamClean d positive ()

theorem clean_pair (d : Nat) (positive : 0 < d) :
    ((clean d positive).1, (none : Option Bool)) = clean d positive := rfl

def program (d : Nat) (positive : 0 < d) :
    Label d → TM2.Stmt (fun _ : Tape => Bool) (Label d) (State d)
  | .split label => MachineCloudPadding.Placement.statement splitRoles Label.split
      (some .dartSeed) (MachineTableSplit.program label)
  | .dartSeed => MachineUnaryAffineAt.seed .output 0 .dartScan
  | .dartScan => MachineUnaryAffineAt.scan .darts .scratch .output 2 .dartScan .dartRestore
  | .dartRestore => Reduction.MachineTransfer.loopAt .scratch .darts id false
      .dartRestore (some .vertexSeed)
  | .vertexSeed => MachineUnaryAffineAt.seed .output 0 .vertexScan
  | .vertexScan => MachineUnaryAffineAt.scan .vertices .scratch .output 1 .vertexScan .vertexRestore
  | .vertexRestore => Reduction.MachineTransfer.loopAt .scratch .vertices id false
      .vertexRestore (some .fuelFirst)
  | .fuelFirst => Reduction.MachineTransfer.loopAt .vertices .scratch id false
      .fuelFirst (some .fuelSecond)
  | .fuelSecond => MachineCopy.forkLoop .scratch .vertices .fuel false
      .fuelSecond (some .seedCounters)
  | .seedCounters => .push .vertex (fun _ => false)
      (.push .reverse (fun _ => false) (.goto fun _ => .guard))
  | .guard => MachineUnaryCounter.guard .fuel .copyVertexFirst .clearVertices
  | .copyVertexFirst => Reduction.MachineTransfer.loopAt .vertex .scratch id false
      .copyVertexFirst (some .copyVertexSecond)
  | .copyVertexSecond => MachineCopy.forkLoop .scratch .vertex .tail false
      .copyVertexSecond (some (.dummy (MachineDummyRows.start d)))
  | .dummy label => MachineCloudPadding.Placement.statement dummyRoles Label.dummy
      (some .clearDummyTail) (MachineDummyRows.program d label)
  | .clearDummyTail => MachineDrain.drain .tail .clearDummyTail (some .clearDummyRelation)
  | .clearDummyRelation => MachineDrain.drain .relation .clearDummyRelation (some (.oldRows (0, none)))
  | .oldRows label => MachineLazyRows.vertexInstruction d positive (2 * d) d oldRoles
      Label.oldRows (some .nextVertex) label
  | .nextVertex => pushWord .reverse (List.replicate d true)
      (.push .vertex (fun _ => true) (.goto fun _ => .guard))
  | .clearVertices => MachineDrain.drain .vertices .clearVertices (some .clearDarts)
  | .clearDarts => MachineDrain.drain .darts .clearDarts (some .clearFuel)
  | .clearFuel => MachineDrain.drain .fuel .clearFuel (some .clearVertex)
  | .clearVertex => MachineDrain.drain .vertex .clearVertex (some .clearReverse)
  | .clearReverse => MachineDrain.drain .reverse .clearReverse none

def loopTapes (d : Nat) (input : List Bool) (n m left v : Nat)
    (source output : List Bool) : Tape → List Bool :=
  frame input source output (encodeWord n) (encodeWord m) (encodeWord left)
    (encodeWord v) (encodeWord (2 * d * v))

def prefixSteps (n m : Nat) (rows : List Bool) : Nat :=
  2 * (encodeWords [n, m] ++ rows).length + 5 * n + 3 * m + 17

theorem prefixTrace (d : Nat) (positive : 0 < d) (n m : Nat) (rows : List Bool) :
    (advance (TM2.step (program d positive)))^[prefixSteps n m rows]
      (some ⟨some (.split .copyFirst), clean d positive,
        initialTapes (encodeWords [n, m] ++ rows)⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d (encodeWords [n, m] ++ rows) n m n 0 rows (encodeWords [n, 2 * m])⟩ := by
  let word := encodeWords [n, m] ++ rows
  let header := encodeWords [n, 2 * m]
  let b₁ := frame word rows [] (encodeWord n) (encodeWord m) [] [] []
  let b₂ := frame word rows (encodeWord (2 * m)) (encodeWord n) (encodeWord m) [] [] []
  let b₃ := frame word rows header (encodeWord n) (encodeWord m) [] [] []
  let b₄ := frame word rows header (encodeWord n) (encodeWord m) (encodeWord n) [] []
  have hstart : MachineCloudPadding.Placement.tapes splitView
      (MachineTableSplit.initialTapes word) (fun _ => []) = initialTapes word := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, splitView,
      MachineTableSplit.initialTapes, MachineTableSplit.tapes, initialTapes, frame]
  have hend : MachineCloudPadding.Placement.tapes splitView
      (MachineTableSplit.resultTapes n m rows) (fun _ => []) = b₁ := by
    funext t
    cases t <;> simp [MachineCloudPadding.Placement.tapes, splitView,
      MachineTableSplit.resultTapes, MachineTableSplit.tapes, b₁, frame, word]
  have split := MachineCloudPadding.Placement.trace splitRoles splitView
    splitRoles_left splitRoles_right Label.split (some .dartSeed) (fun _ => [])
    MachineTableSplit.program (program d positive) (fun _ => rfl) _ _ _
    (MachineTableSplit.splitTrace n m rows (clean d positive).1 none)
  have c₀ : (advance (TM2.step (program d positive)))^[MachineTableSplit.exactSteps n m rows]
      (some ⟨some (.split .copyFirst), clean d positive, initialTapes word⟩) =
      some ⟨some .dartSeed, clean d positive, b₁⟩ := by
    simp only [MachineCloudPadding.Placement.configuration,
      MachineCloudPadding.Placement.label] at split
    rw [hstart, hend] at split
    simpa only [clean_pair] using split
  have hdart : Function.update b₁ Tape.output (encodeWord (2 * m + 0) ++ b₁ .output) = b₂ := by
    funext t; cases t <;> simp [b₁, b₂, frame]
  have dart := MachineUnaryAffineAt.seededAffineTrace Tape.darts .scratch .output
    (by decide) (by decide) (by decide) 2 0 .dartSeed .dartScan .dartRestore
    (some .vertexSeed) (program d positive) rfl rfl rfl b₁ m []
    (by simp [b₁, frame]) rfl (clean d positive).1 none
  have c₁ : (advance (TM2.step (program d positive)))^[2 * (m + 1) + 1]
      (some ⟨some .dartSeed, clean d positive, b₁⟩) =
      some ⟨some .vertexSeed, clean d positive, b₂⟩ := by
    simpa only [hdart, clean_pair] using dart
  have hv : Function.update b₂ Tape.output (encodeWord (1 * n + 0) ++ b₂ .output) = b₃ := by
    funext t; cases t <;> simp [b₂, b₃, frame, header, encodeWords]
  have vertex := MachineUnaryAffineAt.seededAffineTrace Tape.vertices .scratch .output
    (by decide) (by decide) (by decide) 1 0 .vertexSeed .vertexScan .vertexRestore
    (some .fuelFirst) (program d positive) rfl rfl rfl b₂ n []
    (by simp [b₂, frame]) rfl (clean d positive).1 none
  have c₂ : (advance (TM2.step (program d positive)))^[2 * (n + 1) + 1]
      (some ⟨some .vertexSeed, clean d positive, b₂⟩) =
      some ⟨some .fuelFirst, clean d positive, b₃⟩ := by
    simpa only [hv, clean_pair] using vertex
  have hf : Function.update b₃ Tape.fuel (b₃ .vertices ++ b₃ .fuel) = b₄ := by
    funext t; cases t <;> simp [b₃, b₄, frame]
  have fuel := MachineCopy.copyTrace Tape.vertices .fuel .scratch
    (by decide) (by decide) (by decide) false .fuelFirst .fuelSecond
    (some .seedCounters) (program d positive) rfl rfl b₃ rfl (clean d positive).1 none
  rw [hf] at fuel
  have c₃ : (advance (TM2.step (program d positive)))^[2 * (n + 2)]
      (some ⟨some .fuelFirst, clean d positive, b₃⟩) =
      some ⟨some .seedCounters, clean d positive, b₄⟩ := by
    simpa only [clean_pair, show b₃ .vertices = encodeWord n from rfl, encodeWord_length,
      Nat.add_assoc] using fuel
  have c₄ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .seedCounters, clean d positive, b₄⟩) =
      some ⟨some .guard, clean d positive,
        loopTapes d word n m n 0 rows header⟩ := by
    have ht : Function.update (Function.update b₄ Tape.vertex [false]) Tape.reverse [false] =
        loopTapes d word n m n 0 rows header := by
      funext t; cases t <;> simp [b₄, loopTapes, frame, encodeWord]
    simp only [Function.iterate_one, advance_some, TM2.step, program, TM2.stepAux]
    apply congrArg some
    exact congrArg (TM2.Cfg.mk _ _) ht
  have all := joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄
  have hc : MachineTableSplit.exactSteps n m rows + (2 * (m + 1) + 1) +
      (2 * (n + 1) + 1) + 2 * (n + 2) + 1 = prefixSteps n m rows := by
    dsimp [MachineTableSplit.exactSteps, prefixSteps]
    omega
  rw [hc] at all
  exact all

theorem drainPhase (d : Nat) (positive : 0 < d) (tape : Tape) (label : Label d)
    (exit : Option (Label d))
    (atLabel : program d positive label = MachineDrain.drain tape label exit)
    (base : Tape → List Bool) :
    (advance (TM2.step (program d positive)))^[(base tape).length + 1]
      (some ⟨some label, clean d positive, base⟩) =
      some ⟨exit, clean d positive, Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self, clean_pair] using
    MachineDrain.drainTrace tape label exit (program d positive) atLabel base
      (base tape) (clean d positive).1 none

theorem finishTrace (d : Nat) (positive : 0 < d) (input output : List Bool) (n m v : Nat) :
    (advance (TM2.step (program d positive)))^[finishSteps d n m v]
      (some ⟨some .guard, clean d positive, loopTapes d input n m 0 v [] output⟩) =
      some ⟨none, clean d positive, finalTapes input output⟩ := by
  let b₀ := loopTapes d input n m 0 v [] output
  let b₁ := Function.update b₀ Tape.vertices []
  let b₂ := Function.update b₁ Tape.darts []
  let b₃ := Function.update b₂ Tape.fuel []
  let b₄ := Function.update b₃ Tape.vertex []
  have hframe : MachineUnaryCounter.counterTapes Tape.fuel b₀ 0 [] = b₀ := by
    funext t; cases t <;> simp [MachineUnaryCounter.counterTapes, b₀, loopTapes, frame]
  have guard := MachineUnaryCounter.guardTrace_zero Tape.fuel .guard .copyVertexFirst
    .clearVertices (program d positive) rfl b₀ [] (clean d positive).1 none
  have c₀ : (advance (TM2.step (program d positive)))^[1]
      (some ⟨some .guard, clean d positive, b₀⟩) =
      some ⟨some .clearVertices, clean d positive, b₀⟩ := by
    simpa only [hframe, clean_pair] using guard
  have c₁ : (advance (TM2.step (program d positive)))^[n + 2]
      (some ⟨some .clearVertices, clean d positive, b₀⟩) =
      some ⟨some .clearDarts, clean d positive, b₁⟩ := by
    simpa only [show b₀ .vertices = encodeWord n from rfl, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .vertices .clearVertices (some .clearDarts) rfl b₀
  have c₂ : (advance (TM2.step (program d positive)))^[m + 2]
      (some ⟨some .clearDarts, clean d positive, b₁⟩) =
      some ⟨some .clearFuel, clean d positive, b₂⟩ := by
    have hv : b₁ .darts = encodeWord m := by simp [b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .darts .clearDarts (some .clearFuel) rfl b₁
  have c₃ : (advance (TM2.step (program d positive)))^[2]
      (some ⟨some .clearFuel, clean d positive, b₂⟩) =
      some ⟨some .clearVertex, clean d positive, b₃⟩ := by
    have hv : b₂ .fuel = encodeWord 0 := by simp [b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length] using
      drainPhase d positive .fuel .clearFuel (some .clearVertex) rfl b₂
  have c₄ : (advance (TM2.step (program d positive)))^[v + 2]
      (some ⟨some .clearVertex, clean d positive, b₃⟩) =
      some ⟨some .clearReverse, clean d positive, b₄⟩ := by
    have hv : b₃ .vertex = encodeWord v := by simp [b₃, b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc] using
      drainPhase d positive .vertex .clearVertex (some .clearReverse) rfl b₃
  have hend : Function.update b₄ Tape.reverse [] = finalTapes input output := by
    funext t; cases t <;> simp [b₄, b₃, b₂, b₁, b₀, loopTapes, finalTapes, frame]
  have c₅ : (advance (TM2.step (program d positive)))^[2 * d * v + 2]
      (some ⟨some .clearReverse, clean d positive, b₄⟩) =
      some ⟨none, clean d positive, finalTapes input output⟩ := by
    have hv : b₄ .reverse = encodeWord (2 * d * v) := by
      simp [b₄, b₃, b₂, b₁, b₀, loopTapes, frame]
    simpa only [hv, encodeWord_length, Nat.add_assoc, hend] using
      drainPhase d positive .reverse .clearReverse none rfl b₄
  have all := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace c₀ c₁) c₂) c₃) c₄) c₅
  have hc : 1 + (n + 2) + (m + 2) + 2 + (v + 2) + (2 * d * v + 2) =
      finishSteps d n m v := by dsimp [finishSteps]; omega
  rw [hc] at all
  exact all

def inputBlocks {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) : List Bool :=
  events.flatMap (fun v => MachineLazyRows.recordsInput (List.ofFn (PreprocessingLazyWords.row table v)))

theorem encodeWords_flatMap {α : Type} (xs : List α) (f : α → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem inputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    inputBlocks table events = encodeWords
      ((events.flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatMap
        GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [inputBlocks, MachineLazyRows.recordsInput_eq_codec]

theorem input_table_codec {n d : Nat} (table : PortTables.Table n d) :
    PortTables.tableBits table = encodeWords [n, n * d] ++ inputBlocks table (List.finRange n) := by
  rw [inputBlocks_codec]
  change encodeWords (PortTables.tableWords table) = _
  rw [PortTables.tableWords_eq, PreprocessingLazyWords.flatRows_list, encodeWords_append]
  have hrows : (List.ofFn (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatten =
      (List.finRange n).flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v)) := by
    rw [List.ofFn_eq_map]
    rfl
  rw [hrows]

def machine (d : Nat) (positive : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label d
  main := .split .copyFirst
  σ := State d
  initialState := clean d positive
  m := program d positive

theorem initial_configuration (d : Nat) (positive : 0 < d) (input : List Bool) :
    initList (machine d positive) input =
      ⟨some (.split .copyFirst), clean d positive, initialTapes input⟩ := by
  have ht : (initList (machine d positive) input).stk = initialTapes input := by
    funext t; (cases t <;> simp [initList, machine, initialTapes, frame]); rfl
  exact congrArg (TM2.Cfg.mk _ _) ht

end BinPackingGames.Foundations.Complexity.MachineLazyTable

namespace BinPackingGames.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label State)

def rawProgram (d : Nat) (positive : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .input
  output := .output
  main := .split .copyFirst
  initial := MachineLazyTable.clean d positive
  code := MachineLazyTable.program d positive

theorem cleanup_complete (d : Nat) (positive : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram d positive).output := by
  cases k <;> simp [cleanupTapes, rawProgram]

end BinPackingGames.Foundations.Complexity.MachineLazyTableRuntime

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineOverlayRows
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
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

def instruction (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (labels : Label e → Λ) (exit : Option Λ) :
    Label e → TM2.Stmt (fun _ : K => Bool) Λ (State A e)
  | .loadStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .loadLoop)
  | .loadLoop => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1)
      (labels .loadLoop) (some (labels .seedRelation))
  | .seedRelation => pushWord (tape 2) trueBits.reverse
      (.goto fun _ => labels (.row (.inl .copySeed)))
  | .row stage => MachineLazyRows.reindexInstruction e positive (d + e) d
      (tape ∘ bodyIndex) (fun stage => labels (.row stage))
      (some (labels .drainOld)) stage
  | .drainOld => MachineDrain.drain (tape 1) (labels .drainOld) (some (labels .drainNew))
  | .drainNew => MachineDrain.drain (tape 6) (labels .drainNew) (some (labels .drainRelation))
  | .drainRelation => MachineDrain.drain (tape 2) (labels .drainRelation) exit

def rowBits (d e v j : Nat) : List Bool :=
  MachineLazyRows.reindexRowBits e (d + e) d v j trueRelation

def rowSteps (d e v j : Nat) (output : List Bool) : Nat :=
  (j + 2) + 1 + MachineLazyRows.reindexSteps e (d + e) d v j trueRelation output +
    (j + 2) + (MachinePortReindex.value e (d + e) d j + 2) + (trueBits.length + 1)

def resultTapes (d e v j : Nat) (tape : Fin 10 → K) (base : K → List Bool)
    (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) suffix) (tape 7)
    (base (tape 7) ++ rowBits d e v j)

theorem rowBits_eq_expanderRow {n e : Nat} (d : Nat) (H : PCP.ExpanderTables.Table n e)
    (v : Fin n) (p : Fin e) :
    rowBits d e v.val (PCP.ExpanderTables.reverseIndex H
        (PCP.ExpanderTables.rowIndex n e (v, p))).val =
      encodeWords (rowWords (expanderRow d H v p)) := by
  rw [expanderRow_words]
  have h (j : Nat) : MachinePortReindex.value e (d + e) d j = expanderReverseMap d e j := by
    unfold MachinePortReindex.value expanderReverseMap
    omega
  simp only [rowBits, MachineLazyRows.reindexRowBits, h,
    PCP.PreprocessingLazyWords.relationWords_true, List.cons_append,
    List.nil_append, encodeWords, List.append_assoc]

def vertexInstruction (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (labels : VertexLabel e → Λ) (exit : Option Λ) :
    VertexLabel e → TM2.Stmt (fun _ : K => Bool) Λ (State A e)
  | (i, none) => if i.val < e then .goto fun _ => labels (i, some .loadStart)
      else MachinePortReindex.exitAt exit
  | (i, some stage) => if h : i.val < e then
      instruction d e positive tape (fun stage => labels (i, some stage))
        (some (labels (⟨i.val + 1, by omega⟩, none))) stage
      else MachinePortReindex.exitAt exit

def streamOutput (d e v : Nat) (words : List Nat) : List Bool :=
  words.flatMap (rowBits d e v)

def vertexSteps (d e v : Nat) : List Nat → List Bool → Nat
  | [], _ => 1
  | j :: words, output => 1 + rowSteps d e v j output +
      vertexSteps d e v words (output ++ rowBits d e v j)

theorem rowBits_length (d e v j : Nat) :
    (rowBits d e v j).length = v + MachinePortReindex.value e (d + e) d j + trueBits.length + 2 := by
  simp only [rowBits, MachineLazyRows.reindexRowBits, List.length_append, encodeWord_length,
    trueBits]
  omega

theorem rowBits_length_le (d e v j B : Nat) (hj : j ≤ B) :
    (rowBits d e v j).length ≤ rowSizeBound d e v B := by
  rw [rowBits_length]
  have h := value_le d e j B hj
  unfold rowSizeBound
  omega

theorem rowSteps_le (d e v j B : Nat) (hj : j ≤ B) (output : List Bool) :
    rowSteps d e v j output ≤ rowCostBound d e v B + 2 * output.length := by
  have hdiv := (Nat.div_le_self j e).trans hj
  have hval := value_le d e j B hj
  have hsize := rowBits_length_le d e v j B hj
  change (MachineLazyRows.reindexRowBits e (d + e) d v j trueRelation).length ≤
    rowSizeBound d e v B at hsize
  unfold rowSteps MachineLazyRows.reindexSteps MachinePortReindex.steps rowCostBound
  omega

theorem vertexSteps_le_capacity (d e v B capacity : Nat)
    (words : List Nat) (bounded : ∀ j ∈ words, j ≤ B) (output : List Bool)
    (room : output.length + words.length * rowSizeBound d e v B ≤ capacity) :
    vertexSteps d e v words output ≤
      words.length * (rowCostBound d e v B + 2 * capacity + 1) + 1 := by
  induction words generalizing output with
  | nil => simp [vertexSteps]
  | cons j words ih =>
      have hj := bounded j (by simp)
      have hb : ∀ k ∈ words, k ≤ B := fun k hk => bounded k (by simp [hk])
      have hsize := rowBits_length_le d e v j B hj
      have hcost := rowSteps_le d e v j B hj output
      have hout : output.length ≤ capacity := by omega
      have hroom : (output ++ rowBits d e v j).length +
          words.length * rowSizeBound d e v B ≤ capacity := by
        rw [List.length_append]
        simp only [List.length_cons, Nat.succ_mul] at room
        omega
      have htail := ih hb (output ++ rowBits d e v j) hroom
      change 1 + rowSteps d e v j output +
        vertexSteps d e v words (output ++ rowBits d e v j) ≤
        (words.length + 1) * (rowCostBound d e v B + 2 * capacity + 1) + 1
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem vertexSteps_le (d e v B : Nat) (words : List Nat)
    (bounded : ∀ j ∈ words, j ≤ B) (output : List Bool) :
    vertexSteps d e v words output ≤
      words.length * (rowCostBound d e v B +
        2 * (output.length + words.length * rowSizeBound d e v B) + 1) + 1 :=
  vertexSteps_le_capacity d e v B _ words bounded output (Nat.le_refl _)

theorem streamFrame_afterRow (d e v j : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (base : K → List Bool)
    (words : List Nat) (output : List Bool) :
    resultTapes d e v j tape (streamFrame tape base (j :: words) output)
      (encodeWords words ++ base (tape 9)) =
      streamFrame tape base words (output ++ rowBits d e v j) := by
  have h79 : tape 7 ≠ tape 9 := fun h => (by decide : (7 : Fin 10) ≠ 9) (distinct h)
  funext k
  by_cases h7 : k = tape 7
  · subst k
    simp [resultTapes, streamFrame]
  · by_cases h9 : k = tape 9
    · subst k
      simp [resultTapes, streamFrame, Ne.symm h79]
    · simp [resultTapes, streamFrame, h7, h9]

theorem streamOutput_expanderRows {n e : Nat} (d : Nat) (H : PCP.ExpanderTables.Table n e)
    (v : Fin n) :
    streamOutput d e v.val (List.ofFn fun p : Fin e =>
      (PCP.ExpanderTables.reverseIndex H (PCP.ExpanderTables.rowIndex n e (v, p))).val) =
      encodeWords ((List.ofFn (expanderRow d H v)).flatMap rowWords) := by
  rw [encodeWords_flatMap]
  simp only [streamOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  exact rowBits_eq_expanderRow d H v p

end BinPackingGames.Foundations.Complexity.MachineOverlayRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineOverlayTable
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
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

abbrev Ambient (A : Type) (d e : Nat) := ((A × Fin e) × MachineLazyRows.Buffer) × Fin d
abbrev State (A : Type) (d e : Nat) := Ambient A d e × Option Bool

def clean (d e : Nat) (hd : 0 < d) (he : 0 < e) (a : A) : State A d e :=
  MachineLazyRows.streamClean d hd (a, MachineFixedDivMod.residue e he 0)

def expanderState (A : Type) (d e : Nat) :
    MachineOverlayRows.State ((A × MachineLazyRows.Buffer) × Fin d) e ≃ State A d e where
  toFun
    | ((((a, buffer), rd), re), bit) => ((((a, re), buffer), rd), bit)
  invFun
    | ((((a, re), buffer), rd), bit) => ((((a, buffer), rd), re), bit)
  left_inv := by rintro ⟨⟨⟨⟨a, buffer⟩, rd⟩, re⟩, bit⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨a, re⟩, buffer⟩, rd⟩, bit⟩; rfl

theorem expanderState_clean (d e : Nat) (hd : 0 < d) (he : 0 < e) (a : A) :
    expanderState A d e (MachinePortReindex.clean e he
      ((a, MachineRegularOriginalRow.zeroBuffer), MachineFixedDivMod.residue d hd 0)) =
      clean d e hd he a := rfl

def mainInstruction (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    MainLabel d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State A d e)
  | .copyHFirst => Reduction.MachineTransfer.loopAt expanderArchive scratch id false
      (.inr .copyHFirst) (next .copyHSecond)
  | .copyHSecond => MachineCopy.forkLoop scratch expanderArchive expanderStream false
      (.inr .copyHSecond) (next .countSeed)
  | .countSeed => MachineUnaryAffineAt.seed output 0 (.inr .countScan)
  | .countScan => MachineUnaryAffineAt.scan vertexCount scratch output (d + e)
      (.inr .countScan) (.inr .countRestore)
  | .countRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .countRestore) (next .headerSeed)
  | .headerSeed => MachineUnaryAffineAt.seed output 0 (.inr .headerScan)
  | .headerScan => MachineUnaryAffineAt.scan vertexCount scratch output 1
      (.inr .headerScan) (.inr .headerRestore)
  | .headerRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .headerRestore) (next .fuelSeed)
  | .fuelSeed => MachineUnaryAffineAt.seed fuel 0 (.inr .fuelScan)
  | .fuelScan => MachineUnaryAffineAt.scan vertexCount scratch fuel 1
      (.inr .fuelScan) (.inr .fuelRestore)
  | .fuelRestore => Reduction.MachineTransfer.loopAt scratch vertexCount id false
      (.inr .fuelRestore) (next .vertexSeed)
  | .vertexSeed => .push vertex (fun _ => false) (.goto fun _ => .inr .guard)
  | .guard => MachineUnaryCounter.guard fuel (.inr (.old (0, none))) (.inr .drainFuel)
  | .old stage => MachineLazyRows.vertexInstruction d hd (d + e) 0 oldTapes
      (fun stage => .inr (.old stage)) (next .tailSeed) stage
  | .tailSeed => MachineUnaryAffineAt.seed tail 0 (.inr .tailScan)
  | .tailScan => MachineUnaryAffineAt.scan vertex scratch tail 1
      (.inr .tailScan) (.inr .tailRestore)
  | .tailRestore => Reduction.MachineTransfer.loopAt scratch vertex id false
      (.inr .tailRestore) (next (.expander (0, none)))
  | .expander stage => MachineStateEquiv.statement (expanderState A d e)
      (MachineOverlayRows.vertexInstruction d e he expanderTapes
        (fun stage => .inr (.expander stage)) (next .drainTail) stage)
  | .drainTail => MachineDrain.drain tail (.inr .drainTail) (next .increment)
  | .increment => .push vertex (fun _ => true) (.goto fun _ => .inr .guard)
  | .drainFuel => MachineDrain.drain fuel (.inr .drainFuel) (next .drainVertex)
  | .drainVertex => MachineDrain.drain vertex (.inr .drainVertex) (next .drainVertexCount)
  | .drainVertexCount => MachineDrain.drain vertexCount (.inr .drainVertexCount) (next .drainDartCount)
  | .drainDartCount => MachineDrain.drain dartCount (.inr .drainDartCount) none

def program (d e : Nat) (hd : 0 < d) (he : 0 < e) :
    Label d e → TM2.Stmt (fun _ : Tape => Bool) (Label d e) (State A d e)
  | .inl l => Placement.statement Sum.inl Sum.inl (next .copyHFirst)
      (MachineTableSplit.program l)
  | .inr l => mainInstruction d e hd he l

def splitTapes (n m : Nat) (rows rawH : List Bool) : Tape → List Bool :=
  combine (MachineTableSplit.resultTapes n m rows) rawH

theorem splitTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (table : GraphTables.Table) (rawH : List Bool) (a : A) :
    (advance (TM2.step (program d e hd he)))^[MachineTableSplit.exactSteps
      table.vertices table.darts (MachineTableSplit.rowsBits table)]
      (some ⟨some (.inl .copyFirst), clean d e hd he a,
        initialTapes (GraphTables.tableBits table) rawH⟩) =
      some ⟨next .copyHFirst, clean d e hd he a,
        splitTapes table.vertices table.darts (MachineTableSplit.rowsBits table) rawH⟩ := by
  let ambient := (clean d e hd he a).1
  have source := MachineTableSplit.tableTrace table ambient none
  have placed := Placement.trace (Sum.inl : Fin 5 → Tape) splitView (fun _ => rfl)
    (by intro j k h; cases j <;> simp_all [splitView])
    (Sum.inl : MachineTableSplit.Label → Label d e) (next .copyHFirst)
    (initialTapes [] rawH) MachineTableSplit.program (program d e hd he) (fun _ => rfl)
    _ _ _ source
  simp only [Placement.configuration, Placement.label] at placed
  rw [placedTapes, placedTapes] at placed
  simpa only [initialTapes,
    splitTapes, ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using placed

theorem initialTapes_memory (g h : List Bool) :
    initialTapes g h = memory g h [] [] [] [] [] [] [] [] := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [initialTapes, combine, extraTapes, MachineTableSplit.initialTapes,
      MachineTableSplit.tapes, memory]

theorem splitTapes_memory (n m : Nat) (rows rawH : List Bool) :
    splitTapes n m rows rawH = memory (encodeWords [n, m] ++ rows) rawH rows []
      (encodeWord n) (encodeWord m) [] [] [] [] := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [splitTapes, combine, extraTapes, MachineTableSplit.resultTapes,
      MachineTableSplit.tapes, memory]

theorem preparationTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs : List Bool) (n m : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[preparationSteps n h]
      (some ⟨next .copyHFirst, clean d e hd he a,
        memory g h gs [] (encodeWord n) (encodeWord m) [] [] [] []⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩ := by
  let b0 := memory g h gs [] (encodeWord n) (encodeWord m) [] [] [] []
  let b1 := memory g h gs h (encodeWord n) (encodeWord m) [] [] [] []
  let b2 := memory g h gs h (encodeWord n) (encodeWord m) [] [] [] (encodeWord ((d + e) * n))
  let b3 := memory g h gs h (encodeWord n) (encodeWord m) [] [] []
    (encodeWords [n, n * (d + e)])
  let b4 := memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) [] []
    (encodeWords [n, n * (d + e)])
  let ambient := (clean d e hd he a).1
  have hcopy := MachineCopy.copyTrace expanderArchive expanderStream scratch
    (by decide) (by decide) (by decide) false (.inr .copyHFirst) (.inr .copyHSecond)
    (next .countSeed) (program d e hd he) rfl rfl b0 rfl ambient none
  have copyRun : (advance (TM2.step (program d e hd he)))^[2 * (h.length + 1)]
      (some ⟨next .copyHFirst, clean d e hd he a, b0⟩) =
      some ⟨next .countSeed, clean d e hd he a, b1⟩ := by
    simpa only [b0, b1, memory_expanderArchive, memory_expanderStream, next, List.append_nil,
      update_expanderStream, ambient, clean, MachineLazyRows.streamClean,
      MachinePortReindex.clean] using hcopy
  have hcount := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch output
    (by decide) (by decide) (by decide) (d + e) 0
    (.inr .countSeed) (.inr .countScan) (.inr .countRestore) (next .headerSeed)
    (program d e hd he) rfl rfl rfl b1 n [] (by simp [b1, memory, vertexCount]) rfl ambient none
  have countRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .countSeed, clean d e hd he a, b1⟩) =
      some ⟨next .headerSeed, clean d e hd he a, b2⟩ := by
    simpa only [b1, b2, memory_output, next, List.append_nil, Nat.add_zero, update_output,
      ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hcount
  have hheader := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch output
    (by decide) (by decide) (by decide) 1 0
    (.inr .headerSeed) (.inr .headerScan) (.inr .headerRestore) (next .fuelSeed)
    (program d e hd he) rfl rfl rfl b2 n [] (by simp [b2, memory, vertexCount]) rfl ambient none
  have headerRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .headerSeed, clean d e hd he a, b2⟩) =
      some ⟨next .fuelSeed, clean d e hd he a, b3⟩ := by
    simpa only [b2, b3, memory_output, next, Nat.one_mul, Nat.add_zero, update_output,
      Nat.mul_comm (d + e) n, encodeWords, List.append_nil,
      ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hheader
  have hfuel := MachineUnaryAffineAt.seededAffineTrace vertexCount scratch fuel
    (by decide) (by decide) (by decide) 1 0
    (.inr .fuelSeed) (.inr .fuelScan) (.inr .fuelRestore) (next .vertexSeed)
    (program d e hd he) rfl rfl rfl b3 n [] (by simp [b3, memory, vertexCount]) rfl ambient none
  have fuelRun : (advance (TM2.step (program d e hd he)))^[2 * (n + 1) + 1]
      (some ⟨next .fuelSeed, clean d e hd he a, b3⟩) =
      some ⟨next .vertexSeed, clean d e hd he a, b4⟩ := by
    simpa only [b3, b4, memory_fuel, next, List.append_nil, Nat.one_mul, Nat.add_zero,
      update_fuel, ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hfuel
  have seedRun : (advance (TM2.step (program d e hd he)))^[1]
      (some ⟨next .vertexSeed, clean d e hd he a, b4⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs h (encodeWord n) (encodeWord m) (encodeWord n) (encodeWord 0) []
          (encodeWords [n, n * (d + e)])⟩ := by
    change some (TM2.stepAux (program d e hd he (.inr .vertexSeed)) _ _) = _
    simp only [program, mainInstruction, TM2.stepAux, b4, memory_vertex,
      update_vertex, next, encodeWord, List.replicate_zero, List.nil_append]
  have all := joinTrace (joinTrace (joinTrace (joinTrace copyRun countRun) headerRun) fuelRun) seedRun
  have count : preparationSteps n h =
      (((2 * (h.length + 1) + (2 * (n + 1) + 1)) + (2 * (n + 1) + 1)) +
        (2 * (n + 1) + 1)) + 1 := by unfold preparationSteps; omega
  rw [count]
  exact all

theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem encodeWords_flatten (items : List (List Nat)) :
    encodeWords items.flatten = (items.map encodeWords).flatten := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatten_cons, List.map_cons, encodeWords_append, ih]

theorem encodeWords_flatten_flatMap {α : Type*} (items : List (List α))
    (words : α → List Nat) :
    encodeWords (items.flatten.flatMap words) =
      (items.map fun xs => encodeWords (xs.flatMap words)).flatten := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simp only [List.flatten_cons, List.flatMap_append, encodeWords_append, List.map_cons, ih]

def oldBlock {n d : Nat} (G : PortTables.Table n d) (v : Fin n) : List Bool :=
  MachineLazyRows.recordsInput (oldRows G v)
def expanderBlock {n e : Nat} (H : ExpanderTables.Table n e) (v : Fin n) : List Bool :=
  encodeWords (List.ofFn (expanderValues H v))

def oldOutput {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) : List Bool :=
  MachineLazyRows.recordsOutput d (d + e) 0 (oldRows G v)
def expanderOutput {n e : Nat} (d : Nat) (H : ExpanderTables.Table n e) (v : Fin n) : List Bool :=
  MachineOverlayRows.streamOutput d e v.val (List.ofFn (expanderValues H v))
def outputBlock {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) : List Bool := oldOutput G e v ++ expanderOutput d H v

theorem oldOutput_eq {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) :
    oldOutput G e v = encodeWords ((List.ofFn (oldRow G e v)).flatMap rowWords) := by
  rw [encodeWords_flatMap]
  simp only [oldOutput, oldRows, MachineLazyRows.recordsOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  change MachineLazyRows.reindexRowBits d (d + e) 0 (row G v p).tail.val
    (row G v p).reverseIndex.val (row G v p).relation = encodeWords (rowWords (oldRow G e v p))
  rw [oldRow_words]
  simp only [MachineLazyRows.reindexRowBits, MachinePortReindex.value, Nat.add_zero,
    oldReverseMap, row, PreprocessingLazyWords.row, List.cons_append, List.nil_append,
    encodeWords, List.append_assoc]

theorem expanderOutput_eq {n e : Nat} (d : Nat) (H : ExpanderTables.Table n e) (v : Fin n) :
    expanderOutput d H v = encodeWords ((List.ofFn (expanderRow d H v)).flatMap rowWords) :=
  MachineOverlayRows.streamOutput_expanderRows d H v

theorem outputBlock_eq {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    outputBlock G H v = encodeWords ((vertexRows G H v).flatMap rowWords) := by
  rw [outputBlock, oldOutput_eq, expanderOutput_eq]
  simp only [vertexRows, List.flatMap_append, encodeWords_append]

theorem graphRows_blocks {n d : Nat} (G : PortTables.Table n d) :
    MachineTableSplit.rowsBits (PortTables.graphTable G) = (List.ofFn (oldBlock G)).flatten := by
  change encodeWords ((PortTables.flatRows G).toList.flatMap rowWords) = _
  rw [PreprocessingLazyWords.flatRows_list, encodeWords_flatten_flatMap, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact (MachineLazyRows.recordsInput_eq_codec (oldRows G v)).symm

theorem expanderRows_blocks {n e : Nat} (H : ExpanderTables.Table n e) :
    encodeWords (ExpanderTableWords.rotationWords H) = (List.ofFn (expanderBlock H)).flatten := by
  rw [rotationWords_vertices, encodeWords_flatten, List.map_ofFn]
  rfl

theorem tableBits_blocks {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.tableBits (PreprocessingOverlayTables.overlay G H) =
      encodeWords [n, n * (d + e)] ++ (List.ofFn (outputBlock G H)).flatten := by
  rw [tableBits_overlay, encodeWords_append, encodeWords_flatten_flatMap, List.map_ofFn]
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact (outputBlock_eq G H v).symm

theorem oldFrame {n m : Nat} (g h gs hs nv mv f v out : List Bool)
    (rows : List (DartRow n m)) :
    MachineLazyRows.streamFrame oldTapes (memory g h gs hs nv mv f v [] []) rows out =
      memory g h (MachineLazyRows.recordsInput rows ++ gs) hs nv mv f v [] out := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [MachineLazyRows.streamFrame, oldTapes, memory, tail, oldReverse, relation,
      scratch, dividedCopy, quotient, newReverse, output, rowBuffer, graphStream]

theorem expanderFrame (g h gs hs nv mv f v t out : List Bool) (words : List Nat) :
    MachineOverlayRows.streamFrame expanderTapes (memory g h gs hs nv mv f v t []) words out =
      memory g h gs (encodeWords words ++ hs) nv mv f v t out := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [MachineOverlayRows.streamFrame, expanderTapes, memory, tail, oldReverse,
      relation, scratch, dividedCopy, quotient, newReverse, output, rowBuffer, expanderStream]

theorem tailCopyTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs hs nv mv f out : List Bool) (k : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[2 * (k + 1) + 1]
      (some ⟨next .tailSeed, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩) =
      some ⟨next (.expander (0, none)), clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩ := by
  let ambient := (clean d e hd he a).1
  have hrun := MachineUnaryAffineAt.seededAffineTrace vertex scratch tail
    (by decide) (by decide) (by decide) 1 0
    (.inr .tailSeed) (.inr .tailScan) (.inr .tailRestore) (next (.expander (0, none)))
    (program d e hd he) rfl rfl rfl
    (memory g h gs hs nv mv f (encodeWord k) [] out) k []
    (by simp [memory, vertex]) rfl ambient none
  simpa only [memory_tail, next, List.append_nil, Nat.one_mul, Nat.add_zero, update_tail,
    ambient, clean, MachineLazyRows.streamClean, MachinePortReindex.clean] using hrun

theorem tailFinishTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h gs hs nv mv f out : List Bool) (k : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[k + 3]
      (some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (k + 1)) [] out⟩ := by
  let ambient := (clean d e hd he a).1
  have hd₀ := MachineDrain.drainTrace tail (.inr .drainTail) (next .increment)
    (program d e hd he) rfl (memory g h gs hs nv mv f (encodeWord k) [] out)
    (encodeWord k) ambient none
  have drain : (advance (TM2.step (program d e hd he)))^[k + 2]
      (some ⟨next .drainTail, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) (encodeWord k) out⟩) =
      some ⟨next .increment, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩ := by
    simpa only [next, encodeWord_length, Nat.add_assoc, update_tail, ambient, clean,
      MachineLazyRows.streamClean, MachinePortReindex.clean] using hd₀
  have increment : (advance (TM2.step (program d e hd he)))^[1]
      (some ⟨next .increment, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord k) [] out⟩) =
      some ⟨next .guard, clean d e hd he a,
        memory g h gs hs nv mv f (encodeWord (k + 1)) [] out⟩ := by
    change some (TM2.stepAux (program d e hd he (.inr .increment)) _ _) = _
    simp only [program, mainInstruction, TM2.stepAux, memory_vertex, next,
      update_vertex, encodeWord, List.replicate_succ, List.cons_append]
  have all := joinTrace drain increment
  simpa only [Nat.add_assoc] using all

def pairSteps {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (out : List Bool) : Nat :=
  MachineLazyRows.vertexSteps d (d + e) 0 (oldRows G v) out + (2 * (v.val + 1) + 1) +
    MachineOverlayRows.vertexSteps d e v.val (List.ofFn (expanderValues H v))
      (out ++ oldOutput G e v) + (v.val + 3)

theorem cleanupTrace (d e : Nat) (hd : 0 < d) (he : 0 < e)
    (g h out : List Bool) (n m : Nat) (a : A) :
    (advance (TM2.step (program d e hd he)))^[cleanupSteps n m]
      (some ⟨next .drainFuel, clean d e hd he a,
        memory g h [] [] (encodeWord n) (encodeWord m) (encodeWord 0) (encodeWord n) [] out⟩) =
      some ⟨none, clean d e hd he a, memory g h [] [] [] [] [] [] [] out⟩ := by
  let ambient := (clean d e hd he a).1
  have h₁ := MachineDrain.drainTrace fuel (.inr .drainFuel) (next .drainVertex)
    (program d e hd he) rfl
    (memory g h [] [] (encodeWord n) (encodeWord m) [] (encodeWord n) [] out)
    (encodeWord 0) ambient none
  have h₂ := MachineDrain.drainTrace vertex (.inr .drainVertex) (next .drainVertexCount)
    (program d e hd he) rfl
    (memory g h [] [] (encodeWord n) (encodeWord m) [] [] [] out)
    (encodeWord n) ambient none
  have h₃ := MachineDrain.drainTrace vertexCount (.inr .drainVertexCount) (next .drainDartCount)
    (program d e hd he) rfl (memory g h [] [] [] (encodeWord m) [] [] [] out)
    (encodeWord n) ambient none
  have h₄ := MachineDrain.drainTrace dartCount (.inr .drainDartCount) none
    (program d e hd he) rfl (memory g h [] [] [] [] [] [] [] out)
    (encodeWord m) ambient none
  simp only [encodeWord_length, update_fuel, update_vertex, update_vertexCount, update_dartCount] at h₁ h₂ h₃ h₄
  have all := joinTrace (joinTrace (joinTrace h₁ h₂) h₃) h₄
  have hsteps : cleanupSteps n m = ((0 + 1 + 1 + (n + 1 + 1)) + (n + 1 + 1)) + (m + 1 + 1) := by
    unfold cleanupSteps
    omega
  rw [hsteps]
  exact all

def rawExpander {n e : Nat} (H : ExpanderTables.Table n e) : List Bool :=
  encodeWords (ExpanderTableWords.rotationWords H)

def outputPrefix {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (k : Nat) : List Bool := encodeWords [n, n * (d + e)] ++ emittedPrefix (outputBlock G H) k

theorem outputPrefix_step {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    outputPrefix G H (v.val + 1) = outputPrefix G H v.val ++ outputBlock G H v := by
  simp only [outputPrefix, prefix_step, List.append_assoc]

def loopBase {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (r : Nat) : Tape → List Bool :=
  memory (PortTables.tableBits G) (rawExpander H)
    (remaining (oldBlock G) (n - r)) (remaining (expanderBlock H) (n - r))
    (encodeWord n) (encodeWord (n * d)) [] (encodeWord (n - r)) [] (outputPrefix G H (n - r))

def loopCost {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (r : Nat) : Nat :=
  if hr : r < n then
    pairSteps G H ⟨n - (r + 1), by omega⟩ (outputPrefix G H (n - (r + 1)))
  else 0

def tableSteps {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) : Nat :=
  MachineTableSplit.exactSteps n (n * d) (MachineTableSplit.rowsBits (PortTables.graphTable G)) +
    preparationSteps n (rawExpander H) + MachineCountedLoop.totalSteps (loopCost G H) n +
    cleanupSteps n (n * d)

theorem oldOutput_length_le {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) :
    (oldOutput G e v).length ≤ d * oldSize d e n := by
  have bound := flatMap_length_le (oldRows G v)
    (fun r => MachineLazyRows.reindexRowBits d (d + e) 0 r.tail.val r.reverseIndex.val r.relation)
    (oldSize d e n) (fun r _ => MachineLazyRows.reindexRowBits_length_le d (d + e) 0 r)
  simpa only [oldOutput, MachineLazyRows.recordsOutput, oldRows, List.length_ofFn] using bound

theorem expanderOutput_length_le {n e : Nat} (d : Nat) (H : ExpanderTables.Table n e)
    (v : Fin n) : (expanderOutput d H v).length ≤ e * expanderSize d e n := by
  have bound := flatMap_length_le (List.ofFn (expanderValues H v))
    (MachineOverlayRows.rowBits d e v.val) (expanderSize d e n) (by
      intro j hj
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hj
      have hrow := MachineOverlayRows.rowBits_length_le d e v.val (expanderValues H v p)
        (n * e) (MachineOverlayRows.expanderValues_bounded H v p)
      have hv := v.isLt.le
      unfold expanderSize MachineOverlayRows.rowSizeBound at *
      omega)
  simpa only [expanderOutput, MachineOverlayRows.streamOutput, List.length_ofFn] using bound

theorem outputBlock_length_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    (outputBlock G H v).length ≤ blockSize d e n := by
  have hg := oldOutput_length_le G e v
  have hh := expanderOutput_length_le d H v
  simp only [outputBlock, List.length_append, blockSize]
  omega

theorem outputPrefix_length_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (k : Nat) :
    (outputPrefix G H k).length ≤ outputCapacity d e n := by
  have hblocks := flatten_length_le ((List.ofFn (outputBlock G H)).take k)
    (blockSize d e n) (by
      intro xs hx
      have hm := List.mem_of_mem_take hx
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hm
      exact outputBlock_length_le G H v)
  have hlen : ((List.ofFn (outputBlock G H)).take k).length ≤ n := by
    simp only [List.length_take, List.length_ofFn]
    exact Nat.min_le_right _ _
  have hcap := Nat.mul_le_mul_right (blockSize d e n) hlen
  simp only [outputPrefix, emittedPrefix, List.length_append, encodeWords_length,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, Nat.add_zero, outputCapacity]
  omega

theorem pairSteps_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (out : List Bool)
    (hout : out.length ≤ outputCapacity d e n) : pairSteps G H v out ≤ pairBudget d e n := by
  have hold := MachineLazyRows.vertexSteps_le d (d + e) 0 (oldRows G v) out
  simp only [oldRows, List.length_ofFn] at hold
  have hgsize := oldOutput_length_le G e v
  have hnew := MachineOverlayRows.vertexSteps_le d e v.val (n * e)
    (List.ofFn (expanderValues H v)) (by
      intro j hj
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hj
      exact MachineOverlayRows.expanderValues_bounded H v p) (out ++ oldOutput G e v)
  simp only [List.length_ofFn, List.length_append] at hnew
  have hv := v.isLt.le
  have hsize : MachineOverlayRows.rowSizeBound d e v.val (n * e) ≤ expanderSize d e n := by
    unfold expanderSize MachineOverlayRows.rowSizeBound
    omega
  have hcost : MachineOverlayRows.rowCostBound d e v.val (n * e) ≤
      MachineOverlayRows.rowCostBound d e n (n * e) := by
    unfold MachineOverlayRows.rowCostBound
    change _ ≤ 8 * (n * e) + 4 * expanderSize d e n + _ + _ + 28
    omega
  have hsizeMul := Nat.mul_le_mul_left e hsize
  have holdBudget := Nat.mul_le_mul_left d
    (show MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
        2 * (out.length + d * MachineLazyRows.rowSizeBound (d + e) 0 n (n * d)) + 1 ≤
      MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
        2 * (outputCapacity d e n + d * oldSize d e n) + 1 by
      unfold oldSize
      omega)
  have hnewBudget := Nat.mul_le_mul_left e
    (show MachineOverlayRows.rowCostBound d e v.val (n * e) +
        2 * (out.length + (oldOutput G e v).length + e * MachineOverlayRows.rowSizeBound d e v.val (n * e)) + 1 ≤
      MachineOverlayRows.rowCostBound d e n (n * e) +
        2 * (outputCapacity d e n + d * oldSize d e n + e * expanderSize d e n) + 1 by omega)
  unfold pairSteps pairBudget oldRows
  omega

theorem loopSteps_le {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    MachineCountedLoop.totalSteps (loopCost G H) n ≤ n * (pairBudget d e n + 1) + 1 := by
  apply MachineCountedLoop.totalSteps_le
  intro r hr
  rw [loopCost, dite_eq_left hr]
  exact pairSteps_le G H _ _ (outputPrefix_length_le G H _)

theorem tableSteps_le {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    tableSteps G H ≤ (timePolynomial d e).eval ((PortTables.tableBits G).length + (rawExpander H).length) := by
  have hsplit := MachineTableSplit.exactSteps_le n (n * d)
    (MachineTableSplit.rowsBits (PortTables.graphTable G))
  have header : encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G) =
      PortTables.tableBits G := (MachineTableSplit.tableBits_header_rows (PortTables.graphTable G)).symm
  rw [header, MachineTableSplit.timePolynomial_eval] at hsplit
  have hn := PortTables.vertices_le_tableBits_length G
  have hloop := loopSteps_le G H
  have hmono := natPolynomial_eval_mono (phasePolynomial d e)
    (show n ≤ (PortTables.tableBits G).length + (rawExpander H).length by omega)
  rw [phasePolynomial_eval] at hmono
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  unfold tableSteps preparationSteps
  omega

end BinPackingGames.Foundations.Complexity.MachineOverlayTable

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachinePaddedOverlayRuntime
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

abbrev Tape := MachineVertexPadding.Tape ⊕ (MachineExpanderFamily.Tape ⊕ MachineOverlayTable.Tape)
abbrev Alphabet (_ : Tape) := Bool
abbrev Label (d : Nat) := MachineVertexPadding.Label d ⊕ (MachineExpanderFamily.Label baseDegree ⊕ MachineOverlayTable.Label d overlayDegree)
abbrev State (d : Nat) := MachineVertexPadding.State (MachineExpanderFamily.State Unit baseDegree × MachineOverlayTable.State Unit d overlayDegree)

theorem overlayDegree_positive : 0 < overlayDegree :=
  Nat.mul_pos MachineExpanderFamily.baseDegree_positive MachineExpanderFamily.baseDegree_positive

def paddingTape (k : MachineVertexPadding.Tape) : Tape := .inl k

def paddingView : Tape → Option MachineVertexPadding.Tape
  | .inl k => some k
  | .inr _ => none

@[simp] theorem paddingView_left (k : MachineVertexPadding.Tape) : paddingView (paddingTape k) = some k := rfl

theorem paddingView_right (j : Tape) (k : MachineVertexPadding.Tape)
    (h : paddingView j = some k) : paddingTape k = j := by
  cases j with
  | inl j => cases Option.some.inj h; rfl
  | inr j => simp [paddingView] at h

def familyTape (k : MachineExpanderFamily.Tape) : Tape :=
  if k = .inr .remainingLevel then .inl .level else .inr (.inl k)

def familyView : Tape → Option MachineExpanderFamily.Tape
  | .inl .level => some (.inr .remainingLevel)
  | .inr (.inl k) => if k = .inr .remainingLevel then none else some k
  | _ => none

@[simp] theorem familyView_left (k : MachineExpanderFamily.Tape) : familyView (familyTape k) = some k := by
  by_cases h : k = .inr .remainingLevel
  · subst k; rfl
  · simp [familyTape, familyView, h]

theorem familyView_right (j : Tape) (k : MachineExpanderFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  rcases j with j | j
  · cases j <;> simp_all [familyView, familyTape]
  · rcases j with j | j
    · by_cases hj : j = .inr .remainingLevel <;> simp_all [familyView, familyTape]
    · simp [familyView] at h

def overlayTape (k : MachineOverlayTable.Tape) : Tape :=
  if k = MachineOverlayTable.graphArchive then .inl .output
  else if k = MachineOverlayTable.expanderArchive then .inr (.inl MachineExpanderFamily.tableTape)
  else .inr (.inr k)

def overlayView : Tape → Option MachineOverlayTable.Tape
  | .inl .output => some MachineOverlayTable.graphArchive
  | .inr (.inl k) => if k = MachineExpanderFamily.tableTape then some MachineOverlayTable.expanderArchive else none
  | .inr (.inr k) =>
      if k = MachineOverlayTable.graphArchive ∨ k = MachineOverlayTable.expanderArchive then none else some k
  | _ => none

@[simp] theorem overlayView_left (k : MachineOverlayTable.Tape) : overlayView (overlayTape k) = some k := by
  by_cases hg : k = MachineOverlayTable.graphArchive
  · subst k; rfl
  · by_cases he : k = MachineOverlayTable.expanderArchive
    · subst k; rfl
    · simp [overlayTape, overlayView, hg, he]

theorem overlayView_right (j : Tape) (k : MachineOverlayTable.Tape)
    (h : overlayView j = some k) : overlayTape k = j := by
  rcases j with j | j
  · cases j <;> simp_all [overlayView, overlayTape, MachineOverlayTable.graphArchive]
  · rcases j with j | j
    · by_cases hj : j = MachineExpanderFamily.tableTape
      · subst j
        have hk : MachineOverlayTable.expanderArchive = k := by
          simpa [overlayView] using h
        subst k
        rfl
      · simp [overlayView, hj] at h
    · by_cases hg : j = MachineOverlayTable.graphArchive
      · simp [overlayView, hg] at h
      · by_cases he : j = MachineOverlayTable.expanderArchive
        · simp [overlayView, he] at h
        · simp_all [overlayView, overlayTape]

variable {d : Nat}

def paddingLabel (l : MachineVertexPadding.Label d) : Label d := .inl l
def familyLabel (l : MachineExpanderFamily.Label baseDegree) : Label d := .inr (.inl l)
def overlayLabel (l : MachineOverlayTable.Label d overlayDegree) : Label d := .inr (.inr l)
def main : Label d := paddingLabel (.splitCode .copyFirst)
def familyEntry : Label d := familyLabel (.inr .initialize_)
def overlayEntry : Label d := overlayLabel (.inl .copyFirst)

def familyStates (d : Nat) :
    (MachineExpanderFamily.State Unit baseDegree × ((MachineOverlayTable.State Unit d overlayDegree × Bool) × Option Bool)) ≃
      State d where
  toFun s := (((s.1, s.2.1.1), s.2.1.2), s.2.2)
  invFun s := (s.1.1.1, ((s.1.1.2, s.1.2), s.2))
  left_inv := by rintro ⟨f, ⟨⟨o, b⟩, r⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨f, o⟩, b⟩, r⟩; rfl

def overlayStates (d : Nat) :
    (MachineOverlayTable.State Unit d overlayDegree × ((MachineExpanderFamily.State Unit baseDegree × Bool) × Option Bool)) ≃
      State d where
  toFun s := (((s.2.1.1, s.1), s.2.1.2), s.2.2)
  invFun s := (s.1.1.2, ((s.1.1.1, s.1.2), s.2))
  left_inv := by rintro ⟨o, ⟨⟨f, b⟩, r⟩⟩; rfl
  right_inv := by rintro ⟨⟨⟨f, o⟩, b⟩, r⟩; rfl

def familySource (H : BaseTable) (d : Nat) : MachineExpanderFamily.Label baseDegree →
    TM2.Stmt MachineExpanderFamily.BoolAlphabet (MachineExpanderFamily.Label baseDegree) (State d) :=
  MachineStateEquiv.program (familyStates d) (MachineStateFrame.frameProgram
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H MachineExpanderFamily.baseDegree_cloud_gt_one))

def overlaySource (d : Nat) (hd : 0 < d) : MachineOverlayTable.Label d overlayDegree →
    TM2.Stmt (fun _ : MachineOverlayTable.Tape => Bool) (MachineOverlayTable.Label d overlayDegree) (State d) :=
  MachineStateEquiv.program (overlayStates d) (MachineStateFrame.frameProgram
    (MachineOverlayTable.program d overlayDegree hd overlayDegree_positive))

def program (H : BaseTable) (d : Nat) (hd : 0 < d) :
    Label d → TM2.Stmt Alphabet (Label d) (State d)
  | .inl l => Placement.statement paddingTape paddingLabel (some familyEntry) (MachineVertexPadding.program d hd l)
  | .inr (.inl l) => Placement.statement familyTape familyLabel (some overlayEntry)
      (familySource H d l)
  | .inr (.inr l) => Placement.statement overlayTape overlayLabel none (overlaySource d hd l)

def clean (H : BaseTable) (d : Nat) (hd : 0 < d) : State d :=
  (((MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H (),
    MachineOverlayTable.clean d overlayDegree hd overlayDegree_positive ()), false), none)

def memory (input padded level rotor count output : List Bool) : Tape → List Bool
  | .inl k => MachineVertexPadding.memory input padded [] [] [] level [] [] k
  | .inr (.inl (.inl (.inl .table))) => rotor
  | .inr (.inl (.inr .currentSize)) => count
  | .inr (.inl _) => []
  | .inr (.inr k) => if k = MachineOverlayTable.output then output else []

def padded {n d : Nat} (t : PortTables.Table n d) :=
  PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)

def rotor (H : BaseTable) (n : Nat) : List Bool :=
  encodeWords (ExpanderTableWords.rotationWords
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel n)))

def initialTapes {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) [] [] [] [] []

def paddedTapes {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord (PreprocessingLevels.boundedLevel n)) [] [] []

def familyTapes (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord 0) (rotor H n) (encodeWord (PreprocessingLevels.paddedSize n)) []

def finalTapes (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord 0) (rotor H n) (encodeWord (PreprocessingLevels.paddedSize n))
    (PortTables.tableBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩).2)

def placeExecution {K Λ S : Type} [DecidableEq K]
    (tape : K → Tape) (view : Tape → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Label d) (exit : Option (Label d)) (extra : Tape → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ S)
    (target : Label d → TM2.Stmt Alphabet (Label d) S)
    (atLabels : ∀ l, target (labels l) = Placement.statement tape labels exit (source l))
    {a b : TM2.Cfg (fun _ : K => Bool) Λ S} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (Placement.configuration view labels exit extra a)
      (some (Placement.configuration view labels exit extra b)) budget :=
  liftExecutionInTime _ _ _
    (Placement.step_simulation tape view left right labels exit extra source target atLabels) run

theorem padding_initial_memory (input : List Bool) :
    Placement.tapes paddingView (MachineVertexPadding.memory input [] [] [] [] [] [] []) (fun _ => []) =
      memory input [] [] [] [] [] := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;> rfl
      · cases k <;> rfl
    · simp [Placement.tapes, paddingView, memory]

theorem padding_final_memory (input output level : List Bool) :
    Placement.tapes paddingView (MachineVertexPadding.memory input output [] [] [] level [] []) (fun _ => []) =
      memory input output level [] [] [] := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;> rfl
      · cases k <;> rfl
    · simp [Placement.tapes, paddingView, memory]

theorem family_initial_memory (input output : List Bool) (level : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes (MachineExpanderFamily.initialTapes level []))
      (memory input output (encodeWord level) [] [] []) =
      memory input output (encodeWord level) [] [] [] := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, familyView, memory,
      MachineVertexPadding.memory, MachineExpanderFamily.toBoolTapes,
      MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
      MachineEmbedding.tapes]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
            MachineExpanderFamily.tableFrame, MachineEmbedding.tapes]
      · cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
            MachineEmbedding.tapes]
    · rfl

theorem family_final_memory (H : BaseTable) (input output : List Bool) (level : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes (MachineExpanderFamily.familyTapes H level []))
      (memory input output (encodeWord level) [] [] []) =
      memory input output (encodeWord 0)
        (encodeWords (ExpanderTableWords.rotationWords (ExpanderTables.family H level)))
        (encodeWord (ExpanderTables.vertexCount overlayDegree level)) [] := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, familyView, memory,
      MachineVertexPadding.memory, MachineExpanderFamily.toBoolTapes,
      MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
      MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
      MachineEmbedding.tapes]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
            MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.tableFrame,
            MachineEmbedding.tapes]
      · cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
            MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
            MachineEmbedding.tapes, overlayDegree, PreprocessingRegularTables.internalDegree,
            ExpanderRowControl.degree]
    · simp [Placement.tapes, familyView, memory]

theorem rotationWords_resize {n m q : Nat} (h : n = m) (H : ExpanderTables.Table n q) :
    ExpanderTableWords.rotationWords (PreprocessingRegularTables.resizeTable h H) =
      ExpanderTableWords.rotationWords H := by
  cases h
  rfl

theorem rotor_familyAt (H : BaseTable) (n : Nat) :
    MachineOverlayTable.rawExpander (PreprocessingStageMaps.familyAt H n) = rotor H n := by
  unfold MachineOverlayTable.rawExpander PreprocessingStageMaps.familyAt rotor
  exact congrArg encodeWords (rotationWords_resize _ _)

theorem overlay_memory (input graph raw count output : List Bool) :
    Placement.tapes overlayView
      (MachineOverlayTable.memory graph raw [] [] [] [] [] [] [] output)
      (memory input graph (encodeWord 0) raw count []) =
      memory input graph (encodeWord 0) raw count output := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, overlayView, memory, MachineVertexPadding.memory,
      MachineOverlayTable.memory, MachineOverlayTable.graphArchive]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, overlayView, memory, MachineExpanderFamily.tableTape,
            MachineOverlayTable.memory, MachineOverlayTable.expanderArchive]
      · cases k <;>
          simp [Placement.tapes, overlayView, memory, MachineExpanderFamily.tableTape]
    · rcases k with k | k <;> fin_cases k <;>
        simp [Placement.tapes, overlayView, memory, MachineOverlayTable.memory,
          MachineOverlayTable.graphArchive, MachineOverlayTable.expanderArchive,
          MachineOverlayTable.output]

theorem archive_length_le (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) :
    (PortTables.tableBits (padded t)).length + (rotor H n).length ≤
      (archivePolynomial d).eval (PortTables.tableBits t).length := by
  let m := PreprocessingLevels.paddedSize n
  let s := ExpanderFamily.growth * ((PortTables.tableBits t).length + 1)
  have hm : m ≤ s := MachineVertexPadding.power_length_bound t
  have hmd : m*d ≤ s*d := Nat.mul_le_mul_right d hm
  have hmq : m*overlayDegree ≤ s*overlayDegree := Nat.mul_le_mul_right overlayDegree hm
  have hg := GraphTables.tableBits_length_le (PortTables.graphTable (padded t))
  change (PortTables.tableBits (padded t)).length ≤
    m + m*d + 2 + m*d*(m + m*d + 8192) at hg
  have hg' := hg.trans (Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add hm hmd) 2)
    (Nat.mul_le_mul hmd (Nat.add_le_add_right (Nat.add_le_add hm hmd) 8192)))
  have hr := ExpanderTableWords.encode_rotationWords_length_le
    (PreprocessingStageMaps.familyAt H n)
  change (MachineOverlayTable.rawExpander (PreprocessingStageMaps.familyAt H n)).length ≤
    (m*overlayDegree)*(m*overlayDegree+1) at hr
  rw [rotor_familyAt] at hr
  have hr' := hr.trans (Nat.mul_le_mul hmq (Nat.add_le_add_right hmq 1))
  have h := Nat.add_le_add hg' hr'
  simpa only [archivePolynomial, sizePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat,
    s] using h

noncomputable def familyPolynomial : Polynomial Nat :=
  Polynomial.C MachineExpanderFamilyBounds.inputCoefficient * (Polynomial.X + 1)^5

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  MachineVertexPadding.timePolynomial d + familyPolynomial +
    (MachineOverlayTable.timePolynomial d overlayDegree).comp (archivePolynomial d)

def machine (H : BaseTable) (d : Nat) (hd : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .inl .original
  k₁ := .inr (.inr MachineOverlayTable.output)
  Γ := Alphabet
  Λ := Label d
  main := main
  σ := State d
  initialState := clean H d hd
  m := program H d hd

theorem initial_configuration (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    initList (machine H d hd) (PortTables.tableBits t) =
      ⟨some main, clean H d hd, initialTapes t⟩ := by
  have ht : (initList (machine H d hd) (PortTables.tableBits t)).stk = initialTapes t := by
    funext k
    rcases k with k | k
    · (cases k <;> simp [initList, machine, initialTapes, memory, MachineVertexPadding.memory]); rfl
    · rcases k with k | k
      · rcases k with k | k
        · rcases k with k | k <;> cases k <;>
            simp [initList, machine, initialTapes, memory]
        · cases k <;> simp [initList, machine, initialTapes, memory]
      · simp [initList, machine, initialTapes, memory]
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem final_output (H : BaseTable) {n d : Nat} (hd : 0 < d)
    (t : PortTables.Table n d) :
    finalTapes H t (machine H d hd).k₁ =
      PortTables.inputBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩) := by
  simp [finalTapes, machine, memory, PortTables.inputBits]

end BinPackingGames.Foundations.Complexity.MachinePaddedOverlay

namespace BinPackingGames.Foundations.Complexity.MachinePaddedOverlayRuntime

open Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label State)

def rawProgram (H : BaseTable) (d : Nat) (hd : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .inl .original
  output := .inr (.inr MachineOverlayTable.output)
  main := MachinePaddedOverlay.main
  initial := MachinePaddedOverlay.clean H d hd
  code := MachinePaddedOverlay.program H d hd

noncomputable def cleanupTapes : List Tape :=
  (Finset.univ.erase (.inr (.inr MachineOverlayTable.output) : Tape)).toList

theorem cleanup_complete (H : BaseTable) (d : Nat) (hd : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H d hd).output := by
  simp [cleanupTapes, rawProgram]

theorem initial_configuration (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    initList (MachineCanonicalOutput.sourceMachine (rawProgram H d hd))
        (PortTables.inputBits a) =
      ⟨some MachinePaddedOverlay.main, MachinePaddedOverlay.clean H d hd,
        MachinePaddedOverlay.initialTapes a.2⟩ := by
  change initList (MachinePaddedOverlay.machine H d hd) (PortTables.tableBits a.2) = _
  exact MachinePaddedOverlay.initial_configuration H hd a.2

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

theorem rotorSize_le_encodedLength {n q : Nat} (positive : 0 < q)
    (table : ExpanderTables.Table n q) :
    n ≤ (encodeWords (ExpanderTableWords.rotationWords table)).length := by
  have h : n * q ≤ (encodeWords (ExpanderTableWords.rotationWords table)).length := by
    rw [encodeWords_length, ExpanderTableWords.rotationWords_length]
    omega
  exact (Nat.le_mul_of_pos_right n positive).trans h

end BinPackingGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PreprocessingRegularBounds
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
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

theorem inherited_original_words (e : Fin t.darts) :
    GraphTables.rowWords (actualRow t padding tables (.inl e) (.inr ())) =
      [e.val, (q + 1) * t.rows[e].reverseIndex.val + q] ++
        GraphTables.relationWords t.rows[e].relation := by
  simp only [GraphTables.rowWords, actualRow_tail, vertexOrder_original,
    inherited_original_reverse, inherited_original_relation]

theorem actualRow_bits (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    encodeWords (GraphTables.rowWords (actualRow t padding tables x p)) =
      PreprocessingPaddingWords.rowBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) (portOrder q p) := by
  simpa only [actualRow, Equiv.symm_apply_apply] using
    PreprocessingPaddingWords.rowBits_flat (ofCloudTables t padding tables)
      (PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p))

theorem vertexBits_eq (x : Vertex t padding) :
    vertexBits t padding tables x =
      PreprocessingPaddingWords.vertexBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) := by
  unfold vertexBits vertexRows
  rw [List.flatMap_append, encodeWords_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun p : Fin q =>
    encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inl p))))).flatten ++
      encodeWords (GraphTables.rowWords (actualRow t padding tables x (.inr ()))) = _
  simp_rw [actualRow_bits]
  unfold PreprocessingPaddingWords.vertexBits
  rw [List.ofFn_succ_last, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rfl

theorem paddingOrder_ofFn :
    List.ofFn (paddingOrder padding).symm = paddingList padding := by
  calc
    List.ofFn (paddingOrder padding).symm =
        List.ofFn (fun i : Fin (paddingList padding).length =>
          (paddingOrder padding).symm (Fin.cast (paddingList_length padding) i)) :=
      List.ofFn_congr (paddingList_length padding).symm (paddingOrder padding).symm
    _ = paddingList padding := by
      change List.ofFn (fun i => (paddingList padding).get i) = _
      exact List.ofFn_get _

theorem vertexOrder_ofFn {α : Type*} (f : Vertex t padding → α) :
    List.ofFn (fun i : Fin (vertexCount t padding) => f ((vertexOrder t padding).symm i)) =
      List.ofFn (fun e : Fin t.darts => f (.inl e)) ++
        (paddingList padding).map (fun z => f (.inr z)) := by
  let order : Vertex t padding ≃ Fin (t.darts + ∑ v, padding v) := vertexOrder t padding
  change List.ofFn (fun i : Fin (t.darts + ∑ v, padding v) =>
    f (order.symm i)) = _
  rw [List.ofFn_add]
  have hold (e : Fin t.darts) :
      order.symm (e.castLE (Nat.le_add_right t.darts (∑ v, padding v))) =
        Sum.inl e := order.symm_apply_apply (Sum.inl e)
  have hnew (i : Fin (∑ v, padding v)) :
      order.symm (i.natAdd t.darts) =
        Sum.inr ((paddingOrder padding).symm i) := by
    apply order.injective
    rw [Equiv.apply_symm_apply]
    change i.natAdd t.darts = Fin.natAdd t.darts
      ((paddingOrder padding) ((paddingOrder padding).symm i))
    rw [Equiv.apply_symm_apply]
  simp_rw [hold, hnew]
  congr 1
  calc
    List.ofFn (fun i => f (.inr ((paddingOrder padding).symm i))) =
        (List.ofFn (paddingOrder padding).symm).map (fun z => f (.inr z)) :=
      (List.map_ofFn (f := (paddingOrder padding).symm) (g := fun z => f (.inr z))).symm
    _ = _ := by rw [paddingOrder_ofFn]

theorem paddingList_flatMap {α : Type*} (f : (Σ v : Fin t.vertices, Fin (padding v)) → List α) :
    (paddingList padding).flatMap f =
      (List.ofFn (fun v : Fin t.vertices =>
        (List.ofFn (fun j : Fin (padding v) => f ⟨v, j⟩)).flatten)).flatten := by
  simp only [paddingList, List.sigma, List.finRange, List.flatMap_def,
    List.map_flatten, List.flatten_flatten, List.map_ofFn, Function.comp_def]

end BinPackingGames.Foundations.PCP.PreprocessingRegularWords

namespace BinPackingGames.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open BinPackingGames.Foundations.Complexity
open scoped BigOperators

theorem offset_succ {n : Nat} (p : Fin n → Nat) (k : Nat) (h : k < n) :
    PreprocessingPaddingOffsets.offset p (k + 1) =
      PreprocessingPaddingOffsets.offset p k + p ⟨k, h⟩ := by
  unfold PreprocessingPaddingOffsets.offset
  rw [List.take_succ_eq_append_getElem (show k < (List.finRange n).length by simpa using h)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.finRange, List.getElem_ofFn]

def header (t : GraphTables.Table) (p : Fin t.vertices → Nat) (q : Nat) : List Bool :=
  encodeWords [vertexCount t p, vertexCount t p * (q + 1)]

def originalPrefix (t : GraphTables.Table) (p : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + p v) q)
    (k : Nat) : List Bool :=
  header t p q ++ blocksPrefix (originalVertexBits t p tables) k

end BinPackingGames.Foundations.PCP.PreprocessingRegularBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularExecutionBounds
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open BinPackingGames.Foundations.PCP

variable {σ : Type}

def rankView : Tape → Option MachineCloudCount.Tape
  | .inl i => match i.val with
    | 0 => some .original
    | 10 => some .work
    | 9 => some .target
    | 11 => some .scratch
    | 3 => some .count
    | 12 => some .spare
    | _ => none
  | .inr _ => none

def prefixView : Tape → Option MachineCloudPrefix.Tape
  | .inl i => match i.val with
    | 0 => some (.inner .table)
    | 9 => some (.inner .query)
    | 10 => some (.inner .count)
    | 11 => some (.inner .work)
    | 12 => some (.inner .scratch)
    | 13 => some (.inner .spare)
    | 14 => some (.inner .power)
    | 15 => some (.inner .level)
    | 16 => some (.inner .fuel)
    | 17 => some (.inner .product)
    | 2 => some .bound
    | 18 => some .remaining
    | 5 => some .total
    | _ => none
  | .inr _ => none

theorem rankView_left (k : MachineCloudCount.Tape) : rankView (rankTape k) = some k := by
  cases k <;> rfl
theorem rankView_right (j : Tape) (k : MachineCloudCount.Tape)
    (h : rankView j = some k) : rankTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [rankView, rankTape] <;> subst k <;> rfl
  | inr j => simp_all [rankView]

theorem prefixView_left (k : MachineCloudPrefix.Tape) : prefixView (prefixTape k) = some k := by
  cases k with
  | inner k => cases k <;> rfl
  | bound => rfl
  | remaining => rfl
  | total => rfl
theorem prefixView_right (j : Tape) (k : MachineCloudPrefix.Tape)
    (h : prefixView j = some k) : prefixTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [prefixView, prefixTape] <;> subst k <;> rfl
  | inr j => simp_all [prefixView]

theorem drainAt (source : Tape) (again : Label) (exit : Option Label)
    (code : program (σ := σ) again = MachineDrain.drain source again exit)
    (base : Tape → List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[(base source).length + 1]
      (some ⟨some again, ((ambient, false), register), base⟩) =
      some ⟨exit, ((ambient, false), none), Function.update base source []⟩ := by
  simpa only [Function.update_eq_self] using
    MachineDrain.drainTrace source again exit program code base (base source)
      (ambient, false) register

def queryFrame (data : Data) (v x : Nat) : Tape → List Bool :=
  Function.update (Function.update (frame data) (.inl 9) (rankQuery v x))
    (.inl 3) (encodeWord 0)

end BinPackingGames.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalClean

open Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

theorem cleanupTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (base : Tape → List Bool) (state : State σ) :
    (advance (TM2.step program))^[cleanupSteps base]
      (some ⟨some (labels .query), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes base⟩ := by
  let t1 := Function.update base (2 : Tape) []
  let t2 := Function.update t1 (3 : Tape) []
  let t3 := Function.update t2 (4 : Tape) []
  let t4 := Function.update t3 (6 : Tape) []
  have h0 := MachineDrain.drainTrace (2 : Tape) (labels .query) (some (labels .scan))
    program (code .query) base (base 2) state.1 state.2
  have h1 := MachineDrain.drainTrace (3 : Tape) (labels .scan) (some (labels .rawReverse))
    program (code .scan) t1 (t1 3) state.1 none
  have h2 := MachineDrain.drainTrace (4 : Tape) (labels .rawReverse) (some (labels .computedReverse))
    program (code .rawReverse) t2 (t2 4) state.1 none
  have h3 := MachineDrain.drainTrace (6 : Tape) (labels .computedReverse) (some (labels .relation))
    program (code .computedReverse) t3 (t3 6) state.1 none
  have h4 := MachineDrain.drainTrace (7 : Tape) (labels .relation) exit
    program (code .relation) t4 (t4 7) state.1 none
  simp only [Function.update_eq_self] at h0 h1 h2 h3 h4
  simp only [t1, t2, t3, t4, Function.update_of_ne (by decide : (3 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 4),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (6 : Tape) ≠ 2),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 6),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 4),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 3),
    Function.update_of_ne (by decide : (7 : Tape) ≠ 2)] at h1 h2 h3 h4
  exact join_trace (join_trace (join_trace (join_trace h0 h1) h2) h3) h4

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalClean

namespace BinPackingGames.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

def originalView : CoreTape → Option MachineRegularOriginalClean.Tape :=
  ![some 1, some 0, none, none, none, none, none, none, some 9, some 5,
    some 2, some 3, some 4, none, none, none, none, none, none, none,
    none, none, none, none, some 6, some 7, some 8]

theorem originalView_left (k : MachineRegularOriginalClean.Tape) :
    originalView (originalTapes k) = some k := by fin_cases k <;> rfl

theorem originalView_right (j : CoreTape) (k : MachineRegularOriginalClean.Tape)
    (h : originalView j = some k) : originalTapes k = j := by
  fin_cases j <;> simp [originalView] at h
  all_goals subst k; rfl

end BinPackingGames.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularOwnerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

def cfg (H : BaseTable) (label : Option Label) (data : Data) : TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data⟩

theorem metadataPlacement (data extra : Data) :
    MachineCloudPadding.Placement.tapes metadataView (MachineRegularMetadata.frame data)
      (frame extra) = frame data := by
  funext j
  cases j with
  | inl i => rfl
  | inr j => cases j <;> rfl

theorem identityPlacement (base extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes some base extra = base := rfl

theorem clearFrame (data : Data) : clearMemory (frame data) 7 =
    frame { data with
      owner := []
      localRank := []
      count := []
      offset := []
      rotor := []
      padding := []
      level := [] } := by
  funext j
  cases j with
  | inl i => fin_cases i <;>
      simp [clearMemory, clearTape, frame, MachineRegularMetadata.frame]
  | inr j => cases j with
    | inl e => cases e <;>
        simp [clearMemory, clearTape, frame, MachineRegularMetadata.frame]
    | inr e => simp [clearMemory, clearTape, frame]

theorem emittedData_eq (H : BaseTable) (t : GraphTables.Table) (e : Fin t.darts)
    (output : List Bool) : emittedData H t e output =
      familyData H t e (output ++ emittedBits H t e) := rfl

end BinPackingGames.Foundations.Complexity.MachineRegularOriginalBody

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

theorem vertexTotal_eq (t : GraphTables.Table) :
    vertexTotal t = t.darts + paddingTotal t := by
  unfold vertexTotal PreprocessingRegularTables.vertexCount paddingTotal
  rw [PreprocessingPaddingOffsets.offset_all]

theorem initStep (q : Nat) (table output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .init, ((ambient, false), register),
        frame table [] [] [] [] [] [] [] [] [] [] [] output⟩ =
      some ⟨some (.lookup .vertices (.run .copyFirst)), ((ambient, false), register),
        frame table [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem seedMStep (q : Nat) (table n output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .seedM, ((ambient, false), register),
        frame table n [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ =
      some ⟨some (.lookup .darts (.run .copyFirst)), ((ambient, false), register),
        frame table n [] [] [] [] (encodeWord 1) [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem clearIndexStep (q : Nat) (table n m output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .clearIndex, ((ambient, false), register),
        frame table n [] [] [] m (encodeWord 0) [] [] [] [] [] output⟩ =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame table n [] [] [] m [] [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem computeTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[computeTime t]
      (some ⟨some (.copyFirst .count), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .rEmit), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩ := by
  have hc := MachineCopy.copyTrace mTape verticesTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .count) (Label.copySecond .count) (some Label.add)
    (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] [] [] [] output) rfl (ambient, false) register
  simp only [frame_m, frame_vertices, encodeWord_length, List.append_nil, update_frame_vertices] at hc
  have ha := MachineUnaryAddAt.addFromTapes sumTape verticesTape (by decide)
    Label.add (some Label.scaleSeed) (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] (encodeWord t.darts) [] [] output)
    (paddingTotal t) t.darts [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_sum, update_frame_vertices] at ha
  rw [show paddingTotal t + t.darts = vertexTotal t by rw [vertexTotal_eq]; omega] at ha
  have hm := MachineUnaryAffineAt.seededAffineTrace verticesTape scratchTape dartsTape
    (by decide) (by decide) (by decide) (q + 1) 0 Label.scaleSeed Label.scaleScan
    Label.scaleRestore (some (Label.copyFirst .rEmit)) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
      [] [] [] (encodeWord (vertexTotal t)) [] [] output)
    (vertexTotal t) [] (by simp) rfl (ambient, false) none
  simp only [frame_darts, List.append_nil, Nat.add_zero, update_frame_darts] at hm
  rw [show (q + 1) * vertexTotal t = dartTotal q t by unfold dartTotal; ac_rfl] at hm
  exact appendTrace _ (appendTrace _ hc ha) hm

theorem cleanupZerosStep (q : Nat) (table n m N R output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .cleanupZeros, ((ambient, false), register),
        frame table n n (encodeWord 0) (encodeWord 0) m [] [] [] N R [] output⟩ =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame table n n [] [] m [] [] [] N R [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

end Header

namespace Top

def headerView : Tape → Option Header.Tape
  | .inl (.inl i) => match i.val with
    | 0 => some Header.tableTape
    | 6 => some Header.mTape
    | 8 => some Header.outputTape
    | _ => none
  | .inl (.inr _) => none
  | .inr (.inl k) =>
      if k = Header.tableTape ∨ k = Header.mTape ∨ k = Header.outputTape then none else some k
  | .inr (.inr _) => none

theorem headerView_left (k : Header.Tape) : headerView (headerTape k) = some k := by
  by_cases ht : k = Header.tableTape
  · subst k; rfl
  by_cases hm : k = Header.mTape
  · subst k; rfl
  by_cases ho : k = Header.outputTape
  · subst k; rfl
  simp [headerTape, headerView, ht, hm, ho]

theorem headerView_right (j : Tape) (k : Header.Tape)
    (h : headerView j = some k) : headerTape k = j := by
  cases j with
  | inl j =>
    cases j with
    | inl i =>
      fin_cases i <;> simp_all [headerView] <;> subst k <;> rfl
    | inr e => cases h
  | inr j =>
    cases j with
    | inl i =>
      by_cases hi : i = Header.tableTape ∨ i = Header.mTape ∨ i = Header.outputTape
      · simp [headerView, hi] at h
      · have hik : i = k := by simpa [headerView, hi] using h
        subst k
        simp only [not_or] at hi
        simp [headerTape, hi.1, hi.2.1, hi.2.2]
    | inr i => cases h

def bodyView : Tape → Option Body
  | .inl k => some k
  | .inr _ => none

theorem bodyView_left (k : Body) : bodyView (.inl k) = some k := rfl
theorem bodyView_right (j : Tape) (k : Body)
    (h : bodyView j = some k) : Sum.inl k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j => cases h

theorem ownerView_left (k : MachineRegularOwnerBody.Tape) :
    ownerView (ownerTape k) = some k := by
  cases k with
  | inl k => rfl
  | inr i => fin_cases i <;> rfl

theorem ownerView_right (j : Tape) (k : MachineRegularOwnerBody.Tape)
    (h : ownerView j = some k) : ownerTape k = j := by
  cases j with
  | inl j => cases h; rfl
  | inr j =>
    cases j with
    | inl j => cases h
    | inr i => fin_cases i <;> simp_all [ownerView] <;> subst k <;> rfl

def cfg (H : BaseTable) (label : Option Label) (data : Data)
    (header : Header.Tape → List Bool) (counters : Fin 4 → List Bool) :
    TM2.Cfg Alphabet Label State :=
  ⟨label, readyState H, frame data header counters⟩

theorem bodyPlacement (data extra : Data) (header : Header.Tape → List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes bodyView (MachineRegularOriginalBody.frame data)
      (frame extra header counters) = frame data header counters := by
  funext j
  cases j with
  | inl j => rfl
  | inr j => cases j <;> rfl

theorem headerPlacement (data : Data) (t n m N R output : List Bool)
    (counters : Fin 4 → List Bool) :
    MachineCloudPadding.Placement.tapes headerView
      (Header.frame t n [] [] [] m [] [] [] N R [] output)
      (frame data (fun _ => []) counters) =
      frame { data with table := t, darts := m, output := output } (headerAux n N R) counters := by
  funext j
  cases j with
  | inl j =>
    cases j with
    | inl i => fin_cases i <;> rfl
    | inr e => cases e with
      | inl e => cases e <;> rfl
      | inr e => rfl
  | inr j =>
    cases j with
    | inl k =>
      cases k with
      | inl k =>
        cases k with
        | inner k => cases k <;> rfl
        | bound => rfl
        | remaining => rfl
        | total => rfl
      | inr k => cases k <;> rfl
    | inr i => rfl

theorem oldGuardStep (H : BaseTable) (data : Data) (header : Header.Tape → List Bool)
    (remaining : Nat) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldGuard) data header
        (counterStacks (encodeWord (remaining + 1)) [] [] []))) =
      some (cfg H (some (Label.oldBody MachineRegularOriginalBody.entry)) data header
        (counterStacks (encodeWord remaining) [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry)
    (some Label.ownerSeed)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_oldFuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, update_frame_oldFuel]
  rfl

theorem oldGuardExit (H : BaseTable) (data : Data) (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .oldGuard) data header (counterStacks (encodeWord 0) [] [] []))) =
      some (cfg H (some Label.ownerSeed) data header (counterStacks [] [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard oldFuel (Label.oldBody MachineRegularOriginalBody.entry)
    (some Label.ownerSeed)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_oldFuel, encodeWord, List.replicate_zero,
    List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_false, update_frame_oldFuel]
  rfl

theorem ownerGuardStep (H : BaseTable) (data : Data) (header : Header.Tape → List Bool)
    (remaining : Nat) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerGuard) data header
        (counterStacks [] (encodeWord (remaining+1)) [] []))) =
      some (cfg H (some (.ownerBody MachineRegularOwnerBody.entry)) data header
        (counterStacks [] (encodeWord remaining) [] [])) := by
  change some (TM2.stepAux (Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry)
    (clearEntry 0)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_ownerFuel, encodeWord, List.replicate_succ,
    List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_true, update_frame_ownerFuel]
  rfl

theorem ownerGuardExit (H : BaseTable) (data : Data) (header : Header.Tape → List Bool) :
    (advance (TM2.step (program H)))^[1]
      (some (cfg H (some .ownerGuard) data header (counterStacks [] (encodeWord 0) [] []))) =
      some (cfg H (clearEntry 0) data header (counterStacks [] [] [] [])) := by
  change some (TM2.stepAux (Fuel.guard ownerFuel (.ownerBody MachineRegularOwnerBody.entry)
    (clearEntry 0)) (readyState H) _) = _
  simp only [Fuel.guard, TM2.stepAux, frame_ownerFuel, encodeWord, List.replicate_zero,
    List.nil_append, List.head?_cons, List.tail_cons, Option.getD_some,
    Bool.cond_false, update_frame_ownerFuel]
  rfl

theorem drainTrace (H : BaseTable) (i : Fin 7) (base : Tape → List Bool) :
    (advance (TM2.step (program H)))^[(base (clearTape i)).length+1]
      (some ⟨some (.clear i), readyState H, base⟩) =
      some ⟨clearEntry (i.val+1), readyState H, Function.update base (clearTape i) []⟩ := by
  have h := MachineDrain.drainTrace (clearTape i) (.clear i) (clearEntry (i.val+1))
    (program H) rfl base (base (clearTape i)) (MachineRegularOriginalBody.readyState H) none
  simpa only [Function.update_eq_self, readyState] using h

end Top

end BinPackingGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularTableRuntime
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularTableRuntime

open Turing
open PCP
open MachineRegularTable.Top (Tape Label State coreTape readyState)

theorem sourceMachine_eq (H : PreprocessingRegularTables.BaseTable) :
    MachineCanonicalOutput.sourceMachine (rawProgram H) =
      MachineRegularTable.Top.machine H := rfl

end BinPackingGames.Foundations.Complexity.MachineRegularTableRuntime

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringMachineRowBody
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
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

abbrev State := MachineUnaryEqualityBit.State

def instruction (hl : l ≤ max) (hr : r ≤ max) (placement : Tape max → K)
    (left : Fin l → Fin d) (right : Fin r → Fin d)
    (labels : Label l r → Λ) (exit : Option Λ) :
    Label l r → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction l
      (placement ∘ PoweringMachineTapes.wordPlacement hl false) left
      (fun z => labels (.inl z))
      (some (labels (.inr (.inl (PoweringMachineWord.entry r))))) q
  | .inr (.inl q) => PoweringMachineWord.instruction r
      (placement ∘ PoweringMachineTapes.wordPlacement hr true) right
      (fun z => labels (.inr (.inl z)))
      (some (labels (.inr (.inr .seedLeft)))) q
  | .inr (.inr q) => MachineUnaryEqualityBit.instruction
      (placement ∘ PoweringMachineTapes.equalityPlacement max)
      (fun z => labels (.inr (.inr z))) exit q

end BinPackingGames.Foundations.Complexity.PoweringMachineEqualityField

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

@[simp] theorem headerPlacement_start {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inr (PoweringMachineWord.first t)) = start max := by
  simp [headerPlacement, start, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_succ {t max : Nat} (h : t ≤ max) (i : Fin t) :
    headerPlacement h (.inr i.succ) = .inr (Fin.castLE h i) := by
  simp [headerPlacement, leftEndpoint, rowOutput, Equiv.swap_apply_def]

def instruction (n : Nat) (h : n + 1 ≤ max) (placement : Tape max → K)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ) :
    Label n → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl q => affineInstruction (placement (start max)) (placement (scratch max))
      (placement (rowOutput max)) (blockSize d n) (reverseOffset d n ports direction)
      (fun z => labels (.inl z)) (some (labels (tailEntry n direction))) q
  | .inr (.inl q) => PoweringMachineWord.copyInstruction
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (fun z => labels (.inr (.inl z))) exit q
  | .inr (.inr q) => PoweringMachineWord.instruction (n + 1)
      (placement ∘ headerPlacement h) ports (fun z => labels (.inr (.inr z))) exit q

def afterReverse (n : Nat) (placement : Tape max → K) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  Function.update base (placement (rowOutput max))
    (encodeWord (reverseValue d n vertex ports direction) ++ base (placement (rowOutput max)))

def finalTapes (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) : K → List Bool :=
  let mid := afterReverse n placement vertex ports direction base
  if direction then
    PoweringMachineWord.finalTapes input (n + 1) (placement ∘ headerPlacement h) vertex ports mid
  else Function.update mid (placement (rowOutput max))
    (encodeWord vertex.val ++ mid (placement (rowOutput max)))

theorem finalTapes_other (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (query max)) (hscan : k ≠ placement (scan max))
    (hreverse : k ≠ placement (reverse max)) (houtput : k ≠ placement (rowOutput max))
    (hpositions : ∀ i : Fin (n + 1), k ≠ placement (.inr (Fin.castLE h i))) :
    finalTapes input n h placement vertex ports direction base k = base k := by
  cases direction with
  | false => simp only [finalTapes, Bool.false_eq_true, ite_false,
      Function.update_of_ne houtput, afterReverse]
  | true =>
    let mid := afterReverse n placement vertex ports true base
    have hw := PoweringMachineWord.finalTapes_other input (n + 1)
      (placement ∘ headerPlacement h) vertex ports mid k
      (by simpa only [Function.comp_apply, headerPlacement_query] using hquery)
      (by simpa only [Function.comp_apply, headerPlacement_scan] using hscan)
      (by simpa only [Function.comp_apply, headerPlacement_reverse] using hreverse)
      (by simpa only [Function.comp_apply, headerPlacement_output] using houtput)
      (fun i => by simpa only [Function.comp_apply, headerPlacement_succ] using hpositions i)
    calc
      _ = mid k := hw
      _ = base k := by simp only [mid, afterReverse, Function.update_of_ne houtput]

theorem finalTapes_shared (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) (i : Fin 11)
    (hquery : i ≠ 2) (hscan : i ≠ 3) (hreverse : i ≠ 4) (houtput : i ≠ 10) :
    finalTapes input n h placement vertex ports direction base (placement (.inl i)) =
      base (placement (.inl i)) := by
  apply finalTapes_other input n h placement vertex ports direction base
  · intro heq; exact hquery (Sum.inl.inj (distinct heq))
  · intro heq; exact hscan (Sum.inl.inj (distinct heq))
  · intro heq; exact hreverse (Sum.inl.inj (distinct heq))
  · intro heq; exact houtput (Sum.inl.inj (distinct heq))
  · intro j heq; cases distinct heq

end BinPackingGames.Foundations.Complexity.PoweringMachineRowHeaders

namespace BinPackingGames.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

abbrev Tape := PoweringMachineTapes.Tape

def finalTapes (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) : (op : Instruction d) → op.radius ≤ max →
      (K → List Bool) → K → List Bool
  | .relation path port a b, bounded, base =>
      PoweringMachineRelationField.finalTapes placement path bounded port a b graph vertex base
  | .equal left right, bounded, base =>
      PoweringMachineEqualityField.finalTapes graph
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded)
        placement vertex left.get right.get base

structure Ready (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) (suffix : List Bool) (tapes : K → List Bool) : Prop where
  table : tapes (placement (.inl 0)) = PortTables.tableBits graph
  source : tapes (placement (.inl 1)) = encodeWord vertex.val ++ suffix
  scratch : tapes (placement (.inl 5)) = []
  leftCopy : tapes (placement (.inl 8)) = []
  rightCopy : tapes (placement (.inl 9)) = []

theorem finalTapes_role (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (j : Fin 11) (role : j = 0 ∨ j = 1 ∨ j = 5 ∨ j = 8 ∨ j = 9) :
    finalTapes graph placement vertex op bounded base (placement (.inl j)) =
      base (placement (.inl j)) := by
  cases op with
  | relation path port a b =>
      apply PoweringMachineRelationField.finalTapes_frame placement distinct path bounded
        port a b graph vertex base j
      all_goals rcases role with rfl | rfl | rfl | rfl | rfl <;> decide
  | equal left right =>
      exact PoweringMachineEqualityField.finalTapes_role graph _ _ placement distinct
        vertex left.get right.get base j role

theorem ready_finalTapes (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph placement vertex suffix base) :
    Ready graph placement vertex suffix (finalTapes graph placement vertex op bounded base) := by
  constructor
  · rw [finalTapes_role graph placement distinct vertex op bounded base 0 (by simp)]
    exact ready.table
  · rw [finalTapes_role graph placement distinct vertex op bounded base 1 (by simp)]
    exact ready.source
  · rw [finalTapes_role graph placement distinct vertex op bounded base 5 (by simp)]
    exact ready.scratch
  · rw [finalTapes_role graph placement distinct vertex op bounded base 8 (by simp)]
    exact ready.leftCopy
  · rw [finalTapes_role graph placement distinct vertex op bounded base 9 (by simp)]
    exact ready.rightCopy

theorem finalTapes_other (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) (op : Instruction d) (bounded : op.radius ≤ max)
    (base : K → List Bool) (k : K) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph placement vertex op bounded base k = base k := by
  cases op with
  | relation path port a b =>
      exact PoweringMachineRelationField.finalTapes_other placement path bounded port a b
        graph vertex base k outside
  | equal left right =>
      exact PoweringMachineEqualityField.finalTapes_other graph _ _ placement vertex
        left.get right.get base k (outside _) (outside _) (outside _) (outside _)
        (outside _) (outside _) (fun i => outside _)

end BinPackingGames.Foundations.Complexity.PoweringMachineField

namespace BinPackingGames.Foundations.Complexity.PoweringMachinePlan

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

def result (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (op : Command d max) (base : K → List Bool) : K → List Bool :=
  PoweringMachineField.finalTapes graph placement vertex op.val op.property base

def finalTapes (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool) : K → List Bool :=
  MachineFiniteSequence.resultOf (result graph placement vertex) commands base

def steps (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool) : Nat :=
  MachineFiniteSequence.steps (result graph placement vertex)
    (fun op _ => PoweringMachineField.steps graph vertex op.val) commands base

theorem ready_finalTapes (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    PoweringMachineField.Ready graph placement vertex suffix
      (finalTapes graph placement vertex commands base) := by
  induction commands generalizing base with
  | nil => exact ready
  | cons op commands ih =>
      apply ih
      exact PoweringMachineField.ready_finalTapes graph placement distinct vertex op.val
        op.property base suffix ready

end BinPackingGames.Foundations.Complexity.PoweringMachinePlan

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRowBody

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev State (d n : Nat) := PoweringMasterState.Master (bufferSize d n)

def headerPlacement {max : Nat} (placement : PoweringMachineTapes.Tape max → K)
    (output : K) (i : PoweringMachineTapes.Tape max) : K :=
  if i = .inl 10 then output else placement i

omit [DecidableEq K] in
@[simp] theorem headerPlacement_output {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (output : K) :
    headerPlacement placement output (.inl 10) = output := by simp [headerPlacement]

omit [DecidableEq K] in
theorem headerPlacement_injective {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) :
    Function.Injective (headerPlacement placement output) := by
  intro i j h
  by_cases hi : i = .inl 10
  · subst i
    by_cases hj : j = .inl 10
    · exact hj.symm
    · exact False.elim (outside j (by simpa [headerPlacement, hj] using h))
  · by_cases hj : j = .inl 10
    · subst j
      exact False.elim (outside i (by simpa [headerPlacement, hi] using h.symm))
    · exact distinct (by simpa [headerPlacement, hi, hj] using h)

omit [DecidableEq K] in
theorem headerPlacement_excludes_data {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) :
    ∀ i, placement (.inl 10) ≠ headerPlacement placement output i := by
  intro i h
  by_cases hi : i = .inl 10
  · subst i
    exact outside _ (by simpa only [headerPlacement_output] using h.symm)
  · have heq : (.inl 10 : PoweringMachineTapes.Tape max) = i :=
      distinct (by simpa [headerPlacement, hi] using h)
    exact hi heq.symm

def afterPlan (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  PoweringMachinePlan.finalTapes graph placement vertex (commands n ports direction) base

def afterEmit (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  let mid := afterPlan graph n placement vertex ports direction base
  Function.update (Function.update mid (placement (.inl 10)) []) output
    (rowRelation graph n vertex ports direction ++ mid output)

def finalTapes (graph : PortTables.Table vertices d)
    (n : Nat) (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (base : K → List Bool) : K → List Bool :=
  PoweringMachineRowHeaders.finalTapes graph n (by unfold capacity; omega)
    (headerPlacement placement output) vertex ports direction
    (afterEmit graph n placement output vertex ports direction base)

theorem planSteps_eq {max : Nat} (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (vertex : Fin vertices)
    (ops : List (PoweringMachinePlan.Command d max)) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex ops base = planSteps graph vertex ops := by
  induction ops generalizing base with
  | nil => rfl
  | cons op ops ih =>
      change PoweringMachineField.steps graph vertex op.val +
        PoweringMachinePlan.steps graph placement vertex ops
          (PoweringMachinePlan.result graph placement vertex op base) = _
      rw [ih]
      rfl

def Ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (vertex : Fin vertices)
    (suffix : List Bool) (base : K → List Bool) : Prop :=
  PoweringMachineField.Ready graph placement vertex suffix base ∧ base (placement (.inl 10)) = []

theorem plan_other {max : Nat} (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (vertex : Fin vertices)
    (ops : List (PoweringMachinePlan.Command d max)) (base : K → List Bool)
    (k : K) (outside : ∀ i, k ≠ placement i) :
    PoweringMachinePlan.finalTapes graph placement vertex ops base k = base k := by
  induction ops generalizing base with
  | nil => rfl
  | cons op ops ih =>
      change PoweringMachinePlan.finalTapes graph placement vertex ops
        (PoweringMachinePlan.result graph placement vertex op base) k = _
      rw [ih]
      exact PoweringMachineField.finalTapes_other graph placement vertex op.val op.property base k outside

theorem afterEmit_data (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) :
    afterEmit graph n placement output vertex ports direction base (placement (.inl 10)) = [] := by
  simp only [afterEmit, Function.update_of_ne (Ne.symm (outside _)), Function.update_self]

theorem afterEmit_role (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (j : Fin 11) (hj : j ≠ 10) :
    afterEmit graph n placement output vertex ports direction base (placement (.inl j)) =
      afterPlan graph n placement vertex ports direction base (placement (.inl j)) := by
  have hdata : placement (.inl j) ≠ placement (.inl 10) := fun h => hj (Sum.inl.inj (distinct h))
  simp only [afterEmit, Function.update_of_ne (Ne.symm (outside _)), Function.update_of_ne hdata]

theorem afterEmit_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    Ready graph n placement vertex suffix (afterEmit graph n placement output vertex ports direction base) := by
  have hp := PoweringMachinePlan.ready_finalTapes graph placement distinct vertex
    (commands n ports direction) base suffix ready.1
  constructor
  · constructor
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 0 (by decide)]
      exact hp.table
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 1 (by decide)]
      exact hp.source
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 5 (by decide)]
      exact hp.scratch
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 8 (by decide)]
      exact hp.leftCopy
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 9 (by decide)]
      exact hp.rightCopy
  · exact afterEmit_data graph n placement output outside vertex ports direction base

theorem finalTapes_data (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) :
    finalTapes graph n placement output vertex ports direction base (placement (.inl 10)) = [] := by
  have hother := headerPlacement_excludes_data placement distinct output outside
  calc
    finalTapes graph n placement output vertex ports direction base (placement (.inl 10)) =
        afterEmit graph n placement output vertex ports direction base (placement (.inl 10)) :=
      PoweringMachineRowHeaders.finalTapes_other _ _ _ _ _ _ _ _ _
        (hother _) (hother _) (hother _) (hother _) (fun i => hother _)
    _ = [] := afterEmit_data graph n placement output outside vertex ports direction base

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    Ready graph n placement vertex suffix (finalTapes graph n placement output vertex ports direction base) := by
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hrole (j : Fin 11) (h₂ : j ≠ 2) (h₃ : j ≠ 3) (h₄ : j ≠ 4) (h₁₀ : j ≠ 10) :
      finalTapes graph n placement output vertex ports direction base (placement (.inl j)) =
        afterEmit graph n placement output vertex ports direction base (placement (.inl j)) := by
    have h := PoweringMachineRowHeaders.finalTapes_shared graph n (by unfold capacity; omega)
      (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
      vertex ports direction (afterEmit graph n placement output vertex ports direction base) j h₂ h₃ h₄ h₁₀
    dsimp only [finalTapes]
    simpa only [headerPlacement, ite_eq_right (show (Sum.inl j : PoweringMachineTapes.Tape (capacity n)) ≠ .inl 10 from
      fun heq => h₁₀ (Sum.inl.inj heq))] using h
  constructor
  · constructor
    · rw [hrole 0 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.table
    · rw [hrole 1 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.source
    · rw [hrole 5 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.scratch
    · rw [hrole 8 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.leftCopy
    · rw [hrole 9 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.rightCopy
  · exact finalTapes_data graph n placement distinct output outside vertex ports direction base

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (base : K → List Bool) (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output vertex ports direction base k = base k := by
  have hh : ∀ i, k ≠ headerPlacement placement output i := by
    intro i
    by_cases hi : i = .inl 10
    · simpa [headerPlacement, hi] using hout
    · simpa [headerPlacement, hi] using outside i
  calc
    finalTapes graph n placement output vertex ports direction base k =
        afterEmit graph n placement output vertex ports direction base k :=
      PoweringMachineRowHeaders.finalTapes_other _ _ _ _ _ _ _ _ _
        (hh _) (hh _) (hh _) (hh _) (fun i => hh _)
    _ = afterPlan graph n placement vertex ports direction base k := by
      simp only [afterEmit, Function.update_of_ne hout, Function.update_of_ne (outside _)]
    _ = base k := plan_other graph placement vertex _ base k outside

end BinPackingGames.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PoweringTableLayout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PoweringTableLayout

open BinPackingGames.Foundations.Complexity
open PoweringTables PoweringEnumeration

theorem outputWords_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    GenericGraphTables.tableWords (table input n) =
      [vertices, dartCount vertices d n] ++
        (List.finRange vertices).flatMap (vertexRowWords input n) := by
  change [vertices, dartCount vertices d n] ++
      (GenericGraphTables.rowList (table input n)).flatMap GenericGraphTables.rowWords = _
  rw [rowList_eq_vertexRows]
  erw [List.flatMap_assoc]
  rfl

theorem outputBits_vertexRows {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) :
    outputBits input n = encodeWords [vertices, dartCount vertices d n] ++
      (List.finRange vertices).flatMap (vertexRowBits input n) := by
  unfold outputBits GenericGraphTables.tableBits
  rw [outputWords_vertexRows, encodeWords_append, encodeWords_flatMap]
  rfl

end BinPackingGames.Foundations.PCP.PoweringTableLayout

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringMachineRuntime
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.PoweringMachineVertex

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

abbrev State (d n : Nat) := PoweringMachineRowBody.State d n

def result (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (j : Command d n) (base : K → List Bool) :
    K → List Bool :=
  PoweringMachineRowBody.finalTapes graph n placement output vertex (ports j) (direction j) base

def sequenceTapes (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) :
    K → List Bool :=
  MachineFiniteSequence.resultOf (result graph n placement output vertex) ops base

def finalTapes (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (base : K → List Bool) : K → List Bool :=
  sequenceTapes graph n placement output vertex (commands d n) base

def sequenceSteps (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) : Nat :=
  MachineFiniteSequence.steps (result graph n placement output vertex)
    (fun j _ => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j)) ops base

theorem sequenceSteps_eq (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) :
    sequenceSteps graph n placement output vertex ops base = costSum graph vertex n ops := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      change PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
        sequenceSteps graph n placement output vertex ops
          (result graph n placement output vertex j base) = _
      rw [ih]
      rfl

theorem sequenceTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    PoweringMachineRowBody.Ready graph n placement vertex suffix
      (sequenceTapes graph n placement output vertex ops base) := by
  induction ops generalizing base with
  | nil => exact ready
  | cons j ops ih =>
      apply ih
      exact PoweringMachineRowBody.finalTapes_ready graph n placement distinct output outside
        vertex (ports j) (direction j) base suffix ready

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    PoweringMachineRowBody.Ready graph n placement vertex suffix
      (finalTapes graph n placement output vertex base) :=
  sequenceTapes_ready graph n placement distinct output outside vertex (commands d n) base suffix ready

theorem sequenceTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    sequenceTapes graph n placement output vertex ops base k = base k := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      change sequenceTapes graph n placement output vertex ops
        (result graph n placement output vertex j base) k = _
      rw [ih]
      exact PoweringMachineRowBody.finalTapes_other graph n placement output vertex
        (ports j) (direction j) base k hout outside

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output vertex base k = base k :=
  sequenceTapes_other graph n placement output vertex (commands d n) base k hout outside

end BinPackingGames.Foundations.Complexity.PoweringMachineVertex

namespace BinPackingGames.Foundations.Complexity.PoweringMachineOuterLoop

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev Placement (K : Type) (n : Nat) := PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K
abbrev State := PoweringMachineVertex.State

structure Ready (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (base : K → List Bool) : Prop where
  table : base (placement (.inl 0)) = PortTables.tableBits graph
  scratch : base (placement (.inl 5)) = []
  leftCopy : base (placement (.inl 8)) = []
  rightCopy : base (placement (.inl 9)) = []
  data : base (placement (.inl 10)) = []

def counter {length : Nat} (placement : Placement K length) (base : K → List Bool)
    (remaining : Nat) : K → List Bool :=
  MachineUnaryCounter.counterTapes (placement (.inl 1)) base remaining []

theorem counter_other {length : Nat} (placement : Placement K length)
    (distinct : Function.Injective placement)
    (base : K → List Bool) (remaining : Nat) (j : Fin 11) (hj : j ≠ 1) :
    counter placement base remaining (placement (.inl j)) = base (placement (.inl j)) := by
  apply MachineUnaryCounter.counterTapes_other
  intro h
  exact hj (Sum.inl.inj (distinct h))

theorem ready_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (ready : Ready graph n placement base) (vertex : Fin vertices) :
    PoweringMachineRowBody.Ready graph n placement vertex [] (counter placement base vertex.val) := by
  constructor
  · constructor
    · rw [counter_other placement distinct base vertex.val 0 (by decide)]
      exact ready.table
    · simp only [counter, MachineUnaryCounter.counterTapes_counter]
    · rw [counter_other placement distinct base vertex.val 5 (by decide)]
      exact ready.scratch
    · rw [counter_other placement distinct base vertex.val 8 (by decide)]
      exact ready.leftCopy
    · rw [counter_other placement distinct base vertex.val 9 (by decide)]
      exact ready.rightCopy
  · rw [counter_other placement distinct base vertex.val 10 (by decide)]
    exact ready.data

omit [DecidableEq K] in
theorem ready_of_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (base : K → List Bool) (vertex : Fin vertices)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex [] base) :
    Ready graph n placement base :=
  ⟨ready.1.table, ready.1.scratch, ready.1.leftCopy, ready.1.rightCopy, ready.2⟩

def bridge (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  .goto (fun _ => vertexStart d n labels guardLabel)

def finalTapes (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (output : K) : (remaining : Nat) → remaining ≤ vertices → (K → List Bool) → K → List Bool
  | 0, _, base => counter placement base 0
  | r + 1, bounded, base =>
      finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output ⟨r, by omega⟩
          (counter placement base r))

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    Ready graph n placement (finalTapes graph n placement output remaining bounded base) := by
  induction remaining generalizing base with
  | zero =>
      constructor
      · rw [finalTapes, counter_other placement distinct base 0 0 (by decide)]
        exact ready.table
      · rw [finalTapes, counter_other placement distinct base 0 5 (by decide)]
        exact ready.scratch
      · rw [finalTapes, counter_other placement distinct base 0 8 (by decide)]
        exact ready.leftCopy
      · rw [finalTapes, counter_other placement distinct base 0 9 (by decide)]
        exact ready.rightCopy
      · rw [finalTapes, counter_other placement distinct base 0 10 (by decide)]
        exact ready.data
  | succ r ih =>
      apply ih
      apply ready_of_vertex graph n placement _ (⟨r, by omega⟩ : Fin vertices)
      exact PoweringMachineVertex.finalTapes_ready graph n placement distinct output outside
        ⟨r, by omega⟩ _ [] (ready_vertex graph n placement distinct base ready _)

theorem finalTapes_other (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (output : K) (remaining : Nat)
    (bounded : remaining ≤ vertices) (base : K → List Bool)
    (k : K) (hout : k ≠ output) (outside : ∀ i, k ≠ placement i) :
    finalTapes graph n placement output remaining bounded base k = base k := by
  induction remaining generalizing base with
  | zero => exact MachineUnaryCounter.counterTapes_other _ _ (outside _) base 0 []
  | succ r ih =>
      rw [finalTapes, ih, PoweringMachineVertex.finalTapes_other graph n placement output
        ⟨r, by omega⟩ _ k hout outside]
      exact MachineUnaryCounter.counterTapes_other _ _ (outside _) base r []

end BinPackingGames.Foundations.Complexity.PoweringMachineOuterLoop

namespace BinPackingGames.Foundations.Complexity.PoweringMachineGlobal

open Turing

abbrev Tape (n : Nat) :=
  PoweringMachineInitialize.GlobalTape (PoweringMachineRowBody.capacity n)

abbrev State (d n : Nat) :=
  PoweringMasterState.Master (PoweringMachineRowBody.bufferSize d n)

def placement (n : Nat) :
    PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → Tape n :=
  PoweringMachineInitialize.commonPlacement (PoweringMachineRowBody.capacity n)

def inputTape (n : Nat) : Tape n :=
  placement n (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

def outputTape (n : Nat) : Tape n :=
  PoweringMachineInitialize.finalOutput (PoweringMachineRowBody.capacity n)

def headerVertices (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.vertices
def headerDarts (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.darts

def enumeration (n : Nat) :
    Fin (4 + (11 + PoweringMachineRowBody.capacity n + 1)) ≃ Tape n :=
  PoweringGlobalEnumeration.enumeration (PoweringMachineRowBody.capacity n)

abbrev FinishLabel (n : Nat) := PoweringMachineFinish.Label (enumeration n) (outputTape n)

abbrev Label (d n : Nat) := PoweringMachineInitialize.Label ⊕
  (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))

instance labelFintype (d n : Nat) : Fintype (Label d n) :=
  inferInstanceAs (Fintype (PoweringMachineInitialize.Label ⊕
    (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))))

def initLabels (d n : Nat) : PoweringMachineInitialize.Label → Label d n := Sum.inl
def guardLabel (d n : Nat) : Label d n := .inr (.inl false)
def bridgeLabel (d n : Nat) : Label d n := .inr (.inl true)

def vertexLabels (d n : Nat) (label : PoweringMachineVertex.Label d n) : Label d n :=
  .inr (.inr (.inl label))

def finishLabels (d n : Nat) (label : FinishLabel n) : Label d n :=
  .inr (.inr (.inr label))

def finishEntry (d n : Nat) : Label d n := finishLabels d n (.inl .seed)

def main (d n : Nat) : Label d n := initLabels d n (.inr .seed)

end BinPackingGames.Foundations.Complexity.PoweringMachineGlobal

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Information_SourceNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

namespace Eval

open CookLevin.PolynomialMachine

variable {K Λ σ : Type} [DecidableEq K]

def statement (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ) :
    Label p → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl _ => prependFields (word p slots) (indices p slots)
      (.goto fun _ => labels (inner p .start))
  | .inr (.inl l) => MachineHorner.statement slots (fun l => labels (inner p l))
      (some (labels (finish p))) l
  | .inr (.inr _) => clearFields (fun k => (word p slots k).length) (indices p slots)
      (Reduction.MachineTransfer.exitAt (slots (.inl 3)) exit)

end Eval

end BinPackingGames.Foundations.Hastad.SourceHeaderCounts

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierFront
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation

open Turing MachineComposition
open BinPackingGames.Foundations.Hastad.SourceHeaderCounts
open PolynomialMachine

abbrev PhasePrivate (p : Polynomial Nat) := Fin 5 ⊕ Fin (width p)

def Private : List (Polynomial Nat) → Type
  | [] => Empty
  | p :: ps => PhasePrivate p ⊕ Private ps

abbrev Layout (ps : List (Polynomial Nat)) := Unit ⊕ Private ps

def Label : List (Polynomial Nat) → Type
  | [] => Empty
  | p :: ps => Eval.Label p ⊕ Label ps

def Output : List (Polynomial Nat) → Type
  | [] => Empty
  | _ :: ps => Unit ⊕ Output ps

instance privateDecidableEq (ps : List (Polynomial Nat)) : DecidableEq (Private ps) := by
  induction ps with
  | nil => exact inferInstanceAs (DecidableEq Empty)
  | cons p ps ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (PhasePrivate p ⊕ Private ps))

def controlSlots (p : Polynomial Nat) (ps : List (Polynomial Nat)) : Fin 6 ↪ Layout (p :: ps) where
  toFun i := match i.val with
    | 0 => .inl ()
    | 1 => .inr (.inl (.inl 0))
    | 2 => .inr (.inl (.inl 1))
    | 3 => .inr (.inl (.inl 2))
    | 4 => .inr (.inl (.inl 3))
    | _ => .inr (.inl (.inl 4))
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> cases h <;> rfl

def headLayout (p : Polynomial Nat) (ps : List (Polynomial Nat)) :
    MachineHorner.Layout (width p) ↪ Layout (p :: ps) where
  toFun
    | .inl i => controlSlots p ps i
    | .inr i => .inr (.inl (.inr i))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((controlSlots p ps).injective h)
      | inr b => fin_cases a <;> cases h
    | inr a =>
      cases b with
      | inl b => fin_cases b <;> cases h
      | inr b =>
        exact congrArg Sum.inr (Sum.inr.inj (Sum.inl.inj (Sum.inr.inj h)))

def tailLayout (p : Polynomial Nat) (ps : List (Polynomial Nat)) :
    Layout ps ↪ Layout (p :: ps) where
  toFun
    | .inl _ => .inl ()
    | .inr i => .inr (.inr i)
  inj' := by
    intro a b h
    cases a with
    | inl a => cases b <;> cases h; rfl
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj h))

variable {K Λ σ : Type}

def headSlots {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : MachineHorner.Layout (width p) ↪ K :=
  (headLayout p ps).trans slots

def tailSlots {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : Layout ps ↪ K :=
  (tailLayout p ps).trans slots

@[simp] theorem headSlots_input {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : headSlots slots (.inl 0) = slots (.inl ()) := by
  simp only [headSlots, headLayout, controlSlots]
  rfl

@[simp] theorem headSlots_output {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) :
    headSlots slots (.inl 3) = slots (.inr (.inl (.inl 2))) := rfl

@[simp] theorem tailSlots_input {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) : tailSlots slots (.inl ()) = slots (.inl ()) := by
  simp only [tailSlots]
  rfl

theorem head_output_ne_tail {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (i : Layout ps) :
    headSlots slots (.inl 3) ≠ tailSlots slots i := by
  change slots (.inr (.inl (.inl 2))) ≠ slots (tailLayout p ps i)
  apply slots.injective.ne
  cases i <;> intro h <;> cases h

def Clean (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K) (base : K → List Bool) : Prop :=
  ∀ i : Private ps, base (slots (.inr i)) = []

variable [DecidableEq K]

theorem tail_clean_after_head {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (base : K → List Bool)
    (h : Clean (p :: ps) slots base) (value : Nat) :
    Clean ps (tailSlots slots) (MachineHorner.resultTapes (headSlots slots) base value) := by
  intro i
  rw [MachineHorner.resultTapes, Function.update_of_ne (head_output_ne_tail slots (.inr i)).symm]
  exact h (.inr i)

def entry : (ps : List (Polynomial Nat)) → (Label ps → Λ) → Option Λ → Option Λ
  | [], _, exit => exit
  | p :: _, labels, _ => some (labels (.inl (Eval.start p)))

def statement : (ps : List (Polynomial Nat)) → (slots : Layout ps ↪ K) →
    (Label ps → Λ) → Option Λ → Label ps →
      TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | [], _, _, _, l => Empty.elim l
  | p :: ps, slots, labels, exit, .inl l =>
      Eval.statement p (headSlots slots) (fun l => labels (.inl l))
        (entry ps (fun l => labels (.inr l)) exit) l
  | _ :: ps, slots, labels, exit, .inr l =>
      statement ps (tailSlots slots) (fun l => labels (.inr l)) exit l

def resultTapes : (ps : List (Polynomial Nat)) → (Layout ps ↪ K) →
    (K → List Bool) → Nat → K → List Bool
  | [], _, base, _ => base
  | p :: ps, slots, base, n =>
      resultTapes ps (tailSlots slots)
        (MachineHorner.resultTapes (headSlots slots) base (p.eval n)) n

def outputSlot : (ps : List (Polynomial Nat)) → Output ps → Layout ps
  | [], i => Empty.elim i
  | _ :: _, .inl _ => .inr (.inl (.inl 2))
  | p :: ps, .inr i => tailLayout p ps (outputSlot ps i)

def outputPolynomial : (ps : List (Polynomial Nat)) → Output ps → Polynomial Nat
  | [], i => Empty.elim i
  | p :: _, .inl _ => p
  | _ :: ps, .inr i => outputPolynomial ps i

theorem outputSlot_injective (ps : List (Polynomial Nat)) :
    Function.Injective (outputSlot ps) := by
  induction ps with
  | nil => intro i; exact Empty.elim i
  | cons p ps ih =>
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => cases i; cases j; rfl
      | inr j =>
        exact False.elim ((head_output_ne_tail (Function.Embedding.refl (Layout (p :: ps)))
          (outputSlot ps j)) h)
    | inr i =>
      cases j with
      | inl j =>
        exact False.elim ((head_output_ne_tail (Function.Embedding.refl (Layout (p :: ps)))
          (outputSlot ps i)) h.symm)
      | inr j => exact congrArg Sum.inr (ih ((tailLayout p ps).injective h))

theorem resultTapes_off_outputs (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat) (k : K)
    (hk : ∀ i : Output ps, slots (outputSlot ps i) ≠ k) :
    resultTapes ps slots base n k = base k := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih =>
    change resultTapes ps (tailSlots slots)
      (MachineHorner.resultTapes (headSlots slots) base (p.eval n)) n k = base k
    rw [ih _ _ (fun i => hk (.inr i))]
    exact Function.update_of_ne (hk (.inl ())).symm _ _

theorem resultTapes_output (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat) (clean : Clean ps slots base) (i : Output ps) :
    resultTapes ps slots base n (slots (outputSlot ps i)) =
      encodeWord ((outputPolynomial ps i).eval n) := by
  induction ps generalizing base with
  | nil => exact Empty.elim i
  | cons p ps ih =>
    cases i with
    | inl i =>
      change resultTapes ps (tailSlots slots)
        (MachineHorner.resultTapes (headSlots slots) base (p.eval n)) n
          (headSlots slots (.inl 3)) = encodeWord (p.eval n)
      rw [resultTapes_off_outputs _ _ _ _ _
        (fun i => (head_output_ne_tail slots (outputSlot ps i)).symm)]
      rw [MachineHorner.resultTapes_output]
      simp only [headSlots_output, clean (.inl (.inl 2)), List.append_nil]
    | inr i =>
      exact ih (tailSlots slots) _ (tail_clean_after_head slots base clean _) i

theorem resultTapes_ambient (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat) (k : K) (hk : k ∉ Set.range slots) :
    resultTapes ps slots base n k = base k := by
  apply resultTapes_off_outputs
  intro i hi
  exact hk ⟨outputSlot ps i, hi⟩

abbrev ProgramLabel (ps : List (Polynomial Nat)) := Unit ⊕ Label ps

def program (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K) :
    ProgramLabel ps → TM2.Stmt (fun _ : K => Bool) (ProgramLabel ps) (MachineHorner.State σ)
  | .inl _ => .load (fun state => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots (.inl ())) (entry ps Sum.inr none))
  | .inr l => statement ps slots Sum.inr none l

def clockOutput (V : NPVerifier) : Clock → Output (clockPolynomials V)
  | .witness => .inl ()
  | .horizon => .inr (.inl ())
  | .capacity => .inr (.inr (.inl ()))
  | .width => .inr (.inr (.inr (.inl ())))
  | .frameWidth => .inr (.inr (.inr (.inr (.inl ()))))
  | .inputCount => .inr (.inr (.inr (.inr (.inr (.inl ())))))

@[simp] theorem outputPolynomial_clockOutput (V : NPVerifier) (c : Clock) :
    outputPolynomial (clockPolynomials V) (clockOutput V c) = clockPolynomial V c := by
  cases c <;> rfl

theorem clockPolynomial_eval (V : NPVerifier) (n : Nat) (c : Clock) :
    (clockPolynomial V c).eval n = clockValue V n c := by
  cases c <;>
    simp [clockPolynomial, clockValue, VerifierCircuit.widthPolynomial,
      VerifierCircuit.capacity, NPVerifier.horizon, ConfigIndex.Indexing.width, Nat.mul_comm]

theorem clockResult_output (V : NPVerifier) (slots : Layout (clockPolynomials V) ↪ K)
    (base : K → List Bool) (n : Nat) (clean : Clean (clockPolynomials V) slots base)
    (c : Clock) :
    resultTapes (clockPolynomials V) slots base n
      (slots (outputSlot (clockPolynomials V) (clockOutput V c))) =
      encodeWord (clockValue V n c) := by
  rw [resultTapes_output _ _ _ _ clean, outputPolynomial_clockOutput, clockPolynomial_eval]

end BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierFront
open Turing MachineComposition
open BinPackingGames.Foundations.Hastad

abbrev Tape (V : NPVerifier) := Fin 3 ⊕ ClockPreparation.Layout (ClockPreparation.clockPolynomials V)
abbrev ExtraLabel (V : NPVerifier) := Fin 4 ⊕ ClockPreparation.ProgramLabel (ClockPreparation.clockPolynomials V)
abbrev Label (V : NPVerifier) := InputFrame.Label ⊕ ExtraLabel V
abbrev EmbeddedAlphabet (V : NPVerifier) := MachineEmbedding.Alphabet InputFrame.Alphabet
  (fun _ : ClockPreparation.Layout (ClockPreparation.clockPolynomials V) => Bool)

def raw (V : NPVerifier) : Tape V := .inl 0
def stream (V : NPVerifier) : Tape V := .inl 1
def scratch (V : NPVerifier) : Tape V := .inl 2
def clockSlots (V : NPVerifier) : ClockPreparation.Layout (ClockPreparation.clockPolynomials V) ↪ Tape V :=
  ⟨Sum.inr, Sum.inr_injective⟩
def lengthTape (V : NPVerifier) : Tape V := clockSlots V (.inl ())
def clockTape (V : NPVerifier) (c : ClockPreparation.Clock) : Tape V :=
  clockSlots V (ClockPreparation.outputSlot _ (ClockPreparation.clockOutput V c))
def phase (V : NPVerifier) (i : Fin 4) : Label V := .inr (.inl i)
def clockLabel (V : NPVerifier) (l : ClockPreparation.ProgramLabel (ClockPreparation.clockPolynomials V)) : Label V :=
  .inr (.inr l)

theorem alphabet_eq (V : NPVerifier) : EmbeddedAlphabet V = (fun _ : Tape V => Bool) := by
  funext k
  cases k <;> rfl

variable {A : Type}

def extraProgram (V : NPVerifier) : ExtraLabel V → TM2.Stmt (fun _ : Tape V => Bool) (Label V) (State A)
  | .inl i => if i = 0 then
      Reduction.MachineTransfer.loopAt (raw V) (scratch V) id false (phase V 0) (some (phase V 1))
    else if i = 1 then
      MachineCopy.forkLoop (scratch V) (raw V) (stream V) false (phase V 1) (some (phase V 2))
    else if i = 2 then SourceMachine.fieldStart (lengthTape V) (phase V 3)
    else SourceMachine.fieldLoop (raw V) (lengthTape V) (phase V 3) (some (clockLabel V (.inl ())))
  | .inr l => MachineSubroutine.statement (clockLabel V) none
      (MachineStateEquiv.statement (clockStates A)
        (ClockPreparation.program (ClockPreparation.clockPolynomials V) (clockSlots V) l))

def innerExtra (V : NPVerifier) : ExtraLabel V →
    TM2.Stmt (EmbeddedAlphabet V) (Label V) (InputFrame.State × A) := fun l =>
  MachineStateEquiv.statement (frameStates A).symm
    (MachineAlphabetTransport.statement (alphabet_eq V).symm (extraProgram V l))

def embeddedProgram (V : NPVerifier) : Label V →
    TM2.Stmt (EmbeddedAlphabet V) (Label V) (InputFrame.State × A) :=
  MachineEmbedding.program (some (phase V 0)) InputFrame.program (innerExtra V)

def program (V : NPVerifier) : Label V → TM2.Stmt (fun _ : Tape V => Bool) (Label V) (State A) :=
  MachineAlphabetTransport.program (alphabet_eq V)
    (MachineStateEquiv.program (frameStates A) (embeddedProgram V))

@[simp] theorem program_extra (V : NPVerifier) (l : ExtraLabel V) :
    program (A := A) V (.inr l) = extraProgram V l := by
  simp only [program, MachineAlphabetTransport.program, MachineStateEquiv.program,
    embeddedProgram, MachineEmbedding.program, innerExtra]
  have h := MachineStateEquiv.statement_symm_statement (frameStates A).symm
    (MachineAlphabetTransport.statement (alphabet_eq V).symm (extraProgram (A := A) V l))
  simp only [Equiv.symm_symm] at h
  rw [h]
  exact MachineAlphabetTransport.statement_roundtrip _ _

def frameTapes (V : NPVerifier) (word : List Bool) : Tape V → List Bool
  | .inl i => if i = 0 then word else []
  | .inr _ => []

def framedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  frameTapes V (encodeWord input.length ++ input)

def copiedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  Function.update (framedTapes V input) (stream V) (encodeWord input.length ++ input)

def seedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  Function.update (Function.update (copiedTapes V input) (raw V) input)
    (lengthTape V) (encodeWord input.length)

def preparedTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  ClockPreparation.resultTapes (ClockPreparation.clockPolynomials V) (clockSlots V)
    (seedTapes V input) input.length

theorem seed_clean (V : NPVerifier) (input : List Bool) :
    ClockPreparation.Clean (ClockPreparation.clockPolynomials V) (clockSlots V) (seedTapes V input) := by
  intro i
  simp [seedTapes, copiedTapes, framedTapes, frameTapes, lengthTape, raw, stream, clockSlots]

theorem prepared_raw (V : NPVerifier) (input : List Bool) :
    preparedTapes V input (raw V) = input := by
  rw [preparedTapes, ClockPreparation.resultTapes_ambient]
  · simp [seedTapes, lengthTape, clockSlots, raw]
  · rintro ⟨i, hi⟩
    cases hi

theorem prepared_stream (V : NPVerifier) (input : List Bool) :
    preparedTapes V input (stream V) = encodeWord input.length ++ input := by
  rw [preparedTapes, ClockPreparation.resultTapes_ambient]
  · simp [seedTapes, lengthTape, clockSlots, raw, stream, copiedTapes]
  · rintro ⟨i, hi⟩
    cases hi

theorem prepared_clock (V : NPVerifier) (input : List Bool) (c : ClockPreparation.Clock) :
    preparedTapes V input (clockTape V c) =
      encodeWord (ClockPreparation.clockValue V input.length c) :=
  ClockPreparation.clockResult_output V (clockSlots V) (seedTapes V input) input.length
    (seed_clean V input) c

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierFront

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ProducerFrontStage
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

structure Ready (p : Ports K) (base : K → List Bool) (free : Nat) : Prop where
  source : base (p 0) = encodeWord free
  current : base (p 1) = []
  scratch : base (p 2) = []
  count : base (p 3) = []
  cursor : base (p 4) = []

theorem prepared_current (p : Ports K) (base : K → List Bool) (free : Nat)
    (ready : Ready p base free) : prepared p base (p 1) = encodeWord free := by
  simp [prepared, copied, p.injective.eq_iff, ready.source, ready.current]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

open Turing

abbrev Tape (V : NPVerifier) := VerifierFront.Tape V ⊕ Work

def frontPorts (V : NPVerifier) : VerifierFront.Tape V ↪ Tape V :=
  ⟨Sum.inl, Sum.inl_injective⟩

def raw (V : NPVerifier) : Tape V := .inl (VerifierFront.raw V)
def framed (V : NPVerifier) : Tape V := .inl (VerifierFront.stream V)
def clock (V : NPVerifier) (c : ClockPreparation.Clock) : Tape V :=
  .inl (VerifierFront.clockTape V c)
def q (V : NPVerifier) : Tape V := clock V .witness
def capacity (V : NPVerifier) : Tape V := clock V .capacity
def countdown (V : NPVerifier) : Tape V := clock V .horizon
def freeInputs (V : NPVerifier) : Tape V := clock V .inputCount

def shared (V : NPVerifier) (t : ForestStage.Tape) : Tape V :=
  .inr (.transition (.inl t))
def current (V : NPVerifier) : Tape V := shared V (.lower .current)
def roots (V : NPVerifier) : Tape V := shared V .rootTable
def records (V : NPVerifier) : Tape V := shared V .records
def tokens (V : NPVerifier) : Tape V := shared V .tokens
def count (V : NPVerifier) : Tape V := shared V (.lower .remaining)
def cursor (V : NPVerifier) : Tape V := .inr (.transition (.inr .cursor))
def output (V : NPVerifier) : Tape V := .inr (.finish .output)

theorem clock_injective (V : NPVerifier) : Function.Injective (clock V) := by
  intro a b h
  have hs := (VerifierFront.clockSlots V).injective (Sum.inl.inj h)
  have ho := ClockPreparation.outputSlot_injective _ hs
  cases a <;> cases b <;> simp_all [ClockPreparation.clockOutput] <;> cases ho

@[simp] theorem clock_eq_iff (V : NPVerifier) (a b : ClockPreparation.Clock) :
    clock V a = clock V b ↔ a = b := (clock_injective V).eq_iff

@[simp] theorem clock_ne_raw (V : NPVerifier) (c : ClockPreparation.Clock) :
    clock V c ≠ raw V := by
  simp [clock, raw, VerifierFront.clockTape, VerifierFront.clockSlots, VerifierFront.raw]

@[simp] theorem raw_ne_clock (V : NPVerifier) (c : ClockPreparation.Clock) :
    raw V ≠ clock V c := (clock_ne_raw V c).symm

@[simp] theorem clock_ne_framed (V : NPVerifier) (c : ClockPreparation.Clock) :
    clock V c ≠ framed V := by
  simp [clock, framed, VerifierFront.clockTape, VerifierFront.clockSlots, VerifierFront.stream]

@[simp] theorem framed_ne_clock (V : NPVerifier) (c : ClockPreparation.Clock) :
    framed V ≠ clock V c := (clock_ne_framed V c).symm

@[simp] theorem raw_ne_framed (V : NPVerifier) : raw V ≠ framed V := by
  simp [raw, framed, VerifierFront.raw, VerifierFront.stream]

def transitionTape (V : NPVerifier) : TransitionArena.Tape → Tape V
  | .inr .raw => raw V
  | .inr .q => q V
  | .inr .capacity => capacity V
  | .inr .countdown => countdown V
  | t => .inr (.transition t)

def transitionPorts (V : NPVerifier) : TransitionArena.Tape ↪ Tape V where
  toFun := transitionTape V
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => simpa [transitionTape] using h
      | inr b =>
        cases b <;>
          simp_all [transitionTape, raw, q, capacity, countdown, clock]
    | inr a =>
      cases b with
      | inl b =>
        cases a <;>
          simp_all [transitionTape, raw, q, capacity, countdown, clock]
      | inr b =>
        cases a <;> cases b <;>
          simp_all [transitionTape, q, capacity, countdown, raw, clock,
            VerifierFront.raw, VerifierFront.clockTape, VerifierFront.clockSlots,
            ClockPreparation.clockOutput] <;>
          cases h

@[simp] theorem transitionPorts_apply (V : NPVerifier) (t : TransitionArena.Tape) :
    transitionPorts V t = transitionTape V t := rfl

def initializationTape (V : NPVerifier) : InitializationAssembly.Tape 9 → Tape V
  | .rawInput => raw V
  | .framedInput => framed V
  | .witnessBound => q V
  | .capacity => capacity V
  | .reversed => tokens V
  | .count => count V
  | .validityWork j => .inr (.validity j)
  | .cellWork j => .inr (.cells j)

def initializationPorts (V : NPVerifier) : InitializationAssembly.Tape 9 ↪ Tape V where
  toFun := initializationTape V
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [initializationTape, q, capacity, tokens, count, shared,
        raw, framed, clock, VerifierFront.raw, VerifierFront.stream,
        VerifierFront.clockTape, VerifierFront.clockSlots,
        ClockPreparation.clockOutput]
    all_goals
      have impossible := (ClockPreparation.outputSlot_injective (ClockPreparation.clockPolynomials V)) h
      cases impossible

@[simp] theorem initializationPorts_apply (V : NPVerifier) (t : InitializationAssembly.Tape 9) :
    initializationPorts V t = initializationTape V t := rfl

def finishTape (V : NPVerifier) : CircuitFinish.Tape → Tape V
  | .current => current V
  | .freeInputs => freeInputs V
  | .root => roots V
  | .reversedRecords => records V
  | .output => output V
  | .gateCount => .inr (.finish .gateCount)
  | .scratch => .inr (.finish .scratch)

def finishPorts (V : NPVerifier) : CircuitFinish.Tape ↪ Tape V where
  toFun := finishTape V
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [finishTape, current, freeInputs, roots, records, output, shared, clock]

@[simp] theorem finishPorts_apply (V : NPVerifier) (t : CircuitFinish.Tape) :
    finishPorts V t = finishTape V t := rfl

def bootstrapPorts (V : NPVerifier) : ProducerBootstrap.Ports (Tape V) where
  toFun := ![freeInputs V, current V, .inr .bootstrap, count V, cursor V]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp_all [freeInputs, current, count, cursor, shared, clock]

@[simp] theorem bootstrap_source (V : NPVerifier) : bootstrapPorts V 0 = freeInputs V := rfl
@[simp] theorem bootstrap_current (V : NPVerifier) : bootstrapPorts V 1 = current V := rfl
@[simp] theorem bootstrap_scratch (V : NPVerifier) :
    bootstrapPorts V 2 = .inr .bootstrap := rfl
@[simp] theorem bootstrap_count (V : NPVerifier) : bootstrapPorts V 3 = count V := rfl
@[simp] theorem bootstrap_cursor (V : NPVerifier) : bootstrapPorts V 4 = cursor V := rfl

def frontTapes (V : NPVerifier) (contents : VerifierFront.Tape V → List Bool) :
    Tape V → List Bool
  | .inl t => contents t
  | .inr _ => []

@[simp] theorem frontTapes_at (V : NPVerifier)
    (contents : VerifierFront.Tape V → List Bool) (t : VerifierFront.Tape V) :
    frontTapes V contents (frontPorts V t) = contents t := rfl

@[simp] theorem frontTapes_work (V : NPVerifier)
    (contents : VerifierFront.Tape V → List Bool) (t : Work) :
    frontTapes V contents (.inr t) = [] := rfl

def frontendPrepared (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  frontTapes V (VerifierFront.preparedTapes V input)

@[simp] theorem frontendPrepared_raw (V : NPVerifier) (input : List Bool) :
    frontendPrepared V input (raw V) = input := VerifierFront.prepared_raw V input

@[simp] theorem frontendPrepared_framed (V : NPVerifier) (input : List Bool) :
    frontendPrepared V input (framed V) = encodeWord input.length ++ input :=
  VerifierFront.prepared_stream V input

@[simp] theorem frontendPrepared_clock (V : NPVerifier) (input : List Bool)
    (c : ClockPreparation.Clock) : frontendPrepared V input (clock V c) =
      encodeWord (ClockPreparation.clockValue V input.length c) :=
  VerifierFront.prepared_clock V input c

@[simp] theorem frontendPrepared_work (V : NPVerifier) (input : List Bool) (t : Work) :
    frontendPrepared V input (.inr t) = [] := rfl

theorem bootstrapReady (V : NPVerifier) (input : List Bool) :
    ProducerBootstrap.Ready (bootstrapPorts V) (frontendPrepared V input)
      (2 * V.witnessBound.eval input.length + 1) := by
  exact ⟨frontendPrepared_clock V input .inputCount, rfl, rfl, rfl, rfl⟩

def bootstrapPrepared (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  ProducerBootstrap.prepared (bootstrapPorts V) (frontendPrepared V input)

@[simp] theorem bootstrapPrepared_front (V : NPVerifier) (input : List Bool)
    (t : VerifierFront.Tape V) :
    bootstrapPrepared V input (frontPorts V t) = VerifierFront.preparedTapes V input t := by
  apply ProducerBootstrap.prepared_other
  all_goals simp [frontPorts, bootstrapPorts, current, count, cursor, shared]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Initialization
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Driver

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Foundations.Hastad
open RuntimeModel

def program (q : Nat) : Label q → TM2.Stmt Alphabet (Label q) (State q)
  | .setup label => Setup.statement setupPorts Label.setup (some (headerEntry q)) label
  | .header label => emitterStatement
      (Emitter.statement (Emitter.listCommands (headerPlan q)) headerSources .scratch .reversed
        Label.header (some .guard) label)
  | .guard => MachineUnaryCounter.guard .counter .tailStart .reverseOutput
  | .tailStart => SourceMachine.fieldStart .tail .tailLoop
  | .tailLoop => SourceMachine.fieldLoop .cursor .tail .tailLoop (some .reverseStart)
  | .reverseStart => SourceMachine.fieldStart .reverseIndex .reverseLoop
  | .reverseLoop => SourceMachine.fieldLoop .cursor .reverseIndex .reverseLoop (some .readPredicate)
  | .readPredicate => ReadRelation.parser .cursor .headCopyFirst
  | .headCopyFirst => Reduction.MachineTransfer.loopAt .original .scratch id false
      .headCopyFirst (some .headCopySecond)
  | .headCopySecond => MachineCopy.forkLoop .scratch .original .scan false
      .headCopySecond (some .indexCopyFirst)
  | .indexCopyFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .indexCopyFirst (some .indexCopySecond)
  | .indexCopySecond => MachineCopy.forkLoop .scratch .reverseIndex .indexScan false
      .indexCopySecond (some .headVertices)
  | .headVertices => MachineLookup.discard .scan .headVertices .headDarts
  | .headDarts => MachineLookup.discard .scan .headDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement q .indexScan .scan .head Label.headLookup
      (some (.compare .leftFirst)) label
  | .compare label => CompareLoop.statement Label.compare (rowEntry q) label
  | .emit label => emitterStatement
      (Emitter.statement (Emitter.listCommands (rowPlan q)) rowSources .scratch .reversed
        Label.emit (some (.clearField 0)) label)
  | .clearField slot => MachineDrain.drain (fieldPorts slot) (.clearField slot)
      (some (clearNext slot))
  | .increment => nextRow .guard
  | .reverseOutput => Reduction.MachineTransfer.loopAt .reversed .output id false
      .reverseOutput (some (.cleanup 0))
  | .cleanup slot => Cleanup.instruction cleanupPorts Label.cleanup (initial q).1 none slot

def machine (q : Nat) : FinTM2 := by
  letI := ReadRelation.stateFintype Flags q
  exact {
    K := Tape
    k₀ := .original
    k₁ := .output
    Γ := Alphabet
    Λ := Label q
    main := .setup .copyFirst
    σ := State q
    initialState := initial q
    m := program q }

@[simp] theorem program_setup (q : Nat) (label : Setup.Label) :
    program q (.setup label) =
      Setup.statement setupPorts Label.setup (some (headerEntry q)) label := rfl

@[simp] theorem program_guard (q : Nat) : program q .guard =
    MachineUnaryCounter.guard .counter .tailStart .reverseOutput := rfl

@[simp] theorem program_headLookup (q : Nat) (label : Lookup.Label) :
    program q (.headLookup label) = Lookup.statement q .indexScan .scan .head
      Label.headLookup (some (.compare .leftFirst)) label := rfl

@[simp] theorem program_compare (q : Nat) (label : CompareLoop.Label) :
    program q (.compare label) = CompareLoop.statement Label.compare (rowEntry q) label := rfl

@[simp] theorem program_increment (q : Nat) : program q .increment = nextRow .guard := rfl

end BinPackingGames.Foundations.PCP.AlphabetTable.Driver

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Initialization

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def setupTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | .cursor => rowsBits input
  | .vertices => encodeWord input.vertices
  | .darts | .counter => encodeWord input.darts
  | .edge => encodeWord 0
  | _ => []

def loopTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | .cursor => rowsBits input
  | .vertices => encodeWord input.vertices
  | .darts | .counter => encodeWord input.darts
  | .edge => encodeWord 0
  | .reversed => (headerBits input).reverse
  | _ => []

end BinPackingGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PCPSourceHardness
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.AlphabetTable.LoopState

open BinPackingGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def inputBits (input : GenericGraphTables.Table q) : List Bool :=
  GenericGraphTables.tableBits input

def prefixWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q] ++
    ((List.finRange input.darts).take e).flatMap (EmitRows.blockWords input)

def prefixBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (prefixWords input e)

def cursorWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  ((GenericGraphTables.rowList input).drop e).flatMap GenericGraphTables.rowWords

def cursorBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (cursorWords input e)

@[simp] theorem prefixWords_zero (input : GenericGraphTables.Table q) :
    prefixWords input 0 =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  simp [prefixWords]

@[simp] theorem prefixBits_zero (input : GenericGraphTables.Table q) :
    prefixBits input 0 = encodeWords
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  rw [prefixBits, prefixWords_zero]

@[simp] theorem cursorBits_zero (input : GenericGraphTables.Table q) :
    cursorBits input 0 =
      encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords) := by
  simp [cursorBits, cursorWords]

@[simp] theorem cursorBits_full (input : GenericGraphTables.Table q) :
    cursorBits input input.darts = [] := by
  have finished := List.drop_length (l := GenericGraphTables.rowList input)
  rw [GenericGraphTables.rowList_length] at finished
  unfold cursorBits cursorWords
  rw [finished]
  rfl

end BinPackingGames.Foundations.PCP.AlphabetTable.LoopState

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Finish

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel
open scoped BigOperators

def afterReversal (base : Tape → List Bool) (word : List Bool) : Tape → List Bool :=
  Reduction.MachineTransfer.tapesAt .reversed .output base [] word

@[simp] theorem afterReversal_output (base : Tape → List Bool) (word : List Bool) :
    afterReversal base word .output = word := by
  simp [afterReversal, Reduction.MachineTransfer.tapesAt]

@[simp] theorem afterReversal_reversed (base : Tape → List Bool) (word : List Bool) :
    afterReversal base word .reversed = [] := by
  simp [afterReversal, Reduction.MachineTransfer.tapesAt]

def finishBudget (base : Tape → List Bool) (word : List Bool) : Nat :=
  word.length + 1 + (∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) + 16

def reverseInTime (q : Nat) (base : Tape → List Bool) (word : List Bool)
    (state : State q) (hreversed : base .reversed = word.reverse)
    (houtput : base .output = []) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some .reverseOutput, state, base⟩
      (some ⟨some (.cleanup 0), (state.1, none), afterReversal base word⟩)
      (word.length + 1) := by
  have run := Reduction.MachineTransfer.transferAtInTime
    (σ := Ambient q) Tape.reversed Tape.output (by decide) id false
    Driver.Label.reverseOutput (some (.cleanup 0)) (Driver.program q) rfl
    base state.1 state.2
  simpa only [hreversed, houtput, List.length_reverse, List.reverse_reverse,
    List.map_id, List.append_nil, afterReversal, Driver.machine, FinTM2.step] using! run

theorem cleared_eq_haltList (q : Nat) (base : Tape → List Bool) :
    (⟨none, initial q, Cleanup.clearTapes cleanupPorts base⟩ : (Driver.machine q).Cfg) =
      haltList (Driver.machine q) (base .output) := by
  have tapes := Cleanup.clearTapes_outputOnly cleanupPorts Tape.output base
    cleanupPorts_ne_output cleanupPorts_cover
  congr 1

def cleanupInTime (q : Nat) (base : Tape → List Bool) (state : State q) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some (.cleanup 0), state, base⟩
      (some (haltList (Driver.machine q) (base .output)))
      ((∑ i : Fin 15, (base (cleanupPorts i)).length) + 16) := by
  have run := Cleanup.cleanupInTime cleanupPorts Driver.Label.cleanup (initial q).1 none
    (Driver.program q)
    (fun i => by simp only [Driver.program, Cleanup.instruction_drain])
    (by simp only [Driver.program, Cleanup.instruction_finish]) base state.1 state.2
  change StateTransition.EvalsToInTime (Driver.machine q).step
    ⟨some (.cleanup 0), state, base⟩
    (some ⟨none, initial q, Cleanup.clearTapes cleanupPorts base⟩)
    ((∑ i : Fin 15, (base (cleanupPorts i)).length) + 15 + 1) at run
  rw [cleared_eq_haltList] at run
  simpa only [Nat.add_assoc] using run

def finishInTime (q : Nat) (base : Tape → List Bool) (word : List Bool)
    (state : State q) (hreversed : base .reversed = word.reverse)
    (houtput : base .output = []) :
    StateTransition.EvalsToInTime (Driver.machine q).step
      ⟨some .reverseOutput, state, base⟩
      (some (haltList (Driver.machine q) word)) (finishBudget base word) := by
  have first := reverseInTime q base word state hreversed houtput
  have last := cleanupInTime q (afterReversal base word) (state.1, none)
  rw [afterReversal_output] at last
  have run := StateTransition.EvalsToInTime.trans (Driver.machine q).step _ _
    ⟨some .reverseOutput, state, base⟩
    ⟨some (.cleanup 0), (state.1, none), afterReversal base word⟩
    (some (haltList (Driver.machine q) word)) first last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have budgetEq : ((∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) + 16) +
      (word.length + 1) =
      finishBudget base word := by
    dsimp only [finishBudget]
    omega
  exact run.steps_le_m.trans (Nat.le_of_eq budgetEq)

theorem afterReversal_selected_length_le (base : Tape → List Bool) (word : List Bool)
    (i : Fin 15) :
    (afterReversal base word (cleanupPorts i)).length ≤ (base (cleanupPorts i)).length := by
  have ho := cleanupPorts_ne_output i
  by_cases hr : cleanupPorts i = .reversed <;>
    simp [afterReversal, Reduction.MachineTransfer.tapesAt, ho, hr]

theorem stackLength_after_prefix (q : Nat) (input : List Bool)
    (base : Tape → List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (k : Tape) :
    (base k).length ≤ input.length + budget * Runtime.programPushBound (Driver.machine q) := by
  have bound := Runtime.executionSizeBound (Driver.machine q).step
    (fun cfg => (cfg.stk k).length) (Runtime.programPushBound (Driver.machine q))
    (Runtime.stepStackLength (Driver.machine q) k) prefixRun
  exact bound.trans (Nat.add_le_add_right
    (Runtime.initialStackLength (Driver.machine q) input k) _)

theorem finishBudget_le_of_prefix (q : Nat) (input : List Bool)
    (base : Tape → List Bool) (word : List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (hreversed : base .reversed = word.reverse) :
    finishBudget base word ≤
      16 * (input.length + budget * Runtime.programPushBound (Driver.machine q)) + 17 := by
  let B := input.length + budget * Runtime.programPushBound (Driver.machine q)
  have wordBound : word.length ≤ B := by
    simpa only [hreversed, List.length_reverse] using
      stackLength_after_prefix q input base state budget prefixRun .reversed
  have sumBound : (∑ i : Fin 15, (afterReversal base word (cleanupPorts i)).length) ≤ 15 * B := by
    calc
      _ ≤ ∑ _i : Fin 15, B := by
        apply Finset.sum_le_sum
        intro i _
        exact (afterReversal_selected_length_le base word i).trans
          (stackLength_after_prefix q input base state budget prefixRun (cleanupPorts i))
      _ = 15 * B := by simp
  dsimp only [finishBudget]
  omega

noncomputable def completedPolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  prefixTime + Polynomial.C 16 *
    (Polynomial.X + Polynomial.C (Runtime.programPushBound (Driver.machine q)) * prefixTime) +
    Polynomial.C 17

def finishAfterPrefix (q : Nat) (input : List Bool) (base : Tape → List Bool)
    (word : List Bool) (state : State q) (budget : Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩) budget)
    (hreversed : base .reversed = word.reverse) (houtput : base .output = []) :
    TM2OutputsInTime (Driver.machine q) input (some word)
      (budget + 16 * (input.length + budget * Runtime.programPushBound (Driver.machine q)) + 17) := by
  have last := finishInTime q base word state hreversed houtput
  let run := StateTransition.EvalsToInTime.trans (Driver.machine q).step _ _
    (initList (Driver.machine q) input) ⟨some .reverseOutput, state, base⟩
    (some (haltList (Driver.machine q) word)) prefixRun last
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have finishBound := finishBudget_le_of_prefix q input base word state budget prefixRun hreversed
  have allBound := run.steps_le_m
  omega

def finishAfterPolynomialPrefix (q : Nat) (input : List Bool) (base : Tape → List Bool)
    (word : List Bool) (state : State q) (prefixTime : Polynomial Nat)
    (prefixRun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) input) (some ⟨some .reverseOutput, state, base⟩)
      (prefixTime.eval input.length))
    (hreversed : base .reversed = word.reverse) (houtput : base .output = []) :
    TM2OutputsInTime (Driver.machine q) input (some word)
      ((completedPolynomial q prefixTime).eval input.length) := by
  have run := finishAfterPrefix q input base word state (prefixTime.eval input.length)
    prefixRun hreversed houtput
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  simpa only [completedPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Nat.mul_comm] using run.steps_le_m

end BinPackingGames.Foundations.PCP.AlphabetTable.Finish

namespace BinPackingGames.Foundations.PCP.RoundComputation

open Turing
open BinPackingGames.Foundations.Complexity

abbrev PreprocessingCertificate (H : RoundTables.BaseTable) :=
  TM2ComputableInPolyTime GraphTables.tableBits
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (PreprocessingTables.output H)

end BinPackingGames.Foundations.PCP.RoundComputation

namespace BinPackingGames.Foundations.PCP.PreprocessingFinishRuntime

open Turing BinPackingGames.Foundations.Complexity
open PreprocessingRegularTables

def finish (H : PreprocessingTables.BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (2 * (d + internalDegree)) :=
  PreprocessingStageMaps.lazy (d + internalDegree)
    (PreprocessingStageMaps.paddedOverlay H d input)

end BinPackingGames.Foundations.PCP.PreprocessingFinishRuntime

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitializeEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitializeEncoding

open BinPackingGames.Foundations.Complexity

abbrev Data := RawInstance × Bool

end BinPackingGap.SearchInitializeEncoding

end OAI
end


