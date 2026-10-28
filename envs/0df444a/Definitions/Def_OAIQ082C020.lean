-- Prove2me | Definitions.Def_OAIQ082C020
-- name    : OAIQ082C020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:50:55.396287+00:00
-- url     : https://prove2.me/theorems/a4f35fe7-d5d2-4533-b0c7-4d97b7e32413
-- title:
--   Definitions bundle OAIQ082C020 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 409 declarations of OpenAI's Lean: 247 definitions, 7 inductive types or structures, 6 instances and 149 theorems. The definitions and types are `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.configurationBody`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.initTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.initializationTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.stepExpressions`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.transitionTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionArena.preparedTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Nonempty.statement`, `OAI.BinPackingGames.Foundations.Complexity.MachineDrainMany.execution`, `OAI.BinPackingGames.Foundations.PCP.FinalBooleanVerifier.OutputAssignment`, `OAI.BinPackingGames.Foundations.PCP.FinalBooleanVerifier.extractLabeling`, `OAI.BinPackingGames.Foundations.PCP.PreprocessingGuarantees.restrictedLabel`, `OAI.BinPackingGames.Foundations.PCP.PreprocessingGuarantees.roundLabels`, `OAI.BinPackingGames.Foundations.PCP.PreprocessingRegularSoundness.roundLabels`, `OAI.BinPackingGames.Foundations.PCP.RoundTables.Satisfiable`, `OAI.BinPackingGames.Foundations.PCP.RoundTables.gap`, `OAI.BinPackingGap.ApproximationDecisionMachine.cfg`, `OAI.BinPackingGap.ApproximationDecisionMachine.computation`, `OAI.BinPackingGap.ApproximationDecisionMachine.machine`, `OAI.BinPackingGap.ApproximationDecisionMachine.program`, `OAI.BinPackingGap.ApproximationDecisionMachine.rawRun`, `OAI.BinPackingGap.BinaryMonusPreserving.monusInLinearTime`, `OAI.BinPackingGap.BinaryMonusPreserving.monusInTime`, `OAI.BinPackingGap.BinaryPowerMachine.bodyInTime`, `OAI.BinPackingGap.BinaryPowerMachine.loopInTime`, `OAI.BinPackingGap.BinaryPowerMachine.powerInPolynomialTime`, `OAI.BinPackingGap.BinaryPowerMachine.powerInTime`, `OAI.BinPackingGap.BinaryRegisterProgram.clearCommandInTime`, `OAI.BinPackingGap.BinaryRegisterProgram.commandInTime`, `OAI.BinPackingGap.BinaryRegisterProgram.copyCommandInTime`, `OAI.BinPackingGap.BinaryRegisterProgram.monusCommandInTime`, `OAI.BinPackingGap.BinaryRegisterProgram.programInTime`, `OAI.BinPackingGap.BinaryRegisterProgram.runInTime`, `OAI.BinPackingGap.ExtensionCapacityMachine.CoreRun`, `OAI.BinPackingGap.ExtensionCapacityMachine.cfg`, `OAI.BinPackingGap.ExtensionCapacityMachine.cleanupEntry`, `OAI.BinPackingGap.ExtensionCapacityMachine.cleanupInTime`, `OAI.BinPackingGap.ExtensionCapacityMachine.clearRowInTime`, `OAI.BinPackingGap.ExtensionCapacityMachine.compareInTime`, `OAI.BinPackingGap.ExtensionCapacityMachine.coreRun`, `OAI.BinPackingGap.ExtensionCapacityMachine.enlarge` and 214 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_BinaryPowerMachine`, `BinPacking_Arithmetic_BinaryToTallyMachine`, `BinPacking_Arithmetic_NatExpressionBounds`, `BinPacking_Arithmetic_NatExpressionBranch`, `BinPacking_Arithmetic_PackingRegisterUpdate`, `BinPacking_Arithmetic_ResetExpressionCompiler`, `BinPacking_Computation_MachineCanonicalOutput`, `BinPacking_Computation_MachineExpanderFamilyAffine`, `BinPacking_Computation_MachineRegularOwnerProgram`, `BinPacking_CookLevin_ClashMachine`, `BinPacking_CookLevin_PaddingCellsMachine`, `BinPacking_CookLevin_ProducerFrontStage`, `BinPacking_CookLevin_TransitionArena`, `BinPacking_CookLevin_ValidityMachine`, `BinPacking_CookLevin_VerifierCircuit`, `BinPacking_CookLevin_VerifierFront`, `BinPacking_Inventory_PackingConstantPool`, `BinPacking_Machines_GraphPackingGlobalExecution`, `BinPacking_Machines_GraphPackingJobEdge`, `BinPacking_Machines_GraphPackingJobList`, `BinPacking_Machines_GraphPackingMachine`, `BinPacking_Machines_GraphPackingPreparation`, `BinPacking_Machines_GraphPackingPreparationFinish`, `BinPacking_Machines_GraphPackingVerticesBound`, `BinPacking_Machines_PackingCountedProgram`, `BinPacking_Machines_PackingJobLoop`, `BinPacking_Machines_PackingPowerProgram`, `BinPacking_Machines_PackingSetupGraph`, `BinPacking_Machines_PackingVertexUpdate`, `BinPacking_PCP_FinalBooleanVerifier`, `BinPacking_PCP_PreprocessingGuarantees`, `BinPacking_PCP_PreprocessingRegularSoundness`, `BinPacking_PCP_RoundTableGap`, `BinPacking_Packing_PackingAssignments`, `BinPacking_Packing_PairExpressionCompiler`, `BinPacking_Search_ApproximationImpliesP`, `BinPacking_Search_ExtensionCapacityBounds`, `BinPacking_Search_ExtensionShapeMachine`, `BinPacking_Search_ExtensionValidationMachine`, `BinPacking_Search_ExtensionVerifier`, `BinPacking_Search_ExtensionVerifierPipeline`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C010`, `OAIQ082C011`, `OAIQ082C012`, `OAIQ082C013` and `OAIQ082C014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C024` and `OAIQ082C025`; the statements `OAI_BinPackingGames_Foundations_PCP_RoundTableGap_powered_count_gap` and `OAI.BinPackingGames.Foundations.PCP.RoundTableGap.powered_count_gap_oaiq082`; the proofs of `OAI_BinPackingGap_PCPFoundation_packingOutput_sound` and `OAI.BinPackingGap.PCPFoundation.packingOutput_sound_oaiq082`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C010
import Definitions.Def_OAIQ082C011
import Definitions.Def_OAIQ082C012
import Definitions.Def_OAIQ082C013
import Definitions.Def_OAIQ082C014

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryPowerMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryPowerMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinaryAddMachine (State clean)

variable {K Λ A : Type} [DecidableEq K]

section Executions

variable (slots : Fin 11 ↪ K) (labels : Label → Λ) (exit : Option Λ)
variable (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ label, p (labels label) = instruction slots labels exit label)

noncomputable def bodyInTime (base : K → List Bool) (a r : Nat) (token : Bool) (tally : List Bool)
    (ha : base (slots 0) = a.bits) (hr : base (slots 1) = r.bits)
    (ht : base (slots 9) = token :: tally) (hw : Workspace slots base) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .guard), clean ambient, base⟩
      (some ⟨some (labels .guard), clean ambient,
        Function.update (Function.update base (slots 9) tally) (slots 1) (a * r).bits⟩)
      (bodyBudget a r) := by
  have hd (i j : Fin 11) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  let bt := Function.update base (slots 9) tally
  let bm := Function.update bt (slots 2) (a * r).bits
  let bc := Function.update bm (slots 1) []
  let bv := Function.update (Function.update bc (slots 2) []) (slots 10) (a * r).bits.reverse
  let done := Function.update bt (slots 1) (a * r).bits
  have h2 := hw 2 (by decide) (by decide)
  have h10 := hw 10 (by decide) (by decide)
  have guardRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .guard), clean ambient, base⟩
      (some ⟨some (labels (.multiply .copyLeft)), clean ambient, bt⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change some (TM2.stepAux (p (labels .guard)) _ _) = _
    rw [atLabels]
    simp [instruction, TM2.stepAux, clean, BinaryAddMachine.state, ht, bt]
  have ms0 : mulSlots slots 0 = slots 0 := rfl
  have ms1 : mulSlots slots 1 = slots 1 := rfl
  have ms2 : mulSlots slots 2 = slots 2 := rfl
  have hma : bt ((mulSlots slots) 0) = a.bits := by
    simpa [ms0, bt, hd 0 9 (by decide)] using ha
  have hmr : bt ((mulSlots slots) 1) = r.bits := by
    simpa [ms1, bt, hd 1 9 (by decide)] using hr
  have hmw : ∀ i : Fin 9, 3 ≤ i.val → bt ((mulSlots slots) i) = [] := by
    intro i hi
    let j : Fin 11 := ⟨i.val, by omega⟩
    have hjval : j.val = i.val := rfl
    have hj9 : j.val ≠ 9 := by rw [hjval]; omega
    have hj : j ≠ 9 := by
      intro h
      apply hj9
      exact congrArg Fin.val h
    change bt (slots j) = []
    simpa [bt, hd j 9 hj] using hw j (by rw [hjval]; omega) hj9
  have mulRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .copyLeft)), clean ambient, bt⟩
      (some ⟨some (labels .clearAccumulator), clean ambient, bm⟩)
      (BinaryMulMachine.timePolynomial.eval (a.size + r.size)) := by
    have run := BinaryMulMachine.multiplyNatInPolynomialTime (mulSlots slots)
      (fun phase => labels (.multiply phase)) (some (labels .clearAccumulator)) p
      (fun phase => atLabels (.multiply phase)) bt a r hma hmr hmw ambient
    change StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .copyLeft)), clean ambient, bt⟩
      (some ⟨some (labels .clearAccumulator), clean ambient,
        Function.update bt (slots 2) ((a * r).bits ++ bt (slots 2))⟩)
      (BinaryMulMachine.timePolynomial.eval (a.size + r.size)) at run
    have hbt2 : bt (slots 2) = [] := by simp [bt, hd 2 9 (by decide), h2]
    simpa only [hbt2, List.append_nil] using run
  have clearRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .clearAccumulator), clean ambient, bm⟩
      (some ⟨some (labels .reverseProduct), clean ambient, bc⟩) (r.size + 1) := by
    have run := MachineDrain.drainInTime (slots 1) (labels .clearAccumulator)
      (some (labels .reverseProduct)) p (atLabels .clearAccumulator) bm
      ((ambient, false), none) none
    simpa [clean, BinaryAddMachine.state, bc, bm, bt, hd 1 2 (by decide),
      hd 1 9 (by decide), hr, Nat.size_eq_bits_len] using run
  have reverseRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .reverseProduct), clean ambient, bc⟩
      (some ⟨some (labels .restoreAccumulator), clean ambient, bv⟩)
      ((a * r).size + 1) := by
    have run := transferAtInTime (Γ := fun _ : K => Bool) (slots 2) (slots 10) (hd 2 10 (by decide)) id false
      (labels .reverseProduct) (some (labels .restoreAccumulator)) p
      (by simpa only [instruction] using atLabels .reverseProduct) bc ((ambient, false), none) none
    simpa [clean, BinaryAddMachine.state, tapesAt, bv, bc, bm, bt,
      hd 2 1 (by decide), hd 10 1 (by decide), hd 10 2 (by decide),
      hd 10 9 (by decide), h10, Nat.size_eq_bits_len] using run
  have restoreTape : tapesAt (slots 10) (slots 1) bv []
      ((bv (slots 10)).reverse.map id ++ bv (slots 1)) = done := by
    funext k
    by_cases h1 : k = slots 1
    · subst k
      simp [tapesAt, bv, bc, bm, bt, done, hd 1 10 (by decide), hd 1 2 (by decide)]
    · by_cases h2k : k = slots 2
      · subst k
        simp [tapesAt, bv, bc, bm, bt, done, hd 2 1 (by decide), hd 2 10 (by decide),
          hd 2 9 (by decide), h2]
      · by_cases h10k : k = slots 10
        · subst k
          simp [tapesAt, bv, bc, bm, bt, done, hd 10 1 (by decide),
            hd 10 9 (by decide), h10]
        · simp [tapesAt, bv, bc, bm, done, h1, h2k, h10k]
  have restoreRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .restoreAccumulator), clean ambient, bv⟩
      (some ⟨some (labels .guard), clean ambient, done⟩) ((a * r).size + 1) := by
    have run := transferAtInTime (Γ := fun _ : K => Bool) (slots 10) (slots 1) (hd 10 1 (by decide)) id false
      (labels .restoreAccumulator) (some (labels .guard)) p
      (by simpa only [instruction] using atLabels .restoreAccumulator) bv ((ambient, false), none) none
    change StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .restoreAccumulator), clean ambient, bv⟩
      (some ⟨some (labels .guard), clean ambient,
        tapesAt (slots 10) (slots 1) bv []
          ((bv (slots 10)).reverse.map id ++ bv (slots 1))⟩)
      ((bv (slots 10)).length + 1) at run
    rw [restoreTape] at run
    have hword : bv (slots 10) = (a * r).bits.reverse := by simp [bv]
    simpa only [hword, List.length_reverse, Nat.size_eq_bits_len] using run
  exact appendRuns _ (appendRuns _ (appendRuns _ (appendRuns _ guardRun mulRun) clearRun)
    reverseRun) restoreRun

noncomputable def loopInTime (base : K → List Bool) (a r : Nat) (tally : List Bool)
    (ha : base (slots 0) = a.bits) (hr : base (slots 1) = r.bits)
    (ht : base (slots 9) = tally) (hw : Workspace slots base) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .guard), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update (Function.update base (slots 9) []) (slots 1)
          (a ^ tally.length * r).bits⟩) (loopBudget a r tally) := by
  induction tally generalizing base r with
  | nil =>
      refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
      change some (TM2.stepAux (p (labels .guard)) _ _) = _
      rw [atLabels]
      have hself : Function.update (Function.update base (slots 9) []) (slots 1) r.bits =
          Function.update base (slots 9) [] := by
        have hd : slots 1 ≠ slots 9 := slots.injective.ne (by decide)
        have hs : (Function.update base (slots 9) []) (slots 1) = r.bits := by simp [hd, hr]
        rw [← hs, Function.update_eq_self]
      cases exit <;> simp [instruction, BinaryAddMachine.finish, BinaryAddMachine.exitAt,
        clean, BinaryAddMachine.state, TM2.stepAux, ht, hself]
  | cons token tally ih =>
      let next := Function.update (Function.update base (slots 9) tally) (slots 1) (a * r).bits
      have hd (i j : Fin 11) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
      have hna : next (slots 0) = a.bits := by
        simp [next, hd 0 1 (by decide), hd 0 9 (by decide), ha]
      have hnr : next (slots 1) = (a * r).bits := by simp [next]
      have hnt : next (slots 9) = tally := by simp [next, hd 9 1 (by decide)]
      have hnw : Workspace slots next := by
        intro i hi hi9
        have hi1 : i ≠ 1 := by intro h; have := congrArg Fin.val h; omega
        have hi9' : i ≠ 9 := by intro h; exact hi9 (congrArg Fin.val h)
        simp [next, hd i 1 hi1, hd i 9 hi9', hw i hi hi9]
      have first := bodyInTime slots labels exit p atLabels base a r token tally ha hr ht hw ambient
      have second := ih next (a * r) hna hnr hnt hnw
      have joined := appendRuns _ first second
      have hvalue : a ^ tally.length * (a * r) = a ^ (token :: tally).length * r := by
        simp [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      have hfinal : Function.update (Function.update next (slots 9) []) (slots 1)
          (a ^ tally.length * (a * r)).bits =
          Function.update (Function.update base (slots 9) []) (slots 1)
            (a ^ (token :: tally).length * r).bits := by
        funext k
        by_cases h1 : k = slots 1
        · subst k; simp [hvalue]
        · by_cases h9 : k = slots 9
          · subst k; simp [hd 9 1 (by decide)]
          · simp [next, h1, h9]
      simpa only [loopBudget, hfinal] using joined

noncomputable def powerInTime (base : K → List Bool) (a : Nat) (tally : List Bool)
    (ha : base (slots 0) = a.bits) (outputEmpty : base (slots 1) = [])
    (ht : base (slots 9) = tally) (hw : Workspace slots base) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .initialize_), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update (Function.update base (slots 9) []) (slots 1) (a ^ tally.length).bits⟩)
      (1 + loopBudget a 1 tally) := by
  let initial := Function.update base (slots 1) [true]
  have hd (i j : Fin 11) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
  have start : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .initialize_), clean ambient, base⟩
      (some ⟨some (labels .guard), clean ambient, initial⟩) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl _ }
    change some (TM2.stepAux (p (labels .initialize_)) _ _) = _
    rw [atLabels]
    simp [instruction, TM2.stepAux, clean, BinaryAddMachine.state, outputEmpty, initial]
  have hai : initial (slots 0) = a.bits := by simp [initial, hd 0 1 (by decide), ha]
  have hri : initial (slots 1) = (1 : Nat).bits := by simp [initial]
  have hti : initial (slots 9) = tally := by simp [initial, hd 9 1 (by decide), ht]
  have hwi : Workspace slots initial := by
    intro i hi hi9
    have hi1 : i ≠ 1 := by intro h; have := congrArg Fin.val h; omega
    simp [initial, hd i 1 hi1, hw i hi hi9]
  have run := loopInTime slots labels exit p atLabels initial a 1 tally hai hri hti hwi ambient
  have hfinal : Function.update (Function.update initial (slots 9) []) (slots 1)
      (a ^ tally.length * 1).bits =
      Function.update (Function.update base (slots 9) []) (slots 1) (a ^ tally.length).bits := by
    funext k
    by_cases h1 : k = slots 1
    · subst k; simp
    · by_cases h9 : k = slots 9
      · subst k; simp [hd 9 1 (by decide)]
      · simp [initial, h1, h9]
  simpa only [hfinal] using appendRuns _ start run

end Executions

noncomputable def powerInPolynomialTime (slots : Fin 11 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a : Nat) (tally : List Bool)
    (ha : base (slots 0) = a.bits) (outputEmpty : base (slots 1) = [])
    (ht : base (slots 9) = tally) (hw : Workspace slots base) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .initialize_), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update (Function.update base (slots 9) []) (slots 1) (a ^ tally.length).bits⟩)
      (timePolynomial.eval (a.size + tally.length)) := by
  let run := powerInTime slots labels exit p atLabels base a tally ha outputEmpty ht hw ambient
  exact {
    steps := run.steps
    evals_in_steps := run.evals_in_steps
    steps_le_m := run.steps_le_m.trans (budget_le_timePolynomial a tally)
  }

end BinPackingGap.BinaryPowerMachine

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

def execution (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction chosen labels exit l)
    (base : Tapes K) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry chosen labels exit, (ambient, register), base⟩
      (some ⟨exit, (ambient, finalRegister chosen register), finalTapes chosen base⟩)
      (lengthSum chosen base + chosen.length) where
  steps := steps chosen base
  evals_in_steps := trace chosen labels exit program atLabels base ambient register
  steps_le_m := steps_le chosen base

end BinPackingGames.Foundations.Complexity.MachineDrainMany

namespace BinPackingGames.Foundations.Complexity.MachineCanonicalOutput

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

theorem finiteAlphabet (P : Program K Λ σ) (chosen : List K) :
    MachineFiniteAlphabet.FiniteAlphabet (completedMachine P chosen) := by
  intro k
  exact inferInstanceAs (Finite Bool)

theorem computableInPolyTime_finite_alphabet {α β : Type}
    (P : Program K Λ σ) (chosen : List K)
    (complete : ∀ k, k ∈ chosen ↔ k ≠ P.output)
    (encodeIn : α → List Bool) (encodeOut : β → List Bool) (f : α → β)
    (rawTime : Polynomial Nat)
    (run : ∀ a, TerminalRun P (encodeIn a) (encodeOut (f a))
      (rawTime.eval (encodeIn a).length)) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computableInPolyTime P chosen complete encodeIn encodeOut f rawTime run).tm :=
  finiteAlphabet P chosen

end BinPackingGames.Foundations.Complexity.MachineCanonicalOutput

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpressionBranch
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryMonusPreserving

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinaryAddMachine (State clean)
open BinaryArithmetic

variable {K Λ A : Type} [DecidableEq K]

def monusInTime (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a b : Nat)
    (ha : base (slots 0) = a.bits) (hb : base (slots 1) = b.bits)
    (workspace : ∀ i : Fin 7, 2 ≤ i.val → base (slots i) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exit, clean ambient, resultTapes slots base a b⟩) (budget a b) := by
  have hd (i j : Fin 7) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
  have h2 := workspace 2 (by decide)
  have h3 := workspace 3 (by decide)
  have h4 := workspace 4 (by decide)
  have h5 := workspace 5 (by decide)
  have h6 := workspace 6 (by decide)
  let bl := Function.update base (slots 2) a.bits
  let bb := Function.update bl (slots 3) b.bits
  let raw := rawSubtract a.bits b.bits false
  let bs := Function.update base (slots 4) raw.1.reverse
  have rawLength : raw.1.length = max a.size b.size := by
    simpa [raw, Nat.size_eq_bits_len] using rawSubtract_length a.bits b.bits false
  have rawResult : (a - b).bits = if raw.2 then [] else trim raw.1 := by
    rw [← monus_bits, monus, subBorrow_eq_rawSubtract]
    change trim ((if raw.2 then none else some raw.1).getD []) = _
    cases raw.2 <;> simp [trim]
  have leftRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨some (labels .rightOut), clean ambient, bl⟩) (2 * (a.size + 1)) := by
    have run := MachineCopy.copyInTime (slots 0) (slots 2) (slots 6)
      (hd 0 2 (by decide)) (hd 0 6 (by decide)) (hd 2 6 (by decide)) false
      (labels .leftOut) (labels .leftBack) (some (labels .rightOut)) p
      (atLabels .leftOut) (atLabels .leftBack) base h6 ((ambient, false), none) none
    simpa [clean, BinaryAddMachine.state, ha, h2, bl, Nat.size_eq_bits_len] using run
  have rightRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .rightOut), clean ambient, bl⟩
      (some ⟨some (labels .subtract), clean ambient, bb⟩) (2 * (b.size + 1)) := by
    have scratch : bl (slots 6) = [] := by simp [bl, hd 6 2 (by decide), h6]
    have run := MachineCopy.copyInTime (slots 1) (slots 3) (slots 6)
      (hd 1 3 (by decide)) (hd 1 6 (by decide)) (hd 3 6 (by decide)) false
      (labels .rightOut) (labels .rightBack) (some (labels .subtract)) p
      (atLabels .rightOut) (atLabels .rightBack) bl scratch ((ambient, false), none) none
    simpa [clean, BinaryAddMachine.state, bl, bb, hd 1 2 (by decide),
      hd 3 2 (by decide), hb, h3, Nat.size_eq_bits_len] using run
  have subStart : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4)
      bb a.bits b.bits [] = bb := by
    have hleft : bb (slots 2) = a.bits := by simp [bb, bl, hd 2 3 (by decide)]
    have hright : bb (slots 3) = b.bits := by simp [bb]
    have hout : bb (slots 4) = [] := by
      simp [bb, bl, hd 4 3 (by decide), hd 4 2 (by decide), h4]
    have self : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4) bb
        (bb (slots 2)) (bb (slots 3)) (bb (slots 4)) = bb := by simp [BinaryAddMachine.tapes]
    simpa only [hleft, hright, hout] using self
  have subFinish : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4)
      bb [] [] raw.1.reverse = bs := by
    funext k
    by_cases hl : k = slots 2
    · subst k
      simp [BinaryAddMachine.tapes, bs, hd 2 3 (by decide), hd 2 4 (by decide), h2]
    · by_cases hr : k = slots 3
      · subst k
        simp [BinaryAddMachine.tapes, bs, hd 3 4 (by decide), h3]
      · by_cases hs : k = slots 4
        · subst k; simp [BinaryAddMachine.tapes, bs]
        · simp [BinaryAddMachine.tapes, bs, bb, bl, hl, hr, hs]
  have subRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .subtract), clean ambient, bb⟩
      (some ⟨some (labels (if raw.2 then .drain else .trim)), clean ambient, bs⟩)
      (max a.size b.size + 1) := by
    have run := BinaryMonusMachine.subtractInTime (slots 2) (slots 3) (slots 4)
      (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide))
      (labels .subtract) (fun borrow => some (labels (if borrow then .drain else .trim)))
      p (atLabels .subtract) bb ambient a.bits b.bits [] false none none
    simpa only [subStart, List.append_nil, subFinish, Nat.size_eq_bits_len,
      clean, raw] using run
  have prefixRun := appendRuns _ (appendRuns _ leftRun rightRun) subRun
  cases hborrow : raw.2 with
  | true =>
      have hzero : (a - b).bits = [] := by simpa [hborrow] using rawResult
      have hfinish : Function.update bs (slots 4) [] = resultTapes slots base a b := by
        funext k
        by_cases hs : k = slots 4
        · subst k
          simp [bs, resultTapes, hzero, hd 4 5 (by decide), h4]
        · by_cases ho : k = slots 5
          · subst k
            simp [bs, resultTapes, hzero, hd 5 4 (by decide), h5]
          · simp [bs, resultTapes, hs, ho]
      have run := MachineDrain.drainInTime (slots 4) (labels .drain) exit p
        (atLabels .drain) bs ((ambient, false), none) none
      have drainRun : StateTransition.EvalsToInTime (TM2.step p)
          ⟨some (labels .drain), clean ambient, bs⟩
          (some ⟨exit, clean ambient, resultTapes slots base a b⟩)
          (max a.size b.size + 1) := by
        simpa only [clean, BinaryAddMachine.state, hfinish, bs, Function.update_self,
          List.length_reverse, rawLength] using run
      have before : StateTransition.EvalsToInTime (TM2.step p)
          ⟨some (labels .leftOut), clean ambient, base⟩
          (some ⟨some (labels .drain), clean ambient, bs⟩)
          (2 * (a.size + 1) + 2 * (b.size + 1) + (max a.size b.size + 1)) := by
        simpa only [hborrow, ite_true, if_true] using prefixRun
      exact enlarge (appendRuns _ before drainRun) (by unfold budget; omega)
  | false =>
      have hcanonical : trim raw.1 = (a - b).bits := by simpa [hborrow] using rawResult.symm
      let bt := Function.update base (slots 4) (a - b).bits.reverse
      have htrim : Function.update bs (slots 4) (trimHigh (bs (slots 4))) = bt := by
        simp [bs, bt, trimHigh_reverse, hcanonical]
      have trimRun : StateTransition.EvalsToInTime (TM2.step p)
          ⟨some (labels .trim), clean ambient, bs⟩
          (some ⟨some (labels .transfer), clean ambient, bt⟩)
          (max a.size b.size + 1) := by
        have run := BinaryMonusMachine.trimInTime (slots 4) (labels .trim)
          (some (labels .transfer)) p (atLabels .trim) bs ((ambient, false), none) none
        rw [htrim] at run
        simpa only [clean, BinaryAddMachine.state, bs, Function.update_self,
          List.length_reverse, rawLength] using run
      have outputEmpty : bt (slots 5) = [] := by simp [bt, hd 5 4 (by decide), h5]
      have htransfer : tapesAt (slots 4) (slots 5) bt [] (a - b).bits =
          resultTapes slots base a b := by
        funext k
        by_cases ho : k = slots 5
        · subst k; simp [tapesAt, resultTapes]
        · by_cases hs : k = slots 4
          · subst k; simp [tapesAt, resultTapes, hd 4 5 (by decide), h4]
          · simp [tapesAt, resultTapes, bt, ho, hs]
      have transferRun : StateTransition.EvalsToInTime (TM2.step p)
          ⟨some (labels .transfer), clean ambient, bt⟩
          (some ⟨exit, clean ambient, resultTapes slots base a b⟩)
          ((a - b).size + 1) := by
        have atTransfer : p (labels .transfer) =
            loopAt (Γ := fun _ : K => Bool) (slots 4) (slots 5) (id : Bool → Bool) false
              (labels .transfer) exit := by
          simpa only [instruction] using atLabels .transfer
        have run := transferAtInTime (Γ := fun _ : K => Bool) (slots 4) (slots 5)
          (hd 4 5 (by decide)) (id : Bool → Bool) false
          (labels .transfer) exit p atTransfer bt ((ambient, false), none) none
        have word : bt (slots 4) = (a - b).bits.reverse := by simp [bt]
        simpa only [clean, BinaryAddMachine.state, word,
          List.length_reverse, List.reverse_reverse, List.map_id, outputEmpty,
          List.append_nil, Nat.size_eq_bits_len, htransfer] using run
      have before : StateTransition.EvalsToInTime (TM2.step p)
          ⟨some (labels .leftOut), clean ambient, base⟩
          (some ⟨some (labels .trim), clean ambient, bs⟩)
          (2 * (a.size + 1) + 2 * (b.size + 1) + (max a.size b.size + 1)) := by
        simpa only [hborrow, Bool.false_eq_true, ite_false] using prefixRun
      have hsize := size_monus_le a b
      exact enlarge (appendRuns _ (appendRuns _ before trimRun) transferRun)
        (by unfold budget; omega)

def monusInLinearTime (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a b : Nat)
    (ha : base (slots 0) = a.bits) (hb : base (slots 1) = b.bits)
    (workspace : ∀ i : Fin 7, 2 ≤ i.val → base (slots i) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exit, clean ambient, resultTapes slots base a b⟩)
      (5 * (a.size + b.size) + 7) :=
  enlarge (monusInTime slots labels exit p atLabels base a b ha hb workspace ambient)
    (budget_le a b)

end BinPackingGap.BinaryMonusPreserving

namespace BinPackingGap.NatExpressionCompiler

open BinaryRegisterProgram

variable {α Reg L R N : Type}

variable [DecidableEq Reg]

def Correct (inputs : α → Reg) (nodes : N ↪ Reg) (out : N)
    (value : (α → Nat) → Nat) (commands : List (Command Reg)) : Prop :=
  ∀ regs : Reg → Nat, (∀ node, regs (nodes node) = 0) →
    Ready commands regs ∧
      resultOf commands regs (nodes out) = value (fun a => regs (inputs a)) ∧
      ∀ r, (∀ node, r ≠ nodes node) → resultOf commands regs r = regs r

end BinPackingGap.NatExpressionCompiler

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpressionBounds
attribute [-instance] _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryRegisterProgram

section

open Turing
open BinPackingGames.Foundations.Complexity

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

noncomputable def monusCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg)
    (labels : LocalLabel (.monus op) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ label,
      p (labels label) = localInstruction slot (.monus op) labels exit label)
    (base : K → List Bool) (values : Reg → Nat)
    (ready : commandReady (.monus op) values) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.monus op))), BinaryAddMachine.clean ambient,
        registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base (result (.monus op) values)⟩)
      (cost (.monus op) values) := by
  have hd : values op.destination = 0 := ready
  have hwork : ∀ i : Fin 7, 2 ≤ i.val →
      registerTapes slot base values (addSlots slot op i) = [] := by
    intro i hi
    by_cases hout : i = 5
    · subst i; simp [hd]
    · exact registerTapes_add_workspace slot op base values i hi hout
  have run := BinaryMonusPreserving.monusInLinearTime (addSlots slot op) labels exit p
    (fun label => atLabels label) (registerTapes slot base values)
    (values op.left) (values op.right) (by simp) (by simp) hwork ambient
  have hresult : BinaryMonusPreserving.resultTapes (addSlots slot op)
      (registerTapes slot base values) (values op.left) (values op.right) =
      registerTapes slot base (result (.monus op) values) := by
    simpa only [BinaryMonusPreserving.resultTapes, addSlots_five, result, destination, value]
      using registerTapes_update slot base values op.destination
        (values op.left - values op.right)
  simpa only [hresult, main, cost] using run

end

section

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction
open BinaryAddMachine (State clean)

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

noncomputable def clearCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (dst : Reg)
    (labels : LocalLabel (.clear dst) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, p (labels l) = localInstruction slot (.clear dst) labels exit l)
    (base : K → List Bool) (vals : Reg → ℕ)
    (_ready : commandReady (.clear dst) vals) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.clear dst))), clean ambient, registerTapes slot base vals⟩
      (some ⟨exit, clean ambient, registerTapes slot base (result (.clear dst) vals)⟩)
      (cost (.clear dst) vals) := by
  have run := MachineDrain.drainInTime (slot (.inl dst)) (labels ()) exit p
    (by simpa only [localInstruction] using atLabels ())
    (registerTapes slot base vals) ((ambient, false), none) none
  have hframe : Function.update (registerTapes slot base vals) (slot (.inl dst)) [] =
      registerTapes slot base (result (.clear dst) vals) := by
    simpa only [result, destination, value, Nat.zero_bits] using
      registerTapes_update slot base vals dst 0
  rw [hframe] at run
  simpa only [main, cost, BinaryAddMachine.clean, BinaryAddMachine.state,
    registerTapes_reg, Nat.size_eq_bits_len] using run

noncomputable def copyCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (dst src : Reg) (different : dst ≠ src)
    (labels : LocalLabel (.copy dst src different) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l,
      p (labels l) = localInstruction slot (.copy dst src different) labels exit l)
    (base : K → List Bool) (vals : Reg → ℕ)
    (ready : commandReady (.copy dst src different) vals) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.copy dst src different))), clean ambient,
        registerTapes slot base vals⟩
      (some ⟨exit, clean ambient,
        registerTapes slot base (result (.copy dst src different) vals)⟩)
      (cost (.copy dst src different) vals) := by
  have hzero : vals dst = 0 := ready
  have hSD : slot (.inl src) ≠ slot (.inl dst) :=
    slot.injective.ne (by simpa only [ne_eq, Sum.inl.injEq] using different.symm)
  have hSC : slot (.inl src) ≠ slot (.inr (0 : Fin 6)) :=
    slot.injective.ne (by simp)
  have hDC : slot (.inl dst) ≠ slot (.inr (0 : Fin 6)) :=
    slot.injective.ne (by simp)
  have run := MachineCopy.copyInTime (slot (.inl src)) (slot (.inl dst))
    (slot (.inr (0 : Fin 6))) hSD hSC hDC false (labels false) (labels true) exit p
    (by simpa [localInstruction] using atLabels false)
    (by simpa [localInstruction] using atLabels true)
    (registerTapes slot base vals) (by simp only [registerTapes_scratch])
    ((ambient, false), none) none
  have hframe : Function.update (registerTapes slot base vals) (slot (.inl dst))
      (registerTapes slot base vals (slot (.inl src)) ++
        registerTapes slot base vals (slot (.inl dst))) =
      registerTapes slot base (result (.copy dst src different) vals) := by
    simp only [registerTapes_reg, hzero, Nat.zero_bits, List.append_nil]
    exact registerTapes_update slot base vals dst (vals src)
  rw [hframe] at run
  simpa only [main, cost, BinaryAddMachine.clean, BinaryAddMachine.state,
    registerTapes_reg, Nat.size_eq_bits_len] using run

end

open Turing
open BinPackingGames.Foundations.Complexity

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

noncomputable def commandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (command : Command Reg)
    (labels : LocalLabel command → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ l, p (labels l) = localInstruction slot command labels exit l)
    (base : K → List Bool) (values : Reg → Nat) (ready : commandReady command values)
    (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main command)), BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient, registerTapes slot base (result command values)⟩)
      (cost command values) := by
  cases command with
  | add op => exact addCommandInTime slot op labels exit p atLabels base values ready ambient
  | mul op => exact mulCommandInTime slot op labels exit p atLabels base values ready ambient
  | monus op => exact monusCommandInTime slot op labels exit p atLabels base values ready ambient
  | constant dst n =>
      exact constantCommandInTime slot dst n labels exit p atLabels base values ready ambient
  | clear dst => exact clearCommandInTime slot dst labels exit p atLabels base values ready ambient
  | copy dst src different =>
      exact copyCommandInTime slot dst src different labels exit p atLabels base values ready ambient

noncomputable def runInTime (slot : (Reg ⊕ Fin 6) ↪ K)
    (commands : List (Command Reg)) (labels : Label commands → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ l, p (labels l) = instruction slot commands labels exit l)
    (base : K → List Bool) (values : Reg → Nat) (ready : Ready commands values) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨entry commands labels exit, BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base (resultOf commands values)⟩) (budget commands values) := by
  induction commands generalizing values with
  | nil => exact { steps := 0, evals_in_steps := rfl, steps_le_m := Nat.le_refl 0 }
  | cons command commands ih =>
      have firstRun := commandInTime slot command (fun l => labels (.inl l))
        (entry commands (fun l => labels (.inr l)) exit) p
        (fun l => atLabels (.inl l)) base values ready.1 ambient
      have tailRun := ih (fun l => labels (.inr l)) (fun l => atLabels (.inr l))
        (result command values) ready.2
      exact appendRuns firstRun tailRun

noncomputable def programInTime (slot : (Reg ⊕ Fin 6) ↪ K)
    (commands : List (Command Reg)) (base : K → List Bool) (values : Reg → Nat)
    (ready : Ready commands values) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program (A := A) slot commands))
      ⟨entry commands id none, BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      (some ⟨none, BinaryAddMachine.clean ambient,
        registerTapes slot base (resultOf commands values)⟩) (budget commands values) :=
  runInTime slot commands id none (program slot commands) (fun _ => rfl) base values ready ambient

end BinPackingGap.BinaryRegisterProgram

namespace BinPackingGap.NatExpressionCompiler

open BinaryRegisterProgram

variable {α Reg : Type} [DecidableEq Reg]

def compileInto (inputs : α → Reg) :
    (expression : Expr α) → (nodes : Node expression ↪ Reg) →
      (∀ a node, inputs a ≠ nodes node) → List (Command Reg)
  | .constant n, nodes, _ => [.constant (nodes ()) n]
  | .input a, nodes, apart => [.copy (nodes ()) (inputs a) (apart a ()).symm]
  | .add left right, nodes, apart =>
      (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))) ++
      compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node)))) ++
      [command .add (branchOperands nodes (root left) (root right))]
  | .mul left right, nodes, apart =>
      (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))) ++
      compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node)))) ++
      [command .mul (branchOperands nodes (root left) (root right))]
  | .monus left right, nodes, apart =>
      (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))) ++
      compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node)))) ++
      [command .monus (branchOperands nodes (root left) (root right))]

end BinPackingGap.NatExpressionCompiler

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PreprocessingRegularSoundness
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype _root_.OAI.BinPackingGap.UniformTree.nodeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

noncomputable def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    Fin t.vertices → GraphTables.Label :=
  CloudRounding.roundLabels
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (fun z => labels (vertexOrder t (padding t) z))

end BinPackingGames.Foundations.PCP.PreprocessingRegularSoundness

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PreprocessingGuarantees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.PreprocessingGuarantees

open PoweringWalks SpectralReturn PreprocessingTables
open PreprocessingRegularTables (internalDegree regularize)

variable {n d e : Nat}

def restrictedLabel (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) :
    Fin (regularVertices t) → GraphTables.Label :=
  fun v => labels (v.castLE (PreprocessingLevels.le_paddedSize (regularVertices t)))

def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertices t) → GraphTables.Label) : Fin t.vertices → GraphTables.Label :=
  PreprocessingRegularSoundness.roundLabels t (restrictedLabel t labels)

end BinPackingGames.Foundations.PCP.PreprocessingGuarantees

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierCircuit
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

open Turing StatementCircuit CircuitBatch
open scoped BigOperators

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.alphabetFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.labelFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.stateFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.labelDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.stateDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.alphabetDecidable
theorem actualRun_stack_le (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (t : Nat) (ht : t ≤ V.horizon input.length) (k : V.computation.tm.K) :
    ((actualRun V input bits t).stk k).length ≤ capacity V input.length :=
  (BoundedExecution.run_stack_le V.computation.tm (machineInput V input bits)
    (V.horizon input.length) t ht k).trans (stackCapacity_le V input bits)

theorem actualRun_stepSafe (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (t : Nat) (ht : t < V.horizon input.length) :
    MachineCircuit.StepSafe (capacity V input.length) V.computation.tm.m
      (actualRun V input bits t) := by
  intro label _
  apply BoundedExecution.statementSafe_of_budget
  intro k
  exact (BoundedExecution.statement_budget V.computation.tm (machineInput V input bits)
    (V.horizon input.length) t ht label k).trans (stackCapacity_le V input bits)

theorem timeFrame_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (hv : WitnessEncoding.Valid bits) (t : Nat) (ht : t ≤ V.horizon input.length) :
    (timeFrame V input t).eval bits = stateEncoding V input (actualRun V input bits t)
      ((WitnessCircuit.validityExpr _).eval bits) := by
  induction t with
  | zero => exact initialFrame_eval V input bits hv
  | succ t ih =>
    have hprev := ih (by omega)
    change ((timeFrame V input t).step (stepExpressions V input)).eval bits = _
    rw [Frame.step_eval_fun, hprev]
    have hs := stepExpressions_eval V input (actualRun V input bits t)
      (actualRun_stepSafe V input bits t (by omega))
      ((WitnessCircuit.validityExpr _).eval bits)
    change (fun i => (stepExpressions V input i).eval
      (stateEncoding V input (actualRun V input bits t)
        ((WitnessCircuit.validityExpr _).eval bits))) = _ at hs
    simpa only [actualRun, BoundedExecution.run_succ] using hs

theorem circuitOfVerifier_accepts_iff (V : NPVerifier) (input : List Bool)
    (bits : FreeBits V input) :
    (circuitOfVerifier V input).eval bits = true ↔
      WitnessEncoding.Valid bits ∧ V.verify (input, WitnessEncoding.decode bits) = true := by
  rw [circuitOfVerifier_eval]
  constructor
  · intro h
    have hvalid := ((acceptanceExpr_eval V input _).mp h).1
    rw [timeFrame_validity] at hvalid
    have hv : WitnessEncoding.Valid bits := (WitnessCircuit.eval_validityExpr bits).mp hvalid
    rw [timeFrame_eval V input bits hv _ le_rfl] at h
    have he := (acceptanceExpr_stateEncoding V input
      (actualRun V input bits (V.horizon input.length)) _
      (actualRun_stack_le V input bits _ le_rfl)).mp h
    exact ⟨hv, (actualRun_accepting_iff V input bits).mp he.2⟩
  · rintro ⟨hv, hverify⟩
    rw [timeFrame_eval V input bits hv _ le_rfl]
    apply (acceptanceExpr_stateEncoding V input
      (actualRun V input bits (V.horizon input.length)) _
      (actualRun_stack_le V input bits _ le_rfl)).mpr
    exact ⟨(WitnessCircuit.eval_validityExpr bits).mpr hv,
      (actualRun_accepting_iff V input bits).mpr hverify⟩

theorem circuitOfVerifier_correct (V : NPVerifier) (input : List Bool) :
    (circuitOfVerifier V input).toFormula.Satisfiable ↔ V.Accepts input := by
  rw [Circuit.toFormula_satisfiable_iff_eval, WitnessEncoding.accepts_iff_valid_assignment]
  change (∃ bits : FreeBits V input, (circuitOfVerifier V input).eval bits = true) ↔ _
  exact exists_congr (fun bits => circuitOfVerifier_accepts_iff V input bits)

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPowerProgram
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BooleanTapeCode

open Turing FiniteTapeProgram BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {K A : Type} [DecidableEq K]

theorem framePayload_exec (source scratch destination : K)
    (hSW : source ≠ scratch) (hSD : source ≠ destination) (hWD : scratch ≠ destination)
    (base : K → List Bool) (hW : base scratch = []) (a : A) (register : Option Bool) :
    Exec (framePayload source scratch destination) ⟨((a, ()), register), base⟩
      (3 * (base source).length + 2)
      ⟨clean a, Function.update base destination
        (((base source).flatMap (fun b => [true, b])).reverse ++ base destination)⟩ := by
  apply Exec.routine
  simpa only [framePayload_output, clean] using
    MachineTransducerCopy.transduceCopyTrace source scratch destination hSW hSD hWD
      () (fun _ _ => ()) (fun _ b => [true, b]) FrameLabel.scan .restore
      (fun _ b => .emit b) none (frameProgram source scratch destination)
      rfl (fun _ _ => rfl) rfl base hW a () register

theorem frame_exec (source scratch destination : K)
    (hSW : source ≠ scratch) (hSD : source ≠ destination) (hWD : scratch ≠ destination)
    (base : K → List Bool) (hW : base scratch = []) (a : A) (register : Option Bool) :
    Exec (frame source scratch destination) ⟨((a, ()), register), base⟩
      (3 * (base source).length + 3)
      ⟨clean a, Function.update base destination
        ((BinPackingCompleteness.BinaryEncoding.frame (base source)).reverse ++ base destination)⟩ := by
  have first := framePayload_exec source scratch destination hSW hSD hWD base hW a register
  have last := Exec.atom (.push destination (fun _ => false) .done)
    (Data.mk (clean a) (Function.update base destination
      (((base source).flatMap (fun b => [true, b])).reverse ++ base destination)))
  simpa [frame, Action.eval, frame_eq, List.reverse_append, List.append_assoc,
    Nat.add_assoc] using Exec.seq first last

end BinPackingGap.BooleanTapeCode

namespace BinPackingGap.PackingPowerProgram

open Turing
open BinPackingGames.Foundations.Complexity
open FiniteTapeProgram

variable {K A : Type} [DecidableEq K]

def code (slots : Fin 11 ↪ K) : Code (K := K) (S := BinaryAddMachine.State A) :=
  .routine BinaryPowerMachine.Label inferInstance .initialize_ (BinaryPowerMachine.program slots)

end BinPackingGap.PackingPowerProgram

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryToTallyMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.BinaryRegisterStructured

open Turing BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram FiniteTapeProgram

variable {Reg K A : Type} [DecidableEq Reg] [DecidableEq K]

theorem exec (slot : (Reg ⊕ Fin 6) ↪ K) (commands : List (Command Reg))
    (base : K → List Bool) (values : Reg → Nat) (ready : Ready commands values)
    (ambient : A) :
    ∃ steps ≤ budget commands values + 1,
      Exec (code slot commands)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base values⟩ steps
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (resultOf commands values)⟩ := by
  induction commands generalizing values with
  | nil => exact ⟨1, Nat.le_refl _, Exec.atom .done _⟩
  | cons command tail ih =>
    let run := commandInTime slot command id none (localInstruction slot command id none)
      (fun _ => rfl) base values ready.1 ambient
    obtain ⟨n, hn, htail⟩ := ih (result command values) ready.2
    refine ⟨run.steps + n, ?_, ?_⟩
    · have hr := run.steps_le_m
      change run.steps + n ≤ cost command values + budget tail (result command values) + 1
      omega
    · have head : Exec (.routine (LocalLabel command) inferInstance (main command)
          (localInstruction slot command id none))
          ⟨BinaryAddMachine.clean ambient, registerTapes slot base values⟩ run.steps
          ⟨BinaryAddMachine.clean ambient, registerTapes slot base (result command values)⟩ := by
        refine Exec.routine inferInstance (main command)
          (localInstruction slot command id none) _ _ run.steps ?_
        have trace := run.evals_in_steps
        change (MachineComposition.advance (TM2.step
          (localInstruction (A := A) slot command id none)))^[run.steps]
          (some (⟨some (main command), BinaryAddMachine.clean ambient,
            registerTapes slot base values⟩ : TM2.Cfg (fun _ : K => Bool)
              (LocalLabel command) (BinaryAddMachine.State A))) =
          some ⟨none, BinaryAddMachine.clean ambient,
            registerTapes slot base (result command values)⟩ at trace
        exact trace
      exact Exec.seq head htail

theorem exec_polynomial (slot : (Reg ⊕ Fin 6) ↪ K) (commands : List (Command Reg))
    (base : K → List Bool) (values : Reg → Nat) (ready : Ready commands values)
    (ambient : A) (width : Nat) (hwidth : ∀ r, (values r).size ≤ width) :
    ∃ steps ≤ (runtimePolynomial commands).eval width + 1,
      Exec (code slot commands)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base values⟩ steps
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (resultOf commands values)⟩ := by
  obtain ⟨n, hn, hrun⟩ := exec slot commands base values ready ambient
  refine ⟨n, hn.trans ?_, hrun⟩
  rw [runtimePolynomial_eval]
  exact Nat.add_le_add_right
    (budget_le commands values (staticWidth commands width)
      (bitBounded_from_input commands values width hwidth)) 1

end BinPackingGap.BinaryRegisterStructured

namespace BinPackingGap.BinaryToTallyMachine

open BinPackingGames.Foundations.Complexity BinaryRegisterProgram FiniteTapeProgram

variable {K A : Type} [DecidableEq K]

theorem body_exec (slot : (Reg ⊕ Fin 6) ↪ K) (output : K)
    (outside : ∀ q, slot q ≠ output) (base : K → List Bool)
    (n r : Nat) (ambient : A) :
    ∃ steps ≤ 6 * (r + 1).size + 3 * r.size + 19,
      Exec (body slot output)
        ((guard slot).eval
          ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n (r + 1))⟩)
        steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot (Function.update base output (true :: base output)) (running n r)⟩ := by
  obtain ⟨t, ht, run⟩ := BinaryRegisterStructured.exec slot decrementCommands base
    (running n (r + 1)) (decrement_ready n r) ambient
  rw [decrement_result] at run
  rw [decrement_budget] at ht
  have hreset : reset.eval ((guard slot).eval
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n (r + 1))⟩) =
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n (r + 1))⟩ := by
    rfl
  have houtput : registerTapes slot base (running n r) output = base output :=
    registerTapes_other slot base _ output (by simpa only [not_exists] using outside)
  have hpushed : (.push output (fun _ : State A => true) .done : Action K (State A)).eval
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n r)⟩ =
      ⟨BinaryAddMachine.clean ambient,
        registerTapes slot (Function.update base output (true :: base output)) (running n r)⟩ := by
    simp only [Action.eval, houtput, registerTapes_update_external slot output outside]
  refine ⟨1 + (t + 1), by omega, ?_⟩
  apply Exec.seq (Exec.atom reset _)
  rw [hreset]
  exact Exec.seq run (by
    simpa only [hpushed] using
      (Exec.atom (.push output (fun _ : State A => true) .done)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n r)⟩))

theorem loop_exec (slot : (Reg ⊕ Fin 6) ↪ K) (output : K)
    (outside : ∀ q, slot q ≠ output) (base : K → List Bool)
    (n r width : Nat) (bounded : r.size ≤ width) (ambient : A) :
    ∃ steps ≤ r * (9 * width + 20) + 1,
      Exec (loop slot output)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n r)⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot (Function.update base output (List.replicate r true ++ base output))
            (running n 0)⟩ := by
  revert bounded
  induction r generalizing base with
  | zero =>
      intro _
      refine ⟨1, by simp, ?_⟩
      have h : more ((guard slot).eval
          ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n 0)⟩).state =
          false := by rw [guard_zero]; rfl
      simpa only [loop, guard_zero, List.replicate_zero, List.nil_append,
        Function.update_eq_self] using (Exec.loop_false (a := body slot output) h)
  | succ r ih =>
      intro bounded
      have hsmall := (Nat.size_le_size (Nat.le_succ r)).trans bounded
      obtain ⟨b, hb, bodyRun⟩ := body_exec slot output outside base n r ambient
      obtain ⟨t, ht, tailRun⟩ := ih (Function.update base output (true :: base output)) hsmall
      have hfinal : Function.update (Function.update base output (true :: base output)) output
          (List.replicate r true ++
            Function.update base output (true :: base output) output) =
          Function.update base output (List.replicate (r + 1) true ++ base output) := by
        simp only [Function.update_self, Function.update_idem, replicate_append_true]
      rw [hfinal] at tailRun
      refine ⟨b + t + 1, ?_, ?_⟩
      · have hs := Nat.size_le_size (Nat.le_succ r)
        nlinarith
      · exact Exec.loop_true (guard_more slot base n r ambient) bodyRun tailRun

theorem exec (slot : (Reg ⊕ Fin 6) ↪ K) (output : K)
    (outside : ∀ q, slot q ≠ output) (base : K → List Bool)
    (n : Nat) (ambient : A) :
    ∃ steps ≤ runtimeBound n,
      Exec (code slot output)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (initial n)⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot (Function.update base output (List.replicate n true ++ base output))
            (initial n)⟩ := by
  obtain ⟨p, hp, prepareRun⟩ := BinaryRegisterStructured.exec slot prepareCommands base
    (initial n) (prepare_ready n) ambient
  rw [prepare_result] at prepareRun
  rw [prepare_budget] at hp
  obtain ⟨l, hl, loopRun⟩ := loop_exec slot output outside base n n n.size le_rfl ambient
  obtain ⟨f, hf, finishRun⟩ := BinaryRegisterStructured.exec slot finishCommands
    (Function.update base output (List.replicate n true ++ base output))
    (running n 0) (finish_ready n) ambient
  rw [finish_result] at finishRun
  rw [finish_budget] at hf
  refine ⟨p + (l + f), ?_, Exec.seq prepareRun (Exec.seq loopRun finishRun)⟩
  have hlinear : p + (l + f) ≤ 2 * n.size + n * (9 * n.size + 20) + 8 := by omega
  have hfactor : 2 * n.size + n * (9 * n.size + 20) + 8 ≤
      (n + 1) * (9 * n.size + 20) := by nlinarith
  have hcoefficient : 9 * n.size + 20 ≤ 40 * (n.size + 1) ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul_left (n + 1) hcoefficient
  apply (hlinear.trans hfactor).trans
  simpa only [runtimeBound, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using hmul

theorem exec_from_tapes (slot : (Reg ⊕ Fin 6) ↪ K) (output : K)
    (outside : ∀ q, slot q ≠ output) (base : K → List Bool) (n : Nat)
    (registers : ∀ r, base (slot (.inl r)) = (initial n r).bits)
    (scratch : ∀ j, base (slot (.inr j)) = []) (ambient : A) :
    ∃ steps ≤ runtimeBound n,
      Exec (code slot output) ⟨BinaryAddMachine.clean ambient, base⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          Function.update base output (List.replicate n true ++ base output)⟩ := by
  have hframe : registerTapes slot base (initial n) = base := by
    funext k
    by_cases hk : ∃ q, slot q = k
    · obtain ⟨q, rfl⟩ := hk
      cases q with
      | inl r => simpa only [registerTapes_reg] using (registers r).symm
      | inr j => simpa only [registerTapes_scratch] using (scratch j).symm
    · exact registerTapes_other slot base _ k hk
  obtain ⟨t, ht, run⟩ := exec slot output outside base n ambient
  rw [← registerTapes_update_external slot output outside, hframe] at run
  exact ⟨t, ht, run⟩

end BinPackingGap.BinaryToTallyMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingCountedProgram
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.GraphFieldMachine

open Turing
open BinaryEncoding
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction
open GraphTallyMachine (Mode Slot afterName initial transition)

variable {K Λ σ : Type} [DecidableEq K]

theorem extractTrace (field : Field) (slots : Fin 4 ↪ K) (labels : Label → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = instruction field slots labels exit label)
    (base : K → List Bool) (input : GraphReductionInput)
    (sourceWord : base (slots 0) = graphBits input)
    (scratchEmpty : base (slots 1) = []) (temporaryEmpty : base (slots 2) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[steps field input]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨exit, clean ambient, resultTapes field slots base input⟩ := by
  have hd (i j : Fin 4) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  let middle := Function.update base (slots 2) (fieldBits field input).reverse
  have first : (MachineComposition.advance (TM2.step program))^[3 * (graphBits input).length + 2]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨some (labels .transfer), clean ambient, middle⟩ := by
    have run := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 1) (slots 2)
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 1 2 (by decide))
      initial transition (emit field) (labels .scan) (labels .restore)
      (fun mode bit => labels (.emitter mode bit)) (some (labels .transfer))
      program (atLabels .scan) (fun mode bit => atLabels (.emitter mode bit))
      (atLabels .restore) base scratchEmpty ambient initial none
    have hout : MachineTransducer.output transition (emit field) initial (base (slots 0)) =
        fieldBits field input := by
      change scanOutput field initial (base (slots 0)) = _
      rw [sourceWord, output_graphBits]
    rw [hout] at run
    simpa only [sourceWord, temporaryEmpty, List.append_nil, clean, middle] using run
  have middleSource : middle (slots 2) = (fieldBits field input).reverse := by simp [middle]
  have middleDestination : middle (slots 3) = base (slots 3) := by
    simp [middle, hd 3 2 (by decide)]
  have finalTapes : MachineTransfer.tapesAt (slots 2) (slots 3) middle []
      (fieldBits field input ++ base (slots 3)) = resultTapes field slots base input := by
    funext k
    by_cases ht : k = slots 2
    · subst k
      simp [MachineTransfer.tapesAt, resultTapes, temporaryEmpty, hd 2 3 (by decide)]
    · by_cases ho : k = slots 3
      · subst k
        simp [MachineTransfer.tapesAt, resultTapes]
      · simp [MachineTransfer.tapesAt, resultTapes, middle, ht, ho]
  have second : (MachineComposition.advance (TM2.step program))^[(fieldBits field input).length + 1]
      (some ⟨some (labels .transfer), clean ambient, middle⟩) =
      some ⟨exit, clean ambient, resultTapes field slots base input⟩ := by
    have run := MachineTransfer.transferAt_fromTapes
      (Γ := MachineTransducerCopy.Alphabet K) (σ := σ × Mode) (slots 2) (slots 3)
      (hd 2 3 (by decide)) id false (labels .transfer) exit program
      (by simpa only [instruction] using atLabels .transfer) middle (ambient, initial) none
    have next_eq : MachineTransfer.nextAt (slots 3) program =
        MachineComposition.advance (TM2.step program) := by
      funext configuration
      rfl
    rw [next_eq, middleSource, middleDestination] at run
    simpa only [List.length_reverse, List.reverse_reverse, List.map_id,
      finalTapes, clean] using run
  rw [steps, Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGap.GraphFieldMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_PackingRegisterUpdate
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.PackingRegisterUpdate

open Turing
open BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram
open FiniteTapeProgram PackingMachineBlocks

def operands : Operands (Fin 3) where
  destination := 2
  left := 0
  right := 1
  left_ne_right := by decide
  left_ne_destination := by decide
  right_ne_destination := by decide

def operator : Kind → Command (Fin 3)
  | .add => .add operands
  | .multiply => .mul operands

def commands (kind : Kind) : List (Command (Fin 3)) :=
  [operator kind, .clear 1, .copy 1 2 (by decide), .clear 2]

def main (kind : Kind) : BinaryRegisterProgram.Label (commands kind) :=
  .inl (BinaryRegisterProgram.main (operator kind))

variable {K : Type} [DecidableEq K]

def code (slots : (Fin 3 ⊕ Fin 6) ↪ K) (kind : Kind) : Code (K := K) (S := State) :=
  invoke arithmeticControl (BinaryAddMachine.clean ()) (main kind)
    (BinaryRegisterProgram.program slots (commands kind))

end BinPackingGap.PackingRegisterUpdate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PairExpressionCompiler
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PairExpressionCompiler

open NatExpressionCompiler BinaryRegisterProgram

variable {α : Type} [DecidableEq α]

def numCommands (num den : Expr α) : List (Command (Reg num den)) :=
  compileInto (input num den) num (numNodes num den) (by intros; simp [input, numNodes])

def denCommands (num den : Expr α) : List (Command (Reg num den)) :=
  compileInto (input num den) den (denNodes num den) (by intros; simp [input, denNodes])

def commands (num den : Expr α) := numCommands num den ++ denCommands num den

def clearList {Reg : Type} (registers : List Reg) : List (Command Reg) := registers.map Command.clear

theorem clearList_ready {Reg : Type} [DecidableEq Reg] (registers : List Reg) (values : Reg → Nat) :
    Ready (clearList registers) values := by
  induction registers generalizing values with
  | nil => trivial
  | cons r tail ih => exact ⟨True.intro, ih _⟩

def clearCommands (num den : Expr α) := clearList (temporaryList num den)

theorem clear_ready (num den : Expr α) (values : Reg num den → Nat) :
    Ready (clearCommands num den) values := clearList_ready _ _

end BinPackingGap.PairExpressionCompiler

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_ResetExpressionCompiler
attribute [-instance] _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.ResetExpressionCompiler

open NatExpressionCompiler BinaryRegisterProgram PairExpressionCompiler

variable {α Reg : Type} [DecidableEq Reg]

def commands (inputs : α → Reg) (expression : Expr α)
    (nodes : Node expression ↪ Reg) (apart : ∀ a n, inputs a ≠ nodes n)
    (output : Reg) (outputApart : ∀ n, output ≠ nodes n) : List (Command Reg) :=
  .clear output :: (compileInto inputs expression nodes apart ++
    (.copy output (nodes (root expression)) (outputApart _) ::
      clearList (nodeList expression nodes)))

end BinPackingGap.ResetExpressionCompiler

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineExpanderFamilyAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  cases tape <;> exact inferInstanceAs (Fintype Bool)

end BinPackingGames.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularOwnerProgram
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

instance tapeFintype : Fintype Tape := by
  change Fintype
    ((Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕
      (((MachineExpanderRow.Tape ⊕ MachineExpanderTable.ExtraTape) ⊕
        MachineExpanderFamily.ExtraTape) ⊕ MachineCeilingPower.Tape))) ⊕ Fin 2)
  infer_instance

end BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup

namespace BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

instance instFintypeTape : Fintype Tape := MachineRegularOwnerCleanup.tapeFintype

end BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ClashMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate

open StatementCircuit WitnessCircuit WitnessEncoding PostfixModel PostfixAlignment CircuitBatch

theorem nonemptyTokens_eq (q : Nat) :
    nonemptyTokens q = exprTokens Fin.val (nonemptyExpr q) := by
  rw [nonemptyExpr, exprTokens_disjoin, forestTokens_ofFn]
  simp [nonemptyTokens, forTokens_eq_ofFn, selectorExpr, exprTokens]

theorem clashRowTokens_eq (q : Nat) (i : Fin (q + 1)) :
    clashRowTokens q i.val =
      exprTokens Fin.val (Expr.disjoin (List.ofFn (clashPairExpr q i))) := by
  rw [exprTokens_disjoin, forestTokens_ofFn]
  simp only [clashRowTokens, forTokens_eq_ofFn, List.length_ofFn]
  apply congrArg (fun xs : List (List Token) => xs.flatten ++ closeOr (q + 1))
  apply congrArg List.ofFn
  funext j
  exact clashPairTokens_eq q i j

theorem clashTokens_eq (q : Nat) :
    clashTokens q = exprTokens Fin.val (clashExpr q) := by
  rw [clashExpr, exprTokens_disjoin, forestTokens_ofFn]
  simp only [clashTokens, forTokens_eq_ofFn, List.length_ofFn]
  apply congrArg (fun xs : List (List Token) => xs.flatten ++ closeOr (q + 1))
  apply congrArg List.ofFn
  funext i
  exact clashRowTokens_eq q i

theorem validityTokens_eq (q : Nat) :
    validityTokens q = exprTokens Fin.val (validityExpr q) := by
  simp [validityTokens, validityExpr, exprTokens, nonemptyTokens_eq,
    clashTokens_eq, List.append_assoc]

theorem presenceTokens_eq (q n : Nat) :
    presenceTokens q n = exprTokens Fin.val (presenceExpr q n) := by
  rw [presenceExpr, exprTokens_disjoin, forestTokens_ofFn]
  simp [presenceTokens, forTokens_eq_ofFn, selectorExpr, exprTokens]

section Symbols

variable {A : Type*} [DecidableEq A]

theorem inputCellTokens_eq (q : Nat) (input : List Bool) (f : Bool → A) (n : Nat) (a : Option A) :
    inputCellTokens q input f n a = exprTokens Fin.val (inputCellExpr q input f n a) := by
  by_cases hp : n < (inputPrefix input).length
  · simp only [inputCellTokens, inputCellExpr, ite_eq_left hp, exprTokens]
  · by_cases hq : n - (inputPrefix input).length < q
    · simp only [inputCellTokens, inputCellExpr, hp, ite_false, hq, ite_true, if_true, dite_eq_left]
      rw [exprTokens_mux, ← presenceTokens_eq, ← payloadSymbolTokens_eq]
      rfl
    · simp only [inputCellTokens, inputCellExpr, ite_eq_right hp, ite_eq_right hq,
        dite_eq_right hq, exprTokens]

end Symbols

section Initial

variable (V : NPVerifier)
variable [DecidableEq V.computation.tm.Λ] [DecidableEq V.computation.tm.σ]
variable [∀ k, DecidableEq (V.computation.tm.Γ k)]

omit [DecidableEq V.computation.tm.Λ] [DecidableEq V.computation.tm.σ] in
theorem initialCellTokens_eq (input : List Bool) (S : Nat) (k : V.computation.tm.K)
    (i : Fin S) (a : Option (V.computation.tm.Γ k)) :
    initialCellTokens V input S k i a = exprTokens Fin.val (initialCellExpr V input S k i a) := by
  by_cases hk : k = V.computation.tm.k₀
  · subst k
    simpa [initialCellTokens, initialCellExpr] using
      inputCellTokens_eq (V.witnessBound.eval input.length) input
        V.computation.inputAlphabet.invFun i.val a
  · simp [initialCellTokens, initialCellExpr, hk, exprTokens]

def initTokens (input : List Bool) (S : Nat) :
    ConfigBit V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ S → List Token
  | .inl label => [.const (decide (some V.computation.tm.main = label))]
  | .inr (.inl state) => [.const (decide (V.computation.tm.initialState = state))]
  | .inr (.inr ⟨k, i, a⟩) => initialCellTokens V input S k i a

theorem initTokens_eq (input : List Bool) (S : Nat)
    (bit : ConfigBit V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ S) :
    initTokens V input S bit = exprTokens Fin.val (initExpr V input S bit) := by
  rcases bit with label | (state | ⟨k, i, a⟩)
  · rfl
  · rfl
  · exact initialCellTokens_eq V input S k i a

end Initial

noncomputable section Frame

open VerifierCircuit

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.labelDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.stateDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.alphabetDecidable
def configurationBody (V : NPVerifier) (input : List Bool) (j : Nat) : List Token :=
  if hj : j < width V input then
    initTokens V input (capacity V input.length) ((bitEquiv V input).symm ⟨j, hj⟩)
  else []

def initializationTokens (V : NPVerifier) (input : List Bool) : List Token :=
  forTokens (width V input) (configurationBody V input) ++
    validityTokens (V.witnessBound.eval input.length)

theorem initializationTokens_eq (V : NPVerifier) (input : List Bool) :
    initializationTokens V input =
      forestTokens Fin.val (List.ofFn (initialExpressions V input)) := by
  rw [forestTokens_ofFn, List.ofFn_succ']
  simp only [List.concat_eq_append, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  simp only [initialExpressions, Fin.lastCases_castSucc, Fin.lastCases_last]
  simp only [initializationTokens, forTokens_eq_ofFn, configurationBody, Fin.isLt, dite_eq_left]
  rw [validityTokens_eq]
  apply congrArg (fun xs : List (List Token) => xs.flatten ++
    exprTokens Fin.val (validityExpr (V.witnessBound.eval input.length)))
  apply congrArg List.ofFn
  funext i
  exact initTokens_eq V input (capacity V input.length) ((bitEquiv V input).symm i)

end Frame

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted emitted_append emitted_other emitted_nil)

variable {K Λ σ : Type} [DecidableEq K]

namespace SelectorLoop

theorem tokens_succ (count start : Nat) :
    tokens (count + 1) start = [.input start] ++ tokens count (start + 1) := by
  rw [tokens, forTokens_succ_first]
  simp only [Nat.add_zero]
  apply congrArg (List.append [Token.input start])
  apply forTokens_congr
  intro j _
  rw [show start + (j + 1) = start + 1 + j by omega]

end SelectorLoop

namespace Nonempty

def statement (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .initialize_ => .push (slots 2) (fun _ => false) (.goto fun _ => labels (.remaining .seed))
  | .remaining l => copyStatement (slots 0) (slots 3) (slots 1)
      (fun l => labels (.remaining l)) (some (labels (.closure .seed))) l
  | .closure l => copyStatement (slots 0) (slots 3) (slots 4)
      (fun l => labels (.closure l)) (some (labels (.selector .guard))) l
  | .selector l => SelectorLoop.statement (loopMap.trans slots)
      (fun l => labels (.selector l)) (labels .orSeed) l
  | .orSeed => OrClosure.seed (closurePorts slots) (labels .orLoop)
  | .orLoop => OrClosure.loop (closurePorts slots) (labels .orLoop) (some (labels .cleanup))
  | .cleanup => .pop (slots 1) (fun s _ => s)
      (.pop (slots 4) (fun s _ => s) (.goto fun _ => labels .drain))
  | .drain => MachineDrain.drain (slots 2) (labels .drain) exit

end Nonempty

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PaddingCellsMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl

open Turing PostfixModel VerifierCircuit InitializationTemplate
open Reduction.MachineSubstitution

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqΛTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqσTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqΓTmBoolComputation
theorem configurationTokens_eq (V : NPVerifier) (input : List Bool) :
    (TransitionTemplate.outputOrder (indexing V) (capacity V input.length)).flatMap
      (initTokens V input (capacity V input.length)) =
      forTokens (width V input) (configurationBody V input) := by
  simp only [TransitionTemplate.outputOrder, List.flatMap_def,
    ← List.ofFn_eq_map, List.map_ofFn, Function.comp_def,
    forTokens_eq_ofFn, configurationBody, Fin.isLt, dite_eq_left]
  rfl

theorem initializationTokens_eq_blocks (V : NPVerifier) (input : List Bool) :
    initializationTokens V input = tokens V ++ cells V input (capacity V input.length) ++
      validityTokens (V.witnessBound.eval input.length) := by
  rw [initializationTokens, ← configurationTokens_eq, OutputOrder.outputOrder_eq_blocks]
  simp [tokens, cells,
    initTokens, List.flatMap_def, List.map_map, Function.comp_def, List.append_assoc,
    flatten_singletons, List.flatten_flatten]

variable {K Λ σ : Type} [DecidableEq K]

theorem literalTrace (p : Ports K) (ts : List Token) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (code : program entry = literalStatement p ts exit)
    (base : K → List Bool) (state : σ) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some entry, state, base⟩) =
      some ⟨exit, state, emitted p base ts⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some, TM2.step, code]
  rw [literalStep]

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionArena
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

open StatementCircuit CircuitBatch PostfixModel PostfixAlignment

variable {inputs oldWidth newWidth width : Nat}

theorem step_repeat (f : Frame inputs width)
    (es : Fin width → Expr (Fin width)) (n : Nat) :
    (f.step es).repeat es n = f.repeat es (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Frame.repeat, ih]

theorem finalFrame_circuit (V : NPVerifier) (input : List Bool) :
    (finalFrame V input).toCircuit 0 = VerifierCircuit.circuitOfVerifier V input := rfl

theorem transition_cost_le_budget (V : NPVerifier) (input : List Bool)
    (hT : 0 < V.horizon input.length) :
    Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input)) ≤
      (budgetPolynomial V).eval input.length := by
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  rw [VerifierCircuit.circuitOfVerifier_gate_count] at hg
  have hb := budgetPolynomial_eval V input
  have hm := Nat.mul_le_mul_right
    (Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input)))
    (show 1 ≤ V.horizon input.length by omega)
  omega

section GenericTransition

variable {K Λ σ : Type} {Γ : K → Type}
  [DecidableEq K] [DecidableEq Λ] [DecidableEq σ]
  [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]

def stepExpressions (indexing : ConfigIndex.Indexing Γ Λ σ)
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (S : Nat) :
    Fin (indexing.width S + 1) → Expr (Fin (indexing.width S + 1)) :=
  Fin.lastCases (.input (Fin.last (indexing.width S)))
    (fun j => (MachineCircuit.stickyExpr S program
      ((indexing.configIndexEquiv S).symm j)).rename
        (fun b => (indexing.configIndexEquiv S b).castSucc))

def transitionTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (S : Nat) (roots : List Nat) : List Token :=
  TransitionTemplate.forestTokens indexing roots S program ++
    [.input (TransitionTemplate.rootLookup roots (indexing.width S))]

theorem transitionTokens_eq (indexing : ConfigIndex.Indexing Γ Λ σ)
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (S : Nat) (roots : List Nat) :
    transitionTokens indexing program S roots =
      forestTokens (fun i => roots[i.val]?.getD 0)
        (List.ofFn (stepExpressions indexing program S)) := by
  rw [List.ofFn_succ']
  simp only [stepExpressions, Fin.lastCases_castSucc, Fin.lastCases_last,
    List.concat_eq_append, forestTokens, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, exprTokens, List.append_nil]
  unfold transitionTokens
  rw [TransitionTemplate.forestTokens_eq]
  congr 1
  simp only [TransitionTemplate.outputOrder, List.map_map, List.ofFn_eq_map,
    forestTokens, List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  rw [exprTokens_rename]
  rfl

end GenericTransition

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.alphabetFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.labelFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.stateFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.labelDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.stateDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.alphabetDecidable
theorem stepExpressions_verifier (V : NPVerifier) (input : List Bool) :
    stepExpressions (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) =
      VerifierCircuit.stepExpressions V input := rfl

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

end

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionArena

open Turing MachineComposition

theorem tapes_countdown_tail (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) :
    Function.update (tapes base S (remaining + 1) snapshot) (.inr .countdown)
      (tapes base S (remaining + 1) snapshot (.inr .countdown)).tail =
        tapes base S remaining snapshot := by
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;> simp [tapes]
    | tokens => simp [tapes]
    | records => simp [tapes]
    | rootTable => simp [tapes]
  | inr tape => cases tape <;> simp [tapes, encodeWord, List.replicate_succ]

def preparedTapes (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) (tokens : List PostfixModel.Token) : Tape → List Bool :=
  Function.update
    (Function.update (tapes base S remaining snapshot) (.inl .tokens)
      (PostfixModel.tokenBits tokens).reverse)
    (.inl (.lower .remaining)) (encodeWord tokens.length)

theorem place_emitTapes (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) (tokens : List PostfixModel.Token) :
    ForestPlacement.fill termPorts (tapes base S remaining snapshot)
      (TermMachine.emitTapes (fun tape => tapes base S remaining snapshot (termPorts tape)) tokens) =
      preparedTapes base S remaining snapshot tokens := by
  simp only [TermMachine.emitTapes, ForestPlacement.fill_update, ForestPlacement.fill_self]
  simp [termTape, tapes, preparedTapes, encodeWord]

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionArena

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

abbrev OutputAssignment (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) :=
  Fin (VerifierToCNF.outputVariables (verifier G vertices edges)) → Bool

def extractLabeling (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) (assignment : OutputAssignment G vertices edges) : V → Label :=
  labelsOfBits vertices (VerifierToCNF.restrictAssignment (verifier G vertices edges) assignment)

end BinPackingGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierFront
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InputFrame

open Turing MachineComposition
open BinPackingGames.Reduction.MachineTransfer

theorem restoreTrace (input : List Bool) (n : Nat) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 2) [] input.reverse (encodeWord n))) =
        some (cfg (some 3) input [] (encodeWord n)) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 1 0 (by decide)
    id false 2 (some 3) program (by simp [program])
    (tapes [] input.reverse (encodeWord n)) () none
  have ht : tapesAt 1 0 (tapes [] input.reverse (encodeWord n)) [] input =
      tapes input [] (encodeWord n) := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 0 program)^[input.length + 1]
    (some (cfg (some 2) [] input.reverse (encodeWord n))) = _
  simpa only [tapes_one, tapes_zero, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, List.append_nil, ht, nextAt, advance, cfg] using! h

theorem reverseCounterTrace (input : List Bool) (n : Nat) :
    (advance machine.step)^[n + 2]
      (some (cfg (some 3) input [] (encodeWord n))) =
        some (cfg (some 4) input (encodeWord n).reverse []) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 2 1 (by decide)
    id false 3 (some 4) program (by simp [program])
    (tapes input [] (encodeWord n)) () none
  have ht : tapesAt 2 1 (tapes input [] (encodeWord n)) [] (encodeWord n).reverse =
      tapes input (encodeWord n).reverse [] := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 1 program)^[n + 2]
    (some (cfg (some 3) input [] (encodeWord n))) = _
  simpa only [tapes_two, tapes_one, List.map_id_fun, id_eq, List.append_nil,
    encodeWord_length, Nat.add_assoc, ht, nextAt, advance, cfg] using! h

theorem prependTrace (input : List Bool) (n : Nat) :
    (advance machine.step)^[n + 2]
      (some (cfg (some 4) input (encodeWord n).reverse [])) =
        some (cfg none (encodeWord n ++ input) [] []) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 1 0 (by decide)
    id false 4 none program (by simp [program])
    (tapes input (encodeWord n).reverse []) () none
  have ht : tapesAt 1 0 (tapes input (encodeWord n).reverse []) [] (encodeWord n ++ input) =
      tapes (encodeWord n ++ input) [] [] := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 0 program)^[n + 2]
    (some (cfg (some 4) input (encodeWord n).reverse [])) = _
  simpa only [tapes_one, tapes_zero, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, encodeWord_length, Nat.add_assoc, ht, nextAt, advance, cfg] using! h

theorem frameTrace (input : List Bool) :
    (advance machine.step)^[4 * input.length + 7]
      (some (initList machine input)) =
        some (haltList machine (encodeWord input.length ++ input)) := by
  have join :
      (advance machine.step)^[input.length + 2]
        ((advance machine.step)^[input.length + 2]
          ((advance machine.step)^[input.length + 1]
            ((advance machine.step)^[input.length + 1]
              ((advance machine.step)^[1] (some (initList machine input)))))) =
        (advance machine.step)^[4 * input.length + 7]
          (some (initList machine input)) := by
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
      ← Function.iterate_add_apply, ← Function.iterate_add_apply]
    congr 1
    omega
  rw [← join]
  simp only [Function.iterate_one, advance_some]
  rw [startStep, scanTrace]
  simp only [List.append_nil]
  change (advance machine.step)^[input.length + 2]
    ((advance machine.step)^[input.length + 2]
      ((advance machine.step)^[input.length + 1]
        (some (cfg (some 2) [] input.reverse (encodeWord input.length))))) = _
  rw [restoreTrace, reverseCounterTrace, prependTrace, stopped_eq_haltList]

end BinPackingGames.Foundations.Complexity.CookLevin.InputFrame

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ProducerFrontStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem seedTrace (p : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : program (labels .seed) = statement p labels exit .seed)
    (base : K → List Bool) (ambient : σ) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .seed), (ambient, none), copied p base⟩) =
      some ⟨exit, (ambient, none), prepared p base⟩ := by
  change some (TM2.stepAux (program (labels .seed)) _ _) = _
  rw [code]
  cases exit <;>
    simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt, prepared,
      p.injective.eq_iff]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingAssignments

open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks

variable {Reg K : Type} [DecidableEq Reg] [DecidableEq K]

def code (slot : (Reg ⊕ Fin 6) ↪ K) (commands : List (Command Reg)) :
    Code (K := K) (S := State) :=
  PackingArithmeticProgram.code (BinaryRegisterStructured.code slot commands)

def copyCommands (destination source : Reg) (different : destination ≠ source) :
    List (Command Reg) := [.clear destination, .copy destination source different]

def copy (slot : (Reg ⊕ Fin 6) ↪ K) (destination source : Reg)
    (different : destination ≠ source) : Code (K := K) (S := State) :=
  code slot (copyCommands destination source different)

def constantCommands (destination : Reg) (constant : Nat) : List (Command Reg) :=
  [.clear destination, .constant destination constant]

def setConstant (slot : (Reg ⊕ Fin 6) ↪ K) (destination : Reg) (constant : Nat) :
    Code (K := K) (S := State) := code slot (constantCommands destination constant)

end BinPackingGap.PackingAssignments

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingVertexUpdate
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingLayoutCommands

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open PackingMachineLayout

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra]

def inputFromOther (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (source : Other) :
    Code (K := Tape num den Other Extra) (S := State) :=
  PackingAssignments.copy (registers num den) (inputs num den destination)
    (others num den source) (input_ne_other num den destination source)

def setInput (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (constant : Nat) :
    Code (K := Tape num den Other Extra) (S := State) :=
  PackingAssignments.setConstant (registers num den) (inputs num den destination) constant

def setInputTime (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (constant : Nat) : Polynomial Nat :=
  runtimePolynomial (PackingAssignments.constantCommands
    (inputs (Other := Other) num den destination) constant) + 2

def setOther (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Other) (constant : Nat) :
    Code (K := Tape num den Other Extra) (S := State) :=
  PackingAssignments.setConstant (registers num den) (others num den destination) constant

end BinPackingGap.PackingLayoutCommands

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingJobLoop
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingItemBlockMachine

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler
open PairExpressionCompiler

variable {α K A : Type} [DecidableEq α] [DecidableEq K]

def code (num den : Expr α) (slot : (Reg num den ⊕ Fin 6) ↪ K) (output : K) :
    Code (K := K) (S := BinaryAddMachine.State A) :=
  .seq (BinaryRegisterStructured.code slot (commands num den))
    (.seq (.atom (.push output (fun _ => true) .done))
      (.seq (RegisterFrameEmission.code (slot (.inl (numRoot num den))) output)
        (.seq (RegisterFrameEmission.code (slot (.inl (denRoot num den))) output)
          (BinaryRegisterStructured.code slot (clearCommands num den)))))

def widthPolynomial (num den : Expr α) : Polynomial Nat :=
  Polynomial.C (2 ^ (commands num den).length) *
    (Polynomial.X + Polynomial.C (maxConstantSize (commands num den) + 1))

omit [DecidableEq α] in
theorem widthPolynomial_eval (num den : Expr α) (width : Nat) :
    (widthPolynomial num den).eval width = staticWidth (commands num den) width := by
  simp only [widthPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, staticWidth, Nat.add_assoc]

def timePolynomial (num den : Expr α) : Polynomial Nat :=
  runtimePolynomial (commands num den) +
    (runtimePolynomial (clearCommands num den)).comp (widthPolynomial num den) +
    2 * widthPolynomial num den + 5

omit [DecidableEq α] in
theorem timePolynomial_eval (num den : Expr α) (width : Nat) :
    (timePolynomial num den).eval width =
      (runtimePolynomial (commands num den)).eval width +
        (runtimePolynomial (clearCommands num den)).eval (staticWidth (commands num den) width) +
        2 * staticWidth (commands num den) width + 5 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_comp, widthPolynomial_eval]

end BinPackingGap.PackingItemBlockMachine

namespace BinPackingGap.PackingChunkMachine

open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler
open PairExpressionCompiler
open PackingItemBlockMachine (outputTapes)

variable {α δ K A : Type} [DecidableEq α] [DecidableEq K]

def code (numerator : δ → Expr α) (denominator : Expr α)
    (slot : (d : δ) → (Reg (numerator d) denominator ⊕ Fin 6) ↪ K) (output : K) :
    List δ → Code (K := K) (S := BinaryAddMachine.State A)
  | [] => .atom .done
  | [d] => PackingItemBlockMachine.code (numerator d) denominator (slot d) output
  | d :: e :: rest =>
      .seq (PackingItemBlockMachine.code (numerator d) denominator (slot d) output)
        (code numerator denominator slot output (e :: rest))

def timePolynomial (numerator : δ → Expr α) (denominator : Expr α) :
    List δ → Polynomial Nat
  | [] => 1
  | [d] => PackingItemBlockMachine.timePolynomial (numerator d) denominator
  | d :: e :: rest => PackingItemBlockMachine.timePolynomial (numerator d) denominator +
      timePolynomial numerator denominator (e :: rest)

end BinPackingGap.PackingChunkMachine

namespace BinPackingGap.PackingDescriptorExpression

open NatExpressionCompiler PackingInventoryDescriptors

def rawRecords (items : RawInstance) : List Bool := items.flatMap rawRecord

end BinPackingGap.PackingDescriptorExpression

namespace BinPackingGap.PackingJobBody

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

def body (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power repetition : α) (leftPower rightPower one temp : Other)
    (different : one ≠ temp) (output : Extra) :
    Code (K := Tape num den Other Extra) (S := State) :=
  .seq (PackingLayoutCommands.inputFromOther num den power leftPower)
    (.seq (PackingArithmeticProgram.code
      (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors))
      (.seq (PackingLayoutCommands.inputFromOther num den power rightPower)
        (.seq (PackingArithmeticProgram.code
          (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors))
          (PackingRegisterUpdate.code
            (PackingVertexUpdate.updateSlots num den repetition one temp different) .add))))

end BinPackingGap.PackingJobBody

namespace BinPackingGap.PackingJobLoop

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)
open PackingJobBody (nextInput pairRecords )

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

def code (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (labelPower repetitionOne : α) (_distinctInput : labelPower ≠ repetitionOne)
    (leftPower rightPower one temp : Other) (otherDistinct : one ≠ temp)
    (output counter : Extra) :
    Code (K := PackingMachineLayout.Tape num den Other Extra) (S := State) :=
  PackingCountedProgram.loop (.inr counter)
    (PackingJobBody.body num den descriptors labelPower repetitionOne
      leftPower rightPower one temp otherDistinct output)

end BinPackingGap.PackingJobLoop

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_PackingConstantPool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingConstantPool

open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler PairExpressionCompiler
open PackingMachineBlocks
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable {α δ K : Type} [DecidableEq α] [DecidableEq K]

def code (numerator : δ → Expr α) (denominator : Expr α)
    (slot : (d : δ) → (Reg (numerator d) denominator ⊕ Fin 6) ↪ K)
    (output counter : K) (descriptors : List δ) : Code (K := K) (S := State) :=
  PackingCountedProgram.loop counter
    (PackingArithmeticProgram.code
      (PackingChunkMachine.code numerator denominator slot output descriptors))

end BinPackingGap.PackingConstantPool

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingSetupGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingSetupMachine

section

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram
open PackingSetupExpression

def block (p : Parameters) (o : Output) : List (Command (Reg p)) :=
  ResetExpressionCompiler.commands (input p) (expression p o) (nodes p o)
    (by intros; simp [input, nodes]) (output p o) (by
      intro n equal
      change (Sum.inr (Sum.inl o) : Reg p) = Sum.inr (Sum.inr ⟨o, n⟩) at equal
      cases Sum.inr.inj equal)

def commandsFor (p : Parameters) (order : List Output) : List (Command (Reg p)) :=
  order.flatMap (block p)

def commands (p : Parameters) := commandsFor p outputOrder

variable {K A : Type} [DecidableEq K]

def code (p : Parameters) (slot : (Reg p ⊕ Fin 6) ↪ K) :
    Code (K := K) (S := BinaryAddMachine.State A) :=
  BinaryRegisterStructured.code slot (commands p)

end

open BinaryRegisterProgram FiniteTapeProgram PackingSetupExpression

end BinPackingGap.PackingSetupMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobList
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingStockBounds

open scoped BigOperators

variable (fixed : InventoryData) (K : Nat)

def setupCoefficient : Nat :=
  2 ^ (PackingSetupMachine.commands (GraphPackingRegisters.parameters fixed K)).length *
    (BinaryRegisterProgram.maxConstantSize
      (PackingSetupMachine.commands (GraphPackingRegisters.parameters fixed K)) + 2)

def widthCoefficient : Nat :=
  setupCoefficient fixed K + GraphPackingWidths.geometryCoefficient fixed K +
    (GraphPackingBounds.repetitionCoefficient fixed.P K + 3) +
    ((GraphPackingPreparation.geometryFactor fixed).size + 5)

def widthPolynomial : Polynomial Nat :=
  Polynomial.C (widthCoefficient fixed K) * (Polynomial.X + 1) ^ 2

@[simp] theorem widthPolynomial_eval (s : Nat) :
    (widthPolynomial fixed K).eval s = widthCoefficient fixed K * (s + 1) ^ 2 := by
  simp [widthPolynomial]

end BinPackingGap.GraphPackingStockBounds

namespace BinPackingGap.GraphPackingJobs

section

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open PackingDescriptorExpression PackingInventoryDescriptors

variable (fixed : InventoryData) (K : Nat)

def repeatInputs (x : GraphReductionInput) (edge : Nat) : Variable → Nat :=
  Function.update (inputs fixed K x edge) .repetitionOne 1

def edgeWord (x : GraphReductionInput) (e : x.graph.Edge) : List Bool :=
  rawRecords ((List.finRange (GraphPackingPreparation.repetitions fixed K x)).flatMap fun j =>
    (List.finRange 2).flatMap fun side =>
      (jobDescriptors fixed).map
        (rawOfDescriptor (inventory fixed K x) (some (x.graph.endpoint e side))
          e.val (j.val + 1)))

@[simp] theorem repeatInputs_repetition (x : GraphReductionInput) (edge : Nat) :
    repeatInputs fixed K x edge .repetitionOne = 1 := by
  simp [repeatInputs]

end

open BinaryEncoding PackingDescriptorExpression PackingInventoryDescriptors

def edgeFields (x : GraphReductionInput) (es : List x.graph.Edge) : List Bool :=
  listBits (fun e => natBits (x.graph.left e).val ++ natBits (x.graph.right e).val) es

def edgeWords (fixed : InventoryData) (K : Nat) (x : GraphReductionInput)
    (es : List x.graph.Edge) : List Bool :=
  es.flatMap (edgeWord fixed K x)

@[simp] theorem edgeFields_nil (x : GraphReductionInput) :
    edgeFields x [] = [false] := rfl

@[simp] theorem edgeWords_nil (fixed : InventoryData) (K : Nat)
    (x : GraphReductionInput) : edgeWords fixed K x [] = [] := rfl

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingPreparationFinish
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingEndpointPower

open BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks

variable {K : Type} [DecidableEq K]

def code (slots : (Fin 7 ⊕ Fin 6) ↪ K) (tally : K)
    (outside : ∀ q, slots q ≠ tally) : Code (K := K) (S := State) :=
  .seq (PackingArithmeticProgram.code
    (BinaryToTallyMachine.code (tallySlots slots) tally))
    (.seq (PackingArithmeticProgram.code
      (PackingPowerProgram.code (powerSlots slots tally outside)))
      (PackingRegisterUpdate.code (updateSlots slots) .multiply))

end BinPackingGap.PackingEndpointPower

namespace BinPackingGap.PackingVertexLoop

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

def body (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp) (output : Extra) :
    Code (K := VertexTape num den Other Extra) (S := State) :=
  .seq (PackingArithmeticProgram.code
    (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors))
    (PackingRegisterUpdate.code
      (PackingVertexUpdate.updateSlots num den power three temp different) .multiply)

def code (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp)
    (output counter : Extra) : Code (K := VertexTape num den Other Extra) (S := State) :=
  PackingCountedProgram.loop (.inr counter)
    (body num den descriptors power three temp different output)

end BinPackingGap.PackingVertexLoop

namespace BinPackingGap.GraphPackingProgram

section

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters

variable (fixed : InventoryData) (K : Nat)

abbrev Program := Code (K := Tape fixed K) (S := State)

def chain : List (Program fixed K) → Program fixed K
  | [] => .atom .done
  | c :: rest => .seq c (chain rest)

def regTape (r : Register fixed K) : Tape fixed K := slots fixed K (.inl r)

def otherSetup (o : PackingSetupExpression.Output) : Other fixed K :=
  .inl (PackingSetupMachine.output (parameters fixed K) o)

def tally (source : CountSource) (destination : Extra) : Program fixed K :=
  PackingArithmeticProgram.code
    (BinaryToTallyMachine.code (tallySlots fixed K source) (.inr destination))

def tallyToBinary (source : Extra) (destination : PackingSetupExpression.Input) :
    Program fixed K :=
  invoke arithmeticControl (BinaryAddMachine.clean ()) .scan
    (BinaryTallyMachine.instruction (.inr source) (regTape fixed K (input fixed K destination))
      (.inr .scanScratch) id none)

def power (source : CountSource) (destination : PackingItemExpression.Variable) :
    Program fixed K :=
  PackingArithmeticProgram.code (PackingPowerProgram.code (powerSlots fixed K source destination))

def setItem (destination : PackingItemExpression.Variable) (value : Nat) : Program fixed K :=
  PackingLayoutCommands.setInput (Numerator fixed) PackingItemExpression.denominator destination value

def setWork (destination : Work) (value : Nat) : Program fixed K :=
  PackingLayoutCommands.setOther (Numerator fixed) PackingItemExpression.denominator
    (.inr destination) value

def geometryOperands : Operands (Register fixed K) where
  destination := item fixed K .geometry
  left := work fixed K .geometryFactor
  right := item fixed K .totalPower
  left_ne_right := by
    change (Sum.inl (Sum.inr (Sum.inr Work.geometryFactor)) : Register fixed K) ≠
      Sum.inl (Sum.inl PackingItemExpression.Variable.totalPower)
    simp
  left_ne_destination := by
    change (Sum.inl (Sum.inr (Sum.inr Work.geometryFactor)) : Register fixed K) ≠
      Sum.inl (Sum.inl PackingItemExpression.Variable.geometry)
    simp
  right_ne_destination := by simp [item, PackingMachineLayout.inputs]

def geometry : Program fixed K :=
  chain fixed K [setWork fixed K .geometryFactor
      (160 * IntegerPackingArithmetic.widthRadix fixed.geometryBound ^ fixed.L),
    PackingAssignments.code (slots fixed K) [.mul (geometryOperands fixed K)]]

def header : Program fixed K :=
  chain fixed K [
    PackingAssignments.copy (slots fixed K) (work fixed K .header) (output fixed K .bins)
      (by simp [work, output, setup, PackingMachineLayout.others, PackingSetupMachine.output]),
    PackingArithmeticProgram.code
      (RegisterFrameEmission.code (regTape fixed K (work fixed K .header)) (.inr .reverseOutput))]

def prepare : Program fixed K :=
  chain fixed K [
    prepareGraph (graphSlots fixed K),
    tallyToBinary fixed K .vertices .n,
    tallyToBinary fixed K .edges .m,
    PackingArithmeticProgram.code (PackingFieldDecodeMachine.code (thresholdSlots fixed K)),
    PackingArithmeticProgram.code (PackingSetupMachine.code (parameters fixed K) (setupSlots fixed K)),
    tally fixed K (.input .n) .powerCounter,
    power fixed K (.output .three) .vertexPower,
    tally fixed K (.input .m) .powerCounter,
    power fixed K (.output .base) .totalPower,
    geometry fixed K,
    header fixed K]

def vertices : Program fixed K :=
  chain fixed K [setItem fixed K .labelPower 3,
    setItem fixed K .edgePower 1, setItem fixed K .repetitionOne 0,
    tally fixed K (.input .n) .vertexCounter,
    PackingVertexLoop.code (Numerator fixed) PackingItemExpression.denominator
      (PackingInventoryDescriptors.vertexDescriptors fixed) .labelPower
      (otherSetup fixed K .three) (.inr Work.temporary) (by simp [otherSetup])
      .reverseOutput .vertexCounter]

def endpoint (right : Bool) : Program fixed K :=
  chain fixed K [
    PackingArithmeticProgram.code (PackingFieldDecodeMachine.code (decoderSlots fixed K right)),
    PackingEndpointPower.code (endpointSlots fixed K right) (.inr .powerCounter)
      (endpoint_outside fixed K right .powerCounter)]

def incrementEdge : Program fixed K :=
  PackingRegisterUpdate.code
    (PackingVertexUpdate.updateSlots (Numerator fixed) PackingItemExpression.denominator .edgePower
      (otherSetup fixed K .base) (.inr Work.temporary) (by simp [otherSetup])) .multiply

def edgeBody : Program fixed K :=
  chain fixed K [
    .atom (.pop (.inr .endpoints) (fun state _ => state) .done),
    endpoint fixed K false,
    endpoint fixed K true,
    setItem fixed K .repetitionOne 1,
    tally fixed K (.output .repetitions) .repetitionCounter,
    PackingJobLoop.code (Numerator fixed) PackingItemExpression.denominator
      (PackingInventoryDescriptors.jobDescriptors fixed)
      .labelPower .repetitionOne (by decide)
      (.inr Work.leftPower) (.inr Work.rightPower)
      (otherSetup fixed K .one) (.inr Work.temporary) (by simp [otherSetup])
      .reverseOutput .repetitionCounter,
    incrementEdge fixed K,
    setWork fixed K .leftEndpoint 0,
    setWork fixed K .rightEndpoint 0,
    setWork fixed K .leftPower 0,
    setWork fixed K .rightPower 0,
    setItem fixed K .labelPower 0,
    setItem fixed K .repetitionOne 0]

def jobs : Program fixed K :=
  chain fixed K [setItem fixed K .edgePower 1,
    setItem fixed K .labelPower 0, setItem fixed K .repetitionOne 0,
    tally fixed K (.input .m) .edgeCounter,
    PackingCountedProgram.loop (.inr .edgeCounter) (edgeBody fixed K)]

def pool (stock : PackingSetupExpression.Output)
    (descriptor : PackingInventoryDescriptors.ItemDescriptor fixed) : Program fixed K :=
  chain fixed K [tally fixed K (.output stock) .poolCounter,
    PackingConstantPool.code (Numerator fixed) PackingItemExpression.denominator
      (PackingMachineLayout.itemSlots (Numerator fixed) PackingItemExpression.denominator)
      (.inr .reverseOutput) (.inr .poolCounter) [descriptor]]

def globalEdgeBody : Program fixed K :=
  chain fixed K [pool fixed K .edgeStock (.w, .globalEdge true),
    pool fixed K .edgeStock (.w, .globalEdge false), incrementEdge fixed K]

def globals : Program fixed K :=
  chain fixed K [setItem fixed K .labelPower 0,
    setItem fixed K .repetitionOne 0,
    setItem fixed K .edgePower 1,
    pool fixed K .upOne (.up, .globalUnit true),
    pool fixed K .upZero (.up, .globalUnit false),
    pool fixed K .umOne (.um, .globalUnit true),
    pool fixed K .umZero (.um, .globalUnit false),
    tally fixed K (.input .m) .edgeCounter,
    PackingCountedProgram.loop (.inr .edgeCounter) (globalEdgeBody fixed K)]

def flags : Program fixed K :=
  chain fixed K [setItem fixed K .edgePower 1,
    pool fixed K .treeFlags (.ft, .zero),
    pool fixed K .jobFlags (.fm, .zero), pool fixed K .jobFlags (.fg, .zero)]

def finish : Program fixed K :=
  chain fixed K [.atom (.push (.inr .reverseOutput) (fun _ => false) .done),
    PackingArithmeticProgram.code
      (.routine Unit inferInstance ()
        (fun _ => BinPackingGames.Reduction.MachineTransfer.loopAt
          (.inr Extra.reverseOutput) (.inr Extra.output) id false () none))]

def code : Program fixed K :=
  chain fixed K [prepare fixed K, vertices fixed K, jobs fixed K,
    globals fixed K, flags fixed K, finish fixed K]

end

open FiniteTapeProgram

variable {fixed : InventoryData} {K : Nat}

inductive PhaseRuns : List (Program fixed K) →
    Data (GraphPackingRegisters.Tape fixed K) PackingMachineBlocks.State → Nat →
    Data (GraphPackingRegisters.Tape fixed K) PackingMachineBlocks.State → Prop
  | nil (state) : PhaseRuns [] state 0 state
  | cons {head tail before middle after n m}
      (first : Exec head before n middle) (rest : PhaseRuns tail middle m after) :
      PhaseRuns (head :: tail) before (n + m) after

namespace PhaseRuns

theorem single {code : Program fixed K} {before after n}
    (run : Exec code before n after) : PhaseRuns [code] before n after := by
  simpa only [Nat.add_zero] using PhaseRuns.cons run (PhaseRuns.nil after)

theorem toExec {codes : List (Program fixed K)} {before after n}
    (runs : PhaseRuns codes before n after) :
    Exec (chain fixed K codes) before (n + 1) after := by
  induction runs with
  | nil state => exact Exec.atom .done state
  | cons first rest ih =>
      simpa only [chain, Nat.add_assoc] using Exec.seq first ih

end PhaseRuns

end BinPackingGap.GraphPackingProgram

namespace BinPackingGap.GraphPackingTapeBlocks

open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingRegisters PackingRegisterFrame

variable (fixed : InventoryData) (K : Nat)

theorem slots_outside (destination : Extra) (q : Register fixed K ⊕ Fin 6) :
    slots fixed K q ≠ Sum.inr destination := by
  simp [slots, PackingMachineLayout.registers]

@[simp] theorem frame_extra (base : Tape fixed K → List Bool)
    (vals : Register fixed K → Nat) (destination : Extra) :
    registerTapes (slots fixed K) base vals (.inr destination) = base (.inr destination) := by
  apply registerTapes_other
  rintro ⟨q, hq⟩
  exact slots_outside fixed K destination q hq

theorem tally_exec (source : CountSource) (destination : Extra)
    (base : Tape fixed K → List Bool) (vals : Register fixed K → Nat) (state : State)
    (counterZero : vals (work fixed K .counter) = 0)
    (oneZero : vals (work fixed K .one) = 0)
    (temporaryZero : vals (work fixed K .temporary) = 0) :
    ∃ steps ≤ BinaryToTallyMachine.runtimeBound (vals (countRegister fixed K source)) + 1,
      Exec (GraphPackingProgram.tally fixed K source destination)
        ⟨state, registerTapes (slots fixed K) base vals⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes (slots fixed K)
            (Function.update base (.inr destination)
              (List.replicate (vals (countRegister fixed K source)) true ++ base (.inr destination)))
            vals⟩ := by
  have registers : ∀ r,
      registerTapes (slots fixed K) base vals (tallySlots fixed K source (.inl r)) =
        (BinaryToTallyMachine.initial (vals (countRegister fixed K source)) r).bits := by
    intro r
    change registerTapes (slots fixed K) base vals
      (slots fixed K (.inl (match r with
        | .source => countRegister fixed K source
        | .counter => work fixed K .counter
        | .one => work fixed K .one
        | .temporary => work fixed K .temporary))) = _
    rw [registerTapes_reg]
    cases r <;> simp only [BinaryToTallyMachine.initial, counterZero, oneZero, temporaryZero]
  have scratch : ∀ j, registerTapes (slots fixed K) base vals
      (tallySlots fixed K source (.inr j)) = [] := by
    intro j
    simp [tallySlots]
  obtain ⟨t, ht, actual⟩ := BinaryToTallyMachine.exec_from_tapes
    (tallySlots fixed K source) (.inr destination)
    (tally_outside fixed K source destination) (registerTapes (slots fixed K) base vals)
    (vals (countRegister fixed K source)) registers scratch ()
  rw [frame_extra, ← external_update (slots fixed K) base vals (.inr destination)
    (slots_outside fixed K destination)] at actual
  exact PackingArithmeticProgram.exec_in_time
    (BinaryToTallyMachine.code (tallySlots fixed K source) (.inr destination))
    _ _ _ state ⟨t, ht, actual⟩

end BinPackingGap.GraphPackingTapeBlocks

namespace BinPackingGap.GraphPackingPreparation

section

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram PackingRegisterFrame

variable (fixed : InventoryData) (K : Nat)

def setupValues (x : GraphReductionInput) : Register fixed K → Nat :=
  PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator
    (fun _ => 0) (setupOther fixed K x)

@[simp] theorem setupValues_item (x : GraphReductionInput) (v : PackingItemExpression.Variable) :
    setupValues fixed K x (item fixed K v) = 0 := rfl

@[simp] theorem setupValues_work (x : GraphReductionInput) (w : Work) :
    setupValues fixed K x (work fixed K w) = 0 := rfl

@[simp] theorem setupValues_input (x : GraphReductionInput) (i : PackingSetupExpression.Input) :
    setupValues fixed K x (input fixed K i) =
      PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k i := rfl

@[simp] theorem setupValues_output (x : GraphReductionInput) (o : PackingSetupExpression.Output) :
    setupValues fixed K x (output fixed K o) =
      PackingSetupExpression.outputValues (parameters fixed K)
        x.graph.n x.graph.edges.length x.k o := rfl

@[simp] theorem base_powerCounter (x : GraphReductionInput) :
    baseTapes fixed K x [] (.inr .powerCounter) = [] := rfl

end

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram

end BinPackingGap.GraphPackingPreparation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobEdge
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

def resultBase (base : Tape fixed K → List Bool) (suffix word : List Bool) :
    Tape fixed K → List Bool :=
  outputTapes (.inr .reverseOutput) (Function.update base (.inr .endpoints) suffix) word

@[simp] theorem resultBase_endpoints (base : Tape fixed K → List Bool)
    (suffix word : List Bool) : resultBase fixed K base suffix word (.inr .endpoints) = suffix := by
  simp [resultBase, outputTapes]

@[simp] theorem resultBase_other (base : Tape fixed K → List Bool)
    (suffix word : List Bool) (e : Extra) (hne : e ≠ .endpoints) (hno : e ≠ .reverseOutput) :
    resultBase fixed K base suffix word (.inr e) = base (.inr e) := by
  simp [resultBase, outputTapes, hne, hno]

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingGlobalExecution
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPoolExec

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open PackingMachineLayout PackingItemExpression PackingInventoryDescriptors
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes)

section Layout

variable {δ α β ε : Type} [DecidableEq δ] [DecidableEq α]
variable [DecidableEq β] [DecidableEq ε]

theorem layout_external_update (num : δ → Expr α) (den : Expr α)
    (base : Tape num den β ε → List Bool) (input : α → Nat) (other : β → Nat)
    (external : ε) (word : List Bool) :
    tapes num den (Function.update base (.inr external) word) input other =
      Function.update (tapes num den base input other) (.inr external) word := by
  apply RegisterFrameEmission.external_update
  intro i
  simp [registers]

theorem layout_output (num : δ → Expr α) (den : Expr α)
    (base : Tape num den β ε → List Bool) (input : α → Nat) (other : β → Nat)
    (output : ε) (word : List Bool) :
    outputTapes (.inr output) (tapes num den base input other) word =
      tapes num den (outputTapes (.inr output) base word) input other := by
  unfold outputTapes
  rw [tapes_extra, layout_external_update]

theorem layout_counter (num : δ → Expr α) (den : Expr α)
    (base : Tape num den β ε → List Bool) (input : α → Nat) (other : β → Nat)
    (counter : ε) (n : Nat) :
    counterTapes (.inr counter) (tapes num den base input other) n =
      tapes num den (counterTapes (.inr counter) base n) input other := by
  exact (layout_external_update num den base input other counter
    (List.replicate n true)).symm

end Layout

open GraphPackingRegisters

variable (fixed : InventoryData) (K : Nat)

def poolWord (stock : PackingSetupExpression.Output) (descriptor : ItemDescriptor fixed)
    (input : Variable → Nat) (other : Other fixed K → Nat) : List Bool :=
  PackingConstantPool.repeatRecords
    (PackingChunkMachine.records (Numerator fixed) denominator (fun _ => input) [descriptor])
    (other (GraphPackingProgram.otherSetup fixed K stock))

def poolBudget (stock : PackingSetupExpression.Output) (descriptor : ItemDescriptor fixed)
    (other : Other fixed K → Nat) (width : Nat) : Nat :=
  let n := other (GraphPackingProgram.otherSetup fixed K stock)
  BinaryToTallyMachine.runtimeBound n +
    n * ((PackingChunkMachine.timePolynomial (Numerator fixed) denominator [descriptor]).eval width + 2) + 3

end BinPackingGap.GraphPackingPoolExec

namespace BinPackingGap.GraphPackingGlobalLoop

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open PackingMachineLayout GraphPackingProgram GraphPackingPoolExec
open PackingItemExpression (Variable denominator)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

def radix (other : Other fixed K → Nat) : Nat :=
  other (otherSetup fixed K .base)

def edgeInput (input : Variable → Nat) (other : Other fixed K → Nat) (edge : Nat) :
    Variable → Nat := Function.update input .edgePower (radix fixed K other ^ edge)

@[simp] theorem edgeInput_power (input : Variable → Nat) (other : Other fixed K → Nat)
    (edge : Nat) : edgeInput fixed K input other edge .edgePower = radix fixed K other ^ edge := by
  simp [edgeInput]

end BinPackingGap.GraphPackingGlobalLoop

namespace BinPackingGap.GraphPackingGlobalPhases

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open PackingMachineLayout GraphPackingProgram GraphPackingPoolExec
open PackingItemExpression (Variable denominator)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

abbrev Pool := PackingSetupExpression.Output × PackingInventoryDescriptors.ItemDescriptor fixed

def poolListWord (pools : List (Pool fixed)) (input : Variable → Nat)
    (other : Other fixed K → Nat) : List Bool :=
  pools.flatMap (fun pool => poolWord fixed K pool.1 pool.2 input other)

def poolListBudget (pools : List (Pool fixed)) (other : Other fixed K → Nat)
    (width : Nat) : Nat :=
  (pools.map (fun pool => poolBudget fixed K pool.1 pool.2 other width)).sum

def flagPools : List (Pool fixed) :=
  [(.treeFlags, (.ft, .zero)), (.jobFlags, (.fm, .zero)), (.jobFlags, (.fg, .zero))]

theorem update_width (input : Variable → Nat) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (destination : Variable) (constant : Nat)
    (hc : constant.size ≤ width) :
    ∀ a, (Function.update input destination constant a).size ≤ width := by
  intro a
  by_cases h : a = destination
  · subst a
    simpa only [Function.update_self] using hc
  · simpa only [Function.update_of_ne h] using hi a

def flagInput (input : Variable → Nat) : Variable → Nat := Function.update input .edgePower 1

def flagsBudget (other : Other fixed K → Nat) (width : Nat) : Nat :=
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .edgePower 1).eval (width + 1) +
  poolListBudget fixed K (flagPools fixed) other (width + 1) + 1

end BinPackingGap.GraphPackingGlobalPhases

namespace BinPackingGap.GraphPackingPoolRuntime

open BinPackingGames.Foundations.Complexity
open GraphPackingRegisters GraphPackingGlobalPhases PackingInventoryDescriptors
open PackingItemExpression (denominator)

def poolPolynomial (fixed : InventoryData) (descriptor : ItemDescriptor fixed)
    (N W : Polynomial Nat) : Polynomial Nat :=
  tallyPolynomial N + N *
    ((PackingChunkMachine.timePolynomial (Numerator fixed) denominator [descriptor]).comp W +
      Polynomial.C 2) + Polynomial.C 3

@[simp] theorem poolPolynomial_eval (fixed : InventoryData) (descriptor : ItemDescriptor fixed)
    (N W : Polynomial Nat) (s : Nat) :
    (poolPolynomial fixed descriptor N W).eval s =
      (tallyPolynomial N).eval s + N.eval s *
        ((PackingChunkMachine.timePolynomial (Numerator fixed) denominator [descriptor]).eval
          (W.eval s) + 2) + 3 := by
  simp only [poolPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_C]

def poolListPolynomial (fixed : InventoryData) (pools : List (Pool fixed))
    (N W : Polynomial Nat) : Polynomial Nat :=
  (pools.map (fun pool => poolPolynomial fixed pool.2 N W)).sum

@[simp] theorem poolListPolynomial_eval (fixed : InventoryData) (pools : List (Pool fixed))
    (N W : Polynomial Nat) (s : Nat) :
    (poolListPolynomial fixed pools N W).eval s =
      (pools.map (fun pool => (poolPolynomial fixed pool.2 N W).eval s)).sum := by
  simp only [poolListPolynomial, Polynomial.eval_listSum, List.map_map, Function.comp_def]

end BinPackingGap.GraphPackingPoolRuntime

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPreparation

section

open Turing BinPackingGames.Foundations.Complexity
open GraphPackingRegisters GraphPackingProgram PackingMachineBlocks
open FiniteTapeProgram BinaryRegisterProgram

variable (fixed : InventoryData) (K : Nat)

@[simp] theorem graphSlots_apply (i : Fin 7) : graphSlots fixed K i =
    ![.inr .input, .inr .scanScratch, .inr .scanTemporary,
      .inr .threshold, .inr .endpoints, .inr .vertices, .inr .edges] i := by
  simp only [graphSlots]
  rfl

@[simp] theorem thresholdSlots_apply (i : Fin 3) : thresholdSlots fixed K i =
    ![.inr .threshold, .inr .decodeScratch, slots fixed K (.inl (input fixed K .k))] i := by
  simp only [thresholdSlots]
  rfl

@[simp] theorem setup_apply (r : PackingSetupMachine.Reg (parameters fixed K)) :
    setup fixed K r = .inl (.inr (.inl r)) := rfl

end

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram

end BinPackingGap.GraphPackingPreparation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingVerticesBound
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingVertices

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters PackingItemExpression
open GraphPackingProgram (PhaseRuns)

variable (fixed : InventoryData) (K : Nat)

def startInputs (x : GraphReductionInput) : Variable → Nat :=
  Function.update
    (Function.update
      (Function.update (GraphPackingPreparation.preparedInputs fixed K x) .labelPower 3)
      .edgePower 1)
    .repetitionOne 0

def startBase (x : GraphReductionInput) : Tape fixed K → List Bool :=
  GraphPackingPreparation.baseTapes fixed K x
    (BinaryEncoding.natBits (GraphPackingPreparation.binBound fixed K x)).reverse

def startValues (x : GraphReductionInput) : Register fixed K → Nat :=
  PackingMachineLayout.values (Numerator fixed) denominator (startInputs fixed K x)
    (GraphPackingPreparation.preparedOther fixed K x)

@[simp] theorem startValues_count_n (x : GraphReductionInput) :
    startValues fixed K x (countRegister fixed K (.input .n)) = x.graph.n := rfl

@[simp] theorem startValues_counter (x : GraphReductionInput) :
    startValues fixed K x (work fixed K .counter) = 0 := rfl

@[simp] theorem startValues_one (x : GraphReductionInput) :
    startValues fixed K x (work fixed K .one) = 0 := rfl

@[simp] theorem startValues_temporary (x : GraphReductionInput) :
    startValues fixed K x (work fixed K .temporary) = 0 := rfl

@[simp] theorem startBase_vertexCounter (x : GraphReductionInput) :
    startBase fixed K x (.inr .vertexCounter) = [] := rfl

end

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open FiniteTapeProgram PackingMachineBlocks
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

def data (x : GraphReductionInput) : InventoryData :=
  PackingDescriptorExpression.instantiate fixed x.graph
    (GraphPackingPreparation.repetitions fixed K x) x.k

def inputValues (x : GraphReductionInput) : Variable → Nat :=
  PackingDescriptorExpression.values (data fixed K x) none 0 0

def emitted (x : GraphReductionInput) : List Bool :=
  PackingDescriptorExpression.rawRecords (PackingInventoryDescriptors.vertexStream (data fixed K x))

def finalInputs (x : GraphReductionInput) : Variable → Nat :=
  PackingVertexLoop.vertexInput (inputValues fixed K x) .labelPower x.graph.n

def finalBase (x : GraphReductionInput) : Tape fixed K → List Bool :=
  outputTapes (.inr .reverseOutput) (startBase fixed K x) (emitted fixed K x)

def finalTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  PackingCountedProgram.counterTapes (.inr .vertexCounter)
    (PackingMachineLayout.tapes (Numerator fixed) denominator (finalBase fixed K x)
      (finalInputs fixed K x) (preparedOther fixed K x)) 0

@[simp] theorem final_labelPower (x : GraphReductionInput) :
    finalInputs fixed K x .labelPower = 3 ^ (x.graph.n + 1) := by
  exact PackingVertexLoop.vertexInput_power _ _ _

@[simp] theorem final_edgePower (x : GraphReductionInput) :
    finalInputs fixed K x .edgePower = 1 := by
  simp [finalInputs, PackingVertexLoop.vertexInput, inputValues, PackingDescriptorExpression.values]

@[simp] theorem final_repetition (x : GraphReductionInput) :
    finalInputs fixed K x .repetitionOne = 0 := by
  simp [finalInputs, PackingVertexLoop.vertexInput, inputValues, PackingDescriptorExpression.values]

@[simp] theorem final_counter_empty (x : GraphReductionInput) :
    finalTapes fixed K x (.inr .vertexCounter) = [] := by
  simp [finalTapes, PackingCountedProgram.counterTapes]

@[simp] theorem final_output (x : GraphReductionInput) :
    finalTapes fixed K x (.inr .reverseOutput) =
      (emitted fixed K x).reverse ++
        (BinaryEncoding.natBits (binBound fixed K x)).reverse := by
  simp [finalTapes, PackingCountedProgram.counterTapes, finalBase, outputTapes,
    PackingMachineLayout.tapes_extra, startBase, baseTapes]

end BinPackingGap.GraphPackingVertices

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingFinish

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open BinPackingGames.Reduction.MachineTransfer

variable (fixed : InventoryData) (K : Nat)

def transfer : Code (K := Tape fixed K) (S := BinaryAddMachine.State Unit) :=
  .routine Unit inferInstance ()
    (fun _ => loopAt (.inr Extra.reverseOutput) (.inr Extra.output) id false () none)

def resultTapes (base : Tape fixed K → List Bool) (word : List Bool) :
    Tape fixed K → List Bool :=
  Function.update (Function.update base (.inr .reverseOutput) [])
    (.inr .output) (word ++ [false])

@[simp] theorem resultTapes_output (base : Tape fixed K → List Bool) (word : List Bool) :
    resultTapes fixed K base word (.inr .output) = word ++ [false] := by
  simp [resultTapes]

@[simp] theorem resultTapes_reverse (base : Tape fixed K → List Bool) (word : List Bool) :
    resultTapes fixed K base word (.inr .reverseOutput) = [] := by
  simp [resultTapes]

theorem transfer_exec (base : Tape fixed K → List Bool) (word : List Bool)
    (_reverseWord : base (.inr .reverseOutput) = word.reverse)
    (outputEmpty : base (.inr .output) = []) :
    Exec (transfer fixed K)
      ⟨BinaryAddMachine.clean (),
        Function.update base (.inr .reverseOutput) (false :: word.reverse)⟩
      (word.length + 2)
      ⟨BinaryAddMachine.clean (), resultTapes fixed K base word⟩ := by
  let pushed := Function.update base (.inr Extra.reverseOutput) (false :: word.reverse)
  have hreverse : pushed (.inr .reverseOutput) = false :: word.reverse := by simp [pushed]
  have run := transferAt_fromTapes
    (σ := (Unit × Bool) × Option Bool)
    (Γ := fun _ : Tape fixed K => Bool)
    (.inr Extra.reverseOutput) (.inr Extra.output) (by simp)
    id false () none
    (fun _ : Unit => loopAt (.inr Extra.reverseOutput) (.inr Extra.output) id false () none)
    rfl pushed (((), false), none) none
  have after : tapesAt (.inr Extra.reverseOutput) (.inr Extra.output) pushed []
      ((pushed (.inr Extra.reverseOutput)).reverse.map id ++ pushed (.inr Extra.output)) =
      resultTapes fixed K base word := by
    simp [tapesAt, pushed, resultTapes, outputEmpty]
  rw [after, hreverse] at run
  have next_eq :
      nextAt (Γ := fun _ : Tape fixed K => Bool) (σ := (Unit × Bool) × Option Bool)
        (.inr Extra.output)
        (fun _ : Unit => loopAt (.inr Extra.reverseOutput) (.inr Extra.output)
          id false () none) =
      MachineComposition.advance
        (TM2.step (fun _ : Unit => loopAt
          (Γ := fun _ : Tape fixed K => Bool) (σ := (Unit × Bool) × Option Bool)
          (.inr Extra.reverseOutput) (.inr Extra.output) id false () none)) := rfl
  rw [next_eq] at run
  unfold transfer
  apply Exec.routine (K := Tape fixed K) (S := BinaryAddMachine.State Unit) inferInstance ()
    (fun _ : Unit => loopAt (σ := (Unit × Bool) × Option Bool)
      (.inr Extra.reverseOutput) (.inr Extra.output) id false () none)
  simpa only [List.length_cons, List.length_reverse, Nat.add_assoc, Nat.reduceAdd,
    BinaryAddMachine.State, BinaryAddMachine.clean, BinaryAddMachine.state, pushed] using run

theorem finish_exec (base : Tape fixed K → List Bool) (state : State) (word : List Bool)
    (reverseWord : base (.inr .reverseOutput) = word.reverse)
    (outputEmpty : base (.inr .output) = []) :
    Exec (GraphPackingProgram.finish fixed K) ⟨state, base⟩ (word.length + 5)
      ⟨.arithmetic (BinaryAddMachine.clean ()), resultTapes fixed K base word⟩ := by
  let push : Action (Tape fixed K) State :=
    .push (.inr .reverseOutput) (fun _ => false) .done
  let pushed := Function.update base (.inr Extra.reverseOutput) (false :: word.reverse)
  have first : Exec (.atom push) ⟨state, base⟩ 1 ⟨state, pushed⟩ := by
    simpa only [push, pushed, Action.eval, reverseWord] using Exec.atom push ⟨state, base⟩
  have second := PackingArithmeticProgram.exec (transfer fixed K) pushed
    (resultTapes fixed K base word) (word.length + 2) state
    (transfer_exec fixed K base word reverseWord outputEmpty)
  have third := Exec.atom (K := Tape fixed K) (S := State) .done
    ⟨.arithmetic (BinaryAddMachine.clean ()), resultTapes fixed K base word⟩
  have joined := Exec.seq first (Exec.seq second third)
  simpa only [GraphPackingProgram.finish, GraphPackingProgram.chain, transfer, push,
    Nat.add_assoc, Nat.reduceAdd, Nat.add_comm, Nat.add_left_comm, Action.eval] using joined

def rawProgram : MachineCanonicalOutput.Program (Tape fixed K)
    (GraphPackingProgram.code fixed K).Label State where
  input := .inr .input
  output := .inr .output
  main := (GraphPackingProgram.code fixed K).entry
  initial := .arithmetic (BinaryAddMachine.clean ())
  code := (GraphPackingProgram.code fixed K).instruction id none

def cleanupTapes : List (Tape fixed K) :=
  ((Finset.univ : Finset (Tape fixed K)).erase (.inr .output)).toList

theorem cleanup_complete (tape : Tape fixed K) :
    tape ∈ cleanupTapes fixed K ↔ tape ≠ (rawProgram fixed K).output := by
  simp [cleanupTapes, rawProgram]

def canonicalMachine : FinTM2 :=
  MachineCanonicalOutput.completedMachine (rawProgram fixed K) (cleanupTapes fixed K)

end BinPackingGap.GraphPackingFinish

namespace BinPackingGap.GraphPackingFixedParameters

def emptyGraph : GraphInput where
  n := 0
  edges := []
  ordered := by simp
  distinct := by simp

def fixedInventory (c : Nat) (ρ : ℝ) : InventoryData :=
  reductionInventory c ρ emptyGraph 0

theorem inventory_eq (c : Nat) (ρ : ℝ) (x : GraphReductionInput) :
    GraphPackingJobs.inventory (fixedInventory c ρ) (lossAllowance c) x =
      reductionInventory c ρ x.graph x.k := rfl

theorem binBound_eq_inventory (fixed : InventoryData) (K : Nat) (x : GraphReductionInput) :
    GraphPackingPreparation.binBound fixed K x = (GraphPackingJobs.inventory fixed K x).B := by
  exact congrFun (PackingSetupExpression.outputValues_eq_inventory
    (GraphPackingRegisters.parameters fixed K) (GraphPackingJobs.inventory fixed K x)
    rfl rfl rfl rfl) .bins

theorem rawOutput_eq (c : Nat) (ρ : ℝ) (x : GraphReductionInput) :
    (GraphPackingJobs.inventory (fixedInventory c ρ) (lossAllowance c) x).rawOutput =
      graphPackingOutput c ρ x := by
  rw [inventory_eq]
  rfl

end BinPackingGap.GraphPackingFixedParameters

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RoundTableGap
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype _root_.OAI.BinPackingGap.UniformTree.nodeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RoundTables

instance instNonemptyFinDartsValTableLtNatOfNat (input : Input) : Nonempty (Fin input.val.darts) := ⟨⟨0, input.property⟩⟩

def Satisfiable (input : Input) : Prop := (GraphTables.semantics input.val).Satisfiable

noncomputable def gap (input : Input) : ℝ := (GraphTables.semantics input.val).gap

end BinPackingGames.Foundations.PCP.RoundTables

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ApproximationImpliesP
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ApproximationDecisionMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinaryEncoding
open BinPackingCompleteness.BinaryEncoding (bitsValue bitsValue_bits frame)

def program (c : Nat) : MachineCanonicalOutput.Program Tape Label Register where
  input := .input
  output := .output
  main := .start
  initial := clean
  code := code c

abbrev machine (c : Nat) := MachineCanonicalOutput.sourceMachine (program c)

@[simp] theorem machine_code (c : Nat) (label : Label) :
    (machine c).m label = code c label := rfl

theorem machine_step (c : Nat) : (machine c).step = TM2.step (code c) := rfl

def cfg (label : Option Label) (input binary scratch constant output : List Bool) :
    TM2.Cfg Alphabet Label Register := ⟨label, clean, tapes input binary scratch constant output⟩

theorem oneStep {c : Nat} {a b : (machine c).Cfg}
    (h : (machine c).step a = some b) :
    (advance (machine c).step)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

theorem startSome (c : Nat) (input : List Bool) :
    (machine c).step (cfg (some .start) (true :: input) [] [] [] []) =
      some (cfg (some .binRead) input [] [] c.bits []) := by
  change some (TM2.stepAux (code c .start) _ _) = _
  simp [code, TM2.stepAux, cfg, go, read, head, stepAux_pushConstant]

theorem startNone (c : Nat) :
    (machine c).step (cfg (some .start) [false] [] [] [] []) =
      some (cfg none [] [] [] [] [false]) := by
  change some (TM2.stepAux (code c .start) _ _) = _
  simp [code, TM2.stepAux, cfg, finish, read, head]

theorem readBinTrace (c : Nat) (bits suffix binary reversed constant output : List Bool) :
    (advance (machine c).step)^[bits.length + 1]
      (some (cfg (some .binRead) (frame bits ++ suffix) binary reversed constant output)) =
      some (cfg (some .binRestore) suffix binary (bits.reverse ++ reversed) constant output) := by
  induction bits generalizing reversed with
  | nil =>
    apply oneStep
    change some (TM2.stepAux (code c .binRead) _ _) = _
    simp [frame, code, TM2.stepAux, cfg, go, read, head]
    rfl
  | cons bit bits ih =>
    have first : (machine c).step
        (cfg (some .binRead) (frame (bit :: bits) ++ suffix) binary reversed constant output) =
        some (cfg (some .binRead) (frame bits ++ suffix) binary
          (bit :: reversed) constant output) := by
      change some (TM2.stepAux (code c .binRead) _ _) = _
      simp [frame, code, TM2.stepAux, cfg, go, read, head]
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      joinTrace (oneStep first) (ih (bit :: reversed))

theorem restoreTrace (c : Nat) (label : Label) (next : Label)
    (hcode : code c label = loopAt .scratch .binary id false label (some next))
    (input binary scratch constant output : List Bool) :
    (advance (machine c).step)^[scratch.length + 1]
      (some (cfg (some label) input binary scratch constant output)) =
      some (cfg (some next) input (scratch.reverse ++ binary) [] constant output) := by
  have h := transferAt_fromTapes (Γ := Alphabet) Tape.scratch Tape.binary (by decide)
    id false label (some next) (code c) hcode (tapes input binary scratch constant output)
    (((), .eq), none) none
  have hstep : nextAt Tape.binary (code c) = advance (machine c).step := rfl
  rw [hstep] at h
  simpa only [cfg, clean, BinaryOrderMachine.clean, tapes_scratch, tapes_binary,
    List.map_id, tapesAt, update_binary, update_scratch] using! h

theorem borrowCost_le (bits : List Bool) (n : Nat) :
    borrowCost bits n ≤ 2 * bits.length + n + 2 := by
  induction bits generalizing n with
  | nil => simp [borrowCost]
  | cons bit bits ih =>
    cases bit <;> simp [borrowCost]
    have bound := ih (n + 1)
    omega

theorem drainTrace (c : Nat) (input binary scratch constant output : List Bool) :
    (advance (machine c).step)^[scratch.length + 1]
      (some (cfg (some .predDrain) input binary scratch constant output)) =
      some (cfg (some (.items 0)) input binary [] constant output) := by
  induction scratch with
  | nil =>
    apply oneStep
    change some (TM2.stepAux (code c .predDrain) _ _) = _
    simp [code, TM2.stepAux, cfg, go, read, head]
    rfl
  | cons bit tail ih =>
    have first : (machine c).step
        (cfg (some .predDrain) input binary (bit :: tail) constant output) =
        some (cfg (some .predDrain) input binary tail constant output) := by
      change some (TM2.stepAux (code c .predDrain) _ _) = _
      simp [code, TM2.stepAux, cfg, go, read, head]
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      joinTrace (oneStep first) ih

theorem borrowTrace (c : Nat) (bits : List Bool) (n : Nat)
    (input constant output : List Bool) :
    (advance (machine c).step)^[borrowCost bits n]
      (some (cfg (some .decrement) input bits (List.replicate n true) constant output)) =
      some (cfg (some (.items 0)) input (borrowOutput bits n) [] constant output) := by
  induction bits generalizing n with
  | nil =>
    have first : (machine c).step
        (cfg (some .decrement) input [] (List.replicate n true) constant output) =
        some (cfg (some .predDrain) input [] (List.replicate n true) constant output) := by
      change some (TM2.stepAux (code c .decrement) _ _) = _
      simp [code, TM2.stepAux, cfg, go, read, head]
    simpa [borrowCost, borrowOutput, borrowPred, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using joinTrace
      (oneStep first)
      (drainTrace c input [] (List.replicate n true) constant output)
  | cons bit bits ih =>
    cases bit with
    | false =>
      have first : (machine c).step
          (cfg (some .decrement) input (false :: bits) (List.replicate n true) constant output) =
          some (cfg (some .decrement) input bits (List.replicate (n + 1) true) constant output) := by
        change some (TM2.stepAux (code c .decrement) _ _) = _
        simp [code, TM2.stepAux, cfg, go, read, head, List.replicate_succ]
      have hout : borrowOutput bits (n + 1) = borrowOutput (false :: bits) n := by
        unfold borrowOutput
        rw [show borrowPred (false :: bits) = (borrowPred bits).map (true :: ·) from rfl]
        cases h : borrowPred bits with
        | none => rfl
        | some out => simp [List.replicate_add, List.append_assoc]
      simpa only [borrowCost, hout] using joinTrace
        (oneStep first) (ih (n + 1))
    | true =>
      have first : (machine c).step
          (cfg (some .decrement) input (true :: bits) (List.replicate n true) constant output) =
          some (cfg (some .predRestore) input (false :: bits) (List.replicate n true) constant output) := by
        change some (TM2.stepAux (code c .decrement) _ _) = _
        simp [code, TM2.stepAux, cfg, go, read, head]
      simpa [borrowCost, borrowOutput, borrowPred, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using joinTrace
        (oneStep first)
        (restoreTrace c .predRestore (.items 0) rfl input (false :: bits)
          (List.replicate n true) constant output)

theorem decrementTrace (c : Nat) (bits input constant output : List Bool) :
    (advance (machine c).step)^[borrowCost bits 0]
      (some (cfg (some .decrement) input bits [] constant output)) =
      some (cfg (some (.items 0)) input (predWord bits) [] constant output) := by
  have h := borrowTrace c bits 0 input constant output
  cases hb : borrowPred bits <;> simpa [borrowOutput, predWord, hb] using h

theorem nameTrace (c : Nat) (count : Fin 5)
    (bits suffix binary constant output : List Bool) :
    (advance (machine c).step)^[bits.length + 1]
      (some (cfg (some (.name count)) (frame bits ++ suffix) binary [] constant output)) =
      some (cfg (some (if count.val = 4 then .decrement else .items (nextCount count)))
        suffix binary [] constant output) := by
  induction bits with
  | nil =>
    apply oneStep
    change some (TM2.stepAux (code c (.name count)) _ _) = _
    simp [frame, code, TM2.stepAux, cfg, go, read, head]
    rfl
  | cons bit bits ih =>
    have first : (machine c).step
        (cfg (some (.name count)) (frame (bit :: bits) ++ suffix) binary [] constant output) =
        some (cfg (some (.name count)) (frame bits ++ suffix) binary [] constant output) := by
      change some (TM2.stepAux (code c (.name count)) _ _) = _
      simp [frame, code, TM2.stepAux, cfg, go, read, head]
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      joinTrace (oneStep first) ih

theorem itemsTrace (c : Nat) (count : Fin 5) (bits : List Bool)
    (assignments : List Nat) (suffix constant output : List Bool) :
    (advance (machine c).step)^[itemsCost count bits assignments]
      (some (cfg (some (.items count)) (assignmentBits assignments ++ suffix)
        bits [] constant output)) =
      some (cfg (some .compare) suffix (process count bits assignments) [] constant output) := by
  induction assignments generalizing count bits with
  | nil =>
    apply oneStep
    change some (TM2.stepAux (code c (.items count)) _ _) = _
    simp [assignmentBits, listBits, process, code, TM2.stepAux, cfg, go, read, head]
    rfl
  | cons a tail ih =>
    have first : (machine c).step
        (cfg (some (.items count)) (assignmentBits (a :: tail) ++ suffix) bits [] constant output) =
        some (cfg (some (.name count))
          (natBits a ++ (assignmentBits tail ++ suffix)) bits [] constant output) := by
      change some (TM2.stepAux (code c (.items count)) _ _) = _
      simp [assignmentBits, listBits, code, TM2.stepAux, cfg, go, read, head, List.append_assoc]
    have second := nameTrace c count a.bits (assignmentBits tail ++ suffix) bits constant output
    change (advance (machine c).step)^[a.bits.length + 1]
      (some (cfg (some (.name count)) (natBits a ++ (assignmentBits tail ++ suffix))
        bits [] constant output)) = _ at second
    have firstTwo := joinTrace
      (oneStep first) second
    by_cases h : count.val = 4
    · have hc : nextCount count = 0 := by simp [nextCount, h]
      rw [ite_eq_left h] at firstTwo
      have third := decrementTrace c bits (assignmentBits tail ++ suffix) constant output
      have fourth := ih 0 (predWord bits)
      simpa only [itemsCost, process, ite_eq_left h, hc, Nat.size_eq_bits_len,
        Nat.add_assoc] using joinTrace (joinTrace firstTwo third) fourth
    · rw [ite_eq_right h] at firstTwo
      simpa only [itemsCost, process, ite_eq_right h, Nat.add_zero, Nat.size_eq_bits_len,
        Nat.add_assoc] using joinTrace firstTwo (ih (nextCount count) bits)

theorem itemsCost_le (count : Fin 5) (bits : List Bool) (assignments : List Nat) :
    itemsCost count bits assignments ≤
      (assignmentBits assignments).length + (2 * bits.length + 2) * assignments.length := by
  induction assignments generalizing count bits with
  | nil => simp [itemsCost, assignmentBits, listBits]
  | cons a tail ih =>
    have hb := borrowCost_le bits 0
    have hp := predWord_length_le bits
    have hlen : (assignmentBits (a :: tail)).length =
        1 + (2 * a.size + 1) + (assignmentBits tail).length := by
      simp [assignmentBits, listBits]; omega
    by_cases h : count.val = 4
    · have hi := ih (nextCount count) (predWord bits)
      have hm : (2 * (predWord bits).length + 2) * tail.length ≤
          (2 * bits.length + 2) * tail.length := Nat.mul_le_mul_right _ (by omega)
      simp only [itemsCost, ite_eq_left h, List.length_cons, hlen]
      nlinarith
    · have hi := ih (nextCount count) bits
      simp only [itemsCost, ite_eq_right h, List.length_cons, hlen]
      nlinarith

theorem orderExit_eq (a b : Nat) :
    orderExit (BinaryOrderMachine.orderNat a b .eq) = some (.answer (decide (a ≤ b))) := by
  unfold BinaryOrderMachine.orderNat
  split_ifs with hlt hgt
  · simp [orderExit, Nat.le_of_lt hlt]
  · simp [orderExit, Nat.not_le.mpr hgt]
  · have he : a ≤ b := by omega
    simp [orderExit, he]

theorem compareTrace (c : Nat) (bits : List Bool) :
    (advance (machine c).step)^[max bits.length c.bits.length + 2]
      (some (cfg (some .compare) [] bits [] c.bits [])) =
      some (cfg none [] [] [] [] [decide (bitsValue bits ≤ c)]) := by
  have comparison := BinaryOrderMachine.compareTrace_fromTapes
    Tape.binary Tape.constant (by decide) Label.compare orderExit (code c) rfl
    (tapes [] bits [] c.bits []) ()
  have hcomp : (advance (machine c).step)^[max bits.length c.bits.length + 1]
      (some (cfg (some .compare) [] bits [] c.bits [])) =
      some (cfg (some (.answer (decide (bitsValue bits ≤ c)))) [] [] [] [] []) := by
    rw [machine_step]
    simpa only [cfg, clean, tapes_binary, tapes_constant, bitsValue_bits, orderExit_eq,
      tapesAt, update_binary, update_constant] using! comparison
  have answer : (machine c).step
      (cfg (some (.answer (decide (bitsValue bits ≤ c)))) [] [] [] [] []) =
      some (cfg none [] [] [] [] [decide (bitsValue bits ≤ c)]) := by
    change some (TM2.stepAux (code c (.answer _)) _ _) = _
    simp [code, finish, TM2.stepAux, cfg]
  simpa only [Nat.add_assoc] using!
    joinTrace hcomp (oneStep answer)

theorem someTrace (c : Nat) (p : RawPacking) :
    (advance (machine c).step)^[someSteps c p]
      (some (cfg (some .start) (packingResultBits (some p)) [] [] [] [])) =
      some (cfg none [] [] [] [] [approximationAccepts c (some p)]) := by
  have first := startSome c (rawPackingBits p)
  have second := readBinTrace c p.bins.bits (assignmentBits p.assignments) [] [] c.bits []
  have third := restoreTrace c .binRestore (.items 0) rfl
    (assignmentBits p.assignments) [] p.bins.bits.reverse c.bits []
  have fourth := itemsTrace c 0 p.bins.bits p.assignments [] c.bits []
  have fifth := compareTrace c (process 0 p.bins.bits p.assignments)
  have hdecision : decide (bitsValue (process 0 p.bins.bits p.assignments) ≤ c) =
      approximationAccepts c (some p) := by
    simp only [approximationAccepts]
    by_cases h : bitsValue (process 0 p.bins.bits p.assignments) ≤ c
    · have rhs := (process_test c p.bins p.assignments).mp h
      simp [h, rhs]
    · have rhs : ¬5 * p.bins ≤ p.assignments.length + 5 * c :=
        fun hh => h ((process_test c p.bins p.assignments).mpr hh)
      simp [h, rhs]
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at second third fourth
  simpa only [someSteps, packingResultBits, optionBits, rawPackingBits,
    natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
    Nat.size_eq_bits_len, hdecision, Nat.add_assoc] using
    joinTrace (joinTrace (joinTrace (joinTrace
      (oneStep first) second) third) fourth) fifth

theorem someSteps_le (c : Nat) (p : RawPacking) :
    someSteps c p ≤ (rawTime c).eval (packingResultBits (some p)).length := by
  let n := (packingResultBits (some p)).length
  have hlen : n = 2 * p.bins.size + (assignmentBits p.assignments).length + 2 := by
    simp [n, packingResultBits, optionBits, rawPackingBits]; omega
  have hbl : p.bins.bits.length ≤ n := by rw [Nat.size_eq_bits_len]; omega
  have hsize : p.bins.size ≤ n := by omega
  have hal : p.assignments.length ≤ n :=
    (list_length_le_bits_length natBits p.assignments).trans (by
      change (assignmentBits p.assignments).length ≤ n
      omega)
  have hscan := itemsCost_le 0 p.bins.bits p.assignments
  have hscan' : itemsCost 0 p.bins.bits p.assignments ≤ n + (2 * n + 2) * n := by
    have hm : (2 * p.bins.bits.length + 2) * p.assignments.length ≤
        (2 * n + 2) * n := Nat.mul_le_mul (by omega) hal
    omega
  have hprocess := process_length_le 0 p.bins.bits p.assignments
  have hmax : max (process 0 p.bins.bits p.assignments).length c.bits.length ≤ n + c.size := by
    rw [Nat.size_eq_bits_len]
    exact max_le (by omega) (by omega)
  simp only [someSteps, rawTime, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  change _ ≤ (c.size + 20) * (n + 1) ^ 2
  nlinarith

theorem init_eq (c : Nat) (input : List Bool) :
    initList (machine c) input = cfg (some .start) input [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  cases k <;> rfl

noncomputable def rawRun (c : Nat) (p : Option RawPacking) :
    MachineCanonicalOutput.TerminalRun (program c) (packingResultBits p)
      [approximationAccepts c p] ((rawTime c).eval (packingResultBits p).length) := by
  cases p with
  | none =>
    refine {
      state := clean
      tapes := tapes [] [] [] [] [false]
      execution := {
        steps := 1
        evals_in_steps := ?_
        steps_le_m := ?_ }
      output_eq := rfl }
    · change (advance (machine c).step)^[1]
        (some (initList (machine c) (packingResultBits none))) = _
      simp only [Function.iterate_one, advance_some]
      rw [init_eq]
      exact startNone c
    · simp [rawTime, packingResultBits, optionBits]
      omega
  | some p =>
    refine {
      state := clean
      tapes := tapes [] [] [] [] [approximationAccepts c (some p)]
      execution := {
        steps := someSteps c p
        evals_in_steps := ?_
        steps_le_m := someSteps_le c p }
      output_eq := rfl }
    change (advance (machine c).step)^[someSteps c p]
      (some (initList (machine c) (packingResultBits (some p)))) = _
    simpa only [init_eq, cfg] using! someTrace c p

theorem cleanup_complete (c : Nat) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (program c).output := by
  cases k <;> simp [cleanupTapes, program]

noncomputable def computation (c : Nat) :
    TM2ComputableInPolyTime packingResultBits (fun bit => [bit]) (approximationAccepts c) :=
  MachineCanonicalOutput.computableInPolyTime (program c) cleanupTapes (cleanup_complete c)
    packingResultBits (fun bit => [bit]) (approximationAccepts c) (rawTime c) (rawRun c)

end BinPackingGap.ApproximationDecisionMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionCapacityBounds
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionWitness

open BinaryEncoding

theorem bins_size_le_input (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) :
    bins.size ≤ (extensionBits bins items fixed).length := by
  simp only [extensionBits, List.length_append, natBits_length]
  omega

theorem items_length_le_input (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) :
    items.length ≤ (extensionBits bins items fixed).length := by
  have counted := list_length_le_bits_length (pairBits natBits natBits) items
  change items.length ≤ (rawInstanceBits items).length at counted
  simp only [extensionBits, List.length_append]
  omega

theorem assignmentBits_length_le (bins : Nat) (assignments : List Nat)
    (range : ∀ label ∈ assignments, label < bins) :
    (assignmentBits assignments).length ≤ 1 + assignments.length * (2 * bins.size + 2) := by
  induction assignments with
  | nil => simp [assignmentBits, listBits]
  | cons label assignments ih =>
      have head : label.size ≤ bins.size :=
        FractionWidth.size_mono (Nat.le_of_lt (range label (List.mem_cons_self ..)))
      have tail : ∀ value ∈ assignments, value < bins :=
        fun value mem => range value (List.mem_cons_of_mem label mem)
      have rest := ih tail
      have length_eq : (assignmentBits (label :: assignments)).length =
          2 * label.size + 2 + (assignmentBits assignments).length := by
        simp [assignmentBits, listBits]
        omega
      rw [length_eq, List.length_cons]
      nlinarith

theorem assignmentBits_length_le_bound (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) (assignments : List Nat)
    (feasible : (RawPacking.mk bins assignments).Feasible items) :
    (assignmentBits assignments).length ≤ bound (extensionBits bins items fixed).length := by
  have length_bound := assignmentBits_length_le bins assignments feasible.2.1
  rw [feasible.1] at length_bound
  have item_bound := items_length_le_input bins items fixed
  have header_bound := bins_size_le_input bins items fixed
  have product_bound : items.length * (2 * bins.size + 2) ≤
      (extensionBits bins items fixed).length *
        (2 * (extensionBits bins items fixed).length + 2) :=
    Nat.mul_le_mul item_bound (by omega)
  unfold bound
  nlinarith

theorem exists_bounded_witness (input : List Bool)
    (member : ExtensionCertificate.language input) :
    ∃ witness : List Bool, witness.length ≤ bound input.length ∧
      ExtensionCertificate.verify (input, witness) = true := by
  cases parsed : decodeExtension input with
  | none => simp [ExtensionCertificate.language, parsed] at member
  | some query =>
      rcases query with ⟨bins, items, fixed⟩
      have extension : ExtensionQuery.Ext bins items fixed := by
        simpa [ExtensionCertificate.language, parsed] using member
      obtain ⟨valid, assignments, feasible, agrees⟩ := extension
      refine ⟨assignmentBits assignments, ?_, ?_⟩
      · have represented : input = extensionBits bins items fixed :=
          decodeExtension_sound parsed
        rw [represented]
        exact assignmentBits_length_le_bound bins items fixed assignments feasible
      · have checked :=
          (ExtensionCertificate.check_eq_true_iff bins items fixed assignments).mpr
            ⟨valid, feasible, agrees⟩
        simpa [ExtensionCertificate.verify, parsed] using checked

theorem language_iff_bounded_witness (input : List Bool) :
    ExtensionCertificate.language input ↔
      ∃ witness : List Bool, witness.length ≤ bound input.length ∧
        ExtensionCertificate.verify (input, witness) = true := by
  constructor
  · exact exists_bounded_witness input
  · rintro ⟨witness, _, accepted⟩
    exact ExtensionCertificate.verify_sound input witness accepted

end BinPackingGap.ExtensionWitness

namespace BinPackingGap.ExtensionCapacityMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {K Λ A : Type} [DecidableEq K]

def cleanupEntry (result : Bool) : Option FullLabel :=
  MachineDrainMany.entry allTapes (FullLabel.clear result) (some (.emit result))

def program : FullLabel → TM2.Stmt (Alphabet (K := Tape)) FullLabel (State Unit)
  | .initialize_ => .push 1 (fun _ => true) (.goto fun _ => .core .guard)
  | .core label => statement (Function.Embedding.refl Tape) FullLabel.core
      (cleanupEntry true) (cleanupEntry false) label
  | .clear result phase =>
      MachineDrainMany.instruction allTapes (FullLabel.clear result) (some (.emit result)) phase
  | .emit result =>
      .push 0 (fun _ => result)
        (.load (fun _ => BinaryAddMachine.clean ((), .eq)) .halt)

def machine : FinTM2 where
  K := Tape
  k₀ := 2
  k₁ := 0
  Γ _ := Bool
  Λ := FullLabel
  main := .initialize_
  σ := State Unit
  initialState := BinaryAddMachine.clean ((), .eq)
  m := program

def initialCfg (items : RawInstance) (assignments : List Nat) (selected : Nat) : machine.Cfg :=
  ⟨some .initialize_, BinaryAddMachine.clean ((), .eq), initialTapes items assignments selected⟩

def finalCfg (result : Bool) : machine.Cfg :=
  ⟨none, BinaryAddMachine.clean ((), .eq), finalTapes result⟩

theorem initializeStep (items : RawInstance) (assignments : List Nat) (selected : Nat) :
    machine.step (initialCfg items assignments selected) =
      some ⟨some (.core .guard), BinaryAddMachine.clean ((), .eq),
        inputTapes (fun _ => []) 0 1 selected items assignments⟩ := by
  change some (TM2.stepAux (program .initialize_) _ _) = _
  simp only [program, TM2.stepAux]
  congr 1
  congr 1
  funext k
  fin_cases k <;> simp [initialTapes, inputTapes]

def cleanupInTime (result : Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime machine.step
      ⟨cleanupEntry result, BinaryAddMachine.clean ((), .eq), base⟩
      (some (finalCfg result))
      (MachineDrainMany.lengthSum allTapes base + 23) := by
  have first := MachineDrainMany.execution allTapes (FullLabel.clear result)
    (some (.emit result)) program (fun _ => rfl) base
    ((((), .eq), false), none) none
  rw [cleanup_tapes] at first
  have first' : StateTransition.EvalsToInTime machine.step
      ⟨cleanupEntry result, BinaryAddMachine.clean ((), .eq), base⟩
      (some ⟨some (.emit result), BinaryAddMachine.clean ((), .eq), fun _ => []⟩)
      (MachineDrainMany.lengthSum allTapes base + 22) := by
    change StateTransition.EvalsToInTime (TM2.step program)
      ⟨cleanupEntry result, BinaryAddMachine.clean ((), .eq), base⟩
      (some ⟨some (.emit result), BinaryAddMachine.clean ((), .eq), fun _ => []⟩)
      (MachineDrainMany.lengthSum allTapes base + 22)
    simpa only [cleanupEntry, BinaryAddMachine.clean, BinaryAddMachine.state,
      MachineDrainMany.finalRegister_none, allTapes, List.length_ofFn] using first
  have second : StateTransition.EvalsToInTime machine.step
      ⟨some (.emit result), BinaryAddMachine.clean ((), .eq), fun _ => []⟩
      (some (finalCfg result)) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (.emit result)) _ _) = _
      simp only [program, TM2.stepAux, finalCfg]
      congr 1
      congr 1
      funext k
      change Function.update (fun _ : Tape => ([] : List Bool)) 0 [result] k = finalTapes result k
      by_cases h : k = 0
      · subst k
        rfl
      · rw [Function.update_of_ne h]
        simp only [finalTapes, ite_eq_right h]
    steps_le_m := Nat.le_refl _ }
  have combined := StateTransition.EvalsToInTime.trans machine.step _ _ _ _ _ first' second
  exact { toEvalsTo := combined.toEvalsTo
          steps_le_m := by
            have bound := combined.steps_le_m
            omega }

end BinPackingGap.ExtensionCapacityMachine

namespace BinPackingGap.ExtensionCapacityMachine

section

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

def cfg (label : Option FullLabel) (tapes : Tape → List Bool) : machine.Cfg :=
  ⟨label, clean, tapes⟩

def oneStep {start finish : machine.Cfg} (h : machine.step start = some finish) :
    StateTransition.EvalsToInTime machine.step start (some finish) 1 where
  steps := 1
  evals_in_steps := h
  steps_le_m := Nat.le_refl _

def join {start middle finish : machine.Cfg} {firstTime secondTime : Nat}
    (first : StateTransition.EvalsToInTime machine.step start (some middle) firstTime)
    (second : StateTransition.EvalsToInTime machine.step middle (some finish) secondTime) :
    StateTransition.EvalsToInTime machine.step start (some finish) (firstTime + secondTime) := by
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans machine.step firstTime secondTime
      start middle (some finish) first second

def enlarge {start finish : machine.Cfg} {time budget : Nat}
    (run : StateTransition.EvalsToInTime machine.step start (some finish) time)
    (bounded : time ≤ budget) :
    StateTransition.EvalsToInTime machine.step start (some finish) budget where
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans bounded

theorem guard_cons_step (N D i w s a d j U V : List Bool) :
    machine.step (cfg (some (.core .guard)) (work N D (true :: i) (true :: w) s a d j U V)) =
      some (cfg (some (.core (.number .numerator .scan))) (work N D i w s a d j U V)) := by
  change some (TM2.stepAux (program (.core .guard)) _ _) = _
  simp [program, statement, finish, cfg, clean, BinaryAddMachine.clean,
    BinaryAddMachine.state, TM2.stepAux, Function.Embedding.coe_refl, id_eq,
    work, update2, update3]
  rfl

theorem guard_nil_step (N D s : List Bool) :
    machine.step (cfg (some (.core .guard)) (work N D [false] [false] s [] [] [] [] [])) =
      some (cfg (cleanupEntry true) (work N D [] [] s [] [] [] [] [])) := by
  change some (TM2.stepAux (program (.core .guard)) _ _) = _
  cases h : cleanupEntry true <;>
    simp [program, statement, finish, cfg, clean, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, Function.Embedding.coe_refl, id_eq,
      work, update2, update3, h] <;> rfl

def numberInTime (field : Field) (base : Tape → List Bool) (n : Nat) (suffix : List Bool)
    (input : base (numberTapes field 0) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base (numberTapes field 2) = []) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core (.number field .scan))) base)
      (some (cfg (afterNumber FullLabel.core field)
        (ExtensionNatMachine.resultTapes (numberTapes field) base n suffix)))
      (2 * n.size + 2) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.core (.number field .scan)), BinaryAddMachine.clean ((), .eq), base⟩
    (some ⟨afterNumber FullLabel.core field, BinaryAddMachine.clean ((), .eq),
      ExtensionNatMachine.resultTapes (numberTapes field) base n suffix⟩) _
  exact ExtensionNatMachine.natInTime (numberTapes field)
    (fun phase => FullLabel.core (.number field phase))
    (afterNumber FullLabel.core field) (cleanupEntry false) program (fun _ => rfl)
    base n suffix input scratchEmpty ((), .eq)

def parseRowInTime (N D selected : List Bool) (items assignments : List Bool) (a d j : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core (.number .numerator .scan)))
        (work N D (BinaryEncoding.natBits a ++ BinaryEncoding.natBits d ++ items)
          (BinaryEncoding.natBits j ++ assignments) selected [] [] [] [] []))
      (some (cfg (some (.core (.compare .label .leftOut)))
        (work N D items assignments selected a.bits d.bits j.bits [] [])))
      ((2 * a.size + 2) + (2 * d.size + 2) + (2 * j.size + 2)) := by
  have first := numberInTime .numerator
    (work N D (BinaryEncoding.natBits a ++ BinaryEncoding.natBits d ++ items)
      (BinaryEncoding.natBits j ++ assignments) selected [] [] [] [] [])
    a (BinaryEncoding.natBits d ++ items) (by simp [numberTapes, work, List.append_assoc]) rfl
  have second := numberInTime .denominator
    (work N D (BinaryEncoding.natBits d ++ items)
      (BinaryEncoding.natBits j ++ assignments) selected a.bits [] [] [] []) d items rfl rfl
  have third := numberInTime .label
    (work N D items (BinaryEncoding.natBits j ++ assignments) selected a.bits d.bits [] [] [])
    j assignments rfl rfl
  simp only [numberTapes, afterNumber, ExtensionNatMachine.resultTapes,
    Function.Embedding.coeFn_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    update2, update3, update5, update6, update7, work, List.append_nil] at first second third
  exact join (join first second) third

def compareInTime (which : Compare) (base : Tape → List Bool) (a b : Nat)
    (leftWord : base (compareTapes which 0) = a.bits)
    (rightWord : base (compareTapes which 1) = b.bits)
    (leftEmpty : base (compareTapes which 2) = [])
    (rightEmpty : base (compareTapes which 3) = [])
    (scratchEmpty : base (compareTapes which 4) = []) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core (.compare which .leftOut))) base)
      (some (cfg (comparisonExits FullLabel.core (cleanupEntry false) which
        (BinaryOrderMachine.orderNat a b .eq)) base))
      (BinaryOrderMachine.preservingSteps a.size b.size) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.core (.compare which .leftOut)), BinaryAddMachine.clean ((), .eq), base⟩
    (some ⟨comparisonExits FullLabel.core (cleanupEntry false) which
      (BinaryOrderMachine.orderNat a b .eq), BinaryAddMachine.clean ((), .eq), base⟩) _
  exact ExtensionNatMachine.preservingOrderInTime (compareTapes which)
    (fun phase => FullLabel.core (.compare which phase))
    (comparisonExits FullLabel.core (cleanupEntry false) which)
    program (fun _ => rfl) base a b leftWord rightWord leftEmpty rightEmpty scratchEmpty ()

theorem labelComparisonExit (assigned selected : Nat) :
    comparisonExits FullLabel.core (cleanupEntry false) .label
        (BinaryOrderMachine.orderNat assigned selected .eq) =
      some (.core (if assigned = selected then .fraction (.multiply .leftNumerator .copyLeft)
        else .clearItemNumerator)) := by
  unfold BinaryOrderMachine.orderNat
  split_ifs <;> simp_all [comparisonExits]
  omega

theorem capacityComparisonExit (numerator denominator : Nat) :
    comparisonExits FullLabel.core (cleanupEntry false) .capacity
        (BinaryOrderMachine.orderNat numerator denominator .eq) =
      if numerator ≤ denominator then some (.core .clearOldNumerator) else cleanupEntry false := by
  unfold BinaryOrderMachine.orderNat
  split_ifs <;> simp_all [comparisonExits] <;> omega

noncomputable def fractionInTime (num den a d : Nat) (items assignments selected j : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core (.fraction (.multiply .leftNumerator .copyLeft))))
        (work num.bits den.bits items assignments selected a.bits d.bits j [] []))
      (some (cfg (some (.core (.compare .capacity .leftOut)))
        (work num.bits den.bits items assignments selected a.bits d.bits j
          (num * d + a * den).bits (den * d).bits)))
      (ExtensionFractionMachine.arithmeticBudget num den a d) := by
  have run := ExtensionFractionMachine.arithmeticInTime fractionTapes
    (fun phase => .core (.fraction phase)) (some (.core (.compare .capacity .leftOut)))
    program (fun _ => rfl)
    (work num.bits den.bits items assignments selected a.bits d.bits j [] [])
    num den a d rfl rfl rfl rfl
    (by intro i hi; fin_cases i <;> simp_all [fractionTapes, work]) ((), .eq)
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.core (.fraction (.multiply .leftNumerator .copyLeft))),
      BinaryAddMachine.clean ((), .eq),
      work num.bits den.bits items assignments selected a.bits d.bits j [] []⟩
    (some ⟨some (.core (.compare .capacity .leftOut)), BinaryAddMachine.clean ((), .eq),
      Function.update
        (Function.update (work num.bits den.bits items assignments selected a.bits d.bits j [] [])
          12 (den * d).bits) 11 (num * d + a * den).bits⟩) _ at run
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.core (.fraction (.multiply .leftNumerator .copyLeft))),
      BinaryAddMachine.clean ((), .eq),
      work num.bits den.bits items assignments selected a.bits d.bits j [] []⟩
    (some ⟨some (.core (.compare .capacity .leftOut)), BinaryAddMachine.clean ((), .eq),
      work num.bits den.bits items assignments selected a.bits d.bits j
        (num * d + a * den).bits (den * d).bits⟩) _
  simpa only [update11, update12] using run

def clearRowInTime (N D i w s a d j : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core .clearItemNumerator)) (work N D i w s a d j [] []))
      (some (cfg (some (.core .guard)) (work N D i w s [] [] [] [] [])))
      ((a.length + 1) + (d.length + 1) + (j.length + 1)) := by
  have first := MachineDrain.drainInTime (5 : Tape) (.core .clearItemNumerator)
    (some (.core .clearItemDenominator)) program rfl (work N D i w s a d j [] [])
    ((((), Ordering.eq), false), none) none
  have second := MachineDrain.drainInTime (6 : Tape) (.core .clearItemDenominator)
    (some (.core .clearItemLabel)) program rfl (work N D i w s [] d j [] [])
    ((((), Ordering.eq), false), none) none
  have third := MachineDrain.drainInTime (7 : Tape) (.core .clearItemLabel)
    (some (.core .guard)) program rfl (work N D i w s [] [] j [] [])
    ((((), Ordering.eq), false), none) none
  simp only [update5, work] at first
  simp only [update6, work] at second
  simp only [update7, work] at third
  exact join (join first second) third

def installInTime (N D i w s a d j U V : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.core .clearOldNumerator)) (work N D i w s a d j U V))
      (some (cfg (some (.core .clearItemNumerator)) (work U V i w s a d j [] [])))
      (N.length + D.length + 2 * U.length + 2 * V.length + 6) := by
  have oldN := MachineDrain.drainInTime (0 : Tape) (.core .clearOldNumerator)
    (some (.core .clearOldDenominator)) program rfl (work N D i w s a d j U V)
    ((((), Ordering.eq), false), none) none
  have oldD := MachineDrain.drainInTime (1 : Tape) (.core .clearOldDenominator)
    (some (.core .numeratorOut)) program rfl (work [] D i w s a d j U V)
    ((((), Ordering.eq), false), none) none
  have numOut := MachineTransfer.transferAtInTime (11 : Tape) 10 (by decide)
    id false (.core .numeratorOut) (some (.core .numeratorBack)) program rfl
    (work [] [] i w s a d j U V) ((((), Ordering.eq), false), none) none
  have numBack := MachineTransfer.transferAtInTime (10 : Tape) 0 (by decide)
    id false (.core .numeratorBack) (some (.core .denominatorOut)) program rfl
    (work [] [] i w s a d j [] V U.reverse) ((((), Ordering.eq), false), none) none
  have denOut := MachineTransfer.transferAtInTime (12 : Tape) 10 (by decide)
    id false (.core .denominatorOut) (some (.core .denominatorBack)) program rfl
    (work U [] i w s a d j [] V) ((((), Ordering.eq), false), none) none
  have denBack := MachineTransfer.transferAtInTime (10 : Tape) 1 (by decide)
    id false (.core .denominatorBack) (some (.core .clearItemNumerator)) program rfl
    (work U [] i w s a d j [] [] V.reverse) ((((), Ordering.eq), false), none) none
  simp only [update0, work] at oldN
  simp only [update1, work] at oldD
  simp only [MachineTransfer.tapesAt, update11, update10, work, List.map_id_fun,
    id_eq, List.append_nil] at numOut
  simp only [MachineTransfer.tapesAt, update10, update0, work, List.map_id_fun,
    id_eq, List.append_nil, List.reverse_reverse, List.length_reverse] at numBack
  simp only [MachineTransfer.tapesAt, update12, update10, work, List.map_id_fun,
    id_eq, List.append_nil] at denOut
  simp only [MachineTransfer.tapesAt, update10, update1, work, List.map_id_fun,
    id_eq, List.append_nil, List.reverse_reverse, List.length_reverse] at denBack
  have joined := join (join (join (join (join oldN oldD) numOut) numBack) denOut) denBack
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.core .clearOldNumerator), BinaryAddMachine.clean ((), .eq), work N D i w s a d j U V⟩
    (some ⟨some (.core .clearItemNumerator), BinaryAddMachine.clean ((), .eq),
      work U V i w s a d j [] []⟩) _
  exact { toEvalsTo := joined.toEvalsTo
          steps_le_m := by
            have bound := joined.steps_le_m
            omega }

end

end BinPackingGap.ExtensionCapacityMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionShapeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionShapeMachine

open BinaryEncoding
open BinPackingCompleteness.BinaryNameMachine (finalDigit canonical)

theorem accepts_eq_decode (kind : Kind) (input : List Bool) :
    accepts kind input = decodeAccepts kind input := by
  cases kind with
  | extension =>
      cases parsed : decodeExtension input with
      | none =>
          have rejected : run (start .extension) input ≠ .done := by
            intro accepted
            obtain ⟨bins, r, fixed, encoded⟩ := (run_extension_iff input).mp accepted
            have roundtrip := decodeExtension_extensionBits bins r fixed
            rw [← encoded, parsed] at roundtrip
            cases roundtrip
          simp [accepts, decodeAccepts, parsed, rejected]
      | some value =>
          rcases value with ⟨bins, r, fixed⟩
          have encoded := decodeExtension_sound parsed
          have accepted := (run_extension_iff input).mpr ⟨bins, r, fixed, encoded⟩
          simp [accepts, decodeAccepts, parsed, accepted]
  | assignments =>
      cases parsed : decodeAssignments input with
      | none =>
          have rejected : run (start .assignments) input ≠ .done := by
            intro accepted
            obtain ⟨a, encoded⟩ := (run_assignments_iff input).mp accepted
            have roundtrip := decodeAssignments_assignmentBits a
            rw [← encoded, parsed] at roundtrip
            cases roundtrip
          simp [accepts, decodeAccepts, parsed, rejected]
      | some a =>
          have encoded := decodeAssignments_sound parsed
          have accepted := (run_assignments_iff input).mpr ⟨a, encoded⟩
          simp [accepts, decodeAccepts, parsed, accepted]

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution

theorem totalTrace (kind : Kind) (input : List Bool) :
    (advance (machine kind).step)^[2 * input.length + 3]
      (some (initList (machine kind) input)) =
      some (haltList (machine kind) (decodeAccepts kind input :: input)) := by
  rw [initList_eq, haltList_eq]
  simpa only [accepts_eq_decode] using rawTrace kind input

def outputsInTime (kind : Kind) (input : List Bool) :
    TM2OutputsInTime (machine kind) input (some (decodeAccepts kind input :: input))
      (2 * input.length + 3) where
  steps := 2 * input.length + 3
  evals_in_steps := totalTrace kind input
  steps_le_m := Nat.le_refl _

end BinPackingGap.ExtensionShapeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionValidationMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionValidationMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition

def validRows (bins : Nat) : RawInstance → List Nat → Bool
  | [], [] => true
  | (numerator, denominator) :: items, label :: assignments =>
      decide (0 < numerator) && (decide (numerator ≤ denominator) &&
        (decide (label < bins) && validRows bins items assignments))
  | _, _ => false

theorem validRows_eq (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    validRows bins items assignments =
      (ExtensionCertificate.validItems items &&
        (decide (assignments.length = items.length) &&
          assignments.all (fun label => decide (label < bins)))) := by
  induction items generalizing assignments with
  | nil => cases assignments <;> simp [validRows, ExtensionCertificate.validItems]
  | cons item items ih =>
      rcases item with ⟨numerator, denominator⟩
      cases assignments <;>
        simp [validRows, ExtensionCertificate.validItems, ih, Bool.and_assoc,
          Bool.and_comm, Bool.and_left_comm]

def program : Label → TM2.Stmt Alphabet Label State
  | .control phase => controlInstruction phase
  | .number call phase => ExtensionNatMachine.statement (scanPorts call)
      (Label.number call) (some (scanSuccess call)) (some (.control .reject)) phase
  | .order call phase => ExtensionNatMachine.orderStatement (orderPorts call)
      (Label.order call) (orderExit call) phase

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := .number .bins .scan
  σ := State
  initialState := clean
  m := program

def cfg (label : Label) (base : Tape → List Bool) : machine.Cfg :=
  ⟨some label, clean, base⟩

def ready (bins : Nat) (items : RawInstance) (assignments : List Nat) : Tape → List Bool :=
  work bins.bits (BinaryEncoding.rawInstanceBits items)
    (BinaryEncoding.assignmentBits assignments) [] [] []

def oneStep {start finish : machine.Cfg}
    (step : machine.step start = some finish) :
    StateTransition.EvalsToInTime machine.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    change machine.step start = some finish
    exact step
  steps_le_m := Nat.le_refl _

def join {start middle finish : machine.Cfg} {firstTime secondTime : Nat}
    (first : StateTransition.EvalsToInTime machine.step start (some middle) firstTime)
    (second : StateTransition.EvalsToInTime machine.step middle (some finish) secondTime) :
    StateTransition.EvalsToInTime machine.step start (some finish) (firstTime + secondTime) := by
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans machine.step firstTime secondTime
      start middle (some finish) first second

def enlarge {start finish : machine.Cfg} {time budget : Nat}
    (run : StateTransition.EvalsToInTime machine.step start (some finish) time)
    (bounded : time ≤ budget) :
    StateTransition.EvalsToInTime machine.step start (some finish) budget where
  toEvalsTo := run.toEvalsTo
  steps_le_m := Nat.le_trans run.steps_le_m bounded

def scanInTime (call : ScanCall) (base : Tape → List Bool) (n : Nat) (suffix : List Bool)
    (input : base (scanSource call) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base 7 = []) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.number call .scan) base)
      (some (cfg (scanSuccess call)
        (ExtensionNatMachine.resultTapes (scanPorts call) base n suffix)))
      (2 * n.size + 2) :=
  ExtensionNatMachine.natInTime (scanPorts call) (Label.number call)
    (some (scanSuccess call)) (some (.control .reject)) program (fun _ => rfl)
    base n suffix input scratchEmpty ((), .eq)

def orderInTime (call : OrderCall) (base : Tape → List Bool) (a b : Nat)
    (leftWord : base (orderPorts call 0) = a.bits)
    (rightWord : base (orderPorts call 1) = b.bits)
    (leftEmpty : base 8 = []) (rightEmpty : base 9 = []) (scratchEmpty : base 7 = []) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.order call .leftOut) base)
      (some ⟨orderExit call (BinaryOrderMachine.orderNat a b .eq), clean, base⟩)
      (BinaryOrderMachine.preservingSteps a.size b.size) :=
  ExtensionNatMachine.preservingOrderInTime (orderPorts call) (Label.order call)
    (orderExit call) program (fun _ => rfl) base a b leftWord rightWord
    leftEmpty rightEmpty scratchEmpty ()

theorem markerStep (left right : Bool) (b i a n d j : List Bool) :
    machine.step (cfg (.control .marker) (work b (left :: i) (right :: a) n d j)) =
      some (cfg (if left = right then
        if left then .number .numerator .scan else .control .endCheck
        else .control .reject) (work b i a n d j)) := by
  cases left <;> cases right <;>
    change some (TM2.stepAux (program (.control .marker)) _ _) = _ <;>
    simp [program, controlInstruction, jump, cfg, clean, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, update_items, update_assignments, work]
  all_goals rfl

theorem boundEndStep (b i a n d j : List Bool) :
    machine.step (cfg (.control .boundEnd) (work b i a n d j)) =
      some (cfg (.control .marker) (work b i a n d j)) := by
  change some (TM2.stepAux (program (.control .boundEnd)) _ _) = _
  simp [program, controlInstruction, jump, cfg, clean, BinaryAddMachine.clean,
    BinaryAddMachine.state, TM2.stepAux, work]
  congr 1
  congr 1
  funext k
  fin_cases k <;> simp [work]

theorem positiveStep (b i a n d j : List Bool) :
    machine.step (cfg (.control .positive) (work b i a n d j)) =
      some (cfg (if n = [] then .control .reject else .number .denominator .scan)
        (work b i a n d j)) := by
  cases n <;>
    change some (TM2.stepAux (program (.control .positive)) _ _) = _ <;>
    simp [program, controlInstruction, jump, cfg, clean, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, update_numerator, work]
  all_goals rfl

theorem endStep (b n d j : List Bool) :
    machine.step (cfg (.control .endCheck) (work b [] [] n d j)) =
      some (cfg (.control .accept) (work b [] [] n d j)) := by
  change some (TM2.stepAux (program (.control .endCheck)) _ _) = _
  simp [program, controlInstruction, jump, cfg, clean, BinaryAddMachine.clean,
    BinaryAddMachine.state, TM2.stepAux, update_items, update_assignments, work]
  all_goals rfl

def clearInTime (b i a n d j : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.control .clearNumerator) (work b i a n d j))
      (some (cfg (.control .marker) (work b i a [] [] [])))
      ((n.length + 1) + (d.length + 1) + (j.length + 1)) := by
  have first := MachineDrain.drainInTime (4 : Tape) (.control .clearNumerator)
    (some (.control .clearDenominator)) program rfl (work b i a n d j)
    ((((), Ordering.eq), false), none) none
  have second := MachineDrain.drainInTime (5 : Tape) (.control .clearDenominator)
    (some (.control .clearAssigned)) program rfl (work b i a [] d j)
    ((((), Ordering.eq), false), none) none
  have third := MachineDrain.drainInTime (6 : Tape) (.control .clearAssigned)
    (some (.control .marker)) program rfl (work b i a [] [] j)
    ((((), Ordering.eq), false), none) none
  simp only [update_numerator, work] at first
  simp only [update_denominator, work] at second
  simp only [update_assigned, work] at third
  exact join (join first second) third

def numeratorInTime (b suffix assignments : List Bool) (n : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.number .numerator .scan)
        (work b (BinaryEncoding.natBits n ++ suffix) assignments [] [] []))
      (some (cfg (.control .positive) (work b suffix assignments n.bits [] [])))
      (2 * n.size + 2) := by
  simpa only [scanPorts_apply, scanTape, scanSource, scanOutput, Function.Embedding.coeFn_mk,
    ExtensionNatMachine.resultTapes, update_items, update_numerator, work,
    List.append_nil, scanSuccess] using!
    scanInTime .numerator (work b (BinaryEncoding.natBits n ++ suffix) assignments [] [] [])
      n suffix rfl rfl

def denominatorInTime (b suffix assignments : List Bool) (n d : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.number .denominator .scan)
        (work b (BinaryEncoding.natBits d ++ suffix) assignments n.bits [] []))
      (some (cfg (.order .fraction .leftOut) (work b suffix assignments n.bits d.bits [])))
      (2 * d.size + 2) := by
  simpa only [scanPorts_apply, scanTape, scanSource, scanOutput, Function.Embedding.coeFn_mk,
    ExtensionNatMachine.resultTapes, update_items, update_denominator, work,
    List.append_nil, scanSuccess] using!
    scanInTime .denominator
      (work b (BinaryEncoding.natBits d ++ suffix) assignments n.bits [] []) d suffix rfl rfl

def assignedInTime (b items suffix : List Bool) (n d j : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.number .assigned .scan)
        (work b items (BinaryEncoding.natBits j ++ suffix) n.bits d.bits []))
      (some (cfg (.order .bound .leftOut) (work b items suffix n.bits d.bits j.bits)))
      (2 * j.size + 2) := by
  simpa only [scanPorts_apply, scanTape, scanSource, scanOutput, Function.Embedding.coeFn_mk,
    ExtensionNatMachine.resultTapes, update_assignments, update_assigned, work,
    List.append_nil, scanSuccess] using!
    scanInTime .assigned
      (work b items (BinaryEncoding.natBits j ++ suffix) n.bits d.bits []) j suffix rfl rfl

structure LoopRun (bins : Nat) (items : RawInstance) (assignments : List Nat) where
  finish : Tape → List Bool
  bound_preserved : finish 3 = bins.bits
  input_empty : finish 0 = []
  accepted_clean : validRows bins items assignments = true →
    finish = work bins.bits [] [] [] [] []
  execution : StateTransition.EvalsToInTime machine.step
    (cfg (.control .marker) (ready bins items assignments))
    (some (cfg (.control (if validRows bins items assignments then .accept else .reject)) finish))
    (loopTime bins items assignments)

def rowsInTime (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    LoopRun bins items assignments := by
  induction items generalizing assignments with
  | nil =>
      cases assignments with
      | nil =>
          refine ⟨work bins.bits [] [] [] [] [], rfl, rfl, (fun _ => rfl), ?_⟩
          have first := oneStep (markerStep false false bins.bits [] [] [] [] [])
          have second := oneStep (endStep bins.bits [] [] [])
          simpa [ready, BinaryEncoding.rawInstanceBits, BinaryEncoding.assignmentBits,
            BinaryEncoding.listBits, validRows, loopTime, Bool.false_eq_true,
            ↓reduceIte] using join first second
      | cons j assignments =>
          let tail := BinaryEncoding.natBits j ++ BinaryEncoding.assignmentBits assignments
          refine ⟨work bins.bits [] tail [] [] [], rfl, rfl, by simp [validRows], ?_⟩
          have step := oneStep (markerStep false true bins.bits [] tail [] [] [])
          simpa [ready, BinaryEncoding.rawInstanceBits, BinaryEncoding.assignmentBits,
            BinaryEncoding.listBits, validRows, loopTime, tail, Bool.false_eq_true,
            ↓reduceIte] using enlarge step (by omega : 1 ≤ 2)
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      cases assignments with
      | nil =>
          let tail := BinaryEncoding.natBits a ++
            (BinaryEncoding.natBits d ++ BinaryEncoding.rawInstanceBits items)
          refine ⟨work bins.bits tail [] [] [] [], rfl, rfl, by simp [validRows], ?_⟩
          have step := oneStep (markerStep true false bins.bits tail [] [] [] [])
          simpa [ready, BinaryEncoding.rawInstanceBits, BinaryEncoding.assignmentBits,
            BinaryEncoding.listBits, BinaryEncoding.pairBits, validRows, loopTime, tail,
            Bool.false_eq_true, ↓reduceIte, List.append_assoc] using
            enlarge step (by omega : 1 ≤ 2)
      | cons j assignments =>
          let itemTail := BinaryEncoding.rawInstanceBits items
          let labelTail := BinaryEncoding.assignmentBits assignments
          let dstream := BinaryEncoding.natBits d ++ itemTail
          let jstream := BinaryEncoding.natBits j ++ labelTail
          have marker : StateTransition.EvalsToInTime machine.step
              (cfg (.control .marker) (ready bins ((a, d) :: items) (j :: assignments)))
              (some (cfg (.number .numerator .scan)
                (work bins.bits (BinaryEncoding.natBits a ++ dstream) jstream [] [] []))) 1 := by
            simpa [ready, BinaryEncoding.rawInstanceBits, BinaryEncoding.assignmentBits,
              BinaryEncoding.listBits, BinaryEncoding.pairBits, itemTail, labelTail,
              dstream, jstream, ↓reduceIte, List.append_assoc] using
              oneStep (markerStep true true bins.bits
                (BinaryEncoding.natBits a ++ dstream) jstream [] [] [])
          have numerator := numeratorInTime bins.bits dstream jstream a
          have positive := oneStep (positiveStep bins.bits dstream jstream a.bits [] [])
          simp only [bits_eq_nil_iff] at positive
          have initialRun := join (join marker numerator) positive
          by_cases zero : a = 0
          · refine ⟨work bins.bits dstream jstream a.bits [] [], rfl, rfl,
              by simp [validRows, zero], ?_⟩
            simpa only [validRows, zero, Nat.lt_irrefl, decide_false, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte, cfg] using enlarge
                (budget := loopTime bins ((a, d) :: items) (j :: assignments)) initialRun
                (by simp only [loopTime, rowBudget]; omega)
          · have apos : 0 < a := Nat.pos_of_ne_zero zero
            rw [ite_eq_right zero] at initialRun
            have denominator := denominatorInTime bins.bits itemTail jstream a d
            have fraction := orderInTime .fraction
              (work bins.bits itemTail jstream a.bits d.bits []) a d rfl rfl rfl rfl rfl
            rw [fractionExit] at fraction
            have fractionPrefix := join (join initialRun denominator) fraction
            have fractionBound := BinaryOrderMachine.preservingSteps_le a.size d.size
            by_cases fits : a ≤ d
            · rw [ite_eq_left fits] at fractionPrefix
              have assigned := assignedInTime bins.bits itemTail labelTail a d j
              have bounded := orderInTime .bound
                (work bins.bits itemTail labelTail a.bits d.bits j.bits) j bins
                rfl rfl rfl rfl rfl
              rw [boundExit] at bounded
              have boundPrefix := join (join fractionPrefix assigned) bounded
              have labelBound := BinaryOrderMachine.preservingSteps_le j.size bins.size
              by_cases validLabel : j < bins
              · rw [ite_eq_left validLabel] at boundPrefix
                have clear := clearInTime bins.bits itemTail labelTail a.bits d.bits j.bits
                have clearTime : (a.bits.length + 1) + (d.bits.length + 1) +
                    (j.bits.length + 1) = a.size + d.size + j.size + 3 := by
                  simp only [← Nat.size_eq_bits_len]
                  omega
                rw [clearTime] at clear
                let later := ih assignments
                have acceptedClean : validRows bins ((a, d) :: items) (j :: assignments) = true →
                    later.finish = work bins.bits [] [] [] [] [] := by
                  intro h
                  apply later.accepted_clean
                  simpa [validRows, apos, fits, validLabel] using h
                refine ⟨later.finish, later.bound_preserved, later.input_empty, acceptedClean, ?_⟩
                have full := join (join boundPrefix clear) later.execution
                have timeBound :
                    (((((1 + (2 * a.size + 2)) + 1) + (2 * d.size + 2)) +
                      BinaryOrderMachine.preservingSteps a.size d.size) + (2 * j.size + 2)) +
                        BinaryOrderMachine.preservingSteps j.size bins.size +
                        (a.size + d.size + j.size + 3) + loopTime bins items assignments ≤
                      loopTime bins ((a, d) :: items) (j :: assignments) := by
                  simp only [loopTime, rowBudget]
                  omega
                simpa only [validRows, apos, fits, validLabel, decide_true, Bool.true_and,
                  ↓reduceIte] using enlarge full timeBound
              · refine ⟨work bins.bits itemTail labelTail a.bits d.bits j.bits, rfl, rfl,
                  by simp [validRows, apos, fits, validLabel], ?_⟩
                simpa only [validRows, apos, fits, validLabel, decide_true, decide_false,
                  Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte, cfg] using enlarge
                    (budget := loopTime bins ((a, d) :: items) (j :: assignments)) boundPrefix
                    (by simp only [loopTime, rowBudget]; omega)
            · refine ⟨work bins.bits itemTail jstream a.bits d.bits [], rfl, rfl,
                by simp [validRows, apos, fits], ?_⟩
              simpa only [validRows, apos, fits, decide_true, decide_false,
                Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte, cfg] using enlarge
                  (budget := loopTime bins ((a, d) :: items) (j :: assignments)) fractionPrefix
                  (by simp only [loopTime, rowBudget]; omega)

theorem loopTime_le (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    loopTime bins items assignments ≤ 10 * (bins.size + 1) *
      ((BinaryEncoding.rawInstanceBits items).length +
        (BinaryEncoding.assignmentBits assignments).length + 1) := by
  induction items generalizing assignments with
  | nil =>
      exact base_budget bins.size _
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      cases assignments with
      | nil => exact base_budget bins.size _
      | cons j assignments =>
          have hlen : (BinaryEncoding.rawInstanceBits ((a, d) :: items)).length +
                (BinaryEncoding.assignmentBits (j :: assignments)).length + 1 =
              (2 * (a.size + d.size + j.size) + 5) +
                ((BinaryEncoding.rawInstanceBits items).length +
                  (BinaryEncoding.assignmentBits assignments).length + 1) := by
            simp only [BinaryEncoding.rawInstanceBits_length,
              BinaryEncoding.assignmentBits_length, List.map_cons, List.sum_cons]
            omega
          rw [loopTime, hlen, Nat.mul_add]
          exact Nat.add_le_add
            (by simpa only [rowBudget] using
              row_budget bins.size (a.size + d.size + j.size))
            (ih assignments)

def inputTapes (bins : Nat) (items : RawInstance) (assignments : List Nat) : Tape → List Bool :=
  Function.update (work [] (BinaryEncoding.rawInstanceBits items)
    (BinaryEncoding.assignmentBits assignments) [] [] []) 0 (BinaryEncoding.natBits bins)

def initializeInTime (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (.number .bins .scan) (inputTapes bins items assignments))
      (some (cfg (.control .marker) (ready bins items assignments)))
      (2 * bins.size + 3) := by
  have scanned := scanInTime .bins (inputTapes bins items assignments) bins []
    (by simp [inputTapes, scanSource]) (by simp [inputTapes, work])
  have result : ExtensionNatMachine.resultTapes (scanPorts .bins)
      (inputTapes bins items assignments) bins [] = ready bins items assignments := by
    funext k
    fin_cases k <;> simp [ExtensionNatMachine.resultTapes, scanTape,
      scanSource, scanOutput, inputTapes, ready, work]
    change Function.update (β := fun _ => List Bool) _ (scanPorts .bins 1) bins.bits (scanPorts .bins 1) = bins.bits
    exact Function.update_self _ _ _
  rw [result] at scanned
  have finished := oneStep (boundEndStep bins.bits
    (BinaryEncoding.rawInstanceBits items) (BinaryEncoding.assignmentBits assignments) [] [] [])
  have full := join scanned finished
  simpa [scanSuccess, ready, Nat.add_assoc] using full

def inputLength (bins : Nat) (items : RawInstance) (assignments : List Nat) : Nat :=
  (BinaryEncoding.natBits bins).length + (BinaryEncoding.rawInstanceBits items).length +
    (BinaryEncoding.assignmentBits assignments).length

theorem totalTime_le (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    2 * bins.size + 3 + loopTime bins items assignments + 1 ≤
      validationTime.eval (inputLength bins items assignments) := by
  simpa only [validationTime, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat,
    inputLength, BinaryEncoding.natBits_length] using
    total_budget bins.size (BinaryEncoding.rawInstanceBits items).length
      (BinaryEncoding.assignmentBits assignments).length (loopTime bins items assignments)
      (loopTime_le bins items assignments)

theorem flagStep (accepted : Bool) (base : Tape → List Bool) (empty : base 0 = []) :
    machine.step (cfg (.control (if accepted then .accept else .reject)) base) =
      some ⟨none, clean, Function.update base 0 [accepted]⟩ := by
  cases accepted with
  | false =>
      change some (TM2.stepAux (program (.control .reject)) clean base) = _
      simp [program, controlInstruction, TM2.stepAux, empty]
      rfl
  | true =>
      change some (TM2.stepAux (program (.control .accept)) clean base) = _
      simp [program, controlInstruction, TM2.stepAux, empty]
      rfl

structure ValidationRun (bins : Nat) (items : RawInstance) (assignments : List Nat) where
  finish : Tape → List Bool
  flag : finish 0 = [validRows bins items assignments]
  bound_preserved : finish 3 = bins.bits
  accepted_clean : validRows bins items assignments = true →
    finish = Function.update (work bins.bits [] [] [] [] []) 0 [true]
  execution : StateTransition.EvalsToInTime machine.step
    (cfg (.number .bins .scan) (inputTapes bins items assignments))
    (some ⟨none, clean, finish⟩) (validationTime.eval (inputLength bins items assignments))

noncomputable def validationInTime (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    ValidationRun bins items assignments := by
  let rows := rowsInTime bins items assignments
  let final := Function.update rows.finish 0 [validRows bins items assignments]
  refine ⟨final, by simp [final], ?_, ?_, ?_⟩
  · simpa only [final, Function.update_of_ne (by decide : (3 : Tape) ≠ 0)] using
      rows.bound_preserved
  · intro accepted
    change Function.update rows.finish 0 [validRows bins items assignments] = _
    rw [rows.accepted_clean accepted, accepted]
  · have first := initializeInTime bins items assignments
    have last := oneStep (flagStep (validRows bins items assignments) rows.finish rows.input_empty)
    exact enlarge (join (join first rows.execution) last) (totalTime_le bins items assignments)

end BinPackingGap.ExtensionValidationMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionVerifierPipeline
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionCapacityMachine

open Turing
open BinPackingGames.Foundations.Complexity

structure CoreRun (items : RawInstance) (assignments : List Nat)
    (selected num den B : Nat) where
  finish : Tape → List Bool
  bounded : ∀ k, (finish k).length ≤ B + 2
  execution : StateTransition.EvalsToInTime machine.step
    (cfg (some (.core .guard)) (ready num den selected items assignments))
    (some (cfg (cleanupEntry (CapacityScan.scan selected items assignments (num, den))) finish))
    ((items.length + 1) * (1024 * (B + 1) ^ 2))

noncomputable def coreRun (items : RawInstance) (assignments : List Nat)
    (selected num den B : Nat)
    (valid : items.Valid) (sameLength : assignments.length = items.length)
    (fits : num ≤ den)
    (denBudget : den.size + FractionWidth.denominatorBits items ≤ B + 1)
    (itemBound : (BinaryEncoding.rawInstanceBits items).length ≤ B)
    (assignmentBound : (BinaryEncoding.assignmentBits assignments).length ≤ B)
    (selectedBound : selected.size ≤ B) : CoreRun items assignments selected num den B := by
  induction items generalizing assignments num den with
  | nil =>
      have assignmentsNil : assignments = [] := by
        cases assignments with
        | nil => rfl
        | cons head tail => simp at sameLength
      subst assignments
      have hden : den.size ≤ B + 1 := by simpa using denBudget
      have hnum : num.size ≤ B + 1 := (FractionWidth.size_mono fits).trans hden
      refine ⟨work num.bits den.bits [] [] selected.bits [] [] [] [] [], ?_, ?_⟩
      · apply workBound <;> simp only [List.length_nil, Nat.size_eq_bits_len] <;> omega
      · have step := oneStep (guard_nil_step num.bits den.bits selected.bits)
        have time : 1 ≤ (0 + 1) * (1024 * (B + 1) ^ 2) := by
          have positive : 0 < 1024 * (B + 1) ^ 2 := by positivity
          simpa only [Nat.zero_add, Nat.one_mul] using Nat.succ_le_of_lt positive
        simpa [ready, BinaryEncoding.rawInstanceBits, BinaryEncoding.assignmentBits,
          BinaryEncoding.listBits, CapacityScan.scan, fits] using enlarge step time
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      cases assignments with
      | nil => simp at sameLength
      | cons assigned assignments =>
          have validTail : RawInstance.Valid items := fun q hq => valid q (List.mem_cons_of_mem _ hq)
          have sizeTail : assignments.length = items.length := by simpa using sameLength
          have itemValid := valid (a, d) (List.mem_cons_self ..)
          have aq : a ≤ d := itemValid.2
          have hden : den.size + d.size ≤ B + 1 := by
            simp only [FractionWidth.denominatorBits_cons] at denBudget
            omega
          have hnum := FractionWidth.size_mono fits
          have ha := FractionWidth.size_mono aq
          have itemTailBound : (BinaryEncoding.rawInstanceBits items).length ≤ B := by
            simp only [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
              BinaryEncoding.pairBits, List.length_cons, List.length_append] at itemBound ⊢
            omega
          have assignmentTailBound : (BinaryEncoding.assignmentBits assignments).length ≤ B := by
            simp only [BinaryEncoding.assignmentBits, BinaryEncoding.listBits,
              List.length_cons, List.length_append] at assignmentBound ⊢
            omega
          have assignedBound : assigned.size ≤ B := by
            simp only [BinaryEncoding.assignmentBits, BinaryEncoding.listBits,
              List.length_cons, List.length_append, BinaryEncoding.natBits_length] at assignmentBound
            omega
          have tailDenBudget : den.size + FractionWidth.denominatorBits items ≤ B + 1 := by
            simp only [FractionWidth.denominatorBits_cons] at denBudget
            omega
          let itemWord := BinaryEncoding.rawInstanceBits items
          let assignmentWord := BinaryEncoding.assignmentBits assignments
          have guard := oneStep (guard_cons_step num.bits den.bits
            (BinaryEncoding.natBits a ++ BinaryEncoding.natBits d ++ itemWord)
            (BinaryEncoding.natBits assigned ++ assignmentWord) selected.bits [] [] [] [] [])
          have parsed := parseRowInTime num.bits den.bits selected.bits itemWord assignmentWord
            a d assigned
          have compared := compareInTime .label
            (work num.bits den.bits itemWord assignmentWord selected.bits a.bits d.bits
              assigned.bits [] []) assigned selected rfl rfl rfl rfl rfl
          rw [labelComparisonExit] at compared
          have rowPrefix := join (join guard parsed) compared
          have rowBound := rowCost_le num den a d assigned selected B fits aq hden
            assignedBound selectedBound
          have count : (((a, d) :: items).length + 1) * (1024 * (B + 1) ^ 2) =
              1024 * (B + 1) ^ 2 + (items.length + 1) * (1024 * (B + 1) ^ 2) := by
            simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
            omega
          by_cases matched : assigned = selected
          · rw [ite_eq_left matched] at rowPrefix
            have arithmetic := fractionInTime num den a d itemWord assignmentWord selected.bits assigned.bits
            have capacity := compareInTime .capacity
              (work num.bits den.bits itemWord assignmentWord selected.bits a.bits d.bits assigned.bits
                (num * d + a * den).bits (den * d).bits)
              (num * d + a * den) (den * d) rfl rfl rfl rfl rfl
            rw [capacityComparisonExit] at capacity
            have tested := join (join rowPrefix arithmetic) capacity
            have newDenBound := FractionWidth.addFraction_den_size_le (num, den) (a, d)
            have newNumBound := FractionWidth.addFraction_num_size_le
              (x := (num, den)) (q := (a, d)) fits aq
            change (den * d).size ≤ den.size + d.size at newDenBound
            change (num * d + a * den).size ≤ den.size + d.size + 1 at newNumBound
            by_cases accepted : num * d + a * den ≤ den * d
            · rw [ite_eq_left accepted] at tested
              have installed := installInTime num.bits den.bits itemWord assignmentWord selected.bits
                a.bits d.bits assigned.bits (num * d + a * den).bits (den * d).bits
              have cleared := clearRowInTime (num * d + a * den).bits (den * d).bits
                itemWord assignmentWord selected.bits a.bits d.bits assigned.bits
              have nextDenBudget : (den * d).size + FractionWidth.denominatorBits items ≤ B + 1 := by
                simp only [FractionWidth.denominatorBits_cons] at denBudget
                omega
              let later := ih assignments (num * d + a * den) (den * d) validTail sizeTail accepted
                nextDenBudget itemTailBound assignmentTailBound
              refine ⟨later.finish, later.bounded, ?_⟩
              have full := join (join (join tested installed) cleared) later.execution
              have sizeWords : num.bits.length = num.size ∧ den.bits.length = den.size ∧
                  a.bits.length = a.size ∧ d.bits.length = d.size ∧
                  assigned.bits.length = assigned.size ∧
                  (num * d + a * den).bits.length = (num * d + a * den).size ∧
                  (den * d).bits.length = (den * d).size := by
                simp only [Nat.size_eq_bits_len, and_self]
              rcases sizeWords with ⟨wN, wD, wa, wd, wj, wU, wV⟩
              have bounded :
                  (((((1 + ((2 * a.size + 2) + (2 * d.size + 2) +
                    (2 * assigned.size + 2))) +
                    BinaryOrderMachine.preservingSteps assigned.size selected.size) +
                    ExtensionFractionMachine.arithmeticBudget num den a d) +
                    BinaryOrderMachine.preservingSteps (num * d + a * den).size (den * d).size) +
                    (num.bits.length + den.bits.length + 2 * (num * d + a * den).bits.length +
                      2 * (den * d).bits.length + 6)) +
                    ((a.bits.length + 1) + (d.bits.length + 1) + (assigned.bits.length + 1)) +
                    (items.length + 1) * (1024 * (B + 1) ^ 2) ≤
                    (((a, d) :: items).length + 1) * (1024 * (B + 1) ^ 2) := by
                rw [wN, wD, wa, wd, wj, wU, wV, count]
                unfold rowCost at rowBound
                omega
              simpa only [ready, itemWord, assignmentWord, BinaryEncoding.rawInstanceBits,
                BinaryEncoding.assignmentBits, BinaryEncoding.listBits, BinaryEncoding.pairBits,
                CapacityScan.scan, ite_eq_left fits, CapacityScan.step, ite_eq_left matched,
                RawPacking.addFraction] using enlarge full bounded
            · rw [ite_eq_right accepted] at tested
              refine ⟨work num.bits den.bits itemWord assignmentWord selected.bits a.bits d.bits
                assigned.bits (num * d + a * den).bits (den * d).bits, ?_, ?_⟩
              · apply workBound <;>
                  simp only [Nat.size_eq_bits_len, itemWord, assignmentWord] <;> omega
              · have scanRejected := scan_overfull items assignments selected
                  (num * d + a * den) (den * d) (Nat.lt_of_not_ge accepted)
                have bounded :
                    (((1 + ((2 * a.size + 2) + (2 * d.size + 2) + (2 * assigned.size + 2))) +
                      BinaryOrderMachine.preservingSteps assigned.size selected.size) +
                      ExtensionFractionMachine.arithmeticBudget num den a d) +
                      BinaryOrderMachine.preservingSteps (num * d + a * den).size (den * d).size ≤
                      (((a, d) :: items).length + 1) * (1024 * (B + 1) ^ 2) := by
                  rw [count]
                  unfold rowCost at rowBound
                  omega
                simpa only [ready, itemWord, assignmentWord, BinaryEncoding.rawInstanceBits,
                  BinaryEncoding.assignmentBits, BinaryEncoding.listBits, BinaryEncoding.pairBits,
                  CapacityScan.scan, ite_eq_left fits, CapacityScan.step, ite_eq_left matched,
                  RawPacking.addFraction, scanRejected] using enlarge tested bounded
          · rw [ite_eq_right matched] at rowPrefix
            have cleared := clearRowInTime num.bits den.bits itemWord assignmentWord selected.bits
              a.bits d.bits assigned.bits
            let later := ih assignments num den validTail sizeTail fits tailDenBudget
              itemTailBound assignmentTailBound
            refine ⟨later.finish, later.bounded, ?_⟩
            have full := join (join rowPrefix cleared) later.execution
            have bounded :
                ((1 + ((2 * a.size + 2) + (2 * d.size + 2) + (2 * assigned.size + 2))) +
                  BinaryOrderMachine.preservingSteps assigned.size selected.size) +
                  ((a.bits.length + 1) + (d.bits.length + 1) + (assigned.bits.length + 1)) +
                  (items.length + 1) * (1024 * (B + 1) ^ 2) ≤
                  (((a, d) :: items).length + 1) * (1024 * (B + 1) ^ 2) := by
              simp only [Nat.size_eq_bits_len]
              rw [count]
              unfold rowCost at rowBound
              omega
            simpa only [ready, itemWord, assignmentWord, BinaryEncoding.rawInstanceBits,
              BinaryEncoding.assignmentBits, BinaryEncoding.listBits, BinaryEncoding.pairBits,
              CapacityScan.scan, ite_eq_left fits, CapacityScan.step, ite_eq_right matched] using
              enlarge full bounded

noncomputable def innerInPolynomialTime (items : RawInstance) (assignments : List Nat)
    (selected : Nat) (valid : items.Valid) (sameLength : assignments.length = items.length) :
    StateTransition.EvalsToInTime machine.step
      (initialCfg items assignments selected)
      (some (finalCfg (CapacityScan.scan selected items assignments (0, 1))))
      (timePolynomial.eval (inputLength items assignments selected)) := by
  let B := inputLength items assignments selected
  have itemBound : (BinaryEncoding.rawInstanceBits items).length ≤ B := by
    simp only [B, inputLength]
    omega
  have assignmentBound : (BinaryEncoding.assignmentBits assignments).length ≤ B := by
    simp only [B, inputLength]
    omega
  have selectedBound : selected.size ≤ B := by
    simp only [B, inputLength]
    omega
  have denominatorBound : (1 : Nat).size + FractionWidth.denominatorBits items ≤ B + 1 := by
    have h := ExtensionWitness.denominatorBits_le_rawInstanceBits items
    change 1 + FractionWidth.denominatorBits items ≤ B + 1
    omega
  let core := coreRun items assignments selected 0 1 B valid sameLength (by decide)
    denominatorBound itemBound assignmentBound selectedBound
  have initialization := oneStep (initializeStep items assignments selected)
  have ready_eq : inputTapes (fun _ => []) 0 1 selected items assignments =
      ready 0 1 selected items assignments := by
    funext k
    fin_cases k <;> simp [inputTapes, ready, work]
  rw [ready_eq] at initialization
  have cleanup := cleanupInTime (CapacityScan.scan selected items assignments (0, 1)) core.finish
  have all := join (join initialization core.execution) cleanup
  have lengthBound (chosen : List Tape) :
      MachineDrainMany.lengthSum chosen core.finish ≤ chosen.length * (B + 2) := by
    induction chosen with
    | nil => simp [MachineDrainMany.lengthSum]
    | cons k chosen ih =>
        have hk := core.bounded k
        simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
          List.length_cons, Nat.add_mul, Nat.one_mul] at ih ⊢
        omega
  have cleanupBound : MachineDrainMany.lengthSum allTapes core.finish ≤ 22 * (B + 2) := by
    simpa only [allTapes, List.length_ofFn] using lengthBound allTapes
  have itemCount : items.length ≤ B :=
    (BinaryEncoding.list_length_le_bits_length
      (BinaryEncoding.pairBits BinaryEncoding.natBits BinaryEncoding.natBits) items).trans itemBound
  have coreBound : (items.length + 1) * (1024 * (B + 1) ^ 2) ≤ 1024 * (B + 1) ^ 3 := by
    have h := Nat.mul_le_mul_right (1024 * (B + 1) ^ 2)
      (Nat.add_le_add_right itemCount 1)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have powerBound : B + 1 ≤ (B + 1) ^ 3 := by
    have hsq : 1 ≤ (B + 1) ^ 2 := by
      have positive : 0 < (B + 1) ^ 2 := by positivity
      exact Nat.succ_le_of_lt positive
    have hm := Nat.mul_le_mul_left (B + 1) hsq
    nlinarith
  have budget :
      (1 + (items.length + 1) * (1024 * (B + 1) ^ 2)) +
        (MachineDrainMany.lengthSum allTapes core.finish + 23) ≤
        timePolynomial.eval B := by
    simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    omega
  exact enlarge all budget

end BinPackingGap.ExtensionCapacityMachine

namespace BinPackingGap.ExtensionCapacityOuterMachine

open Turing BinPackingGames.Foundations.Complexity BinPackingGames.Reduction

def innerTape (k : ExtensionCapacityMachine.machine.K) : Tape :=
  ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩

def innerView (k : Tape) : Option ExtensionCapacityMachine.machine.K :=
  if small : k.val < 22 then some ⟨k.val, small⟩ else none

theorem innerView_left (k : ExtensionCapacityMachine.machine.K) :
    innerView (innerTape k) = some k := by
  simp [innerView, innerTape, k.isLt]
  rfl

theorem innerView_right (j : Tape) (k : ExtensionCapacityMachine.machine.K)
    (found : innerView j = some k) : innerTape k = j := by
  unfold innerView at found
  split at found
  · have equal := Option.some.inj found
    apply Fin.ext
    exact (congrArg Fin.val equal).symm
  · contradiction

def afterCopy : CopyKind → Label
  | .outerLabels => .guard
  | .items => .copyOut .assignments
  | .assignments => .inner ExtensionCapacityMachine.machine.main

def cleanupEntry (result : Bool) : Option Label :=
  MachineDrainMany.entry allTapes (Label.cleanup result) (some (.emit result))

def program : Label → TM2.Stmt Alphabet Label State
  | .copyOut kind =>
      MachineTransfer.loopAt (copySource kind) 25 id false (.copyOut kind)
        (some (.copyBack kind))
  | .copyBack kind =>
      MachineCopy.forkLoop 25 (copySource kind) (copyDestination kind) false
        (.copyBack kind) (some (afterCopy kind))
  | .guard =>
      .pop 24 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.branch (fun state => state.2.getD false)
            (jump (.number .scan)) (finish (cleanupEntry true)))
          (finish (cleanupEntry false)))
  | .number phase =>
      ExtensionNatMachine.statement numberTapes Label.number
        (some (.copyOut .items)) (cleanupEntry false) phase
  | .inner phase =>
      ExtensionMachinePlacement.statement innerTape Label.inner (some .afterInner)
        (ExtensionMachineRegisters.Lens.identity State)
        (ExtensionCapacityMachine.machine.m phase)
  | .afterInner =>
      .pop 0 (fun state head => (state.1, head))
        (.branch (fun state => decide (state.2 = some true))
          (jump .guard) (finish (cleanupEntry false)))
  | .cleanup result phase =>
      MachineDrainMany.instruction allTapes (Label.cleanup result) (some (.emit result)) phase
  | .emit result => .load (fun _ => clean) (.push 0 (fun _ => result) .halt)

def machine : FinTM2 where
  K := Tape
  k₀ := 22
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := .copyOut .outerLabels
  σ := State
  initialState := clean
  m := program

def join {start middle finish : machine.Cfg} {firstTime secondTime : Nat}
    (first : StateTransition.EvalsToInTime machine.step start (some middle) firstTime)
    (second : StateTransition.EvalsToInTime machine.step middle (some finish) secondTime) :
    StateTransition.EvalsToInTime machine.step start (some finish) (firstTime + secondTime) := by
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans machine.step _ _ _ _ _ first second

def configuration (label : Option Label) (tapes : Tape → List Bool) : machine.Cfg :=
  ⟨label, clean, tapes⟩

def initialCfg (items : RawInstance) (assignments : List Nat) : machine.Cfg :=
  configuration (some machine.main) (initialTapes items assignments)

def finalCfg (result : Bool) : machine.Cfg := configuration none (resultTapes result)

theorem guardStep (base : Tape → List Bool) (bit : Bool) (tail : List Bool)
    (word : base 24 = bit :: tail) :
    machine.step (configuration (some .guard) base) =
      some (configuration
        (if bit then some (.number .scan) else cleanupEntry true)
        (Function.update base 24 tail)) := by
  cases bit <;> cases cleanup : cleanupEntry true <;>
    simp [FinTM2.step, machine, configuration, program, TM2.step, TM2.stepAux,
      word, jump, finish, cleanup] <;> rfl

theorem afterInnerStep (base : Tape → List Bool) (result : Bool)
    (word : base 0 = [result]) :
    machine.step (configuration (some .afterInner) base) =
      some (configuration (if result then some .guard else cleanupEntry false)
        (Function.update base 0 [])) := by
  cases result <;> cases cleanup : cleanupEntry false <;>
    simp [FinTM2.step, machine, configuration, program, TM2.step, TM2.stepAux,
      word, jump, finish, cleanup] <;> rfl

def copyInTime (kind : CopyKind) (base : Tape → List Bool)
    (scratchEmpty : base 25 = []) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some (.copyOut kind)) base)
      (some (configuration (some (afterCopy kind))
        (Function.update base (copyDestination kind)
          (base (copySource kind) ++ base (copyDestination kind)))))
      (2 * ((base (copySource kind)).length + 1)) := by
  have sourceDestination : copySource kind ≠ copyDestination kind := by cases kind <;> decide
  have sourceScratch : copySource kind ≠ 25 := by cases kind <;> decide
  have destinationScratch : copyDestination kind ≠ 25 := by cases kind <;> decide
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.copyOut kind), clean, base⟩
    (some ⟨some (afterCopy kind), clean,
      Function.update base (copyDestination kind)
        (base (copySource kind) ++ base (copyDestination kind))⟩) _
  exact MachineCopy.copyInTime (copySource kind) (copyDestination kind) 25
    sourceDestination sourceScratch destinationScratch false
    (.copyOut kind) (.copyBack kind) (some (afterCopy kind)) program rfl rfl
    base scratchEmpty ((((), .eq), false), none) none

def initialCopyInTime (items : RawInstance) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some (.copyOut .outerLabels)) (initialTapes items assignments))
      (some (configuration (some .guard) (stageTapes items assignments assignments)))
      (2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) := by
  have copied := copyInTime .outerLabels (initialTapes items assignments)
    (by simp [initialTapes, stageTapes])
  have original : initialTapes items assignments 23 = BinaryEncoding.assignmentBits assignments := by
    simp [initialTapes, stageTapes]
  have empty : initialTapes items assignments 24 = [] := by simp [initialTapes]
  have final : Function.update (initialTapes items assignments) 24
      (BinaryEncoding.assignmentBits assignments) = stageTapes items assignments assignments := by
    funext k
    by_cases selected : k = 24
    · subst k
      simp [stageTapes]
    · simp [initialTapes, stageTapes, selected]
  simpa only [copySource, copyDestination, afterCopy, original, empty, List.append_nil, final]
    using copied

def selectedInTime (base : Tape → List Bool) (selected : Nat) (remaining : List Nat)
    (word : base 24 = BinaryEncoding.natBits selected ++ BinaryEncoding.assignmentBits remaining)
    (scratchEmpty : base 25 = []) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some (.number .scan)) base)
      (some (configuration (some (.copyOut .items))
        (ExtensionNatMachine.resultTapes numberTapes base selected
          (BinaryEncoding.assignmentBits remaining))))
      (2 * selected.size + 2) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.number .scan), clean, base⟩
    (some ⟨some (.copyOut .items), clean,
      ExtensionNatMachine.resultTapes numberTapes base selected
        (BinaryEncoding.assignmentBits remaining)⟩) _
  exact ExtensionNatMachine.natInTime numberTapes Label.number (some (.copyOut .items))
    (cleanupEntry false) program (fun _ => rfl) base selected
    (BinaryEncoding.assignmentBits remaining) word scratchEmpty ((), .eq)

def readyTapes (items : RawInstance) (assignments remaining : List Nat) (selected : Nat) :
    Tape → List Bool :=
  ExtensionMachinePlacement.tapes innerView
    (ExtensionCapacityMachine.initialTapes items assignments selected)
    (stageTapes items assignments remaining)

def prepareSelectedInTime (items : RawInstance) (assignments remaining : List Nat)
    (selected : Nat) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
      (some (configuration (some (.inner ExtensionCapacityMachine.machine.main))
        (readyTapes items assignments remaining selected)))
      (1 + (2 * selected.size + 2) +
        2 * ((BinaryEncoding.rawInstanceBits items).length + 1) +
        2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) := by
  let stage := stageTapes items assignments remaining
  let framed := Function.update stage 24
    (BinaryEncoding.natBits selected ++ BinaryEncoding.assignmentBits remaining)
  let parsed := Function.update stage 4 selected.bits
  let copiedItems := Function.update parsed 2 (BinaryEncoding.rawInstanceBits items)
  have guardRun : StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
      (some (configuration (some (.number .scan)) framed)) 1 := {
    steps := 1
    evals_in_steps := by
      change machine.step
        (configuration (some .guard) (stageTapes items assignments (selected :: remaining))) =
        some (configuration (some (.number .scan)) framed)
      have step := guardStep (stageTapes items assignments (selected :: remaining)) true
        (BinaryEncoding.natBits selected ++ BinaryEncoding.assignmentBits remaining)
        (by simp [stageTapes, BinaryEncoding.assignmentBits, BinaryEncoding.listBits])
      have updated : Function.update (stageTapes items assignments (selected :: remaining)) 24
          (BinaryEncoding.natBits selected ++ BinaryEncoding.assignmentBits remaining) = framed := by
        funext k
        by_cases same : k = 24 <;> simp [framed, stage, stageTapes, same]
      simpa only [↓reduceIte, updated] using step
    steps_le_m := Nat.le_refl _ }
  have parseRun := selectedInTime framed selected remaining
    (by simp [framed]) (by simp [framed, stage, stageTapes])
  have parseFinal : ExtensionNatMachine.resultTapes numberTapes framed selected
      (BinaryEncoding.assignmentBits remaining) = parsed := by
    funext k
    fin_cases k <;>
      simp [ExtensionNatMachine.resultTapes, numberTapes, framed, parsed, stage, stageTapes]
  rw [parseFinal] at parseRun
  have itemsRun := copyInTime .items parsed (by simp [parsed, stage, stageTapes])
  have itemsRun' : StateTransition.EvalsToInTime machine.step
      (configuration (some (.copyOut .items)) parsed)
      (some (configuration (some (.copyOut .assignments)) copiedItems))
      (2 * ((BinaryEncoding.rawInstanceBits items).length + 1)) := by
    have source : parsed 22 = BinaryEncoding.rawInstanceBits items := by
      simp [parsed, stage, stageTapes]
    have destination : parsed 2 = [] := by simp [parsed, stage, stageTapes]
    simpa only [copySource, copyDestination, afterCopy, source, destination,
      List.append_nil, copiedItems] using itemsRun
  have assignmentsRun := copyInTime .assignments copiedItems
    (by simp [copiedItems, parsed, stage, stageTapes])
  have assignmentsFinal : Function.update copiedItems 3
      (BinaryEncoding.assignmentBits assignments) = readyTapes items assignments remaining selected := by
    funext k
    fin_cases k <;>
      simp [copiedItems, parsed, stage, stageTapes, readyTapes,
        ExtensionMachinePlacement.tapes, innerView, ExtensionCapacityMachine.initialTapes]
  have assignmentsRun' : StateTransition.EvalsToInTime machine.step
      (configuration (some (.copyOut .assignments)) copiedItems)
      (some (configuration (some (.inner ExtensionCapacityMachine.machine.main))
        (readyTapes items assignments remaining selected)))
      (2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) := by
    have source : copiedItems 23 = BinaryEncoding.assignmentBits assignments := by
      simp [copiedItems, parsed, stage, stageTapes]
    have destination : copiedItems 3 = [] := by simp [copiedItems, parsed, stage, stageTapes]
    simpa only [copySource, copyDestination, afterCopy, source, destination,
      List.append_nil, assignmentsFinal] using assignmentsRun
  have firstTwo := join guardRun parseRun
  have firstThree := join firstTwo itemsRun'
  exact join firstThree assignmentsRun'

def innerExecution (extra : Tape → List Bool)
    {start finish : ExtensionCapacityMachine.machine.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime ExtensionCapacityMachine.machine.step
      start (some finish) budget) :
    StateTransition.EvalsToInTime machine.step
      (ExtensionMachinePlacement.configuration innerView Label.inner (some .afterInner)
        (ExtensionMachineRegisters.Lens.identity State) clean extra start)
      (some (ExtensionMachinePlacement.configuration innerView Label.inner (some .afterInner)
        (ExtensionMachineRegisters.Lens.identity State) clean extra finish)) budget :=
  ExtensionMachinePlacement.execution innerTape innerView innerView_left innerView_right
    Label.inner (some .afterInner) (ExtensionMachineRegisters.Lens.identity State)
    clean extra ExtensionCapacityMachine.machine.m program (fun _ => rfl) run

theorem inner_initial_configuration (items : RawInstance) (assignments remaining : List Nat)
    (selected : Nat) :
    ExtensionMachinePlacement.configuration innerView Label.inner (some .afterInner)
      (ExtensionMachineRegisters.Lens.identity State) clean
      (stageTapes items assignments remaining)
      (ExtensionCapacityMachine.initialCfg items assignments selected) =
    configuration (some (.inner ExtensionCapacityMachine.machine.main))
      (readyTapes items assignments remaining selected) := rfl

theorem inner_final_configuration (items : RawInstance) (assignments remaining : List Nat)
    (result : Bool) :
    ExtensionMachinePlacement.configuration innerView Label.inner (some .afterInner)
      (ExtensionMachineRegisters.Lens.identity State) clean
      (stageTapes items assignments remaining) (ExtensionCapacityMachine.finalCfg result) =
    configuration (some .afterInner)
      (Function.update (stageTapes items assignments remaining) 0 [result]) := by
  change (⟨some .afterInner, clean, _⟩ : machine.Cfg) = ⟨some .afterInner, clean, _⟩
  congr 1
  funext k
  fin_cases k <;>
    simp [ExtensionMachinePlacement.tapes, innerView, ExtensionCapacityMachine.finalCfg,
      ExtensionCapacityMachine.finalTapes, stageTapes]

def afterInnerInTime (items : RawInstance) (assignments remaining : List Nat)
    (result : Bool) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some .afterInner)
        (Function.update (stageTapes items assignments remaining) 0 [result]))
      (some (configuration (if result then some .guard else cleanupEntry false)
        (stageTapes items assignments remaining))) 1 where
  steps := 1
  evals_in_steps := by
    change machine.step (configuration (some .afterInner)
      (Function.update (stageTapes items assignments remaining) 0 [result])) =
      some (configuration (if result then some .guard else cleanupEntry false)
        (stageTapes items assignments remaining))
    have step := afterInnerStep
      (Function.update (stageTapes items assignments remaining) 0 [result]) result (by simp)
    have reset : Function.update (Function.update (stageTapes items assignments remaining) 0 [result])
        0 [] = stageTapes items assignments remaining := by
      rw [Function.update_idem]
      have initial : stageTapes items assignments remaining 0 = [] := by simp [stageTapes]
      rw [← initial]
      simp
    simpa only [reset] using step
  steps_le_m := Nat.le_refl _

def cleanupInTime (result : Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime machine.step
      (configuration (cleanupEntry result) base)
      (some (configuration none (resultTapes result)))
      (MachineDrainMany.lengthSum allTapes base + 27) := by
  have first := MachineDrainMany.execution allTapes (Label.cleanup result)
    (some (.emit result)) program (fun _ => rfl) base
    ((((), .eq), false), none) none
  rw [cleanup_tapes] at first
  have first' : StateTransition.EvalsToInTime machine.step
      (configuration (cleanupEntry result) base)
      (some (configuration (some (.emit result)) (fun _ => [])))
      (MachineDrainMany.lengthSum allTapes base + 26) := by
    change StateTransition.EvalsToInTime (TM2.step program)
      ⟨cleanupEntry result, clean, base⟩
      (some ⟨some (.emit result), clean, fun _ => []⟩) _
    simpa only [cleanupEntry, configuration, clean, BinaryAddMachine.clean,
      BinaryAddMachine.state, MachineDrainMany.finalRegister_none,
      allTapes, List.length_ofFn] using first
  have second : StateTransition.EvalsToInTime machine.step
      (configuration (some (.emit result)) (fun _ => []))
      (some (configuration none (resultTapes result))) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (.emit result)) clean (fun _ => [])) = _
      simp only [program, TM2.stepAux, configuration]
      congr 1
    steps_le_m := Nat.le_refl _ }
  have combined := join first' second
  have clock : MachineDrainMany.lengthSum allTapes base + 26 + 1 =
      MachineDrainMany.lengthSum allTapes base + 27 := by omega
  rw [clock] at combined
  exact combined

def emptyInTime (items : RawInstance) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments []))
      (some (configuration none (resultTapes true)))
      ((BinaryEncoding.rawInstanceBits items).length +
        (BinaryEncoding.assignmentBits assignments).length + 28) := by
  have first : StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments []))
      (some (configuration (cleanupEntry true)
        (Function.update (stageTapes items assignments []) 24 []))) 1 := {
    steps := 1
    evals_in_steps := by
      change machine.step (configuration (some .guard) (stageTapes items assignments [])) =
        some (configuration (cleanupEntry true)
          (Function.update (stageTapes items assignments []) 24 []))
      simpa only [Bool.false_eq_true, ↓reduceIte] using guardStep (stageTapes items assignments []) false []
        (by simp [stageTapes, BinaryEncoding.assignmentBits, BinaryEncoding.listBits])
    steps_le_m := Nat.le_refl _ }
  have second := cleanupInTime true (Function.update (stageTapes items assignments []) 24 [])
  have combined := join first second
  have clock : 1 +
      (MachineDrainMany.lengthSum allTapes
        (Function.update (stageTapes items assignments []) 24 []) + 27) =
      (BinaryEncoding.rawInstanceBits items).length +
        (BinaryEncoding.assignmentBits assignments).length + 28 := by
    rw [ended_lengthSum]
    omega
  rw [clock] at combined
  exact combined

abbrev InnerRuns (items : RawInstance) (assignments : List Nat) :=
  ∀ selected : Nat, StateTransition.EvalsToInTime ExtensionCapacityMachine.machine.step
    (ExtensionCapacityMachine.initialCfg items assignments selected)
    (some (ExtensionCapacityMachine.finalCfg
      (CapacityScan.scan selected items assignments (0, 1))))
    (ExtensionCapacityMachine.timePolynomial.eval
      (ExtensionCapacityMachine.inputLength items assignments selected))

noncomputable def roundFromInner (items : RawInstance) (assignments remaining : List Nat)
    (selected : Nat) (member : selected ∈ assignments) (innerRuns : InnerRuns items assignments) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
      (some (configuration
        (if CapacityScan.scan selected items assignments (0, 1) then some .guard
          else cleanupEntry false) (stageTapes items assignments remaining)))
      (roundBudget ((BinaryEncoding.rawInstanceBits items).length +
        (BinaryEncoding.assignmentBits assignments).length)) := by
  have prepare := prepareSelectedInTime items assignments remaining selected
  have placed := innerExecution (stageTapes items assignments remaining) (innerRuns selected)
  have placed' : StateTransition.EvalsToInTime machine.step
      (configuration (some (.inner ExtensionCapacityMachine.machine.main))
        (readyTapes items assignments remaining selected))
      (some (configuration (some .afterInner)
        (Function.update (stageTapes items assignments remaining) 0
          [CapacityScan.scan selected items assignments (0, 1)])))
      (ExtensionCapacityMachine.timePolynomial.eval
        (ExtensionCapacityMachine.inputLength items assignments selected)) := by
    erw [inner_initial_configuration, inner_final_configuration] at placed
    exact placed
  have finish := afterInnerInTime items assignments remaining
    (CapacityScan.scan selected items assignments (0, 1))
  have firstTwo := join prepare placed'
  have complete := join firstTwo finish
  have selectedWidth := selected_size_le_encoding selected assignments member
  have innerBound := MachineComposition.natPolynomial_eval_mono
    ExtensionCapacityMachine.timePolynomial
    (show ExtensionCapacityMachine.inputLength items assignments selected ≤
      2 * ((BinaryEncoding.rawInstanceBits items).length +
        (BinaryEncoding.assignmentBits assignments).length) by
      unfold ExtensionCapacityMachine.inputLength
      omega)
  refine { toEvalsTo := complete.toEvalsTo, steps_le_m := complete.steps_le_m.trans ?_ }
  unfold roundBudget
  omega

noncomputable def loopFromInner (items : RawInstance) (assignments remaining : List Nat)
    (suffix : ∃ before, assignments = before ++ remaining)
    (innerRuns : InnerRuns items assignments) :
    StateTransition.EvalsToInTime machine.step
      (configuration (some .guard) (stageTapes items assignments remaining))
      (some (configuration none (resultTapes (scanResult items assignments remaining))))
      (loopBudget items assignments remaining) := by
  induction remaining with
  | nil =>
      have run := emptyInTime items assignments
      refine { toEvalsTo := run.toEvalsTo, steps_le_m := run.steps_le_m.trans ?_ }
      simp only [loopBudget, List.length_nil, Nat.zero_mul, Nat.zero_add]
      omega
  | cons selected remaining ih =>
      have member : selected ∈ assignments := by
        obtain ⟨before, equality⟩ := suffix
        rw [equality]
        simp
      have tailSuffix : ∃ before, assignments = before ++ remaining := by
        obtain ⟨before, equality⟩ := suffix
        exact ⟨before ++ [selected],
          by simpa only [List.append_assoc, List.singleton_append] using equality⟩
      have round := roundFromInner items assignments remaining selected member innerRuns
      cases answer : CapacityScan.scan selected items assignments (0, 1) with
      | false =>
          have round' : StateTransition.EvalsToInTime machine.step
              (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
              (some (configuration (cleanupEntry false) (stageTapes items assignments remaining)))
              (roundBudget ((BinaryEncoding.rawInstanceBits items).length +
                (BinaryEncoding.assignmentBits assignments).length)) := by
            simpa only [answer, Bool.false_eq_true, ↓reduceIte] using round
          have cleaned := cleanupInTime false (stageTapes items assignments remaining)
          have complete := join round' cleaned
          have tailEncoding : (BinaryEncoding.assignmentBits remaining).length ≤
              (BinaryEncoding.assignmentBits assignments).length := by
            obtain ⟨before, rfl⟩ := tailSuffix
            exact suffix_encoding_length_le before remaining
          have clock : roundBudget ((BinaryEncoding.rawInstanceBits items).length +
                  (BinaryEncoding.assignmentBits assignments).length) +
                (MachineDrainMany.lengthSum allTapes (stageTapes items assignments remaining) + 27) ≤
              loopBudget items assignments (selected :: remaining) := by
            rw [stage_lengthSum]
            simp only [loopBudget, List.length_cons, Nat.add_mul, Nat.one_mul]
            omega
          have enlarged : StateTransition.EvalsToInTime machine.step
              (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
              (some (configuration none (resultTapes false)))
              (loopBudget items assignments (selected :: remaining)) :=
            { toEvalsTo := complete.toEvalsTo, steps_le_m := complete.steps_le_m.trans clock }
          simpa only [scanResult, List.all_cons, answer, Bool.false_and] using enlarged
      | true =>
          have round' : StateTransition.EvalsToInTime machine.step
              (configuration (some .guard) (stageTapes items assignments (selected :: remaining)))
              (some (configuration (some .guard) (stageTapes items assignments remaining)))
              (roundBudget ((BinaryEncoding.rawInstanceBits items).length +
                (BinaryEncoding.assignmentBits assignments).length)) := by
            simpa only [answer, ↓reduceIte] using round
          have tailRun := ih tailSuffix
          have complete := join round' tailRun
          have clock : roundBudget ((BinaryEncoding.rawInstanceBits items).length +
                  (BinaryEncoding.assignmentBits assignments).length) +
                loopBudget items assignments remaining =
              loopBudget items assignments (selected :: remaining) := by
            simp only [loopBudget, List.length_cons, Nat.add_mul, Nat.one_mul]
            omega
          simpa only [clock, scanResult, List.all_cons, answer, Bool.true_and] using complete

noncomputable def outerInPolynomialTime (items : RawInstance) (assignments : List Nat)
    (valid : items.Valid) (sameLength : assignments.length = items.length) :
    StateTransition.EvalsToInTime machine.step
      (initialCfg items assignments)
      (some (finalCfg (assignments.all (ExtensionCertificate.capacityCheck items assignments))))
      (timePolynomial.eval (inputLength items assignments)) := by
  have first := initialCopyInTime items assignments
  have loops := loopFromInner items assignments assignments ⟨[], rfl⟩
    (fun selected => ExtensionCapacityMachine.innerInPolynomialTime
      items assignments selected valid sameLength)
  have complete := join first loops
  have labelCount : assignments.length ≤ inputLength items assignments := by
    have bound := BinaryEncoding.list_length_le_bits_length BinaryEncoding.natBits assignments
    change assignments.length ≤ (BinaryEncoding.assignmentBits assignments).length at bound
    unfold inputLength
    omega
  have budget := totalBudget_le (BinaryEncoding.rawInstanceBits items).length
    (BinaryEncoding.assignmentBits assignments).length assignments.length labelCount
  have clock : 2 * ((BinaryEncoding.assignmentBits assignments).length + 1) +
      loopBudget items assignments assignments ≤ timePolynomial.eval (inputLength items assignments) := by
    unfold loopBudget inputLength
    omega
  have enlarged : StateTransition.EvalsToInTime machine.step
      (initialCfg items assignments)
      (some (finalCfg (scanResult items assignments assignments)))
      (timePolynomial.eval (inputLength items assignments)) :=
    { toEvalsTo := complete.toEvalsTo, steps_le_m := complete.steps_le_m.trans clock }
  simpa only [scanResult_eq_capacityChecks items valid assignments assignments] using enlarged

end BinPackingGap.ExtensionCapacityOuterMachine

namespace BinPackingGap.ExtensionVerifierMachine

open Turing BinPackingGames.Foundations.Complexity
open ExtensionMachineRegisters (Lens)

instance instFintypeLocalLabel (h : Helper) : Fintype (LocalLabel h) := by cases h <;> infer_instance
instance instDecidableEqLocalLabel (h : Helper) : DecidableEq (LocalLabel h) := by cases h <;> infer_instance

def localInitial : (h : Helper) → LocalState h
  | .pair => ExtensionPairMachine.machine.initialState
  | .query => (ExtensionShapeMachine.machine .extension).initialState
  | .witness => (ExtensionShapeMachine.machine .assignments).initialState
  | .fields => Fields.machine.initialState
  | .validation => ExtensionValidationMachine.machine.initialState
  | .agreement => ExtensionAgreementMachine.machine.initialState
  | .capacity => ExtensionCapacityOuterMachine.machine.initialState

def localMain : (h : Helper) → LocalLabel h
  | .pair => ExtensionPairMachine.machine.main
  | .query => (ExtensionShapeMachine.machine .extension).main
  | .witness => (ExtensionShapeMachine.machine .assignments).main
  | .fields => Fields.machine.main
  | .validation => ExtensionValidationMachine.machine.main
  | .agreement => ExtensionAgreementMachine.machine.main
  | .capacity => ExtensionCapacityOuterMachine.machine.main

def localProgram : (h : Helper) →
    LocalLabel h → TM2.Stmt (fun _ : LocalTape h => Bool) (LocalLabel h) (LocalState h)
  | .pair => ExtensionPairMachine.machine.m
  | .query => (ExtensionShapeMachine.machine .extension).m
  | .witness => (ExtensionShapeMachine.machine .assignments).m
  | .fields => Fields.machine.m
  | .validation => ExtensionValidationMachine.machine.m
  | .agreement => ExtensionAgreementMachine.machine.m
  | .capacity => ExtensionCapacityOuterMachine.machine.m

def clean : State := (localInitial, none)

@[simp] theorem register_clean (h : Helper) :
    (register h).set clean (localInitial h) = clean := by
  simp [register, clean]

def slot : (h : Helper) → LocalTape h → Tape
  | .pair => ![0, 1, 2]
  | .query => ![1, 3, 2]
  | .witness => ![0, 4, 2]
  | .fields => ![3, 5, 6, 7, 8, 9, 10]
  | .validation => ![8, 12, 13, 14, 15, 16, 17, 11, 18, 19]
  | .agreement => ![10, 13]
  | .capacity => ![15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 9, 4, 37, 38]

def view : (h : Helper) → Tape → Option (LocalTape h)
  | .pair, k => match k.val with
      | 0 => some 0
      | 1 => some 1
      | 2 => some 2
      | _ => none
  | .query, k => match k.val with
      | 1 => some 0
      | 3 => some 1
      | 2 => some 2
      | _ => none
  | .witness, k => match k.val with
      | 0 => some 0
      | 4 => some 1
      | 2 => some 2
      | _ => none
  | .fields, k => match k.val with
      | 3 => some 0
      | 5 => some 1
      | 6 => some 2
      | 7 => some 3
      | 8 => some 4
      | 9 => some 5
      | 10 => some 6
      | _ => none
  | .validation, k => match k.val with
      | 8 => some 0
      | 12 => some 1
      | 13 => some 2
      | 14 => some 3
      | 15 => some 4
      | 16 => some 5
      | 17 => some 6
      | 11 => some 7
      | 18 => some 8
      | 19 => some 9
      | _ => none
  | .agreement, k => match k.val with
      | 10 => some 0
      | 13 => some 1
      | _ => none
  | .capacity, k => match k.val with
      | 15 => some 0
      | 16 => some 1
      | 17 => some 2
      | 18 => some 3
      | 19 => some 4
      | 20 => some 5
      | 21 => some 6
      | 22 => some 7
      | 23 => some 8
      | 24 => some 9
      | 25 => some 10
      | 26 => some 11
      | 27 => some 12
      | 28 => some 13
      | 29 => some 14
      | 30 => some 15
      | 31 => some 16
      | 32 => some 17
      | 33 => some 18
      | 34 => some 19
      | 35 => some 20
      | 36 => some 21
      | 9 => some 22
      | 4 => some 23
      | 37 => some 24
      | 38 => some 25
      | _ => none

theorem view_slot (h : Helper) (k : LocalTape h) : view h (slot h k) = some k := by
  cases h <;> fin_cases k <;> rfl

theorem slot_view (h : Helper) (j : Tape) (k : LocalTape h)
    (found : view h j = some k) : slot h k = j := by
  cases h <;> fin_cases j <;> simp only [view] at found
  all_goals
    first
    | contradiction
    | have equal := Option.some.inj found
      subst k
      rfl

def put (h : Helper) (localTapes : LocalTape h → List Bool) (base : Tape → List Bool) :
    Tape → List Bool := ExtensionMachinePlacement.tapes (view h) localTapes base

@[simp] theorem put_slot (h : Helper) (localTapes : LocalTape h → List Bool)
    (base : Tape → List Bool) (k : LocalTape h) :
    put h localTapes base (slot h k) = localTapes k :=
  ExtensionMachinePlacement.tapes_apply (slot h) (view h) (view_slot h) localTapes base k

theorem put_restrict (h : Helper) (base : Tape → List Bool) :
    put h (fun k => base (slot h k)) base = base :=
  ExtensionMachinePlacement.tapes_restrict (slot h) (view h) (slot_view h) base

def allTapes : List Tape := List.ofFn id

inductive Label
  | helper (h : Helper) (phase : LocalLabel h)
  | gate (phase : Gate)
  | copyOut (phase : Copy)
  | copyBack (phase : Copy)
  | cleanup (result : Bool) (phase : MachineDrainMany.Label allTapes)
  | emit (result : Bool)
  deriving DecidableEq, Fintype

def entry (h : Helper) : Label := .helper h (localMain h)

def cleanupEntry (result : Bool) : Option Label :=
  MachineDrainMany.entry allTapes (.cleanup result) (some (.emit result))

def afterHelper : Helper → Label
  | .pair => entry .query
  | .query => .gate .query
  | .witness => .gate .witness
  | .fields => .copyOut .items
  | .validation => .gate .validation
  | .agreement => .gate .agreement
  | .capacity => .gate .capacity

def gateTape : Gate → Tape
  | .query => 3
  | .witness => 4
  | .validation => 8
  | .agreement => 10
  | .capacity => 15

def afterGate : Gate → Option Label
  | .query => some (entry .witness)
  | .witness => some (entry .fields)
  | .validation => some (.copyOut .agreementAssignments)
  | .agreement => some (entry .capacity)
  | .capacity => cleanupEntry true

def copySource : Copy → Tape
  | .items => 9
  | .validationAssignments | .agreementAssignments => 4

def copyDestination : Copy → Tape
  | .items => 12
  | .validationAssignments | .agreementAssignments => 13

def afterCopy : Copy → Label
  | .items => .copyOut .validationAssignments
  | .validationAssignments => entry .validation
  | .agreementAssignments => entry .agreement

def jump (next : Option Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => clean) (match next with
    | some l => .goto fun _ => l
    | none => .halt)

def program : Label → TM2.Stmt Alphabet Label State
  | .helper h phase =>
      ExtensionMachinePlacement.statement (slot h) (.helper h)
        (some (afterHelper h)) (register h) (localProgram h phase)
  | .gate phase =>
      .pop (gateTape phase) (fun state bit => (state.1, bit))
        (.branch (fun state => state.2.getD false)
          (jump (afterGate phase)) (jump (cleanupEntry false)))
  | .copyOut phase =>
      BinPackingGames.Reduction.MachineTransfer.loopAt (copySource phase) 11 id false
        (.copyOut phase) (some (.copyBack phase))
  | .copyBack phase =>
      MachineCopy.forkLoop 11 (copySource phase) (copyDestination phase) false
        (.copyBack phase) (some (afterCopy phase))
  | .cleanup result phase =>
      MachineDrainMany.instruction allTapes (.cleanup result) (some (.emit result)) phase
  | .emit result => .push 0 (fun _ => result) (.load (fun _ => clean) .halt)

def machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := entry .pair
  σ := State
  initialState := clean
  m := program

def cfg (label : Option Label) (tapes : Tape → List Bool) : machine.Cfg :=
  ⟨label, clean, tapes⟩

def stagedTapes (query witness bins items fixed bound itemCopy assignmentCopy : List Bool) :
    Tape → List Bool := fun k =>
  if k = 3 then query else if k = 4 then witness else if k = 8 then bins
  else if k = 9 then items else if k = 10 then fixed else if k = 14 then bound
  else if k = 12 then itemCopy else if k = 13 then assignmentCopy else []

def fieldInput (query witness : List Bool) : Tape → List Bool :=
  stagedTapes query witness [] [] [] [] [] []

def oneStep {start finish : machine.Cfg} (step : machine.step start = some finish) :
    StateTransition.EvalsToInTime machine.step start (some finish) 1 where
  steps := 1
  evals_in_steps := step
  steps_le_m := Nat.le_refl _

def join {start middle finish : machine.Cfg} {firstTime secondTime : Nat}
    (first : StateTransition.EvalsToInTime machine.step start (some middle) firstTime)
    (second : StateTransition.EvalsToInTime machine.step middle (some finish) secondTime) :
    StateTransition.EvalsToInTime machine.step start (some finish) (firstTime + secondTime) := by
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans machine.step firstTime secondTime
      start middle (some finish) first second

def enlarge {start finish : machine.Cfg} {time budget : Nat}
    (run : StateTransition.EvalsToInTime machine.step start (some finish) time)
    (bounded : time ≤ budget) :
    StateTransition.EvalsToInTime machine.step start (some finish) budget where
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans bounded

def callInTime (h : Helper) (base : Tape → List Bool)
    (start finish : TM2.Cfg (fun _ : LocalTape h => Bool) (LocalLabel h) (LocalState h))
    (budget : Nat)
    (run : StateTransition.EvalsToInTime (TM2.step (localProgram h)) start (some finish) budget)
    (startLabel : start.l = some (localMain h)) (endLabel : finish.l = none)
    (startState : start.var = localInitial h) (endState : finish.var = localInitial h)
    (inputs : ∀ k, base (slot h k) = start.stk k) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (entry h)) base)
      (some (cfg (some (afterHelper h)) (put h finish.stk base))) budget := by
  have transported := ExtensionMachinePlacement.execution (slot h) (view h)
    (view_slot h) (slot_view h) (.helper h) (some (afterHelper h))
    (register h) clean base (localProgram h) program (fun _ => rfl) run
  have tapesEqual : put h start.stk base = base := by
    rw [show start.stk = fun k => base (slot h k) from funext fun k => (inputs k).symm]
    exact put_restrict h base
  change ExtensionMachinePlacement.tapes (view h) start.stk base = base at tapesEqual
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.helper h (localMain h)), clean, base⟩
    (some ⟨some (afterHelper h), clean,
      ExtensionMachinePlacement.tapes (view h) finish.stk base⟩) budget
  simpa only [ExtensionMachinePlacement.configuration, ExtensionMachinePlacement.label,
    startLabel, endLabel, startState, endState, register_clean, tapesEqual] using transported

theorem gateStep (gate : Gate) (base : Tape → List Bool) (result : Bool) (tail : List Bool)
    (word : base (gateTape gate) = result :: tail) :
    machine.step (cfg (some (.gate gate)) base) =
      some (cfg (if result then afterGate gate else cleanupEntry false)
        (Function.update base (gateTape gate) tail)) := by
  cases result <;> cases good : afterGate gate <;> cases bad : cleanupEntry false <;>
    simp [FinTM2.step, TM2.step, machine, cfg, program, TM2.stepAux, word, jump, good, bad] <;> rfl

def copyInTime (phase : Copy) (base : Tape → List Bool) (scratchEmpty : base 11 = []) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.copyOut phase)) base)
      (some (cfg (some (afterCopy phase))
        (Function.update base (copyDestination phase)
          (base (copySource phase) ++ base (copyDestination phase)))))
      (2 * ((base (copySource phase)).length + 1)) := by
  exact MachineCopy.copyInTime (copySource phase) (copyDestination phase) 11
    (by cases phase <;> decide) (by cases phase <;> decide) (by cases phase <;> decide)
    false (.copyOut phase) (.copyBack phase) (some (afterCopy phase)) program rfl rfl
    base scratchEmpty localInitial none

theorem cleanup_tapes (base : Tape → List Bool) :
    MachineDrainMany.finalTapes allTapes base = fun _ => [] := by
  funext k
  apply MachineDrainMany.finalTapes_mem
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

def resultTapes (result : Bool) : Tape → List Bool :=
  Function.update (fun _ => []) 0 [result]

def cleanupInTime (result : Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime machine.step (cfg (cleanupEntry result) base)
      (some (cfg none (resultTapes result)))
      (MachineDrainMany.lengthSum allTapes base + 41) := by
  have first := MachineDrainMany.execution allTapes (.cleanup result)
    (some (.emit result)) program (fun _ => rfl) base localInitial none
  rw [cleanup_tapes] at first
  have first' : StateTransition.EvalsToInTime machine.step
      (cfg (cleanupEntry result) base)
      (some (cfg (some (.emit result)) (fun _ => [])))
      (MachineDrainMany.lengthSum allTapes base + 40) := by
    change StateTransition.EvalsToInTime (TM2.step program)
      ⟨cleanupEntry result, clean, base⟩
      (some ⟨some (.emit result), clean, fun _ => []⟩) _
    simpa only [clean, MachineDrainMany.finalRegister_none,
      cleanupEntry, allTapes, List.length_ofFn] using first
  have second := oneStep (show machine.step (cfg (some (.emit result)) (fun _ => [])) =
      some (cfg none (resultTapes result)) from by
    simp [FinTM2.step, machine, TM2.step, TM2.stepAux, program, cfg, clean, resultTapes]
    rfl)
  simpa only [Nat.add_assoc] using join first' second

end BinPackingGap.ExtensionVerifierMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionVerifier
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionVerifierMachine

open Turing BinPackingGames.Foundations.Complexity

def frontTapes (zero one three four : List Bool) : Tape → List Bool := fun k =>
  if k = 0 then zero else if k = 1 then one else if k = 3 then three
  else if k = 4 then four else []

def frontendAccepted (query witness : List Bool) : Bool :=
  (BinaryEncoding.decodeExtension query).isSome &&
    (BinaryEncoding.decodeAssignments witness).isSome

def frontendExit (query witness : List Bool) : Option Label :=
  if frontendAccepted query witness then some (entry .fields) else cleanupEntry false

def frontendTapes (query witness : List Bool) : Tape → List Bool :=
  if (BinaryEncoding.decodeExtension query).isSome then fieldInput query witness
  else frontTapes witness [] query []

@[simp] theorem frontTapes_fieldInput (query witness : List Bool) :
    frontTapes [] [] query witness = fieldInput query witness := by
  funext k
  fin_cases k <;> simp [frontTapes, fieldInput, stagedTapes]

def pairedInputInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (CookLevin.pairBits (query, witness)))
      (some (cfg (some (entry .query)) (frontTapes witness query [] [])))
      (3 * query.length + 4) := by
  let base := frontTapes (CookLevin.pairBits (query, witness)) [] [] []
  have call := callInTime .pair base
    (initList ExtensionPairMachine.machine (CookLevin.pairBits (query, witness)))
    (ExtensionPairMachine.cfg none witness query []) (3 * query.length + 4)
    (ExtensionPairMachine.pairHaltInTime query witness) rfl rfl rfl rfl
    (by
      intro k
      fin_cases k <;>
        simp [base, frontTapes, slot, initList, ExtensionPairMachine.machine,
          BinPackingCompleteness.BinaryPairMachine.machine])
  have initial : cfg (some (entry .pair)) base =
      initList machine (CookLevin.pairBits (query, witness)) := by
    change (⟨some (entry .pair), clean, base⟩ : machine.Cfg) = ⟨some (entry .pair), clean, _⟩
    congr 1
    funext k
    fin_cases k <;> simp [base, frontTapes, machine]
    rfl
  have final : put .pair (ExtensionPairMachine.cfg none witness query []).stk base =
      frontTapes witness query [] [] := by
    funext k
    fin_cases k <;>
      simp [put, ExtensionMachinePlacement.tapes, view, base, frontTapes,
        ExtensionPairMachine.cfg, BinPackingCompleteness.BinaryPairMachine.cfg,
        BinPackingCompleteness.BinaryPairMachine.tapes]
  simpa only [initial, final, afterHelper] using call

def queryShapeInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (entry .query)) (frontTapes witness query [] []))
      (some (cfg (some (.gate .query))
        (frontTapes witness []
          (ExtensionShapeMachine.decodeAccepts .extension query :: query) [])))
      (2 * query.length + 3) := by
  let base := frontTapes witness query [] []
  let output := ExtensionShapeMachine.decodeAccepts .extension query :: query
  have call := callInTime .query base
    (initList (ExtensionShapeMachine.machine .extension) query)
    (haltList (ExtensionShapeMachine.machine .extension) output) (2 * query.length + 3)
    (ExtensionShapeMachine.outputsInTime .extension query) rfl rfl rfl rfl
    (by
      intro k
      fin_cases k <;> simp [base, frontTapes, slot, initList, ExtensionShapeMachine.machine])
  have final : put .query (haltList (ExtensionShapeMachine.machine .extension) output).stk base =
      frontTapes witness [] output [] := by
    funext k
    fin_cases k <;>
      simp [put, ExtensionMachinePlacement.tapes, view, base, frontTapes,
        haltList, ExtensionShapeMachine.machine]
  simpa only [base, final, afterHelper, output] using call

def queryGateInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.gate .query))
        (frontTapes witness []
          (ExtensionShapeMachine.decodeAccepts .extension query :: query) []))
      (some (cfg
        (if ExtensionShapeMachine.decodeAccepts .extension query then
          some (entry .witness) else cleanupEntry false)
        (frontTapes witness [] query []))) 1 := by
  have step := gateStep .query
    (frontTapes witness [] (ExtensionShapeMachine.decodeAccepts .extension query :: query) [])
    (ExtensionShapeMachine.decodeAccepts .extension query) query (by simp [frontTapes, gateTape])
  have final : Function.update
      (frontTapes witness [] (ExtensionShapeMachine.decodeAccepts .extension query :: query) [])
      (gateTape .query) query = frontTapes witness [] query [] := by
    funext k
    by_cases same : k = 3 <;> simp [frontTapes, gateTape, same]
  exact oneStep (by simpa only [afterGate, final] using step)

def witnessShapeInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (entry .witness)) (frontTapes witness [] query []))
      (some (cfg (some (.gate .witness))
        (frontTapes [] [] query
          (ExtensionShapeMachine.decodeAccepts .assignments witness :: witness))))
      (2 * witness.length + 3) := by
  let base := frontTapes witness [] query []
  let output := ExtensionShapeMachine.decodeAccepts .assignments witness :: witness
  have call := callInTime .witness base
    (initList (ExtensionShapeMachine.machine .assignments) witness)
    (haltList (ExtensionShapeMachine.machine .assignments) output) (2 * witness.length + 3)
    (ExtensionShapeMachine.outputsInTime .assignments witness) rfl rfl rfl rfl
    (by
      intro k
      fin_cases k <;> simp [base, frontTapes, slot, initList, ExtensionShapeMachine.machine])
  have final : put .witness (haltList (ExtensionShapeMachine.machine .assignments) output).stk base =
      frontTapes [] [] query output := by
    funext k
    fin_cases k <;>
      simp [put, ExtensionMachinePlacement.tapes, view, base, frontTapes,
        haltList, ExtensionShapeMachine.machine]
  simpa only [base, final, afterHelper, output] using call

def witnessGateInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.gate .witness))
        (frontTapes [] [] query
          (ExtensionShapeMachine.decodeAccepts .assignments witness :: witness)))
      (some (cfg
        (if ExtensionShapeMachine.decodeAccepts .assignments witness then
          some (entry .fields) else cleanupEntry false)
        (fieldInput query witness))) 1 := by
  have step := gateStep .witness
    (frontTapes [] [] query (ExtensionShapeMachine.decodeAccepts .assignments witness :: witness))
    (ExtensionShapeMachine.decodeAccepts .assignments witness) witness
    (by simp [frontTapes, gateTape])
  have final : Function.update
      (frontTapes [] [] query (ExtensionShapeMachine.decodeAccepts .assignments witness :: witness))
      (gateTape .witness) witness = fieldInput query witness := by
    rw [← frontTapes_fieldInput]
    funext k
    by_cases same : k = 4 <;> simp [frontTapes, gateTape, same, -frontTapes_fieldInput]
  exact oneStep (by simpa only [afterGate, final] using step)

def frontendInTime (query witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (CookLevin.pairBits (query, witness)))
      (some (cfg (frontendExit query witness) (frontendTapes query witness)))
      (16 * ((CookLevin.pairBits (query, witness)).length + 1)) := by
  have first := join (join (pairedInputInTime query witness) (queryShapeInTime query witness))
    (queryGateInTime query witness)
  cases queryFlag : (BinaryEncoding.decodeExtension query).isSome with
  | false =>
      have stopped : StateTransition.EvalsToInTime machine.step
          (initList machine (CookLevin.pairBits (query, witness)))
          (some (cfg (frontendExit query witness) (frontendTapes query witness)))
          ((3 * query.length + 4) + (2 * query.length + 3) + 1) := by
        simpa [ExtensionShapeMachine.decodeAccepts, queryFlag, frontendExit,
          frontendAccepted, frontendTapes] using first
      exact enlarge stopped (by rw [CookLevin.pairBits_length]; dsimp only; omega)
  | true =>
      have continued : StateTransition.EvalsToInTime machine.step
          (initList machine (CookLevin.pairBits (query, witness)))
          (some (cfg (some (entry .witness)) (frontTapes witness [] query [])))
          ((3 * query.length + 4) + (2 * query.length + 3) + 1) := by
        simpa [ExtensionShapeMachine.decodeAccepts, queryFlag] using first
      have all := join (join continued (witnessShapeInTime query witness))
        (witnessGateInTime query witness)
      have completed : StateTransition.EvalsToInTime machine.step
          (initList machine (CookLevin.pairBits (query, witness)))
          (some (cfg (frontendExit query witness) (frontendTapes query witness)))
          ((((3 * query.length + 4) + (2 * query.length + 3) + 1) +
            (2 * witness.length + 3)) + 1) := by
        simpa [ExtensionShapeMachine.decodeAccepts, queryFlag, frontendExit,
          frontendAccepted, frontendTapes] using! all
      exact enlarge completed (by rw [CookLevin.pairBits_length]; dsimp only; omega)

def extractedTapes (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Tape → List Bool :=
  stagedTapes [] (BinaryEncoding.assignmentBits assignments) (BinaryEncoding.natBits bins)
    (BinaryEncoding.rawInstanceBits items) (ExtensionAgreementMachine.fixedBits fixed) [] [] []

def validationInput (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Tape → List Bool :=
  stagedTapes [] (BinaryEncoding.assignmentBits assignments) (BinaryEncoding.natBits bins)
    (BinaryEncoding.rawInstanceBits items) (ExtensionAgreementMachine.fixedBits fixed) []
    (BinaryEncoding.rawInstanceBits items) (BinaryEncoding.assignmentBits assignments)

def checkedTapes (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Tape → List Bool :=
  stagedTapes [] (BinaryEncoding.assignmentBits assignments) []
    (BinaryEncoding.rawInstanceBits items) (ExtensionAgreementMachine.fixedBits fixed) bins.bits [] []

def agreementInput (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Tape → List Bool :=
  stagedTapes [] (BinaryEncoding.assignmentBits assignments) []
    (BinaryEncoding.rawInstanceBits items) (ExtensionAgreementMachine.fixedBits fixed) bins.bits []
    (BinaryEncoding.assignmentBits assignments)

def capacityInput (bins : Nat) (items : RawInstance) (assignments : List Nat) :
    Tape → List Bool :=
  stagedTapes [] (BinaryEncoding.assignmentBits assignments) []
    (BinaryEncoding.rawInstanceBits items) [] bins.bits [] []

def extractionInTime (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (entry .fields)) (fieldInput (BinaryEncoding.extensionBits bins items fixed)
        (BinaryEncoding.assignmentBits assignments)))
      (some (cfg (some (.copyOut .items)) (extractedTapes bins items fixed assignments)))
      (2 * (BinaryEncoding.extensionBits bins items fixed).length + 4) := by
  have lifted := callInTime .fields
    (fieldInput (BinaryEncoding.extensionBits bins items fixed)
      (BinaryEncoding.assignmentBits assignments))
    _ _ _ (Fields.extensionInTime bins items fixed) rfl rfl rfl rfl
    (by intro k; fin_cases k <;> rfl)
  have words : put .fields (Fields.tapes [] Fields.empty (Fields.encodedWords bins items fixed))
      (fieldInput (BinaryEncoding.extensionBits bins items fixed)
        (BinaryEncoding.assignmentBits assignments)) = extractedTapes bins items fixed assignments := by
    funext k
    fin_cases k <;> simp [put, ExtensionMachinePlacement.tapes, view, Fields.tapes,
      Fields.empty, Fields.encodedWords, fieldInput, extractedTapes, stagedTapes,
      ExtensionAgreementMachine.fixedBits]
  simpa only [Fields.cfg, words, afterHelper] using lifted

def prepareValidationInTime (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.copyOut .items)) (extractedTapes bins items fixed assignments))
      (some (cfg (some (entry .validation)) (validationInput bins items fixed assignments)))
      (2 * ((BinaryEncoding.rawInstanceBits items).length + 1) +
        2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) := by
  have first := copyInTime .items (extractedTapes bins items fixed assignments) rfl
  have second := copyInTime .validationAssignments
    (Function.update (extractedTapes bins items fixed assignments) 12
      (BinaryEncoding.rawInstanceBits items)) (by simp [extractedTapes, stagedTapes])
  have output : Function.update (Function.update (extractedTapes bins items fixed assignments)
      12 (BinaryEncoding.rawInstanceBits items)) 13 (BinaryEncoding.assignmentBits assignments) =
      validationInput bins items fixed assignments := by
    funext k
    fin_cases k <;> simp [extractedTapes, validationInput, stagedTapes]
  have firstSource : extractedTapes bins items fixed assignments 9 =
      BinaryEncoding.rawInstanceBits items := rfl
  have firstEmpty : extractedTapes bins items fixed assignments 12 = [] := rfl
  have secondSource :
      Function.update (extractedTapes bins items fixed assignments) 12
        (BinaryEncoding.rawInstanceBits items) 4 = BinaryEncoding.assignmentBits assignments := rfl
  have secondEmpty :
      Function.update (extractedTapes bins items fixed assignments) 12
        (BinaryEncoding.rawInstanceBits items) 13 = [] := rfl
  simp only [copySource, copyDestination, afterCopy, firstSource, firstEmpty,
    List.append_nil] at first
  simp only [copySource, copyDestination, afterCopy, secondSource, secondEmpty,
    List.append_nil] at second
  have joined := join first second
  rw [output] at joined
  exact joined

def prepareAgreementInTime (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.copyOut .agreementAssignments)) (checkedTapes bins items fixed assignments))
      (some (cfg (some (entry .agreement)) (agreementInput bins items fixed assignments)))
      (2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) := by
  have copied := copyInTime .agreementAssignments (checkedTapes bins items fixed assignments) rfl
  have output : Function.update (checkedTapes bins items fixed assignments) 13
      (BinaryEncoding.assignmentBits assignments) = agreementInput bins items fixed assignments := by
    funext k
    fin_cases k <;> simp [checkedTapes, agreementInput, stagedTapes]
  have source : checkedTapes bins items fixed assignments 4 =
      BinaryEncoding.assignmentBits assignments := rfl
  have empty : checkedTapes bins items fixed assignments 13 = [] := rfl
  simp only [copySource, copyDestination, afterCopy, source, empty, List.append_nil] at copied
  rw [output] at copied
  exact copied

theorem check_factor (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) :
    ExtensionCertificate.check bins items fixed assignments =
      (ExtensionValidationMachine.validRows bins items assignments &&
        (ExtensionCertificate.agreesBool fixed assignments &&
          assignments.all (ExtensionCertificate.capacityCheck items assignments))) := by
  simp only [ExtensionCertificate.check, ExtensionValidationMachine.validRows_eq, Bool.and_assoc]

noncomputable def canonicalBudget (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Nat :=
  (2 * (BinaryEncoding.extensionBits bins items fixed).length + 4) +
  (2 * ((BinaryEncoding.rawInstanceBits items).length + 1) +
    2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) +
  ExtensionValidationMachine.validationTime.eval
    (ExtensionValidationMachine.inputLength bins items assignments) + 1 +
  2 * ((BinaryEncoding.assignmentBits assignments).length + 1) +
  (ExtensionAgreementMachine.agreementTime.eval
    ((ExtensionAgreementMachine.fixedBits fixed).length +
      (BinaryEncoding.assignmentBits assignments).length) + 1) + 1 +
  ExtensionCapacityOuterMachine.timePolynomial.eval
    (ExtensionCapacityOuterMachine.inputLength items assignments) + 1

structure CanonicalRun (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) where
  finish : Tape → List Bool
  execution : StateTransition.EvalsToInTime machine.step
    (cfg (some (entry .fields)) (fieldInput (BinaryEncoding.extensionBits bins items fixed)
      (BinaryEncoding.assignmentBits assignments)))
    (some (cfg (cleanupEntry (ExtensionCertificate.check bins items fixed assignments)) finish))
    (canonicalBudget bins items fixed assignments)

noncomputable def canonicalRun (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : CanonicalRun bins items fixed assignments := by
  let validated := ExtensionValidationMachine.validationInTime bins items assignments
  have extracted := extractionInTime bins items fixed assignments
  have copied := prepareValidationInTime bins items fixed assignments
  have validation := callInTime .validation (validationInput bins items fixed assignments)
    _ _ _ validated.execution rfl rfl rfl rfl
    (by intro k; fin_cases k <;>
        simp [validationInput, stagedTapes, slot, ExtensionValidationMachine.cfg,
          ExtensionValidationMachine.inputTapes, ExtensionValidationMachine.work])
  let afterValidation := put .validation validated.finish (validationInput bins items fixed assignments)
  have validationFlag : afterValidation 8 = [ExtensionValidationMachine.validRows bins items assignments] := by
    change put .validation validated.finish (validationInput bins items fixed assignments)
      (slot .validation 0) = _
    simpa only [put_slot] using validated.flag
  have validateGate := oneStep (gateStep .validation afterValidation
    (ExtensionValidationMachine.validRows bins items assignments) [] validationFlag)
  have checkedPrefix := join (join (join extracted copied) validation) validateGate
  by_cases valid : ExtensionValidationMachine.validRows bins items assignments = true
  · have validity : items.Valid := by
      have h := valid
      rw [ExtensionValidationMachine.validRows_eq, Bool.and_eq_true] at h
      exact (ExtensionCertificate.validItems_eq_true_iff items).mp h.1
    have sameLength : assignments.length = items.length := by
      have h := valid
      simp only [ExtensionValidationMachine.validRows_eq, Bool.and_eq_true,
        decide_eq_true_eq] at h
      exact h.2.1
    have validatedWords : Function.update afterValidation 8 [] =
        checkedTapes bins items fixed assignments := by
      rw [show afterValidation = put .validation
        (Function.update (ExtensionValidationMachine.work bins.bits [] [] [] [] []) 0 [true])
        (validationInput bins items fixed assignments) from congrArg
          (fun v => put .validation v (validationInput bins items fixed assignments))
          (validated.accepted_clean valid)]
      funext k
      fin_cases k <;>
        simp [put, ExtensionMachinePlacement.tapes, view, validationInput, stagedTapes,
          checkedTapes, ExtensionValidationMachine.work]
    simp only [valid, ↓reduceIte,
      afterGate, gateTape, validatedWords] at checkedPrefix
    have copiedAgain := prepareAgreementInTime bins items fixed assignments
    have agreement := callInTime .agreement (agreementInput bins items fixed assignments)
      _ _ _ (ExtensionAgreementMachine.agreementFlagInTime fixed assignments) rfl rfl rfl rfl
      (by intro k; fin_cases k <;>
          simp [agreementInput, stagedTapes, slot, ExtensionAgreementMachine.cfg,
            ExtensionAgreementMachine.tapes])
    let agreementResult := ExtensionCertificate.agreesBool fixed assignments
    let afterAgreement := put .agreement (ExtensionAgreementMachine.tapes [agreementResult] [])
      (agreementInput bins items fixed assignments)
    have agreementFlag : afterAgreement 10 = [agreementResult] := by
      change put .agreement _ _ (slot .agreement 0) = _
      simp [put_slot, ExtensionAgreementMachine.tapes]
    have agreeGate := oneStep (gateStep .agreement afterAgreement agreementResult [] agreementFlag)
    have throughAgreement := join (join (join checkedPrefix copiedAgain) agreement) agreeGate
    by_cases agrees : agreementResult = true
    · have agreedWords : Function.update afterAgreement 10 [] =
          capacityInput bins items assignments := by
        funext k
        fin_cases k <;>
          simp [afterAgreement, put, ExtensionMachinePlacement.tapes, view,
            ExtensionAgreementMachine.tapes, agreementInput, stagedTapes, capacityInput]
      simp only [agrees, ↓reduceIte,
        afterGate, gateTape, agreedWords] at throughAgreement
      have capacity := callInTime .capacity (capacityInput bins items assignments) _ _ _
        (ExtensionCapacityOuterMachine.outerInPolynomialTime items assignments validity sameLength)
        rfl rfl rfl rfl
        (by intro k; fin_cases k <;>
            simp [slot, capacityInput, stagedTapes, ExtensionCapacityOuterMachine.initialCfg,
              ExtensionCapacityOuterMachine.configuration, ExtensionCapacityOuterMachine.initialTapes,
              ExtensionCapacityOuterMachine.stageTapes])
      let result := assignments.all (ExtensionCertificate.capacityCheck items assignments)
      let afterCapacity := put .capacity (ExtensionCapacityOuterMachine.resultTapes result)
        (capacityInput bins items assignments)
      have capacityFlag : afterCapacity 15 = [result] := by
        change put .capacity _ _ (slot .capacity 0) = _
        simp [put_slot, ExtensionCapacityOuterMachine.resultTapes]
      have capacityGate := oneStep (gateStep .capacity afterCapacity result [] capacityFlag)
      have finish := join (join throughAgreement capacity) capacityGate
      refine ⟨Function.update afterCapacity 15 [], ?_⟩
      have semantics : ExtensionCertificate.check bins items fixed assignments = result := by
        simp only [check_factor, valid, Bool.true_and, ← show
          agreementResult = ExtensionCertificate.agreesBool fixed assignments from rfl, agrees,
          Bool.true_and, result]
      have exit : (if result then afterGate .capacity else cleanupEntry false) = cleanupEntry result := by
        cases result <;> rfl
      simpa only [canonicalBudget, ExtensionCapacityOuterMachine.finalCfg,
        ExtensionCapacityOuterMachine.configuration, afterHelper, gateTape, exit, semantics,
        afterCapacity, afterAgreement, agreementResult, result] using finish
    · have rejected : agreementResult = false := Bool.eq_false_of_not_eq_true agrees
      refine ⟨Function.update afterAgreement 10 [], ?_⟩
      have semantics : ExtensionCertificate.check bins items fixed assignments = false := by
        simp only [check_factor, valid, Bool.true_and, ← show
          agreementResult = ExtensionCertificate.agreesBool fixed assignments from rfl,
          rejected, Bool.false_and]
      have bounded :
          (((((2 * (BinaryEncoding.extensionBits bins items fixed).length + 4) +
            (2 * ((BinaryEncoding.rawInstanceBits items).length + 1) +
              2 * ((BinaryEncoding.assignmentBits assignments).length + 1))) +
            ExtensionValidationMachine.validationTime.eval
              (ExtensionValidationMachine.inputLength bins items assignments)) + 1) +
            2 * ((BinaryEncoding.assignmentBits assignments).length + 1)) +
            (ExtensionAgreementMachine.agreementTime.eval
              ((ExtensionAgreementMachine.fixedBits fixed).length +
                (BinaryEncoding.assignmentBits assignments).length) + 1) + 1 ≤
          canonicalBudget bins items fixed assignments := by
        unfold canonicalBudget
        omega
      simpa only [rejected, Bool.cond_false, Bool.false_eq_true, ↓reduceIte,
        gateTape, semantics, afterHelper,
        afterAgreement, agreementResult] using enlarge throughAgreement bounded
  · have rejected : ExtensionValidationMachine.validRows bins items assignments = false :=
      Bool.eq_false_of_not_eq_true valid
    refine ⟨Function.update afterValidation 8 [], ?_⟩
    have semantics : ExtensionCertificate.check bins items fixed assignments = false := by
      simp only [check_factor, rejected, Bool.false_and]
    have bounded :
        (((2 * (BinaryEncoding.extensionBits bins items fixed).length + 4) +
          (2 * ((BinaryEncoding.rawInstanceBits items).length + 1) +
            2 * ((BinaryEncoding.assignmentBits assignments).length + 1))) +
          ExtensionValidationMachine.validationTime.eval
            (ExtensionValidationMachine.inputLength bins items assignments)) + 1 ≤
        canonicalBudget bins items fixed assignments := by
      unfold canonicalBudget
      omega
    simpa only [rejected, Bool.cond_false, Bool.false_eq_true, ↓reduceIte,
      gateTape, semantics, afterHelper, afterValidation]
      using enlarge checkedPrefix bounded

theorem canonicalBudget_le (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) :
    canonicalBudget bins items fixed assignments ≤ canonicalTime.eval
      ((BinaryEncoding.extensionBits bins items fixed).length +
        (BinaryEncoding.assignmentBits assignments).length) := by
  let n := (BinaryEncoding.extensionBits bins items fixed).length +
    (BinaryEncoding.assignmentBits assignments).length
  have queryLength : (BinaryEncoding.extensionBits bins items fixed).length =
      (BinaryEncoding.natBits bins).length + (BinaryEncoding.rawInstanceBits items).length +
        (ExtensionAgreementMachine.fixedBits fixed).length := by
    simp [BinaryEncoding.extensionBits, ExtensionAgreementMachine.fixedBits, Nat.add_assoc]
  have validationBound : ExtensionValidationMachine.inputLength bins items assignments ≤ n := by
    simp only [ExtensionValidationMachine.inputLength, n, queryLength]
    omega
  have capacityBound : ExtensionCapacityOuterMachine.inputLength items assignments ≤ n := by
    simp only [ExtensionCapacityOuterMachine.inputLength, n, queryLength]
    omega
  have validationClock := MachineComposition.natPolynomial_eval_mono
    ExtensionValidationMachine.validationTime validationBound
  have capacityClock := MachineComposition.natPolynomial_eval_mono
    ExtensionCapacityOuterMachine.timePolynomial capacityBound
  simp only [canonicalBudget, canonicalTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, ExtensionAgreementMachine.agreementTime,
    Polynomial.eval_ofNat]
  dsimp [n] at validationClock capacityClock
  omega

noncomputable def canonicalInPolynomialTime (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (entry .fields)) (fieldInput (BinaryEncoding.extensionBits bins items fixed)
        (BinaryEncoding.assignmentBits assignments)))
      (some (cfg (cleanupEntry (ExtensionCertificate.check bins items fixed assignments))
        (canonicalRun bins items fixed assignments).finish))
      (canonicalTime.eval ((BinaryEncoding.extensionBits bins items fixed).length +
        (BinaryEncoding.assignmentBits assignments).length)) :=
  enlarge (canonicalRun bins items fixed assignments).execution
    (canonicalBudget_le bins items fixed assignments)

structure DecisionRun (query witness : List Bool) where
  finish : Tape → List Bool
  execution : StateTransition.EvalsToInTime machine.step
    (initList machine (CookLevin.pairBits (query, witness)))
    (some (cfg (cleanupEntry (ExtensionCertificate.verify (query, witness))) finish))
    (decisionTime.eval (CookLevin.pairBits (query, witness)).length)

noncomputable def decisionRun (query witness : List Bool) : DecisionRun query witness := by
  have frontend := frontendInTime query witness
  have frontendBound : 16 * ((CookLevin.pairBits (query, witness)).length + 1) ≤
      decisionTime.eval (CookLevin.pairBits (query, witness)).length := by
    simp only [decisionTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    omega
  cases queryDecoded : BinaryEncoding.decodeExtension query with
  | none =>
      refine ⟨frontendTapes query witness, ?_⟩
      simpa [frontendExit, frontendAccepted, queryDecoded, ExtensionCertificate.verify] using
        enlarge frontend frontendBound
  | some data =>
      rcases data with ⟨bins, items, fixed⟩
      cases witnessDecoded : BinaryEncoding.decodeAssignments witness with
      | none =>
          refine ⟨frontendTapes query witness, ?_⟩
          simpa [frontendExit, frontendAccepted, queryDecoded, witnessDecoded,
            ExtensionCertificate.verify] using enlarge frontend frontendBound
      | some assignments =>
          have queryEncoding := BinaryEncoding.decodeExtension_sound queryDecoded
          have witnessEncoding := BinaryEncoding.decodeAssignments_sound witnessDecoded
          have canonical := canonicalInPolynomialTime bins items fixed assignments
          rw [← queryEncoding, ← witnessEncoding] at canonical
          have parsedPrefix : StateTransition.EvalsToInTime machine.step
              (initList machine (CookLevin.pairBits (query, witness)))
              (some (cfg (some (entry .fields)) (fieldInput query witness)))
              (16 * ((CookLevin.pairBits (query, witness)).length + 1)) := by
            simpa [frontendExit, frontendAccepted, frontendTapes, queryDecoded, witnessDecoded]
              using frontend
          have complete := join parsedPrefix canonical
          refine ⟨(canonicalRun bins items fixed assignments).finish, ?_⟩
          have lengthBound : query.length + witness.length ≤
              (CookLevin.pairBits (query, witness)).length := by
            rw [CookLevin.pairBits_length]
            dsimp only
            omega
          have canonicalBound := MachineComposition.natPolynomial_eval_mono canonicalTime lengthBound
          have budget : 16 * ((CookLevin.pairBits (query, witness)).length + 1) +
              canonicalTime.eval (query.length + witness.length) ≤
              decisionTime.eval (CookLevin.pairBits (query, witness)).length := by
            simp only [decisionTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_X]
            omega
          simpa only [ExtensionCertificate.verify, queryDecoded, witnessDecoded] using
            enlarge complete budget

theorem initialConfiguration (input : List Bool) :
    initList machine input = cfg (some (entry .pair)) (Function.update (fun _ => []) 0 input) := by
  unfold initList cfg machine
  congr 1
  funext k
  fin_cases k <;> rfl

theorem finalConfiguration (result : Bool) :
    cfg none (resultTapes result) = haltList machine [result] := by
  unfold haltList cfg resultTapes
  congr 1
  funext k
  fin_cases k <;> rfl

theorem initial_mass (input : List Bool) :
    MachineDrainMany.lengthSum allTapes (initList machine input).stk = input.length := by
  rw [initialConfiguration]
  simp [MachineDrainMany.lengthSum, allTapes, List.ofFn_succ, cfg]

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C (40 * Runtime.programPushBound machine + 1) * decisionTime +
    Polynomial.X + Polynomial.C 41

noncomputable def outputsInTime (query witness : List Bool) :
    TM2OutputsInTime machine (CookLevin.pairBits (query, witness))
      (some [ExtensionCertificate.verify (query, witness)])
      (timePolynomial.eval (CookLevin.pairBits (query, witness)).length) := by
  let run := decisionRun query witness
  have cleanup := cleanupInTime (ExtensionCertificate.verify (query, witness)) run.finish
  have complete := join run.execution cleanup
  have space := ExtensionMachineSpace.execution_lengthSum machine allTapes run.execution
  change MachineDrainMany.lengthSum allTapes run.finish ≤
    MachineDrainMany.lengthSum allTapes
      (initList machine (CookLevin.pairBits (query, witness))).stk +
      allTapes.length * (decisionTime.eval (CookLevin.pairBits (query, witness)).length *
        Runtime.programPushBound machine) at space
  rw [initial_mass] at space
  simp only [allTapes, List.length_ofFn] at space
  have budget :
      decisionTime.eval (CookLevin.pairBits (query, witness)).length +
        (MachineDrainMany.lengthSum allTapes run.finish + 41) ≤
      timePolynomial.eval (CookLevin.pairBits (query, witness)).length := by
    calc
      _ ≤ decisionTime.eval (CookLevin.pairBits (query, witness)).length +
          ((CookLevin.pairBits (query, witness)).length +
            40 * (decisionTime.eval (CookLevin.pairBits (query, witness)).length *
              Runtime.programPushBound machine) + 41) := Nat.add_le_add_left
                (Nat.add_le_add_right space 41) _
      _ = _ := by
        simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X]
        ring
  change StateTransition.EvalsToInTime machine.step
    (initList machine (CookLevin.pairBits (query, witness)))
    (some (haltList machine [ExtensionCertificate.verify (query, witness)]))
    (timePolynomial.eval (CookLevin.pairBits (query, witness)).length)
  simpa only [finalConfiguration] using enlarge complete budget

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime CookLevin.pairBits (fun bit : Bool => [bit])
      ExtensionCertificate.verify where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun pair := by
    rcases pair with ⟨query, witness⟩
    change TM2OutputsInTime machine ((CookLevin.pairBits (query, witness)).map id)
      (some ([ExtensionCertificate.verify (query, witness)].map id))
      (timePolynomial.eval (CookLevin.pairBits (query, witness)).length)
    have input_eq : @List.map (machine.Γ machine.k₀) (machine.Γ machine.k₀) id
        (CookLevin.pairBits (query, witness)) = CookLevin.pairBits (query, witness) := List.map_id _
    simpa only [input_eq, List.map_cons, List.map_nil, id_eq] using! outputsInTime query witness

end BinPackingGap.ExtensionVerifierMachine

end OAI
end


