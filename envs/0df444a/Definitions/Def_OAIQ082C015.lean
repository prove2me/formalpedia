-- Prove2me | Definitions.Def_OAIQ082C015
-- name    : OAIQ082C015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:35:24.460708+00:00
-- url     : https://prove2.me/theorems/1c9ba99e-f39a-4757-91b6-d3ae7b9f8e0c
-- title:
--   Definitions bundle OAIQ082C015 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 193 declarations of OpenAI's Lean: 99 definitions, 1 inductive type or structure, 3 instances and 90 theorems. The definitions and types are `OAI.BinPackingGap.InventoryData.earlierW`, `OAI.BinPackingGap.InventoryData.earlierWItems`, `OAI.BinPackingGap.InventoryData.encodedCoordinate`, `OAI.BinPackingGap.InventoryData.encodedLabel`, `OAI.BinPackingGap.InventoryData.encodedSubclass`, `OAI.BinPackingGap.InventoryData.globalUnit`, `OAI.BinPackingGap.InventoryData.localDepth`, `OAI.BinPackingGap.InventoryData.packingOfRoleEquivs`, `OAI.BinPackingGap.InventoryData.prefixJobIndex`, `OAI.BinPackingGap.InventoryData.prefixWIndex`, `OAI.BinPackingGap.InventoryData.roleLabelData`, `OAI.BinPackingGap.InventoryData.rowPosition`, `OAI.BinPackingGap.LiteralSlotGraph.Independent`, `OAI.BinPackingGap.LiteralSlotGraph.chosenSlot`, `OAI.BinPackingGap.LiteralSlotGraph.failedClauses`, `OAI.BinPackingGap.LiteralSlotGraph.satisfiedClauses`, `OAI.BinPackingGap.LiteralSlotGraph.selectedSlots`, `OAI.BinPackingGap.LiteralSlotGraphMachine.TaggedLiteral`, `OAI.BinPackingGap.LiteralSlotGraphMachine.bodyAccumulator`, `OAI.BinPackingGap.LiteralSlotGraphMachine.clauseLiterals`, `OAI.BinPackingGap.LiteralSlotGraphMachine.edgeRecords`, `OAI.BinPackingGap.LiteralSlotGraphMachine.emitPair`, `OAI.BinPackingGap.LiteralSlotGraphMachine.formulaLiterals`, `OAI.BinPackingGap.LiteralSlotGraphMachine.forwardRows`, `OAI.BinPackingGap.LiteralSlotGraphMachine.frame`, `OAI.BinPackingGap.LiteralSlotGraphMachine.increment`, `OAI.BinPackingGap.LiteralSlotGraphMachine.indexFrom`, `OAI.BinPackingGap.LiteralSlotGraphMachine.innerBodyCost`, `OAI.BinPackingGap.LiteralSlotGraphMachine.innerBodyResult`, `OAI.BinPackingGap.LiteralSlotGraphMachine.innerLoopCost`, `OAI.BinPackingGap.LiteralSlotGraphMachine.innerLoopResult`, `OAI.BinPackingGap.LiteralSlotGraphMachine.literalBits`, `OAI.BinPackingGap.LiteralSlotGraphMachine.literalsBits`, `OAI.BinPackingGap.LiteralSlotGraphMachine.outerBodyCost`, `OAI.BinPackingGap.LiteralSlotGraphMachine.outerBodyResult`, `OAI.BinPackingGap.LiteralSlotGraphMachine.outerLoopCost`, `OAI.BinPackingGap.LiteralSlotGraphMachine.outerLoopResult`, `OAI.BinPackingGap.LiteralSlotGraphMachine.pairEntry`, `OAI.BinPackingGap.LiteralSlotGraphMachine.pairRecord`, `OAI.BinPackingGap.LiteralSlotGraphMachine.phaseCosts` and 60 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Hardness_LiteralSlotGraph`, `BinPacking_Hardness_LiteralSlotGraphComputation`, `BinPacking_Hardness_LiteralSlotGraphEnumeration`, `BinPacking_Inventory_EdgeLongConsumption`, `BinPacking_Inventory_IntegralSpeciesCounts`, `BinPacking_Inventory_InventoryPrefixConservation`, `BinPacking_Inventory_InventoryScores`, `BinPacking_Inventory_PackingExclusions`, `BinPacking_Machines_MachineBoundedIteration`, `BinPacking_Machines_MachineKeepDecisionTyped`, `BinPacking_Machines_PackingJobCoverage`, `BinPacking_Machines_PackingPowerProgram`, `BinPacking_Packing_GoodAnchorBound`, `BinPacking_Packing_LiteralSlotGap`, `BinPacking_Packing_LocalJobCounts`, `BinPacking_Packing_LocalTemplateBases`, `BinPacking_Packing_PackingCoordinates`, `BinPacking_Packing_PackingFeasibility`, `BinPacking_Packing_PackingScalar`, `BinPacking_Packing_PackingScalarExpression`, `BinPacking_Packing_PackingSelections`, `BinPacking_Packing_PhysicalRolePacking`, `BinPacking_Search_SearchFinalizeMachine`, `BinPacking_Search_SearchFixedReplaceMachine`, `BinPacking_Search_SearchInitialItemsMachine`, `BinPacking_Search_SearchInitialShapeMachine`, `BinPacking_Search_SearchInitializeEncoding`, `BinPacking_Search_SearchPrepareMachine`, `BinPacking_Trees_IntegerTreeGeometry`, `BinPacking_Trees_TestGeometry`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C005`, `OAIQ082C006`, `OAIQ082C007`, `OAIQ082C008` and `OAIQ082C009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C021` and `OAIQ082C022`; the statements `OAI_BinPackingGap_InventoryData_badAnchorsAt_card_le` and `OAI.BinPackingGap.InventoryData.badAnchorsAt_card_le_oaiq082`; the proofs of `OAI_BinPackingGap_InventoryData_badAnchorsAt_card_le` and `OAI.BinPackingGap.InventoryData.badAnchorsAt_card_le_oaiq082`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C005
import Definitions.Def_OAIQ082C006
import Definitions.Def_OAIQ082C007
import Definitions.Def_OAIQ082C008
import Definitions.Def_OAIQ082C009

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_LiteralSlotGraph
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype _root_.OAI.BinPackingGap.instFintypeGlobalSpecies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraph

open BinPackingGames.Foundations.Target

theorem graph_edges_nonempty (F : Formula) (hF : F.clauses ≠ []) :
    (graph F).edges ≠ [] := by
  have hm : 0 < F.clauses.length := List.length_pos_iff.mpr hF
  let c : Fin F.clauses.length := ⟨0, hm⟩
  have he : (index F c 0, index F c 1) ∈ edgeList F := by
    apply (mem_edgeList _ _ _).mpr
    constructor
    · change 3 * c.val + 0 < 3 * c.val + 1
      omega
    · exact Or.inl (by simp)
  intro hn
  change edgeList F = [] at hn
  simp [hn] at he

def Independent (F : Formula) (S : Finset (Vertex F)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬Conflict F u v

def chosenSlot (F : Formula) (A : Fin F.variables → Bool)
    (c : Fin F.clauses.length) : Fin 3 :=
  if (F.clauses[c])[0].eval A = true then 0
  else if (F.clauses[c])[1].eval A = true then 1 else 2

def selectedSlots (F : Formula) (A : Fin F.variables → Bool) : Finset (Vertex F) :=
  Finset.univ.image (fun c => index F c (chosenSlot F A c))

end BinPackingGap.LiteralSlotGraph

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_MachineBoundedIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.MachineBoundedIteration

open Turing BinPackingGames.Foundations.Complexity

noncomputable def computation {α : Type} (encode : α → List Bool) (step : α → α)
    (body : TM2ComputableInPolyTime encode encode step)
    (growth : Polynomial Nat) (bounded : GrowthBound encode step growth) :
    TM2ComputableInPolyTime (inputBits encode) encode (iterate step) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := timeBound body.time growth
  outputsFun p := by
    let words : Nat → List Bool := fun i => encode (step^[i] p.2)
    let budgets : Nat → Nat := fun i => body.time.eval (words i).length
    have runs : ∀ i, i < p.1 →
        TM2OutputsInTime body.tm ((words i).map body.inputAlphabet.symm)
          (some ((words (i + 1)).map body.outputAlphabet.symm)) (budgets i) := by
      intro i _
      simpa only [words, budgets, Function.iterate_succ_apply', Equiv.invFun_as_coe] using
        body.outputsFun (step^[i] p.2)
    have run := MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
      p.1 words budgets runs
    have countBound : p.1 ≤ (inputBits encode p).length := by
      rw [inputBits_length]
      omega
    have bodyBound : ∀ i, i < p.1 →
        budgets i ≤ body.time.eval (growth.eval (inputBits encode p).length) := by
      intro i hi
      exact MachineComposition.natPolynomial_eval_mono body.time
        (bounded p i (Nat.le_of_lt hi))
    have lengthBound : ∀ i, i ≤ p.1 →
        (words i).length ≤ growth.eval (inputBits encode p).length := by
      intro i hi
      exact bounded p i hi
    have loopBound := MachineRepeat.loopBudget_le p.1 words budgets
      (body.time.eval (growth.eval (inputBits encode p).length))
      (growth.eval (inputBits encode p).length) bodyBound lengthBound
    have productBound := Nat.mul_le_mul_right
      (body.time.eval (growth.eval (inputBits encode p).length) +
        2 * growth.eval (inputBits encode p).length + 3) countBound
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    have actualBound := run.steps_le_m
    rw [timeBound_eval]
    omega

end BinPackingGap.MachineBoundedIteration

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_MachineKeepDecisionTyped
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.MachineKeepDecision

section

open Turing BinPackingGames.Foundations
open Complexity

def program (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool)
    (output : M.Γ M.k₁ ≃ Bool) : Label M → TM2.Stmt (Symbols M) (Label M) (State M) :=
  MachineEmbedding.program (some (.inr .transfer)) M.m (auxProgram M input output)

def machine (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool)
    (output : M.Γ M.k₁ ≃ Bool) : FinTM2 where
  K := Tape M
  kFin := by letI := M.kFin; exact inferInstanceAs (Fintype (Tape M))
  k₀ := .inl M.k₀
  k₁ := .inr .output
  Γ := Symbols M
  Λ := Label M
  ΛFin := by letI := M.ΛFin; exact inferInstanceAs (Fintype (Label M))
  main := .inr .parse
  σ := State M
  σFin := by
    letI := M.σFin
    letI := M.Γk₀Fin
    exact inferInstanceAs (Fintype (State M))
  initialState := (M.initialState, none)
  Γk₀Fin := M.Γk₀Fin
  m := program M input output

def embedded (M : FinTM2) (saved : List (M.Γ M.k₀)) (c : M.Cfg) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  MachineEmbedding.configuration (some (.inr .transfer))
    (none : Option (M.Γ M.k₀)) (extraTapes M saved []) c

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem parseStep_digit (bit : Bool) (word saved : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M (input.symm true :: input.symm bit :: word) saved) =
    some (inputConfig M word (input.symm bit :: saved)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState, none)
    (inputTapes M (input.symm true :: input.symm bit :: word) saved)) = _
  simp [auxProgram, TM2.stepAux, inputTapes_update_input, inputTapes_update_saved,
    inputConfig]

theorem parseStep_end (word saved : List (M.Γ M.k₀)) :
    (machine M input output).step
      (inputConfig M (input.symm false :: word) saved) =
    some (embedded M saved (initList M word)) := by
  change some (TM2.stepAux (auxProgram M input output .parse)
    (M.initialState, none) (inputTapes M (input.symm false :: word) saved)) = _
  simp only [auxProgram, TM2.stepAux, inputTapes_input, List.head?_cons,
    Option.getD_some, Equiv.apply_symm_apply, Bool.cond_false, List.tail_cons,
    inputTapes_update_input]
  rfl

theorem parseTrace (state : List Bool) (query saved : List (M.Γ M.k₀)) :
    (MachineComposition.advance (machine M input output).step)^[state.length + 1]
      (some (inputConfig M ((frame state).map input.symm ++ query) saved)) =
    some (embedded M (state.reverse.map input.symm ++ saved) (initList M query)) := by
  induction state generalizing saved with
  | nil =>
    simpa only [frame, List.map_singleton, List.singleton_append, List.length_nil,
      Nat.zero_add, List.reverse_nil, List.map_nil, List.nil_append,
      Function.iterate_one, MachineComposition.advance_some] using!
      parseStep_end M input output query saved
  | cons bit state ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (machine M input output).step)^[state.length + 1]
      ((machine M input output).step
        (inputConfig M ((frame (bit :: state)).map input.symm ++ query) saved)) = _
    simp only [frame, List.map_cons, List.cons_append]
    rw [parseStep_digit]
    simpa only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append] using! ih (input.symm bit :: saved)

theorem inputConfig_init (word : List (M.Γ M.k₀)) :
    inputConfig M word [] = initList (machine M input output) word := by
  unfold inputConfig initList
  congr 1
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList, machine]; rfl
    · simp [inputTapes, initList, machine, h]
  | inr k => cases k <;> simp [inputTapes, initList, machine, extraTapes]

def decisionExecution (saved query : List (M.Γ M.k₀))
    (answer : M.Γ M.k₁) (budget : Nat)
    (run : TM2OutputsInTime M query (some [answer]) budget) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M saved (initList M query))
      (some (embedded M saved (haltList M [answer]))) budget :=
  MachineComposition.embeddedExecution (some (.inr .transfer : Label M))
    (none : Option (M.Γ M.k₀)) (extraTapes M saved []) M.m
    (auxProgram M input output) run

theorem returnTransfer_tapes (saved : List (M.Γ M.k₀)) (answer : M.Γ M.k₁) :
    BinPackingGames.Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .saved) (.inr .output)
      (embedded M saved (haltList M [answer])).stk [] saved.reverse =
    returnTapes M answer saved.reverse := by
  funext k
  cases k with
  | inl k => simp [BinPackingGames.Reduction.MachineTransfer.tapesAt, embedded,
      MachineEmbedding.configuration, returnTapes]
  | inr k => cases k <;> simp [BinPackingGames.Reduction.MachineTransfer.tapesAt, embedded,
      MachineEmbedding.configuration, returnTapes, extraTapes]

def returnTransfer (saved : List (M.Γ M.k₀)) (answer : M.Γ M.k₁) :
    StateTransition.EvalsToInTime (machine M input output).step
      (embedded M saved (haltList M [answer]))
      (some (returnConfig M answer saved.reverse)) (saved.length + 1) := by
  have run := BinPackingGames.Reduction.MachineTransfer.transferAtInTime
    (Γ := Symbols M) (.inr .saved) (.inr .output) (by intro h; cases h)
    id (input.symm false) (.inr .transfer) (some (.inr .finish))
    (program M input output) rfl
    (embedded M saved (haltList M [answer])).stk M.initialState none
  have hs : (embedded M saved (haltList M [answer])).stk (.inr .saved) = saved := rfl
  have hd : (embedded M saved (haltList M [answer])).stk (.inr .output) = [] := rfl
  rw [hs, hd, List.map_id, List.append_nil, returnTransfer_tapes] at run
  exact run

theorem finish_tapes (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    Function.update
      (Function.update (returnTapes M answer word) (.inl M.k₁) [])
      (.inr .output) (input.symm (output answer) :: word) =
    (haltList (machine M input output) (input.symm (output answer) :: word)).stk := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₁
    · subst k; simp [returnTapes, haltList, machine]
    · simp [returnTapes, haltList, machine, h]
  | inr k =>
    cases k <;> simp [returnTapes, haltList, machine, extraTapes]
    rfl

theorem finishStep (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    (machine M input output).step (returnConfig M answer word) =
    some (haltList (machine M input output) (input.symm (output answer) :: word)) := by
  have ha : returnTapes M answer word (.inl M.k₁) = [answer] := by
    simp [returnTapes, haltList]
  have hw : returnTapes M answer word (.inr .output) = word := rfl
  change some (TM2.stepAux (auxProgram M input output .finish)
    (M.initialState, none) (returnTapes M answer word)) = _
  simp only [auxProgram, TM2.stepAux, ha, List.head?_cons, List.tail_cons,
    Option.map_some, Option.getD_some]
  have hw' : (Function.update (returnTapes M answer word) (.inl M.k₁) [])
      (.inr .output) = word := by simp [hw]
  rw [hw', finish_tapes]
  rfl

def outputsInTime (state query : List Bool) (answer : Bool) (budget : Nat)
    (run : TM2OutputsInTime M (query.map input.symm)
      (some [output.symm answer]) budget) :
    TM2OutputsInTime (machine M input output)
      ((frame state ++ query).map input.symm)
      (some ((answer :: state).map input.symm))
      (budget + 2 * state.length + 3) := by
  let parsed : StateTransition.EvalsToInTime (machine M input output).step
      (inputConfig M ((frame state).map input.symm ++ query.map input.symm) [])
      (some (embedded M (state.reverse.map input.symm)
        (initList M (query.map input.symm)))) (state.length + 1) := {
    steps := state.length + 1
    evals_in_steps := by
      change (MachineComposition.advance (machine M input output).step)^[state.length + 1] _ = _
      simpa only [List.append_nil] using!
        parseTrace M input output state (query.map input.symm) []
    steps_le_m := le_refl _ }
  have decision := decisionExecution M input output (state.reverse.map input.symm)
    (query.map input.symm) (output.symm answer) budget run
  have transfer := returnTransfer M input output (state.reverse.map input.symm)
    (output.symm answer)
  have restored : (state.reverse.map input.symm).reverse = state.map input.symm := by
    rw [List.map_reverse, List.reverse_reverse]
  rw [restored, List.length_map, List.length_reverse] at transfer
  have finish := oneStep _ _ _ (finishStep M input output
    (output.symm answer) (state.map input.symm))
  simp only [Equiv.apply_symm_apply] at finish
  have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parsed decision
  have second := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first transfer
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ second finish
  rw [inputConfig_init] at full
  simp only [← List.map_append] at full
  refine { toEvalsTo := full.toEvalsTo, steps_le_m := ?_ }
  have h := full.steps_le_m
  omega

theorem machine_finiteAlphabet (finite : MachineFiniteAlphabet.FiniteAlphabet M) :
    MachineFiniteAlphabet.FiniteAlphabet (machine M input output) := by
  intro k
  cases k with
  | inl k => exact finite k
  | inr _ => exact MachineFiniteAlphabet.input_finite M

noncomputable def computation (decide : List Bool → Bool)
    (certificate : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) decide) :
    TM2ComputableInPolyTime inputBits outputBits (keep decide) where
  tm := machine certificate.tm certificate.inputAlphabet certificate.outputAlphabet
  inputAlphabet := certificate.inputAlphabet
  outputAlphabet := certificate.inputAlphabet
  time := certificate.time + Polynomial.C 2 * Polynomial.X + Polynomial.C 3
  outputsFun pair := by
    have run := outputsInTime certificate.tm certificate.inputAlphabet
      certificate.outputAlphabet pair.1 pair.2 (decide pair.2)
      (certificate.time.eval pair.2.length) (certificate.outputsFun pair.2)
    have hq : pair.2.length ≤ (inputBits pair).length := by
      rw [inputBits_length]; omega
    have hs : pair.1.length ≤ (inputBits pair).length := by
      rw [inputBits_length]; omega
    have ht := MachineComposition.natPolynomial_eval_mono certificate.time hq
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    have hr := run.steps_le_m
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

theorem computation_finiteAlphabet (decide : List Bool → Bool)
    (certificate : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) decide)
    (finite : MachineFiniteAlphabet.FiniteAlphabet certificate.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (computation decide certificate).tm :=
  machine_finiteAlphabet certificate.tm certificate.inputAlphabet certificate.outputAlphabet finite

end

open Turing BinPackingGames.Foundations.Complexity

noncomputable def computationWithSavedCodec {α : Type} (encode : α → List Bool)
    (decide : List Bool → Bool)
    (certificate : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) decide) :
    TM2ComputableInPolyTime (typedInputBits encode) (typedOutputBits encode)
      (typedKeep decide) where
  tm := (computation decide certificate).tm
  inputAlphabet := (computation decide certificate).inputAlphabet
  outputAlphabet := (computation decide certificate).outputAlphabet
  time := (computation decide certificate).time
  outputsFun p := (computation decide certificate).outputsFun (encode p.1, p.2)

theorem computationWithSavedCodec_finiteAlphabet {α : Type} (encode : α → List Bool)
    (decide : List Bool → Bool)
    (certificate : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) decide)
    (finite : MachineFiniteAlphabet.FiniteAlphabet certificate.tm) :
    MachineFiniteAlphabet.FiniteAlphabet
      (computationWithSavedCodec encode decide certificate).tm :=
  computation_finiteAlphabet decide certificate finite

end BinPackingGap.MachineKeepDecision

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitializeEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchEncoding

open SearchSemantics BinaryEncoding BinPackingGames.Foundations.Complexity

theorem listBits_set_length_le {α : Type} (encode : α → List Bool)
    (xs : List α) (i : Nat) (x : α) :
    (listBits encode (xs.set i x)).length ≤
      (listBits encode xs).length + (encode x).length := by
  induction xs generalizing i with
  | nil => simp [listBits]
  | cons head tail ih =>
    cases i with
    | zero => simp [listBits]; omega
    | succ i =>
      have bound := ih i
      simp only [List.set_cons_succ, listBits, List.length_cons, List.length_append]
      omega

end BinPackingGap.SearchEncoding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialItemsMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialItemsMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer

def instruction : Control → TM2.Stmt Alphabet Label State
  | .entry => .pop 0 (fun s bit => (s.1, bit))
      (.branch (fun s => s.2.getD false)
        (jump (.control .copyOut)) (jump (.control .malformedDrain)))
  | .malformedDrain => MachineDrain.drain 0 (.control .malformedDrain)
      (some (.control .malformedFinish))
  | .malformedFinish => .push 0 (fun _ => false) (.push 0 (fun _ => false)
      (.push 0 (fun _ => false) (.load (fun _ => clean true) .halt)))
  | .copyOut => loopAt 0 2 id false (.control .copyOut) (some (.control .copyBack))
  | .copyBack => MachineCopy.forkLoop 2 0 1 false (.control .copyBack)
      (some (.control .seed))
  | .seed => .push 7 (fun _ => false) (jump (.control .marker))
  | .marker => .pop 1 (fun s bit => (s.1, bit))
      (.branch (fun s => s.2.getD false)
        (.push 7 (fun _ => true) (jump (.number .numerator .scan)))
        (jump (.control .countOut)))
  | .positive => .pop 3 (fun s bit => (s.1, bit))
      (.branch (fun s => s.2.isSome)
        (.push 3 (fun s => s.2.getD false) (jump (.number .denominator .scan)))
        (.load (fun _ => clean false) (.goto fun _ => .number .denominator .scan)))
  | .failed => .load (fun _ => clean false) (.goto fun _ => .control .clearNumerator)
  | .clearNumerator => MachineDrain.drain 3 (.control .clearNumerator)
      (some (.control .clearDenominator))
  | .clearDenominator => MachineDrain.drain 4 (.control .clearDenominator)
      (some (.control .marker))
  | .countOut => loopAt 7 2 id false (.control .countOut) (some (.control .countBack))
  | .countBack => loopAt 2 0 id false (.control .countBack) (some (.control .finish))
  | .finish => .push 0 validity (.load (fun _ => clean true) .halt)

end BinPackingGap.SearchInitialItemsMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPowerProgram
attribute [-instance] _root_.OAI.BinPackingGap.LiteralSlotGraphMachine.instDecidableBodyEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

open Turing BinPackingGames.Foundations BinPackingGames.Foundations.Target
open FiniteTapeProgram

def transfer (source destination : Tape) : Program :=
  BooleanTapeCode.transfer source destination
def frame (source scratchTape destination : Tape) : Program :=
  BooleanTapeCode.frame source scratchTape destination
def increment (binary : Tape) : Program :=
  BooleanTapeCode.increment binary .unary .scratch

def vertexBody : Program := sequence [
  pushBit .accumulator true,
  frame .outerIndex .scratch .accumulator,
  increment .outerIndex]

def vertices : Program :=
  .loop (.pop .vertexCount saveHead .done) (fun s => s.2.isSome) vertexBody

def emitPair : Program := sequence [
  pushBit .accumulator true,
  frame .outerIndex .scratch .accumulator,
  frame .innerIndex .scratch .accumulator]

end BinPackingGap.LiteralSlotGraphMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_LiteralSlotGraphEnumeration
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

section

open FiniteTapeProgram BinPackingGames.Foundations.Complexity

theorem readVariable_loop_exec (source destination : Tape) (different : source ≠ destination)
    (base : Tape → List Bool) (s : State) (n : Nat) (suffix marks : List Bool) :
    Exec (.loop (.pop source saveHead .done) (fun s => s.2.getD false)
      (.atom (.push destination (fun _ => true) .done)))
      ⟨s, twoTapes base source destination (encodeWord n ++ suffix) marks⟩ (2 * n + 1)
      ⟨(s.1, some false), twoTapes base source destination suffix (List.replicate n true ++ marks)⟩ := by
  induction n generalizing s marks with
  | zero =>
      have h := Exec.loop_false (g := Action.pop source saveHead .done)
        (p := fun s : State => s.2.getD false)
        (a := Code.atom (.push destination (fun _ => true) .done))
        (d := ⟨s, twoTapes base source destination (encodeWord 0 ++ suffix) marks⟩)
        (by simp [Action.eval, saveHead, encodeWord, twoTapes_source, different])
      simpa [Action.eval, saveHead, encodeWord, twoTapes_source, different,
        twoTapes_update_source] using h
  | succ n ih =>
      let d : Data Tape State :=
        ⟨s, twoTapes base source destination (encodeWord (n + 1) ++ suffix) marks⟩
      have body := Exec.atom (.push destination (fun _ => true) .done)
        ((Action.pop source saveHead .done).eval d)
      have bodyEq : (Action.push destination (fun _ : State => true) .done).eval
          ((Action.pop source saveHead .done).eval d) =
          ⟨(s.1, some true), twoTapes base source destination
            (encodeWord n ++ suffix) (true :: marks)⟩ := by
        simp [d, Action.eval, saveHead, encodeWord, List.replicate_succ,
          twoTapes_source, different, twoTapes_update_source]
      rw [bodyEq] at body
      have tail := ih (s.1, some true) (true :: marks)
      have run := Exec.loop_true
        (g := Action.pop source saveHead .done)
        (p := fun s : State => s.2.getD false)
        (by simp [d, Action.eval, saveHead, encodeWord, List.replicate_succ,
          twoTapes_source, different]) body tail
      have marksEq : List.replicate n true ++ true :: marks =
          List.replicate (n + 1) true ++ marks := by
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.singleton_append]
      simpa only [d, marksEq, show 1 + (2 * n + 1) + 1 = 2 * (n + 1) + 1 by omega] using run

theorem readVariable_exec (source destination : Tape) (different : source ≠ destination)
    (base : Tape → List Bool) (s : State) (n : Nat) (suffix marks : List Bool) :
    Exec (readVariable source destination)
      ⟨s, twoTapes base source destination (encodeWord n ++ suffix) marks⟩ (2 * n + 2)
      ⟨(s.1, none), twoTapes base source destination suffix (List.replicate n true ++ marks)⟩ := by
  have run := readVariable_loop_exec source destination different base s n suffix marks
  have final := Exec.atom (.load resetHead .done)
    (Data.mk (s.1, some false) (twoTapes base source destination suffix (List.replicate n true ++ marks)))
  simpa [readVariable, Action.eval, resetHead, Nat.add_assoc] using Exec.seq run final

theorem readSign_exec (source : Tape) (setSign : Control → Bool → Control)
    (base : Tape → List Bool) (s : State) (sign : Bool) (suffix : List Bool) :
    Exec (readSign source setSign)
      ⟨s, Function.update base source (encodeWord (if sign then 1 else 0) ++ suffix)⟩ 1
      ⟨BooleanTapeCode.clean (setSign s.1.1 sign), Function.update base source suffix⟩ := by
  have run := Exec.atom
    (.pop source saveHead
      (.load (fun s => ((setSign s.1.1 (s.2.getD false), ()), s.2))
        (.branch (fun s => s.2.getD false)
          (.pop source saveHead (.load resetHead .done))
          (.load resetHead .done))))
    (Data.mk s (Function.update base source (encodeWord (if sign then 1 else 0) ++ suffix)))
  cases sign <;> simpa [readSign, Action.eval, saveHead, resetHead, BooleanTapeCode.clean,
    encodeWord] using run

theorem compareLoop_exec (base : Tape → List Bool) (a : Control)
    (register : Option Bool) (n m : Nat) :
    Exec (.loop compareGuard (fun s : State => s.1.1.otherHead.isSome || s.2.isSome) skip)
      ⟨((a, ()), register), twoTapes base .comparison .innerVariable
        (List.replicate n true) (List.replicate m true)⟩
      (2 * max n m + 1)
      ⟨BooleanTapeCode.clean (comparisonResult a n m),
        twoTapes base .comparison .innerVariable [] []⟩ := by
  by_cases hz : n + m = 0
  · have hn : n = 0 := by omega
    have hm : m = 0 := by omega
    subst n; subst m
    have run := Exec.loop_false (g := compareGuard)
      (p := fun s : State => s.1.1.otherHead.isSome || s.2.isSome) (a := skip)
      (d := Data.mk ((a, ()), register) (twoTapes base .comparison .innerVariable [] []))
      (by rw [show ([] : List Bool) = List.replicate 0 true from rfl,
        compareGuard_eval]; simp [comparedControl, counterHead])
    have finish : compareGuard.eval
        ⟨((a, ()), register), twoTapes base .comparison .innerVariable [] []⟩ =
        ⟨BooleanTapeCode.clean (comparisonResult a 0 0),
          twoTapes base .comparison .innerVariable [] []⟩ := by
      simpa [comparisonResult, comparedControl, counterHead, BooleanTapeCode.clean] using
        compareGuard_eval base a register 0 0
    rw [finish] at run
    simpa using run
  · have headNonempty : (counterHead n).isSome || (counterHead m).isSome = true := by
      cases n <;> cases m <;> simp_all [counterHead]
    let next := comparedControl a (counterHead n) (counterHead m)
    let d : Data Tape State :=
      ⟨((a, ()), register), twoTapes base .comparison .innerVariable
        (List.replicate n true) (List.replicate m true)⟩
    have body : Exec skip (compareGuard.eval d) 1 (compareGuard.eval d) :=
      Exec.atom .done _
    have tail := compareLoop_exec base next (counterHead m) (n - 1) (m - 1)
    have run := Exec.loop_true (g := compareGuard)
      (p := fun s : State => s.1.1.otherHead.isSome || s.2.isSome)
      (d := d) (by simpa [d, compareGuard_eval, comparedControl] using headNonempty)
      body (by simpa only [d, compareGuard_eval, next] using tail)
    have cost : 1 + (2 * max (n - 1) (m - 1) + 1) + 1 = 2 * max n m + 1 := by omega
    simpa only [d, next, comparisonResult_step, cost] using run
termination_by n + m
decreasing_by omega

theorem compareVariables_exec (base : Tape → List Bool) (a : Control)
    (register : Option Bool) (n m : Nat) :
    Exec compareVariables
      ⟨((a, ()), register), twoTapes base .comparison .innerVariable
        (List.replicate n true) (List.replicate m true)⟩
      (2 * max n m + 2)
      ⟨BooleanTapeCode.clean {a with otherHead := none, equal := decide (n = m)},
        twoTapes base .comparison .innerVariable [] []⟩ := by
  have first := Exec.atom (.load (mapControl (fun a => {a with equal := true})) .done)
    (Data.mk ((a, ()), register) (twoTapes base .comparison .innerVariable
      (List.replicate n true) (List.replicate m true)))
  have second := compareLoop_exec base {a with equal := true} register n m
  have run := Exec.seq (by simpa [Action.eval, mapControl] using first) second
  simpa [compareVariables, changeControl, comparisonResult,
    show 1 + (2 * max n m + 1) = 2 * max n m + 2 by omega] using run

def vertexBodyCost (i : Nat) : Nat :=
  3 * i.bits.length + UnaryToBinaryMachine.steps 1 i + 6

def vertexRecord (i : Nat) : List Bool := true :: BinaryEncoding.natBits i

def vertexRecords : Nat → Nat → List Bool
  | _, 0 => []
  | i, n + 1 => vertexRecord i ++ vertexRecords (i + 1) n

def vertexLoopCost : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, i => vertexBodyCost i + vertexLoopCost n (i + 1) + 1

def vertexResult (base : Tape → List Bool) (n i : Nat) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .vertexCount [])
    .outerIndex (i + n).bits) .accumulator
      ((vertexRecords i n).reverse ++ base .accumulator)

theorem vertexRecords_listBits (i n : Nat) :
    vertexRecords i n ++ [false] =
      BinaryEncoding.listBits BinaryEncoding.natBits (List.range' i n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      simp [vertexRecords, List.range'_succ, vertexRecord, BinaryEncoding.listBits,
        List.append_assoc, ih]

def pairRecord (u v : Nat) : List Bool :=
  true :: (BinaryEncoding.natBits u ++ BinaryEncoding.natBits v)

def literalBits (literal : RawLiteral) : List Bool :=
  encodeWord literal.1 ++ encodeWord (if literal.2 then 1 else 0)

def literalsBits (literals : List RawLiteral) : List Bool := literals.flatMap literalBits

def innerBodyCost (a : Control) (left right : RawLiteral) (u v : Nat) : Nat :=
  (2 * right.1 + 2) + (1 + (2 * (left.1 + 1) + ((2 * max left.1 right.1 + 2) +
    (branchCost a left right u v + ((1 + UnaryToBinaryMachine.steps 1 v) + (1 + 1))))))

def bodyAccumulator (base : Tape → List Bool) (a : Control) (left right : RawLiteral)
    (u v : Nat) : List Bool :=
  if bodyEdge a left right then (pairRecord u v).reverse ++ base .accumulator
  else base .accumulator

def innerBodyResult (base : Tape → List Bool) (a : Control) (left right : RawLiteral)
    (u v : Nat) (suffix : List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .innerSource suffix)
    .accumulator (bodyAccumulator base a left right u v)) .innerIndex (v + 1).bits

theorem literalsBits_cons (literal : RawLiteral) (rest : List RawLiteral) :
    literalsBits (literal :: rest) = literalBits literal ++ literalsBits rest := rfl

def edgeRecords (edges : List (Nat × Nat)) : List Bool :=
  edges.flatMap (fun edge => pairRecord edge.1 edge.2)

def innerLoopCost (a : Control) (left : RawLiteral) (u v : Nat) : List RawLiteral → Nat
  | [] => 1
  | right :: rest => innerBodyCost a left right u v +
      innerLoopCost (bodyControl a left right) left u (v + 1) rest + 1

def innerLoopResult (base : Tape → List Bool) (left : RawLiteral) (u v : Nat)
    (rest : List RawLiteral) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .innerSource [])
    .innerIndex (v + rest.length).bits) .accumulator
      ((edgeRecords (rowEdges u v left rest)).reverse ++ base .accumulator)

def outerBodyCost (a : Control) (left : RawLiteral) (u : Nat) (rest : List RawLiteral) : Nat :=
  (2 * left.1 + 2) + (1 + (2 * ((literalsBits rest).length + 1) +
    (2 * (u.bits.length + 1) + ((1 + UnaryToBinaryMachine.steps 1 u) + (1 +
      (innerLoopCost (rowStartControl a left) left u (u + 1) rest +
        (((u + 1 + rest.length).bits.length + 1) + ((left.1 + 1) +
          ((1 + UnaryToBinaryMachine.steps 1 u) + (1 + 1))))))))))

def outerBodyResult (base : Tape → List Bool) (left : RawLiteral) (u : Nat)
    (rest : List RawLiteral) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .input (literalsBits rest))
    .accumulator ((edgeRecords (rowEdges u (u + 1) left rest)).reverse ++ base .accumulator))
      .outerIndex (u + 1).bits

def outerLoopCost (a : Control) (u : Nat) : List RawLiteral → Nat
  | [] => 1
  | left :: rest => outerBodyCost a left u rest +
      outerLoopCost (outerBodyControl a left rest) (u + 1) rest + 1

def outerLoopResult (base : Tape → List Bool) (u : Nat) (literals : List RawLiteral) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .input [])
    .outerIndex (u + literals.length).bits) .accumulator
      ((edgeRecords (suffixEdges u literals)).reverse ++ base .accumulator)

theorem skipField_exec (source : Tape) (base : Tape → List Bool) (s : State)
    (n : Nat) (suffix : List Bool) (hS : base source = encodeWord n ++ suffix) :
    Exec (skipField source) ⟨s, base⟩ (2 * n + 1)
      ⟨(s.1, some false), Function.update base source suffix⟩ := by
  induction n generalizing base s with
  | zero =>
      have run := Exec.loop_false (g := Action.pop source saveHead .done)
        (p := fun s : State => s.2.getD false) (a := skip) (d := Data.mk s base)
        (by simp [Action.eval, saveHead, hS, encodeWord])
      simpa [skipField, Action.eval, saveHead, hS, encodeWord] using run
  | succ n ih =>
      let b₁ := Function.update base source (encodeWord n ++ suffix)
      have guardEq : (Action.pop source saveHead .done).eval ⟨s, base⟩ =
          ⟨(s.1, some true), b₁⟩ := by
        simp [Action.eval, saveHead, hS, encodeWord, List.replicate_succ, b₁]
      have body : Exec skip ⟨(s.1, some true), b₁⟩ 1 ⟨(s.1, some true), b₁⟩ := Exec.atom .done _
      have tail := ih b₁ (s.1, some true) (by simp [b₁])
      have run := Exec.loop_true (g := Action.pop source saveHead .done)
        (p := fun s : State => s.2.getD false) (d := Data.mk s base)
        (by rw [guardEq]; rfl) (by simpa only [guardEq] using body) tail
      simpa [skipField, b₁, show 1 + (2 * n + 1) + 1 = 2 * (n + 1) + 1 by omega] using run

theorem countHeader_exec (base : Tape → List Bool) (s : State) (m : Nat)
    (suffix : List Bool) (hS : base .input = encodeWord m ++ suffix) :
    Exec countHeader ⟨s, base⟩ (2 * m + 1)
      ⟨(s.1, some false), countHeaderResult base m suffix⟩ := by
  induction m generalizing base s with
  | zero =>
      have run := Exec.loop_false (g := Action.pop Tape.input saveHead .done)
        (p := fun s : State => s.2.getD false)
        (a := Code.atom (.push .unary (fun _ => true) (.push .unary (fun _ => true)
          (.push .vertexCount (fun _ => true) (.push .vertexCount (fun _ => true)
            (.push .vertexCount (fun _ => true) .done))))))
        (d := Data.mk s base) (by simp [Action.eval, saveHead, hS, encodeWord])
      have result : countHeaderResult base 0 suffix = Function.update base Tape.input suffix := by
        funext tape
        cases tape <;> simp [countHeaderResult]
      simpa [countHeader, Action.eval, saveHead, hS, encodeWord, result] using run
  | succ m ih =>
      let b₀ := Function.update base Tape.input (encodeWord m ++ suffix)
      let b₁ := Function.update (Function.update b₀ Tape.unary (true :: true :: base .unary))
        Tape.vertexCount (true :: true :: true :: base .vertexCount)
      have guardEq : (Action.pop Tape.input saveHead .done).eval ⟨s, base⟩ =
          ⟨(s.1, some true), b₀⟩ := by
        simp [Action.eval, saveHead, hS, encodeWord, List.replicate_succ, b₀]
      have body := Exec.atom (.push Tape.unary (fun _ : State => true) (.push .unary (fun _ => true)
        (.push .vertexCount (fun _ => true) (.push .vertexCount (fun _ => true)
          (.push .vertexCount (fun _ => true) .done)))))
        (Data.mk (s.1, some true) b₀)
      have bodyEq : (Action.push Tape.unary (fun _ : State => true) (.push .unary (fun _ => true)
          (.push .vertexCount (fun _ => true) (.push .vertexCount (fun _ => true)
            (.push .vertexCount (fun _ => true) .done))))).eval ⟨(s.1, some true), b₀⟩ =
          ⟨(s.1, some true), b₁⟩ := by
        simp [Action.eval, b₁, b₀]
      rw [bodyEq] at body
      have tail := ih b₁ (s.1, some true) (by simp [b₁, b₀])
      have run := Exec.loop_true (g := Action.pop Tape.input saveHead .done)
        (p := fun s : State => s.2.getD false) (d := Data.mk s base)
        (by rw [guardEq]; rfl) (by simpa only [guardEq] using body) tail
      have unaryAppend : List.replicate (2 * m) true ++ true :: true :: base .unary =
          List.replicate (2 * (m + 1)) true ++ base .unary := by
        rw [show 2 * (m + 1) = 2 * m + 2 by omega, List.replicate_add]
        simp [List.append_assoc, List.replicate_succ]
      have vertexAppend : List.replicate (3 * m) true ++ true :: true :: true :: base .vertexCount =
          List.replicate (3 * (m + 1)) true ++ base .vertexCount := by
        rw [show 3 * (m + 1) = 3 * m + 3 by omega, List.replicate_add]
        simp [List.append_assoc, List.replicate_succ]
      have result : countHeaderResult b₁ m suffix = countHeaderResult base (m + 1) suffix := by
        funext tape
        cases tape <;> simp [countHeaderResult, b₁, b₀, unaryAppend, vertexAppend]
      simpa only [countHeader, result,
        show 1 + (2 * m + 1) + 1 = 2 * (m + 1) + 1 by omega] using run

def rawInput («variables» clauses : Nat) (literals : List RawLiteral) : List Bool :=
  encodeWord «variables» ++ encodeWord clauses ++ literalsBits literals

def rawGraphWord (clauses : Nat) (literals : List RawLiteral) : List Bool :=
  BinaryEncoding.natBits (2 * clauses) ++ vertexRecords 0 (3 * clauses) ++ [false] ++
    edgeRecords (suffixEdges 0 literals) ++ [false]

def phaseCosts («variables» clauses : Nat) (literals : List RawLiteral) : List Nat :=
  [2 * «variables» + 1, 1, 2 * clauses + 1, 1,
    UnaryToBinaryMachine.steps (2 * clauses) 0,
    3 * (2 * clauses).bits.length + 3, (2 * clauses).bits.length + 1,
    vertexLoopCost (3 * clauses) 0, 1, (3 * clauses).bits.length + 1,
    outerLoopCost initialControl 0 literals, 1, literals.length.bits.length + 1,
    (rawGraphWord clauses literals).length + 1, 1]

def rawCost («variables» clauses : Nat) (literals : List RawLiteral) : Nat :=
  (phaseCosts «variables» clauses literals).sum + 1

end

open BinPackingGames.Foundations.Target BinPackingGames.Foundations.Complexity

def rawLiteral {n : Nat} (literal : Literal n) : RawLiteral :=
  (literal.variableIndex.val, literal.positive)

def clauseLiterals {n : Nat} (clause : Clause n) : List RawLiteral :=
  [rawLiteral clause[0], rawLiteral clause[1], rawLiteral clause[2]]

def formulaLiterals (F : Formula) : List RawLiteral :=
  F.clauses.flatMap clauseLiterals

@[simp] theorem clauseLiterals_length {n : Nat} (clause : Clause n) :
    (clauseLiterals clause).length = 3 := rfl

@[simp] theorem formulaLiterals_length (F : Formula) :
    (formulaLiterals F).length = 3 * F.clauses.length := by
  unfold formulaLiterals
  induction F.clauses with
  | nil => rfl
  | cons clause rest ih =>
      simp only [List.flatMap_cons, List.length_append, clauseLiterals_length,
        List.length_cons, ih]
      omega

theorem clauseLiterals_bits {n : Nat} (clause : Clause n) :
    literalsBits (clauseLiterals clause) = encodeWords (clauseWords clause) := by
  simp [clauseLiterals, literalsBits, literalBits, rawLiteral, clauseWords,
    literalWords, encodeWords, List.append_assoc]

theorem clausesLiterals_bits {n : Nat} (clauses : List (Clause n)) :
    literalsBits (clauses.flatMap clauseLiterals) =
      encodeWords (clauses.flatMap clauseWords) := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      simp only [List.flatMap_cons, literalsBits, List.flatMap_append, encodeWords_append]
      change literalsBits (clauseLiterals clause) ++ literalsBits (rest.flatMap clauseLiterals) =
        encodeWords (clauseWords clause) ++ encodeWords (rest.flatMap clauseWords)
      rw [clauseLiterals_bits, ih]

theorem formulaBits_eq_formulaLiterals (F : Formula) :
    formulaBits F = encodeWord F.variables ++ encodeWord F.clauses.length ++
      literalsBits (formulaLiterals F) := by
  rw [formulaLiterals, clausesLiterals_bits]
  simp [formulaBits, formulaWords, encodeWords, List.append_assoc]

theorem literalSlots_le_formulaBits_length (F : Formula) :
    3 * F.clauses.length ≤ (formulaBits F).length := by
  have h := encodeWords_length (formulaWords F)
  have hs := formulaWords_length F
  unfold formulaBits
  omega

theorem formulaLiterals_eq_ofFn (F : Formula) :
    formulaLiterals F =
      List.ofFn (fun u : LiteralSlotGraph.Vertex F =>
        rawLiteral (LiteralSlotGraph.literal F u)) := by
  change F.clauses.flatMap clauseLiterals =
    List.ofFn (fun u : Fin (3 * F.clauses.length) =>
      rawLiteral (LiteralSlotGraph.literal F u))
  rw [List.ofFn_mul']
  have inner :
      (fun c : Fin F.clauses.length => List.ofFn (fun j : Fin 3 =>
        rawLiteral (LiteralSlotGraph.literal F (LiteralSlotGraph.index F c j)))) =
      (fun c : Fin F.clauses.length => clauseLiterals F.clauses[c]) := by
    funext c
    simp only [LiteralSlotGraph.literal_index]
    simp [clauseLiterals, List.ofFn_succ]
  change F.clauses.flatMap clauseLiterals =
    (List.ofFn (fun c : Fin F.clauses.length => List.ofFn (fun j : Fin 3 =>
      rawLiteral (LiteralSlotGraph.literal F (LiteralSlotGraph.index F c j))))).flatten
  rw [inner]
  simp only [Fin.getElem_fin]
  rw [List.ofFn_getElem_eq_map]
  induction F.clauses with
  | nil => rfl
  | cons clause rest ih => simp [ih]

abbrev TaggedLiteral := Nat × RawLiteral

def indexFrom (u : Nat) : List RawLiteral → List TaggedLiteral
  | [] => []
  | literal :: rest => (u, literal) :: indexFrom (u + 1) rest

def taggedConflict (a b : TaggedLiteral) : Prop :=
  a.1 / 3 = b.1 / 3 ∨ (a.2.1 = b.2.1 ∧ a.2.2 ≠ b.2.2)

instance instDecidableTaggedConflict (a b : TaggedLiteral) : Decidable (taggedConflict a b) := by
  unfold taggedConflict
  infer_instance

def pairEntry (a b : TaggedLiteral) : Option (Nat × Nat) :=
  if a.1 < b.1 ∧ taggedConflict a b then some (a.1, b.1) else none

def rowEntry (a b : TaggedLiteral) : Option (Nat × Nat) :=
  if taggedConflict a b then some (a.1, b.1) else none

def forwardRows : List TaggedLiteral → List (Nat × Nat)
  | [] => []
  | a :: rest => rest.filterMap (rowEntry a) ++ forwardRows rest

theorem rowEdges_eq_filterMap (u v : Nat) (left : RawLiteral)
    (xs : List RawLiteral) :
    rowEdges u v left xs = (indexFrom v xs).filterMap (rowEntry (u, left)) := by
  induction xs generalizing v with
  | nil => rfl
  | cons right rest ih =>
      simp only [rowEdges, indexFrom, List.filterMap_cons, rowEntry, taggedConflict]
      split_ifs with h <;> simp [h, ih]

theorem suffixEdges_eq_forwardRows (u : Nat) (xs : List RawLiteral) :
    suffixEdges u xs = forwardRows (indexFrom u xs) := by
  induction xs generalizing u with
  | nil => rfl
  | cons literal rest ih =>
      simp only [suffixEdges, indexFrom, forwardRows, rowEdges_eq_filterMap, ih]

theorem indexFrom_ofFn {n : Nat} (u : Nat) (f : Fin n → RawLiteral) :
    indexFrom u (List.ofFn f) = List.ofFn (fun i => (u + i.val, f i)) := by
  induction n generalizing u with
  | zero => simp [indexFrom]
  | succ n ih =>
      simp only [List.ofFn_succ, indexFrom, ih, Fin.val_zero, Nat.add_zero]
      congr 1
      apply congrArg List.ofFn
      funext i
      simp [Nat.add_comm, Nat.add_left_comm]

theorem forwardRows_eq_allPairs (xs : List TaggedLiteral)
    (sorted : xs.Pairwise (fun a b => a.1 < b.1)) :
    forwardRows xs = xs.flatMap (fun a => xs.filterMap (pairEntry a)) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      rcases List.pairwise_cons.mp sorted with ⟨ahead, restSorted⟩
      have first : rest.filterMap (rowEntry a) = rest.filterMap (pairEntry a) := by
        apply List.filterMap_congr
        intro b hb
        simp [rowEntry, pairEntry, ahead b hb]
      have tails : rest.flatMap (fun b => (a :: rest).filterMap (pairEntry b)) =
          rest.flatMap (fun b => rest.filterMap (pairEntry b)) := by
        apply List.flatMap_congr
        intro b hb
        have hnot : ¬b.1 < a.1 := by have := ahead b hb; omega
        simp [pairEntry, hnot]
      rw [forwardRows, List.flatMap_cons, first, ih restSorted, tails]
      simp only [List.filterMap_cons, show pairEntry a a = none by simp [pairEntry]]

theorem filtered_product (α : Type*) (select : α → α → Bool)
    (value : α → α → Nat × Nat) (xs ys : List α) :
    xs.flatMap (fun a => ys.filterMap
      (fun b => if select a b then some (value a b) else none)) =
    ((xs.product ys).filter (fun e => select e.1 e.2)).map (fun e => value e.1 e.2) := by
  have row (a : α) :
      ys.filterMap (fun b => if select a b then some (value a b) else none) =
        ((ys.map (fun b => (a, b))).filter (fun e => select e.1 e.2)).map
          (fun e => value e.1 e.2) := by
    induction ys with
    | nil => rfl
    | cons b tail ihy =>
        cases hs : select a b <;> simp [hs, ihy]
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      change
        ys.filterMap (fun b => if select a b then some (value a b) else none) ++
            rest.flatMap (fun a => ys.filterMap
              (fun b => if select a b then some (value a b) else none)) =
          (((ys.map (fun b => (a, b))) ++ rest.product ys).filter
            (fun e => select e.1 e.2)).map (fun e => value e.1 e.2)
      rw [List.filter_append, List.map_append, row a, ih]

def tagVertex (F : Formula) (u : LiteralSlotGraph.Vertex F) : TaggedLiteral :=
  (u.val, rawLiteral (LiteralSlotGraph.literal F u))

theorem tagVertex_conflict (F : Formula) (u v : LiteralSlotGraph.Vertex F) :
    taggedConflict (tagVertex F u) (tagVertex F v) ↔ LiteralSlotGraph.Conflict F u v := by
  simp [taggedConflict, tagVertex, rawLiteral, LiteralSlotGraph.Conflict,
    LiteralSlotGraph.occurrence, Fin.ext_iff]

end BinPackingGap.LiteralSlotGraphMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_LiteralSlotGraphComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

section

open BinPackingGames.Foundations.Target BinPackingGames.Foundations.Complexity

theorem literal_variable_add_two_le_bits (literal : RawLiteral) :
    literal.1 + 2 ≤ (literalBits literal).length := by
  simp only [literalBits, List.length_append, encodeWord_length]
  omega

theorem literal_bits_length_le_literalsBits {literal : RawLiteral}
    {xs : List RawLiteral} (h : literal ∈ xs) :
    (literalBits literal).length ≤ (literalsBits xs).length := by
  induction xs with
  | nil => simp at h
  | cons head rest ih =>
      rcases List.mem_cons.mp h with h | h
      · subst literal
        simp only [literalsBits_cons, List.length_append]
        omega
      · have ht := ih h
        simp only [literalsBits_cons, List.length_append]
        omega

theorem literal_variable_le_literalsBits {literal : RawLiteral}
    {xs : List RawLiteral} (h : literal ∈ xs) :
    literal.1 ≤ (literalsBits xs).length := by
  have h₁ := literal_variable_add_two_le_bits literal
  have h₂ := literal_bits_length_le_literalsBits h
  omega

theorem literalsBits_formula_length_le (F : Formula) :
    (literalsBits (formulaLiterals F)).length ≤ (formulaBits F).length := by
  rw [formulaBits_eq_formulaLiterals]
  simp only [List.length_append]
  omega

theorem formula_literal_variable_le_input (F : Formula) {literal : RawLiteral}
    (h : literal ∈ formulaLiterals F) :
    literal.1 ≤ (formulaBits F).length :=
  (literal_variable_le_literalsBits h).trans (literalsBits_formula_length_le F)

theorem natBits_length_le_unary (n : Nat) :
    (BinaryEncoding.natBits n).length ≤ 2 * n + 1 := by
  have hb := bits_length_le n
  rw [Nat.size_eq_bits_len] at hb
  rw [BinaryEncoding.natBits_length]
  omega

theorem pairRecord_length_le (u v B : Nat) (hu : u ≤ B) (hv : v ≤ B) :
    (pairRecord u v).length ≤ 4 * B + 3 := by
  have h₁ := natBits_length_le_unary u
  have h₂ := natBits_length_le_unary v
  simp only [pairRecord, List.length_cons, List.length_append]
  omega

theorem vertexRecord_length_le (i B : Nat) (hi : i ≤ B) :
    (vertexRecord i).length ≤ 2 * B + 2 := by
  have h := natBits_length_le_unary i
  simp only [vertexRecord, List.length_cons]
  omega

theorem vertexRecords_length_le (i n B : Nat) (h : i + n ≤ B) :
    (vertexRecords i n).length ≤ n * (2 * B + 2) := by
  induction n generalizing i with
  | zero => simp [vertexRecords]
  | succ n ih =>
      have hi := vertexRecord_length_le i B (by omega)
      have ht := ih (i + 1) (by omega)
      simp only [vertexRecords, List.length_append]
      nlinarith

theorem rowEdges_length_le (u v : Nat) (left : RawLiteral) (xs : List RawLiteral) :
    (rowEdges u v left xs).length ≤ xs.length := by
  induction xs generalizing v with
  | nil => simp [rowEdges]
  | cons right rest ih =>
      have ht := ih (v + 1)
      simp only [rowEdges]
      split_ifs <;> simp only [List.length_cons] <;> omega

theorem rowEdges_endpoint_bounds (u v : Nat) (left : RawLiteral)
    (xs : List RawLiteral) {edge : Nat × Nat} (h : edge ∈ rowEdges u v left xs) :
    edge.1 = u ∧ v ≤ edge.2 ∧ edge.2 < v + xs.length := by
  induction xs generalizing v with
  | nil => simp [rowEdges] at h
  | cons right rest ih =>
      simp only [rowEdges] at h
      split_ifs at h with hc
      · rcases List.mem_cons.mp h with he | he
        · subst edge
          simp only [List.length_cons]
          exact ⟨True.intro, le_rfl, by omega⟩
        · obtain ⟨hu, hv, ht⟩ := ih (v + 1) he
          simp only [List.length_cons]
          exact ⟨hu, by omega, by omega⟩
      · obtain ⟨hu, hv, ht⟩ := ih (v + 1) h
        simp only [List.length_cons]
        exact ⟨hu, by omega, by omega⟩

theorem suffixEdges_endpoint_bounds (u : Nat) (xs : List RawLiteral)
    {edge : Nat × Nat} (h : edge ∈ suffixEdges u xs) :
    u ≤ edge.1 ∧ edge.1 < edge.2 ∧ edge.2 < u + xs.length := by
  induction xs generalizing u with
  | nil => simp [suffixEdges] at h
  | cons literal rest ih =>
      simp only [suffixEdges, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨hu, hv, ht⟩ := rowEdges_endpoint_bounds u (u + 1) literal rest h
        simp only [List.length_cons]
        exact ⟨by omega, by omega, by omega⟩
      · obtain ⟨hu, hv, ht⟩ := ih (u + 1) h
        simp only [List.length_cons]
        exact ⟨by omega, hv, by omega⟩

theorem suffixEdges_length_le_sq (u : Nat) (xs : List RawLiteral) :
    (suffixEdges u xs).length ≤ xs.length ^ 2 := by
  induction xs generalizing u with
  | nil => simp [suffixEdges]
  | cons literal rest ih =>
      have hr := rowEdges_length_le u (u + 1) literal rest
      have ht := ih (u + 1)
      simp only [suffixEdges, List.length_append, List.length_cons]
      nlinarith

theorem edgeRecords_length_le (edges : List (Nat × Nat)) (B : Nat)
    (bounded : ∀ edge ∈ edges, edge.1 ≤ B ∧ edge.2 ≤ B) :
    (edgeRecords edges).length ≤ edges.length * (4 * B + 3) := by
  induction edges with
  | nil => simp [edgeRecords]
  | cons edge rest ih =>
      have he := bounded edge (by simp)
      have hp := pairRecord_length_le edge.1 edge.2 B he.1 he.2
      have ht := ih (fun e he => bounded e (by simp [he]))
      simp only [edgeRecords, List.flatMap_cons, List.length_append, List.length_cons]
      change (pairRecord edge.1 edge.2).length + (edgeRecords rest).length ≤ _
      nlinarith

theorem suffixEdgeRecords_length_le (u : Nat) (xs : List RawLiteral) (B : Nat)
    (hB : u + xs.length ≤ B) :
    (edgeRecords (suffixEdges u xs)).length ≤ xs.length ^ 2 * (4 * B + 3) := by
  have he := edgeRecords_length_le (suffixEdges u xs) B (by
    intro edge h
    obtain ⟨h₁, h₂, h₃⟩ := suffixEdges_endpoint_bounds u xs h
    exact ⟨by omega, by omega⟩)
  exact he.trans (Nat.mul_le_mul_right _ (suffixEdges_length_le_sq u xs))

theorem formulaEdgeRecords_length_le (F : Formula) :
    (edgeRecords (suffixEdges 0 (formulaLiterals F))).length ≤
      (formulaBits F).length ^ 2 * (4 * (formulaBits F).length + 3) := by
  have hn : (formulaLiterals F).length ≤ (formulaBits F).length := by
    rw [formulaLiterals_length]
    exact literalSlots_le_formulaBits_length F
  have he := suffixEdgeRecords_length_le 0 (formulaLiterals F)
    (formulaBits F).length (by simpa using hn)
  have hs : (formulaLiterals F).length ^ 2 ≤ (formulaBits F).length ^ 2 := by
    nlinarith
  exact he.trans (Nat.mul_le_mul_right _ hs)

theorem formulaGraphWord_length_le (F : Formula) :
    (BinaryEncoding.natBits (2 * F.clauses.length) ++
      vertexRecords 0 (3 * F.clauses.length) ++ [false] ++
      edgeRecords (suffixEdges 0 (formulaLiterals F)) ++ [false]).length ≤
      4 * (formulaBits F).length ^ 3 + 5 * (formulaBits F).length ^ 2 +
        4 * (formulaBits F).length + 3 := by
  let s := (formulaBits F).length
  have hn : 3 * F.clauses.length ≤ s := literalSlots_le_formulaBits_length F
  have hh := natBits_length_le_unary (2 * F.clauses.length)
  have hv := vertexRecords_length_le 0 (3 * F.clauses.length) s (by omega)
  have hv' : (vertexRecords 0 (3 * F.clauses.length)).length ≤ s * (2 * s + 2) :=
    hv.trans (Nat.mul_le_mul_right _ hn)
  have he := formulaEdgeRecords_length_le F
  simp only [List.length_append, List.length_cons, List.length_nil]
  change _ ≤ 4 * s ^ 3 + 5 * s ^ 2 + 4 * s + 3
  change (edgeRecords (suffixEdges 0 (formulaLiterals F))).length ≤ s ^ 2 * (4 * s + 3) at he
  nlinarith

end

open Turing FiniteTapeProgram BinPackingGames.Foundations.Target
open BinPackingGames.Foundations.Complexity

theorem edgeRecords_listBits (edges : List (Nat × Nat)) :
    edgeRecords edges ++ [false] = BinaryEncoding.listBits
      (BinaryEncoding.pairBits BinaryEncoding.natBits BinaryEncoding.natBits) edges := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      change (pairRecord edge.1 edge.2 ++ edgeRecords rest) ++ [false] = _
      rw [List.append_assoc, ih]
      rfl

theorem rawInput_formula (F : Formula) :
    rawInput F.variables F.clauses.length (formulaLiterals F) = formulaBits F :=
  (formulaBits_eq_formulaLiterals F).symm

end BinPackingGap.LiteralSlotGraphMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalar
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

namespace Packing

variable {I : Instance} {b : ℕ}

instance instDecidableEqTableBin (p : Packing I b) (subclass : I.Item → Subclass) :
    DecidableEq (p.TableBin subclass) := Classical.decEq _

end Packing

end

open scoped BigOperators

def primaryTotal (s : Fin 5 → Subclass) : ℤ := ∑ i, primaryScore (s i)

def secondaryTotal {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) : ℤ := ∑ i, secondaryScore (s i) (label i)

namespace Packing

variable {I : Instance} {b n : ℕ}

def fiveEquiv (p : Packing I b) (j : Fin b) (hc : (p.binItems j).card = 5) :
    Fin 5 ≃ p.binItems j := (Finset.equivFinOfCardEq hc).symm

def outsideTableItems (p : Packing I b) (subclass : I.Item → Subclass) :
    Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => ¬ p.IsTableBin subclass (p.assignment i)

end Packing

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_IntegerTreeGeometry
attribute [-instance] _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.TreeGeometry

open _root_.OAI.BinPackingGap.Geometry UniformTree

theorem nonroot_endpoints (m R D : ℕ) (s : Side) {w : List ℕ}
    (hw : w ≠ []) (hb : BoundedAddress D w) :
    rootOffset s ≤ left m R D s w ∧ right m R D s w < rootOffset s + 1 / 10 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    have ha := hb a (by simp)
    have hroot := prefix_endpoints m R D s (u := []) List.nil_prefix hb
    have hfirst := prefix_endpoints m R D s (u := [a]) ⟨w, rfl⟩ hb
    simp only [List.singleton_append] at hfirst
    have hm : (4 * (a : ℚ) + 1) * lambda m R D 1 ≤
        (4 * (D : ℚ) + 1) * lambda m R D 1 := by
      have hcast : (a : ℚ) ≤ D := by exact_mod_cast ha
      exact mul_le_mul_of_nonneg_right (by linarith) (lambda_nonneg m R D 1)
    have hf := first_children_lt_tenth m R D
    have hr := right_append_singleton m R D s [] a
    simp only [List.nil_append, List.length_nil, Nat.zero_add, left_nil] at hr
    exact ⟨by simpa only [left_nil] using hroot.1, by linarith [hfirst.2]⟩

theorem same_depth_gap (m R D ell : ℕ) {s t : Side} {u v : List ℕ}
    (hu : u.length = ell) (hv : v.length = ell)
    (hbu : BoundedAddress D u) (hbv : BoundedAddress D v)
    (hne : (s, u) ≠ (t, v)) :
    right m R D s u + 3 * lambda m R D ell ≤ left m R D t v ∨
      right m R D t v + 3 * lambda m R D ell ≤ left m R D s u := by
  induction ell generalizing s t u v with
  | zero =>
    have hu0 : u = [] := List.length_eq_zero_iff.mp hu
    have hv0 : v = [] := List.length_eq_zero_iff.mp hv
    subst u
    subst v
    have hscale := lambda_le_one m R D 0
    cases s <;> cases t <;> simp only [left_nil, right_nil, rootOffset] at *
    · exact (hne rfl).elim
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact (hne rfl).elim
  | succ ell ih =>
    obtain ⟨u, a, rfl, hup⟩ := exists_snoc_of_length_succ hu
    obtain ⟨v, b, rfl, hvp⟩ := exists_snoc_of_length_succ hv
    have hau : a ≤ D := hbu a (by simp)
    have hbv' : b ≤ D := hbv b (by simp)
    have hpu : BoundedAddress D u := fun c hc => hbu c (by simp [hc])
    have hpv : BoundedAddress D v := fun c hc => hbv c (by simp [hc])
    by_cases hp : (s, u) = (t, v)
    · have hs : s = t := congrArg Prod.fst hp
      have huv : u = v := congrArg Prod.snd hp
      subst t
      subst v
      have hab : a ≠ b := by
        intro heq
        exact hne (by simp [heq])
      have hscale := lambda_nonneg m R D (ell + 1)
      rw [right_append_singleton, right_append_singleton,
        left_append_singleton, left_append_singleton, hup]
      rcases lt_or_gt_of_ne hab with hab | hba
      · left
        have hc : (a : ℚ) + 1 ≤ b := by exact_mod_cast (Nat.succ_le_iff.mpr hab)
        nlinarith
      · right
        have hc : (b : ℚ) + 1 ≤ a := by exact_mod_cast (Nat.succ_le_iff.mpr hba)
        nlinarith
    · have hgap := ih hup hvp hpu hpv hp
      have hcu := child_endpoints m R D s u hau
      have hcv := child_endpoints m R D t v hbv'
      have hscale := lambda_antitone m R D (Nat.le_succ ell)
      rcases hgap with hgap | hgap
      · left
        linarith [hcu.2, hcv.1]
      · right
        linarith [hcv.2, hcu.1]

def nodeCell (m R D : ℕ) (s : Side) {T : UniformTree} (v : T.Node) : Set ℚ :=
  cell m R D s v.val

end BinPackingGap.TreeGeometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryScores
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

theorem itemSubclass_role (i : D.Item) : (D.itemSubclass i).role = D.itemRole i := by
  rcases i with ⟨r, i⟩
  cases r with
  | x =>
      rcases i with ⟨v, (row | job)⟩
      · rcases row with (plus | (minus | padding)) <;> rfl
      · rfl
  | anchor => rcases i with ⟨v, (deadline | key)⟩ <;> rfl
  | «global» =>
      rcases i with ⟨s, copy⟩
      cases s <;> rfl
  | «local» => rcases i with ⟨v, (main | edge)⟩ <;> rfl
  | flag =>
      rcases i with ⟨s, copy⟩
      cases s <;> rfl

def rowPosition {v : D.Vertex} : D.RowAt v → Option D.Position
  | .inl _ => none
  | .inr r => some (D.jobPosition r.2)

def globalUnit : D.GlobalCopy → Bool
  | ⟨.up unit, _⟩ => unit
  | ⟨.um unit, _⟩ => unit
  | ⟨.edge _ _, _⟩ => false

def localDepth {v : D.Vertex} : D.LocalAt v → Option D.Depth
  | .inl (.inl p) => some p.1
  | _ => none

end InventoryData

def labelledRoleCount {ι : Type*} [Fintype ι] {n : ℕ}
    (s : ι → Subclass) (label : ι → Option (Fin n)) (r : Role) (v : Fin n) : ℤ :=
  ∑ i, if (s i).role = r ∧ label i = some v then 1 else 0

end BinPackingGap

noncomputable section

namespace BinPackingGap
namespace InventoryData

variable (D : InventoryData)

def prefixJobIndex (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (j : ((Fin h × Fin 2) × Fin D.R) × Fin D.d) :
    ((D.Edge × Fin 2) × Fin D.R) × Fin D.d :=
  ((⟨⟨j.1.1.1.val, lt_of_lt_of_le j.1.1.1.isLt hle⟩, j.1.1.2⟩, j.1.2), j.2)

def prefixWIndex (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (w : (Fin h × Bool) × Fin (D.d * D.R)) :
    (D.Edge × Bool) × Fin (D.d * D.R) :=
  ((⟨w.1.1.val, lt_of_lt_of_le w.1.1.isLt hle⟩, w.1.2), w.2)

def earlierW (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset D.Item := by
  classical
  exact Finset.univ.image fun w => D.edgeResourceItem (D.prefixWIndex h hle w)

end InventoryData
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_GoodAnchorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

open scoped BigOperators

variable {I : Instance} {b n : ℕ}

namespace RoleLabelData

def of_valid (cls : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (hlabeled : ∀ i, (cls i).role = .x ∨ (cls i).role = .anchor ∨
      (cls i).role = .«local» → ∃ v, label i = some v)
    (hunlabeled : ∀ i, (cls i).role = .«global» ∨ (cls i).role = .flag →
      label i = none) : RoleLabelData cls label where
  row i := Classical.choose (hlabeled i.val (Or.inl i.property))
  anchor i := Classical.choose (hlabeled i.val (Or.inr (Or.inl i.property)))
  localLabel i := Classical.choose (hlabeled i.val (Or.inr (Or.inr i.property)))
  row_spec i := Classical.choose_spec (hlabeled i.val (Or.inl i.property))
  anchor_spec i := Classical.choose_spec (hlabeled i.val (Or.inr (Or.inl i.property)))
  local_spec i := Classical.choose_spec (hlabeled i.val (Or.inr (Or.inr i.property)))
  global_spec i := hunlabeled i.val (Or.inl i.property)
  flag_spec i := hunlabeled i.val (Or.inr i.property)

end RoleLabelData

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingSelections
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open scoped BigOperators

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def xplus (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) : ℕ :=
  (fundedTuples p e (.up true) v).card

def xminus (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) : ℕ :=
  (fundedTuples p e (.um true) v).card

def localDepthResources (e : D.Item ≃ I.Item) (v : D.Vertex) (ell : D.Depth) :
    Finset I.Item := by
  classical
  exact Finset.univ.image fun i : Fin (D.quota ell.val) =>
    e ⟨.«local», ⟨v, Sum.inl (Sum.inl ⟨ell, i⟩)⟩⟩

end PackingCounts
end BinPackingGap

end

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def elementAtRole (i : D.Item) (r : Role) (h : i.1 = r) : D.RoleCopies r :=
  h ▸ i.2

theorem selected_role (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    (e.symm (p.itemAtRole (subclass e) t r)).1 = r := by
  change D.itemRole (e.symm (p.itemAtRole (subclass e) t r)) = r
  rw [← D.itemSubclass_role]
  exact p.itemAtRole_role (subclass e) t r

def roleCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) : D.RoleCopies r :=
  elementAtRole (e.symm (p.itemAtRole (subclass e) t r)) r (selected_role p e t r)

abbrev rowCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Σ v : D.Vertex, D.RowAt v :=
  roleCopy p e t .x

abbrev anchorCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Σ v : D.Vertex, D.AnchorAt v :=
  roleCopy p e t .anchor

abbrev globalCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : D.GlobalCopy :=
  roleCopy p e t .«global»

abbrev localCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Σ v : D.Vertex, D.LocalAt v :=
  roleCopy p e t .«local»

def zeroPositiveTuples (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) :
    Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    D.globalUnit (globalCopy p e t) = false ∧
      p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v

def tupleLocalDepth (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℕ :=
  ((D.localDepth (localCopy p e t).2).map Subtype.val).getD 0

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TestGeometry
attribute [-instance] _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

theorem tree_endpoints_in_root {T : UniformTree} (v : T.Node)
    (s : TreeGeometry.Side) (hT : T.branchBound ≤ D.geometryBound) :
    TreeGeometry.rootOffset s ≤
        TreeGeometry.left D.graph.edges.length D.R D.geometryBound s v.val ∧
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound s v.val ≤
        TreeGeometry.rootOffset s + 1 := by
  simpa only [TreeGeometry.left_nil, TreeGeometry.right_nil] using
    TreeGeometry.prefix_endpoints D.graph.edges.length D.R D.geometryBound s
      (u := []) (v := v.val) List.nil_prefix (TreeGeometry.boundedAddress_node v hT)

theorem same_depth_cells_disjoint {s t : TreeGeometry.Side} {u w : List ℕ}
    (hu : u.length = D.L) (hw : w.length = D.L)
    (hbu : TreeGeometry.BoundedAddress D.geometryBound u)
    (hbw : TreeGeometry.BoundedAddress D.geometryBound w) (hne : (s, u) ≠ (t, w)) :
    Disjoint (TreeGeometry.cell D.graph.edges.length D.R D.geometryBound s u)
      (TreeGeometry.cell D.graph.edges.length D.R D.geometryBound t w) := by
  have hg := TreeGeometry.same_depth_gap D.graph.edges.length D.R D.geometryBound D.L
    hu hw hbu hbw hne
  have hp := Geometry.lambda_pos D.graph.edges.length D.R D.geometryBound D.L
  rcases hg with hg | hg
  · exact disjoint_of_endpoint_lt (by linarith)
  · exact (disjoint_of_endpoint_lt (by linarith)).symm

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingCoordinates
attribute [-instance] _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

theorem stateMainLength_nonneg {v : D.Vertex} (selected : Bool) (b : D.MBase v) :
    0 ≤ D.stateMainLength selected b := by
  rcases b with (⟨p, i⟩ | ⟨m, i⟩ | i) | j
  all_goals simp only [stateMainLength, stateMainGlobalSpecies, globalSpeciesLength]
  all_goals split_ifs <;> norm_num

theorem fundedRoot_injective (v : D.Vertex) (selected : Bool) :
    Function.Injective (D.fundedRoot (v := v) selected) := by
  intro i j h
  cases selected <;> simpa [fundedRoot] using h

end BinPackingGap.InventoryData

noncomputable section

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def tupleBaseline (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ := D.rowBaseline (rowCopy p e t).2

def tupleShort (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Bool := D.rowShort (rowCopy p e t).2

def tupleGlobalLength (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ := D.globalLength (globalCopy p e t)

def tupleLocalLength (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ := D.localLength (localCopy p e t).2

def tupleFinish (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ :=
  completion (tupleBaseline p e t) (tupleShort p e t)
    (tupleGlobalLength p e t) (tupleLocalLength p e t)
    (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L)

def tupleClosedInterval (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Set ℚ :=
  Set.Icc (tupleFinish p e t) (tupleBaseline p e t)

def tupleCovering (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryPrefixConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

def encodedSubclass (i : D.packingInstance.Item) : Subclass :=
  D.itemSubclass (D.itemEquiv.symm i)

def encodedLabel (i : D.packingInstance.Item) : Option D.Vertex :=
  D.itemLabel (D.itemEquiv.symm i)

def encodedCoordinate (i : D.packingInstance.Item) : ℚ :=
  D.itemCoordinate (D.itemEquiv.symm i)

theorem itemLabel_some_of_labelled (i : D.Item)
    (h : D.itemRole i = .x ∨ D.itemRole i = .anchor ∨ D.itemRole i = .«local») :
    ∃ v, D.itemLabel i = some v := by
  rcases i with ⟨r, i⟩
  cases r <;> simp only [itemRole] at h
  · exact ⟨i.1, rfl⟩
  · exact ⟨i.1, rfl⟩
  · simp at h
  · exact ⟨i.1, rfl⟩
  · simp at h

theorem itemLabel_none_of_unlabelled (i : D.Item)
    (h : D.itemRole i = .«global» ∨ D.itemRole i = .flag) :
    D.itemLabel i = none := by
  rcases i with ⟨r, i⟩
  cases r <;> simp_all [itemRole, itemLabel]

theorem encodedLabel_some_of_labelled (i : D.packingInstance.Item)
    (h : (D.encodedSubclass i).role = .x ∨ (D.encodedSubclass i).role = .anchor ∨
      (D.encodedSubclass i).role = .«local») :
    ∃ v, D.encodedLabel i = some v := by
  apply D.itemLabel_some_of_labelled (D.itemEquiv.symm i)
  simpa only [encodedSubclass, D.itemSubclass_role] using h

theorem encodedLabel_none_of_unlabelled (i : D.packingInstance.Item)
    (h : (D.encodedSubclass i).role = .«global» ∨ (D.encodedSubclass i).role = .flag) :
    D.encodedLabel i = none := by
  apply D.itemLabel_none_of_unlabelled (D.itemEquiv.symm i)
  simpa only [encodedSubclass, D.itemSubclass_role] using h

end InventoryData

end

namespace InventoryData

open scoped BigOperators

variable (D : InventoryData)

def roleLabelData : RoleLabelData D.encodedSubclass D.encodedLabel :=
  RoleLabelData.of_valid D.encodedSubclass D.encodedLabel
    D.encodedLabel_some_of_labelled D.encodedLabel_none_of_unlabelled

end InventoryData
end BinPackingGap

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem physicalGlobalPool_nonempty_iff (s : GlobalSpecies D.graph) :
    (D.physicalGlobalPool s).Nonempty ↔ 0 < D.globalStock s := by
  rw [← Finset.card_pos, card_physicalGlobalPool]

theorem physicalFlagPool_nonempty_iff (s : FlagSpecies) :
    (D.physicalFlagPool s).Nonempty ↔ 0 < D.flagStock s := by
  rw [← Finset.card_pos, card_physicalFlagPool]

theorem mem_physicalGlobalPool (s : GlobalSpecies D.graph) (i : D.packingInstance.Item) :
    i ∈ D.physicalGlobalPool s ↔
      ∃ j : Fin (D.globalStock s), D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ = i := by
  simp only [physicalGlobalPool, Finset.mem_map, Finset.mem_univ, true_and,
    globalCopyEmbedding_apply]

theorem mem_physicalFlagPool (s : FlagSpecies) (i : D.packingInstance.Item) :
    i ∈ D.physicalFlagPool s ↔
      ∃ j : Fin (D.flagStock s), D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ = i := by
  simp only [physicalFlagPool, Finset.mem_map, Finset.mem_univ, true_and,
    flagCopyEmbedding_apply]

theorem role_eq_global_of_mem_physicalGlobalPool (s : GlobalSpecies D.graph)
    {i : D.packingInstance.Item} (hi : i ∈ D.physicalGlobalPool s) :
    (D.itemEquiv.symm i).1 = .«global» := by
  obtain ⟨j, rfl⟩ := (D.mem_physicalGlobalPool s i).mp hi
  simp only [Equiv.symm_apply_apply]

theorem role_eq_flag_of_mem_physicalFlagPool (s : FlagSpecies)
    {i : D.packingInstance.Item} (hi : i ∈ D.physicalFlagPool s) :
    (D.itemEquiv.symm i).1 = .flag := by
  obtain ⟨j, rfl⟩ := (D.mem_physicalFlagPool s i).mp hi
  simp only [Equiv.symm_apply_apply]

theorem physicalGlobalPool_disjoint_physicalFlagPool
    (s : GlobalSpecies D.graph) (t : FlagSpecies) :
    Disjoint (D.physicalGlobalPool s) (D.physicalFlagPool t) := by
  apply Finset.disjoint_left.mpr
  intro i hi ht
  have h := (D.role_eq_global_of_mem_physicalGlobalPool s hi).symm.trans
    (D.role_eq_flag_of_mem_physicalFlagPool t ht)
  cases h

theorem labeledItems_disjoint_physicalGlobalPool (s : GlobalSpecies D.graph) :
    Disjoint D.labeledItems (D.physicalGlobalPool s) := by
  apply Finset.disjoint_left.mpr
  intro i hi hg
  have hr := D.role_eq_global_of_mem_physicalGlobalPool s hg
  have hl := (D.mem_labeledItems i).mp hi
  simp [hr] at hl

theorem labeledItems_disjoint_physicalFlagPool (s : FlagSpecies) :
    Disjoint D.labeledItems (D.physicalFlagPool s) := by
  apply Finset.disjoint_left.mpr
  intro i hi hf
  have hr := D.role_eq_flag_of_mem_physicalFlagPool s hf
  have hl := (D.mem_labeledItems i).mp hi
  simp [hr] at hl

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingFeasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

open scoped BigOperators

variable {D : InventoryData} {I : Instance} {b : ℕ}

structure EdgeTupleData (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) where
  short : Bool
  row : D.JobCopy (rowCopy p e t).1
  key : D.JobCopy (anchorCopy p e t).1
  localJob : D.JobCopy (localCopy p e t).1
  edge : D.Edge
  permit : Bool
  globalIndex : Fin (D.globalStock (.edge edge permit))
  row_eq : (rowCopy p e t).2 = .inr (short, row)
  anchor_eq : (anchorCopy p e t).2 = .inr key
  local_eq : (localCopy p e t).2 = .inr localJob
  global_eq : globalCopy p e t = ⟨.edge edge permit, globalIndex⟩

namespace EdgeTupleData

variable {p : Packing I b} {e : D.Item ≃ I.Item} {t : p.TableBin (subclass e)}

def expression (w : EdgeTupleData p e t) : ℚ :=
  Geometry.keyExpression D.graph.edges.length D.R D.geometryBound D.L
    (D.jobPosition w.row) (D.jobPosition w.key) w.edge (!w.permit) w.short

end EdgeTupleData

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_EdgeLongConsumption
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace InventoryData

section

variable (D : InventoryData) {b : ℕ}

def earlierWItems (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Finset D.packingInstance.Item := (D.earlierW h hle).image D.itemEquiv

end

open scoped BigOperators
open PackingCounts

end InventoryData
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_LocalJobCounts
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem card_jobCopy_edge_of_endpoint (v : D.Vertex) (e : D.Edge) (s : Fin 2)
    (hs : D.graph.endpoint e s = v) :
    (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card =
      D.d * D.R := by
  classical
  let f : Fin D.R × Fin D.d → D.JobCopy v :=
    fun rc => ((⟨(e, s), hs⟩, rc.1), rc.2)
  have hf : Function.Injective f := by
    intro a b hab
    apply Prod.ext
    · exact congrArg (fun j : D.JobCopy v => j.1.2) hab
    · exact congrArg (fun j : D.JobCopy v => j.2) hab
  have hfilter :
      Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e) =
        Finset.univ.image f := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj
      apply Finset.mem_image.mpr
      refine ⟨(j.1.2, j.2), Finset.mem_univ _, ?_⟩
      rcases j with ⟨⟨⟨⟨e', s'⟩, hv⟩, r⟩, c⟩
      change e' = e at hj
      subst e'
      have hslot : s = s' := D.graph.endpoint_injective e (hs.trans hv.symm)
      subst s'
      rfl
    · intro hj
      obtain ⟨rc, _, rfl⟩ := Finset.mem_image.mp hj
      rfl
  rw [hfilter, Finset.card_image_of_injective _ hf, Finset.card_univ]
  simp [Nat.mul_comm]

theorem card_jobCopy_edge (v : D.Vertex) (e : D.Edge) :
    (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card =
      if D.graph.left e = v ∨ D.graph.right e = v then D.d * D.R else 0 := by
  classical
  by_cases hv : D.graph.left e = v ∨ D.graph.right e = v
  · rw [ite_eq_left hv]
    rcases hv with hl | hr
    · exact D.card_jobCopy_edge_of_endpoint v e 0 (by simpa using hl)
    · exact D.card_jobCopy_edge_of_endpoint v e 1 (by simpa using hr)
  · rw [ite_eq_right hv]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    apply hv
    have he : j.1.1.val.1 = e := (Finset.mem_filter.mp hj).2
    have hep : D.graph.endpoint e j.1.1.val.2 = v := by
      rw [← he]
      exact j.1.1.property
    have hslot : j.1.1.val.2 = 0 ∨ j.1.1.val.2 = 1 := by omega
    rcases hslot with hzero | hone
    · left
      simpa only [hzero, GraphInput.endpoint_zero] using hep
    · right
      simpa only [hone, GraphInput.endpoint_one] using hep

theorem sum_card_jobCopy_edge (e : D.Edge) :
    (∑ v : D.Vertex,
      (Finset.univ.filter (fun j : D.JobCopy v => (D.jobPosition j).1 = e)).card) =
      2 * D.d * D.R := by
  classical
  calc
    _ =
        (Finset.univ.filter (fun j : D.JobCopy (D.graph.left e) =>
          (D.jobPosition j).1 = e)).card +
        (Finset.univ.filter (fun j : D.JobCopy (D.graph.right e) =>
          (D.jobPosition j).1 = e)).card := by
      refine Finset.sum_eq_add_of_mem (D.graph.left e) (D.graph.right e)
        (Finset.mem_univ _) (Finset.mem_univ _) (D.graph.left_ne_right e) ?_
      intro v _ hv
      rw [D.card_jobCopy_edge]
      simp [Ne.symm hv.1, Ne.symm hv.2]
    _ = D.d * D.R + D.d * D.R := by simp [D.card_jobCopy_edge]
    _ = 2 * D.d * D.R := by simp [two_mul, Nat.add_mul]

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_IntegralSpeciesCounts
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem up_indicator_add (g : GlobalSpecies D.graph) :
    (if g = .up true then 1 else 0) + (if g = .up false then 1 else 0) =
      match g with | .up _ => 1 | _ => 0 := by
  cases g with
  | up b => cases b <;> rfl
  | um b => rfl
  | edge e b => rfl

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_PackingExclusions
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def tupleHitsJob (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : D.Position) : Prop :=
  (tupleClosedInterval p e t ∩
    Geometry.closedJobCell D.graph.edges.length D.R D.geometryBound D.L r).Nonempty

def excludedAt (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) :
    Finset D.Position :=
  excludedPositions (zeroPositiveTuples p e v) (tupleHitsJob p e)

def goodRepetitions (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (edge : D.Edge) : Finset (Fin D.R) :=
  nonexcludedRepetitions (excludedAt p e v) edge

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingJobCoverage
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def shortMainAt (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) : Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    tupleBaseline p e t = Geometry.baseline D.graph.edges.length D.R r ∧
      tupleShort p e t = true

end PackingCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_LiteralSlotGap
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraph

open BinPackingGames.Foundations.Target
open scoped BigOperators

def satisfiedClauses (F : Formula) (A : Fin F.variables → Bool) :
    Finset (Fin F.clauses.length) :=
  Finset.univ.filter (fun c => (F.clauses[c]).eval A = true)

def failedClauses (F : Formula) (A : Fin F.variables → Bool) :
    Finset (Fin F.clauses.length) :=
  Finset.univ.filter (fun c => (F.clauses[c]).eval A ≠ true)

end BinPackingGap.LiteralSlotGraph

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_LocalTemplateBases
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

theorem encoded_pattern_role_sum {n : ℕ} (p : Pattern) (v : Fin n) (w : Role → ℚ) :
    (∑ r, encodedSize (patternSubclass p r) (tableRoleLabel v v v r) (w r)) =
      1 + nu n * ∑ r, w r := by
  have hp : (∑ r, primaryScore (patternSubclass p r)) = 0 :=
    sum_primaryScore_eq_zero_of_coefficients _ (pattern_primaryCoeff_sum p)
  have hq : (∑ r, secondaryScore (patternSubclass p r) (tableRoleLabel v v v r)) = 0 := by
    rw [Role.sum_univ]
    cases p <;>
      simp [secondaryScore, patternSubclass, Subclass.role, tableRoleLabel] <;> ring
  have hpQ : (∑ r, (primaryScore (patternSubclass p r) : ℚ)) = 0 := by
    exact_mod_cast hp
  have hqQ : (∑ r, (secondaryScore (patternSubclass p r)
      (tableRoleLabel v v v r) : ℚ)) = 0 := by
    exact_mod_cast hq
  calc
    _ = (∑ _r : Role, (1 / 5 : ℚ)) +
        gamma * (∑ r, (primaryScore (patternSubclass p r) : ℚ)) +
        mu n * (∑ r, (secondaryScore (patternSubclass p r)
          (tableRoleLabel v v v r) : ℚ)) + nu n * ∑ r, w r := by
      simp only [encodedSize, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hpQ, hqQ]; norm_num

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalarExpression
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

open IntegerPackingArithmetic

variable (D : InventoryData)

variable (hplus : D.plus.height ≤ D.L) (hminus : D.minus.height ≤ D.L)

theorem coordinateDenominator_mul_globalCoordinate (r : D.GlobalCopy) :
    (D.coordinateDenominator : ℚ) * D.globalCoordinate r =
      (D.globalIntegerCoordinate r : ℚ) := by
  rcases r with ⟨species, j⟩
  cases species with
  | up b =>
      cases b <;> simp [globalCoordinate, globalIntegerCoordinate, coordinateDenominator]
  | um b =>
      cases b <;> simp [globalCoordinate, globalIntegerCoordinate, coordinateDenominator]
  | edge e b =>
      cases b <;>
        simp [globalCoordinate, globalIntegerCoordinate, mul_add, coordinateDenominator,
          geomDenominator_mul_beta, geomDenominator_mul_delta]

theorem coordinateDenominator_mul_localCoordinate {v : D.Vertex} (r : D.LocalAt v) :
    (D.coordinateDenominator : ℚ) * D.localCoordinate r =
      (D.localIntegerCoordinate r : ℚ) := by
  rcases r with (⟨ell, j⟩ | j) | j
  · have hell : ell.val ≤ D.L := (Finset.mem_Icc.mp ell.property).2
    simp only [localCoordinate, localLength, localIntegerCoordinate, mul_neg,
      Int.cast_neg, Int.cast_natCast, coordinateDenominator,
      geomDenominator_mul_lambda D.graph.edges.length D.R D.geometryBound D.L ell.val hell]
  · simp [localCoordinate, localLength, localIntegerCoordinate]
  · simp [localCoordinate, localLength, localIntegerCoordinate]

end BinPackingGap.InventoryData

namespace BinPackingGap.PackingScalarExpression

open NatExpressionCompiler NaturalPackingNumerator IntegerPackingArithmetic

instance instFintypeVariable : Fintype Variable where
  elems := {.vertexPower, .geometry, .labelPower, .coordinatePositive, .coordinateNegative}
  complete v := by cases v <;> simp

end BinPackingGap.PackingScalarExpression

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PhysicalRolePacking
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

def packingOfRoleEquivs {Bin : Type*} [Fintype Bin]
    (e : ∀ r : Role, Bin ≃ D.RoleCopies r)
    (hcapacity : ∀ b, (∑ r : Role, D.itemSize ⟨r, e r b⟩) ≤ 1) :
    Packing D.packingInstance (Fintype.card Bin) := by
  classical
  let enum : Bin ≃ Fin (Fintype.card Bin) := Fintype.equivFin Bin
  let a : D.Item → Fin (Fintype.card Bin) := fun i => enum ((e i.1).symm i.2)
  refine packingOfFintype D.itemSize D.itemSize_pos D.itemSize_le_one a ?_
  intro j
  change (∑ i : (Σ r : Role, D.RoleCopies r),
    if enum ((e i.1).symm i.2) = j then D.itemSize i else 0) ≤ 1
  rw [Fintype.sum_sigma]
  have hsum : (∑ r : Role, ∑ c : D.RoleCopies r,
      if enum ((e r).symm c) = j then D.itemSize ⟨r, c⟩ else 0) =
      ∑ r : Role, D.itemSize ⟨r, e r (enum.symm j)⟩ := by
    apply Finset.sum_congr rfl
    intro r _
    rw [← (e r).sum_comp]
    have he (b : Bin) : enum b = j ↔ b = enum.symm j := by
      constructor
      · intro h
        exact enum.injective (h.trans (enum.apply_symm_apply j).symm)
      · rintro rfl
        exact enum.apply_symm_apply j
    simp only [Equiv.symm_apply_apply, he]
    simp
  rw [hsum]
  exact hcapacity (enum.symm j)

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchFinalizeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchFinalizeMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchSemantics SearchEncoding BinaryEncoding
open BinPackingGames.Reduction.MachineTransfer

def code : Label → TM2.Stmt (fun _ : Tape => Bool) Label Register
  | .start => .pop .input (fun _ head => ((), head))
      (.branch (fun state => state.2.getD false)
        (.pop .input (fun _ head => ((), head))
          (.branch (fun state => state.2.getD true) reject
            (.push .reversed (fun _ => true) (go (.convert .scan)))))
        reject)
  | .convert label => UnaryToBinaryMachine.instruction .input .binary .scratch
      Label.convert (some .emitBinary) label
  | .emitBinary => .pop .binary (fun _ head => ((), head))
      (.branch (fun state => state.2.isSome)
        (.push .reversed (fun _ => true)
          (.push .reversed (fun state => state.2.getD false) (go .emitBinary)))
        (.push .reversed (fun _ => false) (go .skipItem)))
  | .skipItem => skipUnary .skipItem .skipLabel
  | .skipLabel => skipUnary .skipLabel .items
  | .items => skipUnary .numerator .fixed
  | .numerator => skipUnary .numeratorDigit .denominator
  | .numeratorDigit => skipDigit .numerator
  | .denominator => skipUnary .denominatorDigit .items
  | .denominatorDigit => skipDigit .denominator
  | .fixed => .pop .input (fun _ head => ((), head))
      (.push .reversed (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false) (go .option) (go .reverse)))
  | .option => .pop .input (fun _ head => ((), head))
      (.branch (fun state => state.2.getD false) (go .name)
        (.push .reversed (fun _ => false) (go .fixed)))
  | .name => .pop .input (fun _ head => ((), head))
      (.push .reversed (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false) (go .nameDigit) (go .fixed)))
  | .nameDigit => .pop .input (fun _ head => ((), head))
      (.push .reversed (fun state => state.2.getD false) (go .name))
  | .reverse => loopAt .reversed .output id false .reverse none

end BinPackingGap.SearchFinalizeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchFixedReplaceMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchFixedReplaceMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinaryEncoding SearchEncoding

variable {K Λ A : Type} [DecidableEq K]
variable (place : Slot → K) (distinct : Function.Injective place)
variable (labels : Label → Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Register A))
variable (atLabels : ∀ l, program (labels l) = instruction place labels exit l)
variable (base : K → List Bool) (ambient : A)

local notation "C" => configuration place labels exit base ambient
local notation "tick" => advance (TM2.step program)

include distinct atLabels

theorem optionTrace (action : Action) (entry : Option Nat)
    (source index payload reversed : List Bool) :
    tick^[(optionBits natBits entry).length]
      (some (C (some (.option action))
        (words (optionBits natBits entry ++ source) index payload reversed))) =
      some (C (some action.next)
        (words source index payload (saved action (optionBits natBits entry) reversed))) := by
  cases entry with
  | none =>
      have h := one place distinct labels exit program atLabels base ambient
        (.option action) (words (false :: source) index payload reversed)
      cases action <;> simpa [next, consume, emit, put_words, words, saved,
        optionBits, Action.writes, Action.next] using h
  | some value =>
      have first := one place distinct labels exit program atLabels base ambient
        (.option action) (words (true :: (natBits value ++ source)) index payload reversed)
      have second := nameTrace place distinct labels exit program atLabels base ambient
        action value.bits source index payload
        (if action.writes then true :: reversed else reversed)
      have clock : 1 + (BinPackingCompleteness.BinaryEncoding.frame value.bits).length =
          (optionBits natBits (some value)).length := by
        simp only [optionBits, natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
          List.length_cons]
        omega
      cases action <;>
        simp only [saved, Action.writes, Action.next, Bool.false_eq_true,
          ↓reduceIte] at second ⊢ <;>
        simp [next, consume, emit, put_words, words, Action.writes,
          natBits, BinPackingCompleteness.BinaryEncoding.nameBits] at first <;>
        have full := joinTrace (oneStepTrace first) second <;>
        rw [clock] at full <;>
        simpa only [optionBits, natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
          List.cons_append, List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using full

end BinPackingGap.SearchFixedReplaceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialShapeMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialShapeMachine

open BinaryEncoding
open BinPackingCompleteness.BinaryNameMachine (finalDigit canonical)

theorem run_name (next : Continuation) (name : Nat) (rest : List Bool) :
    run (.name next true) (natBits name ++ rest) = run (afterName next) rest := by
  apply run_frame
  exact (finalDigit_true_iff name.bits).mpr
    (BinPackingCompleteness.BinaryParsing.canonical_nat_bits name)

theorem run_items (items : RawInstance) (rest : List Bool) :
    run .items (rawInstanceBits items ++ rest) = run .done rest := by
  induction items with
  | nil => simp [rawInstanceBits, listBits, run, nextMode]
  | cons q items ih =>
      simp only [rawInstanceBits, listBits, List.cons_append, run, nextMode,
        pairBits, List.append_assoc, run_name, afterName]
      exact ih

theorem run_rawInstanceBits (items : RawInstance) :
    run .items (rawInstanceBits items) = .done := by
  simpa only [List.append_nil, run] using run_items items []

theorem name_inverse (next : Continuation) (input : List Bool)
    (accepted : run (.name next true) input = .done) :
    ∃ name rest, input = natBits name ++ rest ∧ run (afterName next) rest = .done := by
  obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := frame_inverse next true input accepted
  have hcanonical := (finalDigit_true_iff bits).mp hvalid
  have hbits := (BinPackingCompleteness.BinaryParsing.canonical_iff bits).mp hcanonical
  refine ⟨BinPackingCompleteness.BinaryEncoding.bitsValue bits, rest, ?_, hrest⟩
  simpa only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits, hbits] using hinput

theorem items_inverse_aux (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .items input = .done) :
    ∃ items, input = rawInstanceBits items := by
  induction fuel generalizing input with
  | zero => omega
  | succ fuel ih =>
      cases input with
      | nil => simp [run] at accepted
      | cons flag input =>
          cases flag with
          | false =>
              have hdone : run .done input = .done := accepted
              have hempty := (run_done_iff input).mp hdone
              subst input
              exact ⟨[], rfl⟩
          | true =>
              have haccepted : run (.name .numerator true) input = .done := accepted
              obtain ⟨num, afterNum, hnum, hafterNum⟩ :=
                name_inverse .numerator input haccepted
              obtain ⟨den, rest, hden, hrest⟩ :=
                name_inverse .denominator afterNum hafterNum
              have hlength := congrArg List.length hnum
              have hlength' := congrArg List.length hden
              simp only [List.length_append] at hlength hlength'
              have henough : rest.length < fuel := by
                simp only [List.length_cons] at enough
                omega
              obtain ⟨items, htail⟩ := ih rest henough hrest
              refine ⟨(num, den) :: items, ?_⟩
              simp [rawInstanceBits, listBits, pairBits, hnum, hden, htail, List.append_assoc]

theorem run_items_iff (input : List Bool) :
    run .items input = .done ↔ ∃ items, input = rawInstanceBits items := by
  constructor
  · intro accepted
    exact items_inverse_aux (input.length + 1) input (by omega) accepted
  · rintro ⟨items, rfl⟩
    exact run_rawInstanceBits items

def decodeAccepts (input : List Bool) : Bool := (decodeRawInstance input).isSome

theorem accepts_eq_decode (input : List Bool) :
    accepts input = (decodeRawInstance input).isSome := by
  cases parsed : decodeRawInstance input with
  | none =>
      have rejected : run .items input ≠ .done := by
        intro accepted
        obtain ⟨items, encoded⟩ := (run_items_iff input).mp accepted
        have roundtrip := decodeRawInstance_rawInstanceBits items
        rw [← encoded, parsed] at roundtrip
        cases roundtrip
      simp [accepts, rejected]
  | some items =>
      have encoded := decodeRawInstance_sound parsed
      have accepted := (run_items_iff input).mpr ⟨items, encoded⟩
      simp [accepts, accepted]

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution

theorem totalTrace (input : List Bool) :
    (advance machine.step)^[2 * input.length + 3]
      (some (initList machine input)) =
      some (haltList machine (decodeAccepts input :: input)) := by
  rw [initList_eq, haltList_eq]
  simpa only [accepts_eq_decode, decodeAccepts] using rawTrace input

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input (some (decodeAccepts input :: input))
      (2 * input.length + 3) where
  steps := 2 * input.length + 3
  evals_in_steps := totalTrace input
  steps_le_m := Nat.le_refl _

end BinPackingGap.SearchInitialShapeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchPrepareMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchPrepareMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchSemantics SearchEncoding BinaryEncoding
open BinPackingGames.Reduction.MachineTransfer

def code : Label → TM2.Stmt (fun _ : Tape => Bool) Label Register
  | .save => loopAt .input .scratch id false .save (some .saveRestore)
  | .saveRestore => MachineCopy.forkLoop .scratch .input .payload false
      .saveRestore (some .frameSaved)
  | .frameSaved => FrameEmitMachine.instruction .payload .reversed .frameSaved (some .phase)
  | .phase => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false) (go .reverse)
        (.pop .input (fun state head => (state.1, head))
          (.load (fun state => (state.2.getD false, none))
            (.goto fun _ => .convertBins .scan))))
  | .convertBins label => UnaryToBinaryMachine.instruction .input .binary .scratch
      Label.convertBins (some .emitBins) label
  | .emitBins => FrameEmitMachine.instruction .binary .reversed .emitBins (some .seedIndex)
  | .seedIndex => .push .index (fun _ => false) (go .index)
  | .index => .pop .input (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.push .index (fun _ => true) (go .index))
        (go (.convertLabel .scan)))
  | .convertLabel label => UnaryToBinaryMachine.instruction .input .binary .scratch
      Label.convertLabel (some .emitLabel) label
  | .emitLabel => FrameEmitMachine.instruction .binary .scratch .emitLabel (some .restoreLabel)
  | .restoreLabel => loopAt .scratch .payload id false .restoreLabel (some .items)
  | .items => copyFlag .numerator .dispatch
  | .numerator => copyFlag .numeratorDigit .denominator
  | .numeratorDigit => copyDigit .numerator
  | .denominator => copyFlag .denominatorDigit .items
  | .denominatorDigit => copyDigit .denominator
  | .dispatch => .branch Prod.fst (go (.replace (.entry true))) (go .fixed)
  | .replace label => SearchFixedReplaceMachine.instruction replacePlace
      Label.replace (some .reverse) label
  | .fixed => loopAt .input .reversed id false .fixed (some .reverse)
  | .reverse => loopAt .reversed .output id false .reverse none

end BinPackingGap.SearchPrepareMachine

end OAI
end


