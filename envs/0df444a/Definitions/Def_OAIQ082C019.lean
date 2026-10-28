-- Prove2me | Definitions.Def_OAIQ082C019
-- name    : OAIQ082C019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:40:39.721044+00:00
-- url     : https://prove2.me/theorems/006cfc90-1ee9-4f63-a335-c06b9e9bb309
-- title:
--   Definitions bundle OAIQ082C019 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 170 declarations of OpenAI's Lean: 59 definitions, 1 inductive type or structure, 2 instances and 108 theorems. The definitions and types are `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.closurePorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.closureProgram`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.closureSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.rootSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.widthAddress`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan.mismatchForest`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceTemplate.mismatchTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceTemplate.tokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.Agrees`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.Ready`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.tokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.gateInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.outputInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.circuitInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer.computableInPolyTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer.fullRunInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders.headersInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop.bodyInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop.loopInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerRuntime.fullRunInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages.cleanupInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages.finishInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages.tagInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Full.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Pair.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Row.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.steps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.State`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.initialState`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerTime.forestSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Emitter.ChoiceLabel`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Emitter.choice`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Emitter.choiceProgram`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Emitter.congr`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Emitter.literal`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Emitter.literalProgram`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Emitter.seq`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Emitter.seqProgram` and 20 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Computation_MachineExpanderFamilyAffine`, `BinPacking_Computation_MachineHorner`, `BinPacking_Computation_MachineRegularTable`, `BinPacking_CookLevin_CellsTokensAlignment`, `BinPacking_CookLevin_CircuitEncodingBridge`, `BinPacking_CookLevin_CircuitFinish`, `BinPacking_CookLevin_CircuitProducer`, `BinPacking_CookLevin_ClashMachine`, `BinPacking_CookLevin_ForestStage`, `BinPacking_CookLevin_InitializationMachineAt`, `BinPacking_CookLevin_OutputOrder`, `BinPacking_CookLevin_PaddingCellsMachine`, `BinPacking_CookLevin_PayloadPresenceMachine`, `BinPacking_CookLevin_PostfixBounds`, `BinPacking_CookLevin_ProducerFrontStage`, `BinPacking_CookLevin_TermMachine`, `BinPacking_CookLevin_TransitionArena`, `BinPacking_CookLevin_TransitionIteration`, `BinPacking_CookLevin_TransitionIterationTime`, `BinPacking_CookLevin_ValidityComposition`, `BinPacking_CookLevin_VerifierFront`, `BinPacking_Information_SourceFieldArray`, `BinPacking_Information_SourceNonempty`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C010`, `OAIQ082C011`, `OAIQ082C012` and `OAIQ082C013` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ082C024`.
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

section
-- module Solutions.OAIQ082_BP.BinPacking_Information_SourceFieldArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Hastad.SourceMachine

open Turing
open BinPackingGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

def fourFieldsInTime (source : K) (destination : Fin 4 → K)
    (hsep : ∀ j, source ≠ destination j)
    (start loopLabel : Fin 4 → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : ∀ j, program (start j) = fieldStart (destination j) (loopLabel j))
    (atLoop : ∀ j, program (loopLabel j) =
      fieldLoop source (destination j) (loopLabel j) (fieldNext start exit j))
    (base : K → List Bool) (a b c d : Nat) (suffix : List Bool)
    (hinput : base source = encodeWords [a, b, c, d] ++ suffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (start 0), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), fourTapes source destination base a b c d suffix⟩)
      (a + b + c + d + 8) := by
  let t₀ := afterField source (destination 0) base a (encodeWords [b, c, d] ++ suffix)
  let t₁ := afterField source (destination 1) t₀ b (encodeWords [c, d] ++ suffix)
  let t₂ := afterField source (destination 2) t₁ c (encodeWords [d] ++ suffix)
  have h₀ : base source = encodeWord a ++ (encodeWords [b, c, d] ++ suffix) := by
    simpa only [encodeWords, List.append_assoc] using hinput
  have h₁ : t₀ source = encodeWord b ++ (encodeWords [c, d] ++ suffix) := by
    simp [t₀, afterField, hsep, encodeWords, List.append_assoc]
  have h₂ : t₁ source = encodeWord c ++ (encodeWords [d] ++ suffix) := by
    simp [t₁, afterField, hsep, encodeWords, List.append_assoc]
  have h₃ : t₂ source = encodeWord d ++ suffix := by
    simp [t₂, afterField, hsep, encodeWords]
  have p₀ := fieldInTime source (destination 0) (hsep 0) (start 0) (loopLabel 0)
    (some (start 1)) program (atStart 0) (atLoop 0) base a
    (encodeWords [b, c, d] ++ suffix) h₀ ambient register
  have p₁ := fieldInTime source (destination 1) (hsep 1) (start 1) (loopLabel 1)
    (some (start 2)) program (atStart 1) (atLoop 1) t₀ b
    (encodeWords [c, d] ++ suffix) h₁ ambient none
  have p₂ := fieldInTime source (destination 2) (hsep 2) (start 2) (loopLabel 2)
    (some (start 3)) program (atStart 2) (atLoop 2) t₁ c
    (encodeWords [d] ++ suffix) h₂ ambient none
  have p₃ := fieldInTime source (destination 3) (hsep 3) (start 3) (loopLabel 3)
    exit program (atStart 3) (atLoop 3) t₂ d suffix h₃ ambient none
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ p₁
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂
  let p := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  exact {
    toEvalsTo := p.toEvalsTo
    steps_le_m := by have h := p.steps_le_m; omega
  }

end BinPackingGames.Foundations.Hastad.SourceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineHorner
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

theorem bodyTrace (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b r : ℕ) (hr : r < b)
    (operand : base (slots 0) = encodeWord a) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[bodySteps a]
      (some (MachineCountedLoop.bodyConfiguration (slots 3) (labels .scan) []
        (fun _ => (ambient, ())) (loopBase slots base a b) r)) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) r) := by
  have h04 : slots 0 ≠ slots 4 := slots.injective.ne (by decide)
  have h02 : slots 0 ≠ slots 2 := slots.injective.ne (by decide)
  have h42 : slots 4 ≠ slots 2 := slots.injective.ne (by decide)
  have h03 : slots 0 ≠ slots 3 := slots.injective.ne (by decide)
  have h43 : slots 4 ≠ slots 3 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let start := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b (r + 1)) r []
  have hstartA : start (slots 0) = encodeWord a := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h03, h02, operand]
  have hstartScratch : start (slots 4) = [] := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h43, h42, scratchEmpty]
  have hscan : p (labels .scan) = MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore) := atLabels .scan
  have hemit : ∀ control bit, p (emitterLabel labels control bit) =
      MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) control bit := by
    intro control bit
    cases control
    cases bit <;> exact atLabels _
  have hrestore : p (labels .restore) = Reduction.MachineTransfer.loopAt (slots 4) (slots 0)
      id false (labels .restore) (some (labels .guard)) := atLabels .restore
  have hcopy := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 4) (slots 2)
    h04 h02 h42 () transition payload (labels .scan) (labels .restore) (emitterLabel labels)
    (some (labels .guard)) p hscan hemit hrestore start hstartScratch ambient () none
  rw [hstartA, output_encodeWord, List.reverse_replicate] at hcopy
  have hcount : a + a * (b - (r + 1)) = a * (b - r) := by
    have hr' : b - r = b - (r + 1) + 1 := by omega
    rw [hr']
    ring
  have hfinish : Function.update start (slots 2)
      (List.replicate a true ++ start (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b r) r [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp only [Function.update_self]
      simp only [start, MachineUnaryCounter.counterTapes_other (slots 3) (slots 2) h23,
        loopBase, resultTapes_output]
      rw [prepend_payload, hcount]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [start, MachineUnaryCounter.counterTapes, hk2]
      · simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  rw [hfinish] at hcopy
  simpa only [bodySteps, encodeWord, List.length_append, List.length_replicate,
    List.length_singleton, MachineCountedLoop.bodyConfiguration,
    MachineCountedLoop.guardConfiguration] using hcopy

theorem multiplyTrace (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps a b]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
  have h13 : slots 1 ≠ slots 3 := slots.injective.ne (by decide)
  have h14 : slots 1 ≠ slots 4 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let copied := Function.update base (slots 3) (encodeWord b)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (b + 2)]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .seed), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 1) (slots 3) (slots 4) h13 h14 h34 false
      (labels .copyDrain) (labels .copyFork) (some (labels .seed)) p
      (atLabels .copyDrain) (atLabels .copyFork) base scratchEmpty (ambient, ()) register
    simpa only [copied, operandB, counterEmpty, List.append_nil, encodeWord, List.length_append,
      List.length_replicate, List.length_singleton, Nat.add_assoc, Nat.reduceAdd] using h
  have hseedTapes : Function.update copied (slots 2) (false :: copied (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b b) b [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h23, encodeWord]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [copied, MachineUnaryCounter.counterTapes, hk2]
      · simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), ((ambient, ()), none), copied⟩) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) b) := by
    change some (TM2.stepAux (p (labels .seed)) ((ambient, ()), none) copied) = _
    rw [atLabels .seed]
    change some (⟨some (labels .guard), ((ambient, ()), none),
      Function.update copied (slots 2) (false :: copied (slots 2))⟩ :
        TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
    rw [hseedTapes]
    rfl
  have hloop := MachineCountedLoop.loopTrace (slots 3) (labels .guard) (labels .scan)
    (labels .finish) p (atLabels .guard) [] (fun _ => (ambient, ())) (fun _ => none)
    (loopBase slots base a b) (fun _ => bodySteps a) b
    (fun r hr => bodyTrace slots labels exit p atLabels base a b r hr operandA scratchEmpty ambient)
  let finalCounter := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b 0) 0 []
  have hfinishTapes : Function.update finalCounter (slots 3) ((finalCounter (slots 3)).tail) =
      resultTapes slots base (a * b) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp [finalCounter, MachineUnaryCounter.counterTapes, encodeWord, resultTapes,
        Ne.symm h23, counterEmpty]
    · simp [finalCounter, MachineUnaryCounter.counterTapes, loopBase, hk3]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some (MachineCountedLoop.exitConfiguration (slots 3) (labels .finish) []
        (fun _ => (ambient, ())) (loopBase slots base a b))) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) finalCounter) = _
    rw [atLabels .finish]
    cases exit <;>
      simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using
        congrArg (fun tapes => some (⟨_, ((ambient, ()), none), tapes⟩ :
          TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
  rw [show steps a b = 1 + (MachineCountedLoop.totalSteps (fun _ => bodySteps a) b +
      (1 + 2 * (b + 2))) by rw [totalSteps_eq]; unfold steps bodySteps; ring]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    hcopy, hseed, hloop]
  exact hfinish

end BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

namespace BinPackingGames.Foundations.Complexity.MachineRadixStep

open Turing

variable {K Λ σ : Type}

variable [DecidableEq K]

theorem radixStepTrace (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : ℕ)
    (operandRadix : base (slots 0) = encodeWord radix)
    (operandAcc : base (slots 1) = encodeWord acc)
    (operandDigit : base (slots 2) = encodeWord digit)
    (counterEmpty : base (slots 4) = []) (scratchEmpty : base (slots 5) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps radix acc digit]
      (some ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ := by
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  have h24 : slots 2 ≠ slots 4 := slots.injective.ne (by decide)
  have h25 : slots 2 ≠ slots 5 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h53 : slots 5 ≠ slots 3 := slots.injective.ne (by decide)
  have h45 : slots 4 ≠ slots 5 := slots.injective.ne (by decide)
  let multiplied := resultTapes slots base (radix * acc)
  have hmul : (MachineComposition.advance (TM2.step p))^[MachineUnaryMultiply.steps radix acc]
      (some ⟨some (labels (.multiply .copyDrain)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .digitDrain), ((ambient, ()), none), multiplied⟩ := by
    have h := MachineUnaryMultiply.multiplyTrace (multiplySlots slots)
      (fun l => labels (.multiply l)) (some (labels .digitDrain)) p
      (fun l => atLabels (.multiply l)) base radix acc operandRadix operandAcc
      counterEmpty scratchEmpty ambient register
    simpa only [MachineUnaryMultiply.resultTapes, multiplySlots_two, multiplied, resultTapes] using h
  have hmulDigit : multiplied (slots 2) = encodeWord digit := by
    simp [multiplied, resultTapes, h23, operandDigit]
  have hmulCounter : multiplied (slots 4) = [] := by
    simp [multiplied, resultTapes, Ne.symm h34, counterEmpty]
  have hmulScratch : multiplied (slots 5) = [] := by
    simp [multiplied, resultTapes, h53, scratchEmpty]
  let copied := Function.update multiplied (slots 4) (encodeWord digit)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (digit + 2)]
      (some ⟨some (labels .digitDrain), ((ambient, ()), none), multiplied⟩) =
      some ⟨some (labels .add), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 2) (slots 4) (slots 5) h24 h25 h45 false
      (labels .digitDrain) (labels .digitFork) (some (labels .add)) p
      (atLabels .digitDrain) (atLabels .digitFork) multiplied hmulScratch (ambient, ()) none
    simpa only [copied, hmulDigit, hmulCounter, List.append_nil, encodeWord,
      List.length_append, List.length_replicate, List.length_singleton,
      Nat.add_assoc, Nat.reduceAdd] using h
  have hcopiedCounter : copied (slots 4) = encodeWord digit ++ [] := by simp [copied]
  have hcopiedOutput : copied (slots 3) = encodeWord (radix * acc) ++ base (slots 3) := by
    simp [copied, multiplied, resultTapes, h34]
  let added := MachineUnaryAddAt.unaryTapes (slots 4) (slots 3) copied
    0 (digit + radix * acc) [] (base (slots 3))
  have hadd : (MachineComposition.advance (TM2.step p))^[digit + 1]
      (some ⟨some (labels .add), ((ambient, ()), none), copied⟩) =
      some ⟨some (labels .finish), ((ambient, ()), none), added⟩ :=
    MachineUnaryAddAt.addFromTapes (slots 4) (slots 3) (Ne.symm h34)
      (labels .add) (some (labels .finish)) p (atLabels .add) copied digit (radix * acc)
      [] (base (slots 3)) hcopiedCounter hcopiedOutput (ambient, ()) none
  have hfinishTapes : Function.update added (slots 4) ((added (slots 4)).tail) =
      resultTapes slots base (radix * acc + digit) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp only [Function.update_of_ne h34, added, MachineUnaryAddAt.unaryTapes_destination,
        resultTapes_output]
      rw [Nat.add_comm digit (radix * acc)]
    · by_cases hk4 : k = slots 4
      · subst k
        simp [added, MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
          resultTapes, encodeWord, Ne.symm h34, counterEmpty]
      · simp [added, MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
          copied, multiplied, resultTapes, hk3, hk4]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .finish), ((ambient, ()), none), added⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (radix * acc + digit)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) added) = _
    rw [atLabels .finish]
    have hcfg := congrArg (fun tapes => some (⟨exit, ((ambient, ()), none), tapes⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
    cases exit <;> simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using hcfg
  rw [show steps radix acc digit =
      1 + ((digit + 1) + (2 * (digit + 2) + MachineUnaryMultiply.steps radix acc)) by
        unfold steps MachineUnaryMultiply.steps; ring]
  rw [Function.iterate_add_apply _ 1,
    Function.iterate_add_apply _ (digit + 1),
    Function.iterate_add_apply _ (2 * (digit + 2)), hmul, hcopy, hadd]
  exact hfinish

end BinPackingGames.Foundations.Complexity.MachineRadixStep

namespace BinPackingGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

theorem digitTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix acc digit : Nat) (i : Fin width)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigit : base (slots (.inr i)) = encodeWord digit)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[stepCost radix acc digit]
      (some ⟨some (labels (.radix i (.multiply .copyDrain))), ((ambient, ()), register),
        stageTapes slots base i.val acc⟩) =
      some ⟨some (labels (entryLabel width (i.val + 1))), ((ambient, ()), none),
        stageTapes slots base (i.val + 1) (radix * acc + digit)⟩ := by
  let rs := radixSlots slots i
  let before := stageTapes slots base i.val acc
  let after := MachineRadixStep.resultTapes rs before (radix * acc + digit)
  have h01 : rs 0 ≠ rs 1 := rs.injective.ne (by decide)
  have h21 : rs 2 ≠ rs 1 := rs.injective.ne (by decide)
  have h31 : rs 3 ≠ rs 1 := rs.injective.ne (by decide)
  have h41 : rs 4 ≠ rs 1 := rs.injective.ne (by decide)
  have h51 : rs 5 ≠ rs 1 := rs.injective.ne (by decide)
  have hb : before (rs 0) = encodeWord radix := by
    change Function.update base (rs 1) (encodeWord acc) (rs 0) = _
    rw [Function.update_of_ne h01]
    exact operandRadix
  have ha : before (rs 1) = encodeWord acc := by
    exact Function.update_self _ _ _
  have hd : before (rs 2) = encodeWord digit := by
    change Function.update base (rs 1) (encodeWord acc) (rs 2) = _
    rw [Function.update_of_ne h21]
    exact operandDigit
  have hc : before (rs 4) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 4) = _
    rw [Function.update_of_ne h41]
    exact clean.counter
  have hs : before (rs 5) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 5) = _
    rw [Function.update_of_ne h51]
    exact clean.scratch
  have hout : before (rs 3) = [] := by
    change Function.update base (rs 1) (encodeWord acc) (rs 3) = _
    rw [Function.update_of_ne h31]
    exact clean.acc _
  have hradix := MachineRadixStep.radixStepTrace rs (fun l => labels (.radix i l))
    (some (labels (.clear i))) p (fun l => atLabels (.radix i l)) before radix acc digit
    hb ha hd hc hs ambient register
  have hold : after (rs 1) = encodeWord acc := by
    change Function.update before (rs 3) _ (rs 1) = _
    rw [Function.update_of_ne (Ne.symm h31), ha]
  have hstart : Function.update after (rs 1) (encodeWord acc ++ []) = after := by
    rw [List.append_nil, ← hold, Function.update_eq_self]
  have hfinish : Function.update after (rs 1) [] =
      stageTapes slots base (i.val + 1) (radix * acc + digit) := by
    have hempty : base (rs 1) = [] := clean.acc _
    change Function.update (Function.update (Function.update base (rs 1) (encodeWord acc))
      (rs 3) (encodeWord (radix * acc + digit) ++ before (rs 3))) (rs 1) [] =
      Function.update base (rs 3) (encodeWord (radix * acc + digit))
    rw [hout, List.append_nil]
    funext k
    by_cases h1 : k = rs 1
    · subst k; simp [Ne.symm h31, hempty]
    · by_cases h3 : k = rs 3
      · subst k; simp [h31]
      · simp [h1, h3]
  have hdrain := drainTrace (rs 1) (labels (.clear i))
    (some (labels (entryLabel width (i.val + 1)))) p (atLabels (.clear i))
    after acc [] ambient none
  rw [hstart, hfinish] at hdrain
  rw [show stepCost radix acc digit = (acc + 1) + MachineRadixStep.steps radix acc digit by
    unfold stepCost; omega, Function.iterate_add_apply, hradix]
  exact hdrain

theorem prefixTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (n : Nat) (hn : n ≤ width) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps radix digits n]
      (some ⟨some (labels (entryLabel width 0)), ((ambient, ()), none), stageTapes slots base 0 0⟩) =
      some ⟨some (labels (entryLabel width n)), ((ambient, ()), none),
        stageTapes slots base n (value radix digits n)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < width := by omega
    let i : Fin width := ⟨n, hlt⟩
    rw [prefixSteps, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
    have h := digitTrace slots labels exit p atLabels base radix (value radix digits n)
      (digits n) i operandRadix (operandDigits i) clean ambient none
    simpa only [entryLabel, dite_eq_left hlt, i, value] using h

theorem finishTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (acc : Nat) (clean : Clean slots base) (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[2 * acc + 4]
      (some ⟨some (labels .finishDrain), ((ambient, ()), none), stageTapes slots base width acc⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base acc⟩ := by
  let src := slots (.inl (accumulator (parity width)))
  let scratch := slots (.inl 5)
  let dst := slots (.inl 3)
  have hsrcScratch : src ≠ scratch := by
    apply slots.injective.ne
    cases parity width <;> simp [accumulator]
  have hsrcDst : src ≠ dst := by
    apply slots.injective.ne
    cases parity width <;> simp [accumulator]
  have hscratchDst : scratch ≠ dst := slots.injective.ne (by simp)
  have hsrc : base src = [] := clean.acc _
  have hs : base scratch = [] := clean.scratch
  let before := stageTapes slots base width acc
  let middle := Function.update base scratch (encodeWord acc).reverse
  have hinput : before src = encodeWord acc := Function.update_self _ _ _
  have hscratch : before scratch = [] := by
    change Function.update base src (encodeWord acc) scratch = []
    rw [Function.update_of_ne (Ne.symm hsrcScratch), hs]
  have hfirstTapes : Reduction.MachineTransfer.tapesAt src scratch before []
      ((before src).reverse.map id ++ before scratch) = middle := by
    rw [hinput, hscratch, List.append_nil, List.map_id]
    funext k
    by_cases h1 : k = src
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, middle, hsrcScratch, hsrc]
    · by_cases h2 : k = scratch
      · subst k; simp [Reduction.MachineTransfer.tapesAt, middle]
      · simp [Reduction.MachineTransfer.tapesAt, middle, before, stageTapes, h1, h2, src]
  have first := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (σ := σ × Unit) src scratch hsrcScratch id false
    (labels .finishDrain) (some (labels .finishRestore)) p (atLabels .finishDrain)
    before (ambient, ()) none
  rw [hfirstTapes] at first
  have hlength : (before src).length + 1 = acc + 2 := by
    simp [hinput, encodeWord, Nat.add_assoc]
  rw [hlength] at first
  change (MachineComposition.advance (TM2.step p))^[acc + 2]
    (some ⟨some (labels .finishDrain), ((ambient, ()), none), before⟩) =
      some ⟨some (labels .finishRestore), ((ambient, ()), none), middle⟩ at first
  have hmSource : middle scratch = (encodeWord acc).reverse := Function.update_self _ _ _
  have hmOutput : middle dst = base dst := by
    exact Function.update_of_ne (Ne.symm hscratchDst) _ _
  have hsecondTapes : Reduction.MachineTransfer.tapesAt scratch dst middle []
      ((middle scratch).reverse.map id ++ middle dst) = resultTapes slots base acc := by
    rw [hmSource, hmOutput, List.reverse_reverse, List.map_id]
    funext k
    by_cases h1 : k = dst
    · subst k; simp [Reduction.MachineTransfer.tapesAt, resultTapes, dst]
    · by_cases h2 : k = scratch
      · subst k
        simp [Reduction.MachineTransfer.tapesAt, resultTapes, middle, hscratchDst, hs, scratch, dst]
      · simp [Reduction.MachineTransfer.tapesAt, resultTapes, middle, h1, h2, dst]
  have second := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (σ := σ × Unit) scratch dst hscratchDst id false
    (labels .finishRestore) exit p (atLabels .finishRestore) middle (ambient, ()) none
  rw [hsecondTapes] at second
  have hmLength : (middle scratch).length + 1 = acc + 2 := by
    simp [hmSource, encodeWord, Nat.add_assoc]
  rw [hmLength] at second
  change (MachineComposition.advance (TM2.step p))^[acc + 2]
    (some ⟨some (labels .finishRestore), ((ambient, ()), none), middle⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base acc⟩ at second
  rw [show 2 * acc + 4 = (acc + 2) + (acc + 2) by omega,
    Function.iterate_add_apply, first]
  exact second

theorem hornerTrace (slots : Layout width ↪ K) (labels : Label width → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (radix : Nat) (digits : Nat → Nat)
    (operandRadix : base (slots (.inl 0)) = encodeWord radix)
    (operandDigits : ∀ i : Fin width, base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps radix digits width]
      (some ⟨some (labels .start), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (value radix digits width)⟩ := by
  have start : TM2.step p ⟨some (labels .start), ((ambient, ()), register), base⟩ =
      some ⟨some (labels (entryLabel width 0)), ((ambient, ()), none), stageTapes slots base 0 0⟩ := by
    change some (TM2.stepAux (p (labels .start)) _ _) = _
    rw [atLabels .start]
    simp only [statement, TM2.stepAux, clean.accA, stageTapes, parity, accumulator,
      Bool.false_eq_true, ↓reduceIte, encodeWord, List.replicate_zero, List.nil_append]
  have prefixRun := prefixTrace slots labels exit p atLabels base radix digits operandRadix
    operandDigits clean ambient width (Nat.le_refl _)
  have final := finishTrace slots labels exit p atLabels base (value radix digits width) clean ambient
  have hend : entryLabel width width = .finishDrain := by simp [entryLabel]
  rw [hend] at prefixRun
  rw [show steps radix digits width =
    ((2 * value radix digits width + 4) + prefixSteps radix digits width) + 1 by
      unfold steps; omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step p))^[
    (2 * value radix digits width + 4) + prefixSteps radix digits width]
      (TM2.step p ⟨some (labels .start), ((ambient, ()), register), base⟩) = _
  rw [start, Function.iterate_add_apply, prefixRun]
  exact final

open scoped BigOperators

end BinPackingGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineExpanderFamilyAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

instance alphabetFintype (tape : Tape) : Fintype (Alphabet tape) := by
  rw [alphabet_eq]
  exact inferInstanceAs (Fintype Bool)

end BinPackingGames.Foundations.Complexity.MachineExpanderFamily

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

namespace Top

instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

end Top

end BinPackingGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitEncodingBridge
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission

open Turing
open BinPackingGames.Reduction
open CircuitProducerModel

theorem contextTrace (context : Context) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[contextSteps context base]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState, contextTapes context base⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (contextSource context) Tape.scratch Tape.reversed
    (contextSource_ne_scratch context) (contextSource_ne_reversed context) (by decide)
    defaultControl (fun control _ => control) emission
    (.scan context) (.restore context) (fun control symbol => .emit context control symbol)
    (contextNext context) program rfl (by intros; rfl) rfl base scratchEmpty () context none
  rw [contextSteps, show 3 * (base (contextSource context)).length + 3 =
      (3 * (base (contextSource context)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step program))^[
    3 * (base (contextSource context)).length + 2]
    (TM2.step program ⟨some (.setup context), state, base⟩) = _
  rw [setupStep]
  exact copied

theorem contextTrace_word (context : Context) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State) (value : Nat)
    (cached : base (contextSource context) = encodeWord value) :
    (MachineComposition.advance (TM2.step program))^[3 * (value + 1) + 3]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState,
        Function.update base .reversed
          ((encodeWords (contextWords context value)).reverse ++ base .reversed)⟩ := by
  simpa only [contextSteps, contextTapes, contextOutput, cached, encodeWord_length, output_word]
    using contextTrace context base scratchEmpty state

theorem contextListTrace (contexts : List Context) (exit : Option Label)
    (linked : ContextListLinked contexts exit) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (emptyInitial : contexts = [] → state = initialState) :
    (MachineComposition.advance (TM2.step program))^[contextListSteps contexts base]
      (some ⟨contextListStart contexts exit, state, base⟩) =
      some ⟨exit, initialState, Function.update base .reversed
        ((contextListOutput contexts base).reverse ++ base .reversed)⟩ := by
  induction contexts generalizing base state with
  | nil =>
    rw [emptyInitial rfl]
    simp [contextListSteps, contextListOutput, contextListStart]
  | cons context rest ih =>
    let after := contextTapes context base
    have first := contextTrace context base scratchEmpty state
    have second := ih linked.2 after (by simpa [after] using scratchEmpty)
      initialState (by intro _; rfl)
    rw [linked.1] at first
    have combined := chain first second
    simp only [after, contextTapes, contextListSteps_update, contextListOutput_update,
      Function.update_self, Function.update_idem] at combined
    rw [show contextListSteps (context :: rest) base =
        contextListSteps rest base + contextSteps context base by
      simp [contextListSteps, Nat.add_comm]]
    simpa only [contextListStart, contextListOutput, List.flatMap_cons,
      List.reverse_append, List.append_assoc] using combined

theorem gateTrace (record : Record) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    (MachineComposition.advance (TM2.step program))^[gateSteps record]
      (some ⟨some (.setup (.gate record.tag 0)), state, base⟩) =
      some ⟨some (.cleanup 0), initialState, Function.update base .reversed
        (record.outputBits.reverse ++ base .reversed)⟩ := by
  have trace := contextListTrace (gateContexts record.tag) (some (.cleanup 0))
    (gateContexts_linked record.tag) base scratchEmpty state
    (by intro h; have := congrArg List.length h; simp [gateContexts] at this)
  rw [gateSteps_eq record base h1 h2 h3, gateOutput_words record base h1 h2 h3] at trace
  simpa [contextListStart, gateContexts, List.finRange] using trace

def gateInTime (record : Record) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.setup (.gate record.tag 0)), state, base⟩
      (some ⟨some (.cleanup 0), initialState, Function.update base .reversed
        (record.outputBits.reverse ++ base .reversed)⟩)
      (gateSteps record) where
  steps := gateSteps record
  evals_in_steps := gateTrace record base scratchEmpty state h1 h2 h3
  steps_le_m := Nat.le_refl _

theorem outputTrace (selected : Nat) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (cached : base .selected = encodeWord selected) :
    (MachineComposition.advance (TM2.step program))^[9 * (selected + 1) + 9]
      (some ⟨some (.setup (.output 0)), state, base⟩) =
      some ⟨some .finalCounter, initialState, Function.update base .reversed
        ((encodeWords (outputWords selected)).reverse ++ base .reversed)⟩ := by
  have trace := contextListTrace outputContexts (some .finalCounter)
    outputContexts_linked base scratchEmpty state (by simp [outputContexts])
  have steps : contextListSteps outputContexts base = 9 * (selected + 1) + 9 := by
    simp [contextListSteps, outputContexts, contextSteps, contextSource, cached]
    omega
  have out : contextListOutput outputContexts base = encodeWords (outputWords selected) := by
    simp [contextListOutput, outputContexts, contextOutput, contextSource, cached,
      output_word, contextWords, outputWords, encodeWords, List.append_assoc]
  rw [steps, out] at trace
  exact trace

def outputInTime (selected : Nat) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (cached : base .selected = encodeWord selected) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.setup (.output 0)), state, base⟩
      (some ⟨some .finalCounter, initialState, Function.update base .reversed
        ((encodeWords (outputWords selected)).reverse ++ base .reversed)⟩)
      (9 * (selected + 1) + 9) where
  steps := 9 * (selected + 1) + 9
  evals_in_steps := outputTrace selected base scratchEmpty state cached
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_OutputOrder
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PositionMachine

open Turing MachineComposition TransitionTemplate

section Statements

variable {K Λ σ : Type} [DecidableEq K]

theorem seedTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (p : Position) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement source scratch destination p labels exit l)
    (base : K → List Bool) (cursor : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord cursor ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[seedSteps p cursor]
      (some ⟨some (labels .start), (ambient, register), base⟩) =
      some ⟨some (labels .finish), (ambient, if usesCurrent p then none else register),
        Function.update base destination (encodeWord (initialValue p cursor) ++ base destination)⟩ := by
  cases hc : usesCurrent p with
  | false =>
    simp only [seedSteps, initialValue, hc, Bool.false_eq_true, ↓reduceIte,
      Function.iterate_one, advance_some]
    change some (TM2.stepAux (program (labels .start)) (ambient, register) base) = _
    rw [atLabels]
    simp [statement, hc, TM2.stepAux, encodeWord]
  | true =>
    have h := MachineUnaryAffineAt.seededAffineTrace source scratch destination hs hd hsd
      1 0 (labels .start) (labels .scan) (labels .restore) (some (labels .finish))
      program (by simpa [statement, hc] using atLabels .start)
      (atLabels .scan) (atLabels .restore) base cursor suffix sourceWord scratchEmpty
      ambient register
    simpa only [seedSteps, initialValue, hc, ↓reduceIte, one_mul, add_zero] using h

theorem positionTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (p : Position) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement source scratch destination p labels exit l)
    (base : K → List Bool) (cursor : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord cursor ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps p cursor]
      (some ⟨some (labels .start), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (p.eval cursor) ++ base destination)⟩ := by
  rw [steps, Nat.add_comm (seedSteps p cursor) 1, Function.iterate_add_apply,
    seedTrace source scratch destination hs hd hsd p labels exit program atLabels
      base cursor suffix sourceWord scratchEmpty ambient register,
    finishTrace source scratch destination p labels exit program (atLabels .finish),
    transform_initialValue]

end Statements

end BinPackingGames.Foundations.Complexity.CookLevin.PositionMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ClashMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

namespace Input

theorem trace (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n : Nat)
    (sourceWord : base (slots 0) = encodeWord n) (scratchEmpty : base (slots 1) = [])
    (ambient : σ) :
    (advance (TM2.step program))^[steps n]
      (some ⟨some (labels .tag), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 2) (slots 3) base [.input n]⟩ := by
  let tagged := Function.update (Function.update base (slots 2)
    ((encodeWord 5).reverse ++ base (slots 2))) (slots 3) (true :: base (slots 3))
  have htag : (advance (TM2.step program))^[1]
      (some ⟨some (labels .tag), clean ambient, base⟩) =
      some ⟨some (labels .scan), clean ambient, tagged⟩ := by
    change some (TM2.stepAux (program (labels .tag)) _ _) = _
    rw [atLabels, statement, stepAux_pushWord]
    simp [TM2.stepAux, tagged, slots.injective.eq_iff]
  have hs : tagged (slots 0) = encodeWord n := by
    simpa [tagged, slots.injective.eq_iff] using sourceWord
  have ht : tagged (slots 1) = [] := by
    simpa [tagged, slots.injective.eq_iff] using scratchEmpty
  have hcopy := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 1) (slots 2)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
    (slots.injective.ne (by decide)) false (fun (_ : Bool) _ => false) (fun _ b => [b])
    (labels .scan) (labels .restore) (fun _ b => labels (.emit b)) exit program
    (atLabels .scan)
    (fun (control symbol : Bool) => by
      simpa only [statement, MachineTransducerCopy.emitter] using (atLabels (Label.emit symbol)))
    (atLabels .restore) tagged ht ambient false none
  rw [hs, encodeWord_length, identity_output] at hcopy
  have hout : Function.update tagged (slots 2) ((encodeWord n).reverse ++ tagged (slots 2)) =
      emitted (slots 2) (slots 3) base [.input n] := by
    funext k
    by_cases ho : k = slots 2
    · subst k
      simp [tagged, emitted, tokenBits, tokenWords, Token.words, encodeWords,
        slots.injective.eq_iff, List.reverse_append, List.append_assoc]
    · by_cases hc : k = slots 3
      · subst k
        simp [tagged, emitted, slots.injective.eq_iff]
      · simp [tagged, emitted, ho, hc]
  rw [hout] at hcopy
  have h := chain htag hcopy
  simpa only [steps, clean, Nat.add_comm 1] using h

end Input

namespace Pair

def statement (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .left l => MachineUnaryLessAt.statement (leftMap.trans slots)
      (fun l => labels (.left l)) (some (labels .branchLeft)) l
  | .right l => MachineUnaryLessAt.statement (rightMap.trans slots)
      (fun l => labels (.right l)) (some (labels .branchRight)) l
  | .branchLeft => choose (labels (.inputLeft .tag)) (labels (.right .scan))
  | .branchRight => choose (labels (.inputLeft .tag)) (labels .diagonal)
  | .diagonal => literal (slots 4) (slots 5) [.const false]
      (Reduction.MachineTransfer.exitAt (slots 4) exit)
  | .inputLeft l => Input.statement (inputLeftMap.trans slots)
      (fun l => labels (.inputLeft l)) (some (labels (.inputRight .tag))) l
  | .inputRight l => Input.statement (inputRightMap.trans slots)
      (fun l => labels (.inputRight l)) (some (labels .conjunction)) l
  | .conjunction => literal (slots 4) (slots 5) [.and]
      (Reduction.MachineTransfer.exitAt (slots 4) exit)

theorem offTrace (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (i j : Nat)
    (leftWord : base (slots 0) = encodeWord i) (rightWord : base (slots 1) = encodeWord j)
    (leftEmpty : base (slots 2) = []) (ambient : σ) :
    (advance (TM2.step program))^[offSteps i j]
      (some ⟨some (labels (.inputLeft .tag)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 4) (slots 5) base [.input i, .input j, .and]⟩ := by
  have hi := Input.trace (inputLeftMap.trans slots) (fun l => labels (.inputLeft l))
    (some (labels (.inputRight .tag))) program (fun _ => atLabels _)
    base i leftWord leftEmpty ambient
  change (advance (TM2.step program))^[Input.steps i]
    (some ⟨some (labels (.inputLeft .tag)), clean ambient, base⟩) =
    some ⟨some (labels (.inputRight .tag)), clean ambient,
      emitted (slots 4) (slots 5) base [.input i]⟩ at hi
  let afterLeft := emitted (slots 4) (slots 5) base [.input i]
  have hjWord : afterLeft (slots 1) = encodeWord j := by
    simpa [afterLeft, emitted, slots.injective.eq_iff] using rightWord
  have hjScratch : afterLeft (slots 2) = [] := by
    simpa [afterLeft, emitted, slots.injective.eq_iff] using leftEmpty
  have hj := Input.trace (inputRightMap.trans slots) (fun l => labels (.inputRight l))
    (some (labels .conjunction)) program (fun _ => atLabels _)
    afterLeft j hjWord hjScratch ambient
  change (advance (TM2.step program))^[Input.steps j]
    (some ⟨some (labels (.inputRight .tag)), clean ambient, afterLeft⟩) =
    some ⟨some (labels .conjunction), clean ambient,
      emitted (slots 4) (slots 5) afterLeft [.input j]⟩ at hj
  let afterRight := emitted (slots 4) (slots 5) afterLeft [.input j]
  have hand : (advance (TM2.step program))^[1]
      (some ⟨some (labels .conjunction), clean ambient, afterRight⟩) =
      some ⟨exit, clean ambient, emitted (slots 4) (slots 5) afterRight [.and]⟩ := by
    change some (TM2.stepAux (program (labels .conjunction)) _ _) = _
    rw [atLabels, statement, stepAux_literal _ _ (slots.injective.ne (by decide))]
    cases exit <;> rfl
  have h := chain (chain hi hj) hand
  simp only [afterRight, afterLeft,
    emitted_append (slots 4) (slots 5) (slots.injective.ne (by decide : (4 : Fin 6) ≠ 5)),
    List.singleton_append] at h
  exact h

theorem trace (slots : Fin 6 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (i j : Nat)
    (leftWord : base (slots 0) = encodeWord i) (rightWord : base (slots 1) = encodeWord j)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = []) (ambient : σ) :
    (advance (TM2.step program))^[steps i j]
      (some ⟨some (labels (.left .scan)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 4) (slots 5) base (clashPairTokens i j)⟩ := by
  have hl := MachineUnaryLessAt.lessThanTrace (leftMap.trans slots)
    (fun l => labels (.left l)) (some (labels .branchLeft)) program (fun _ => atLabels _)
    base i j [] [] (by simpa [leftMap] using leftWord) (by simpa [leftMap] using rightWord)
    leftEmpty rightEmpty ambient false none
  change (advance (TM2.step program))^[MachineUnaryLessAt.steps i j]
    (some ⟨some (labels (.left .scan)), clean ambient, base⟩) =
    some ⟨some (labels .branchLeft), ((ambient, decide (i < j)), none), base⟩ at hl
  have hr := MachineUnaryLessAt.lessThanTrace (rightMap.trans slots)
    (fun l => labels (.right l)) (some (labels .branchRight)) program (fun _ => atLabels _)
    base j i [] [] (by simpa [rightMap] using rightWord) (by simpa [rightMap] using leftWord)
    leftEmpty rightEmpty ambient false none
  change (advance (TM2.step program))^[MachineUnaryLessAt.steps j i]
    (some ⟨some (labels (.right .scan)), clean ambient, base⟩) =
    some ⟨some (labels .branchRight), ((ambient, decide (j < i)), none), base⟩ at hr
  have hbl : (advance (TM2.step program))^[1]
      (some ⟨some (labels .branchLeft), ((ambient, decide (i < j)), none), base⟩) =
      some ⟨some (if i < j then labels (.inputLeft .tag) else labels (.right .scan)),
        clean ambient, base⟩ := by
    change some (TM2.stepAux (program (labels .branchLeft)) _ _) = _
    rw [atLabels, statement, stepAux_choose]
    simp
  have hbr : (advance (TM2.step program))^[1]
      (some ⟨some (labels .branchRight), ((ambient, decide (j < i)), none), base⟩) =
      some ⟨some (if j < i then labels (.inputLeft .tag) else labels .diagonal),
        clean ambient, base⟩ := by
    change some (TM2.stepAux (program (labels .branchRight)) _ _) = _
    rw [atLabels, statement, stepAux_choose]
    simp
  have hoff := offTrace slots labels exit program atLabels base i j leftWord rightWord leftEmpty ambient
  by_cases hij : i < j
  · rw [ite_eq_left hij] at hbl
    have h := chain (chain hl hbl) hoff
    simpa only [steps, ite_eq_left hij, clashPairTokens, ite_eq_right (Nat.ne_of_lt hij)] using h
  · rw [ite_eq_right hij] at hbl
    by_cases hji : j < i
    · rw [ite_eq_left hji] at hbr
      have h := chain (chain (chain (chain hl hbl) hr) hbr) hoff
      simpa only [steps, ite_eq_right hij, ite_eq_left hji, clashPairTokens,
        ite_eq_right (Ne.symm (Nat.ne_of_lt hji)), Nat.add_assoc] using h
    · rw [ite_eq_right hji] at hbr
      have hd : (advance (TM2.step program))^[1]
          (some ⟨some (labels .diagonal), clean ambient, base⟩) =
          some ⟨exit, clean ambient, emitted (slots 4) (slots 5) base [.const false]⟩ := by
        change some (TM2.stepAux (program (labels .diagonal)) _ _) = _
        rw [atLabels, statement, stepAux_literal _ _ (slots.injective.ne (by decide))]
        cases exit <;> rfl
      have heq : i = j := by omega
      have h := chain (chain (chain (chain hl hbl) hr) hbr) hd
      simpa only [steps, ite_eq_right hij, ite_eq_right hji, clashPairTokens,
        ite_eq_left heq, Nat.add_assoc] using h

end Pair

namespace Row

def statement (slots : Fin 7 ↪ K) (labels : Label → Λ) (done : Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .guard => MachineUnaryCounter.guard (slots 0) (labels (.pair (.left .scan))) done
  | .pair l => Pair.statement (pairMap.trans slots) (fun l => labels (.pair l))
      (some (labels .increment)) l
  | .increment => .push (slots 2) (fun _ => true) (.goto fun _ => labels .guard)

theorem tokens_succ (count i start : Nat) :
    tokens (count + 1) i start = clashPairTokens i start ++ tokens count i (start + 1) := by
  rw [tokens, forTokens_succ_first]
  simp only [Nat.add_zero]
  apply congrArg (List.append (clashPairTokens i start))
  apply forTokens_congr
  intro j _
  rw [show start + (j + 1) = start + 1 + j by omega]

theorem trace (slots : Fin 7 ↪ K) (labels : Label → Λ) (done : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels done l)
    (base : K → List Bool) (count i start : Nat)
    (leftWord : base (slots 1) = encodeWord i)
    (leftEmpty : base (slots 3) = []) (rightEmpty : base (slots 4) = []) (ambient : σ) :
    (advance (TM2.step program))^[steps count i start]
      (some ⟨some (labels .guard), clean ambient, frame slots base count start⟩) =
      some ⟨some done, clean ambient,
        frame slots (emitted (slots 5) (slots 6) base (tokens count i start)) 0 (start + count)⟩ := by
  induction count generalizing base start with
  | zero =>
    have h := MachineUnaryCounter.guardTrace_zero (slots 0) (labels .guard)
      (labels (.pair (.left .scan))) done program (atLabels .guard)
      (frame slots base 0 start) [] (ambient, false) none
    simpa only [counter_frame, steps, tokens_zero, emitted_nil, Nat.add_zero, clean] using h
  | succ count ih =>
    have hg := MachineUnaryCounter.guardTrace_succ (slots 0) (labels .guard)
      (labels (.pair (.left .scan))) done program (atLabels .guard)
      (frame slots base count start) count [] (ambient, false) none
    simp only [counter_frame] at hg
    have hiWord : frame slots base count start (slots 1) = encodeWord i := by
      simpa [frame, slots.injective.eq_iff] using leftWord
    have hsLeft : frame slots base count start (slots 3) = [] := by
      simpa [frame, slots.injective.eq_iff] using leftEmpty
    have hsRight : frame slots base count start (slots 4) = [] := by
      simpa [frame, slots.injective.eq_iff] using rightEmpty
    have hp := Pair.trace (pairMap.trans slots) (fun l => labels (.pair l))
      (some (labels .increment)) program (fun _ => atLabels _)
      (frame slots base count start) i start hiWord (frame_current slots base count start)
      hsLeft hsRight ambient
    change (advance (TM2.step program))^[Pair.steps i start]
      (some ⟨some (labels (.pair (.left .scan))), clean ambient, frame slots base count start⟩) =
      some ⟨some (labels .increment), clean ambient,
        emitted (slots 5) (slots 6) (frame slots base count start) (clashPairTokens i start)⟩ at hp
    rw [emitted_frame] at hp
    let nextBase := emitted (slots 5) (slots 6) base (clashPairTokens i start)
    have hn : (advance (TM2.step program))^[1]
        (some ⟨some (labels .increment), clean ambient, frame slots nextBase count start⟩) =
        some ⟨some (labels .guard), clean ambient, frame slots nextBase count (start + 1)⟩ := by
      change some (TM2.stepAux (program (labels .increment)) _ _) = _
      rw [atLabels, statement]
      simp only [TM2.stepAux, frame_current, increment_frame]
    have hni : nextBase (slots 1) = encodeWord i := by
      simpa [nextBase, emitted, slots.injective.eq_iff] using leftWord
    have hnl : nextBase (slots 3) = [] := by
      simpa [nextBase, emitted, slots.injective.eq_iff] using leftEmpty
    have hnr : nextBase (slots 4) = [] := by
      simpa [nextBase, emitted, slots.injective.eq_iff] using rightEmpty
    have hr := ih nextBase (start + 1) hni hnl hnr
    have h := chain (chain (chain hg hp) hn) hr
    rw [show start + 1 + count = start + (count + 1) by omega] at h
    simp only [nextBase,
      emitted_append (slots 5) (slots 6) (slots.injective.ne (by decide : (5 : Fin 7) ≠ 6)),
      ← tokens_succ] at h
    exact h

end Row

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PaddingCellsMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl

open Turing PostfixModel VerifierCircuit InitializationTemplate
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqΛTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqσTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqΓTmBoolComputation
def statement (V : NPVerifier) (p : Ports K) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ σ := literalStatement p (tokens V) exit

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_InitializationMachineAt
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt

open Turing PostfixModel
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
open InitializationMachine (Label termTokens bodySteps selectorSteps)

variable {K Λ σ : Type} [DecidableEq K]

theorem indexTrace (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[3 * (i + 1) + 2]
      (some ⟨some (label .scan), initialState ambient, tapes p base m i d output count⟩) =
      some ⟨some (label .test), initialState ambient,
        tapes p base m i d ((encodeWord i).reverse ++ output) count⟩ := by
  have h := MachineTransducerCopy.transduceCopyTrace (p 1) (p 3) (p 4)
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))
    false (fun _ _ => false) (fun _ symbol => [symbol])
    (label .scan) (label .restore) (fun _ b => label (.emit b)) (some (label .test)) program
    (ha .scan (by decide))
    (by intro control symbol; exact ha (.emit symbol) (by intro h; cases h))
    (ha .restore (by decide)) (tapes p base m i d output count)
    (by simp [contents]) ambient false none
  simpa [contents, identity_output, update_reversed, initialState] using h

theorem bodyTrace (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[bodySteps i]
      (some ⟨some (label .inputTag), initialState ambient, tapes p base m i d output count⟩) =
      some ⟨some (label .guard), initialState ambient, tapes p base m (i + 1) (d - 1)
        ((tokenBits (termTokens i d)).reverse ++ output) (true :: true :: true :: count)⟩ := by
  have tag : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some (label .inputTag), initialState ambient, tapes p base m i d output count⟩) =
      some ⟨some (label .scan), initialState ambient,
        tapes p base m i d ((encodeWord 5).reverse ++ output) count⟩ := by
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      inputTagStep p label program ha base m i d output count ambient
  have index := indexTrace p label program ha base m i d
    ((encodeWord 5).reverse ++ output) count ambient
  let out := (encodeWord i).reverse ++ ((encodeWord 5).reverse ++ output)
  have test : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some (label .test), initialState ambient, tapes p base m i d out count⟩) =
      some ⟨some (label (.result (decide (d = 0)))), initialState ambient,
        tapes p base m i (d - 1) out count⟩ := by
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      thresholdStep p label program ha base m i d out count ambient
  have result : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some (label (.result (decide (d = 0)))), initialState ambient,
        tapes p base m i (d - 1) out count⟩) =
      some ⟨some (label .guard), initialState ambient, tapes p base m (i + 1) (d - 1)
        ((encodeWords [if decide (d = 0) then 1 else 0, 3]).reverse ++ out)
        (true :: true :: true :: count)⟩ := by
    simpa only [Function.iterate_one, MachineComposition.advance_some] using
      resultStep p label program ha base m i (d - 1) out count ambient (decide (d = 0))
  have whole := chain (chain (chain tag index) test) result
  have ht : 1 + (3 * (i + 1) + 2) + 1 + 1 = bodySteps i := by
    unfold InitializationMachine.bodySteps
    omega
  rw [ht] at whole
  simpa only [InitializationMachine.termTokens_bits, List.reverse_append,
    List.append_assoc, out] using whole

theorem selectorTrace (p : Ports K) (label : Label ↪ Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (base : K → List Bool) (m i d : Nat) (output count : List Bool) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[selectorSteps i m]
      (some ⟨some (label .guard), initialState ambient, tapes p base m i d output count⟩) =
      some ⟨some (label .done), initialState ambient, tapes p base 0 (i + m) (d - m)
        ((tokenBits (InitializationTemplate.selectorLoopTokens m i d)).reverse ++ output)
        (List.replicate (3 * m) true ++ count)⟩ := by
  induction m generalizing i d output count with
  | zero =>
    simpa only [InitializationMachine.selectorSteps, InitializationTemplate.selectorLoopTokens,
      InitializationTemplate.forTokens, tokenBits, tokenWords, List.flatMap_nil,
      encodeWords, List.reverse_nil, List.nil_append, Nat.add_zero, Nat.sub_zero,
      Nat.mul_zero, List.replicate_zero, Function.iterate_one, MachineComposition.advance_some] using
      guardStep_zero p label program ha base i d output count ambient
  | succ m ih =>
    have guard : (MachineComposition.advance (TM2.step program))^[1]
        (some ⟨some (label .guard), initialState ambient, tapes p base (m + 1) i d output count⟩) =
        some ⟨some (label .inputTag), initialState ambient, tapes p base m i d output count⟩ := by
      simpa only [Function.iterate_one, MachineComposition.advance_some] using
        guardStep_succ p label program ha base m i d output count ambient
    have body := bodyTrace p label program ha base m i d output count ambient
    have rest := ih (i + 1) (d - 1) ((tokenBits (termTokens i d)).reverse ++ output)
      (true :: true :: true :: count)
    have whole := chain (chain guard body) rest
    rw [prepend_three] at whole
    have hs : InitializationTemplate.selectorLoopTokens (m + 1) i d =
        termTokens i d ++ InitializationTemplate.selectorLoopTokens m (i + 1) (d - 1) :=
      InitializationTemplate.selectorLoopTokens_succ m i d
    rw [hs, InitializationMachine.tokens_append_bits, List.reverse_append, List.append_assoc]
    simpa only [InitializationMachine.selectorSteps, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.sub_sub, Nat.mul_succ] using whole

theorem presenceTrace (p : Ports K) (label : Label ↪ Λ)
    (closing : K) (hc : ∀ j, closing ≠ p j) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) (ha : Agrees p label program)
    (atSeed : program (label .done) = OrClosure.seed (closurePorts p closing hc) again)
    (atLoop : program again = OrClosure.loop (closurePorts p closing hc) again exit)
    (base : K → List Bool) (q n : Nat) (suffix output count : List Bool)
    (hclosing : base closing = encodeWord (q + 1) ++ suffix) (ambient : σ) :
    let selected := tapes p base 0 (q + 1) (n + 1 - (q + 1))
      ((tokenBits (InitializationTemplate.selectorLoopTokens (q + 1) 0 (n + 1))).reverse ++ output)
      (List.replicate (3 * (q + 1)) true ++ count)
    (MachineComposition.advance (TM2.step program))^[selectorSteps 0 (q + 1) + (q + 1 + 2)]
      (some ⟨some (label .guard), initialState ambient, tapes p base (q + 1) 0 (n + 1) output count⟩) =
      some ⟨exit, initialState ambient,
        OrClosure.frame (closurePorts p closing hc) selected (encodeWord 0 ++ suffix)
          ((tokenBits (InitializationTemplate.presenceTokens q n)).reverse ++ output)
          (List.replicate (4 * (q + 1) + 1) true ++ count)⟩ := by
  dsimp only
  let out := (tokenBits (InitializationTemplate.selectorLoopTokens (q + 1) 0 (n + 1))).reverse ++ output
  let cnt := List.replicate (3 * (q + 1)) true ++ count
  let selected := tapes p base 0 (q + 1) (n + 1 - (q + 1)) out cnt
  have hs := selectorTrace p label program ha base (q + 1) 0 (n + 1) output count ambient
  simp only [Nat.zero_add] at hs
  have hr : selected closing = encodeWord (q + 1) ++ suffix :=
    (tapes_other p base _ _ _ out cnt closing hc).trans hclosing
  have ho : selected (p 4) = out := by simp [selected, contents]
  have hn : selected (p 5) = cnt := by simp [selected, contents]
  have hf : OrClosure.frame (closurePorts p closing hc) selected
      (encodeWord (q + 1) ++ suffix) out cnt = selected := by
    simpa only [closurePorts, hr, ho, hn] using
      OrClosure.frame_self (closurePorts p closing hc) selected
  have hclose := OrClosure.closureTrace (closurePorts p closing hc) (label .done) again exit
    program atSeed atLoop selected (q + 1) suffix out cnt (ambient, false) none
  rw [hf] at hclose
  have whole := chain hs hclose
  have hout : (tokenBits (InitializationTemplate.closeOr (q + 1))).reverse ++ out =
      (tokenBits (InitializationTemplate.presenceTokens q n)).reverse ++ output := by
    rw [← InitializationTemplate.selectorLoopTokens_presence q n,
      InitializationMachine.tokens_append_bits, List.reverse_append, List.append_assoc]
  have hcnt : List.replicate (q + 1 + 1) true ++ cnt =
      List.replicate (4 * (q + 1) + 1) true ++ count := by
    dsimp only [cnt]
    rw [← List.append_assoc, List.replicate_append_replicate]
    congr 2
    omega
  rw [hout, hcnt] at whole
  exact whole

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityComposition
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

namespace Full

def statement (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => .push (slots 3) (fun _ => false) (.goto fun _ => labels (.copy .outer .seed))
  | .copy c .seed => MachineUnaryAffineAt.seed (copyTarget slots c) 1 (labels (.copy c .scan))
  | .copy c .scan => MachineUnaryAffineAt.scan (slots 0) (slots 5) (copyTarget slots c) 1
      (labels (.copy c .scan)) (labels (.copy c .restore))
  | .copy c .restore => Reduction.MachineTransfer.loopAt (slots 5) (slots 0) id false
      (labels (.copy c .restore)) (some (copyExit labels c))
  | .outerGuard => MachineUnaryCounter.guard (slots 1) (labels .rowSeed) (labels (.copy .allClose .seed))
  | .rowSeed => .push (slots 4) (fun _ => false) (.goto fun _ => labels (.copy .inner .seed))
  | .row l => Row.statement (rowMap.trans slots) (fun l => labels (.row l)) (labels .discardInner) l
  | .discardInner => MachineLookup.discard (slots 4) (labels .discardInner) (labels .afterInner)
  | .afterInner => .pop (slots 2) (fun s _ => s) (.goto fun _ => labels (.copy .rowClose .seed))
  | .rowCloseSeed => OrClosure.seed (closurePorts slots) (labels .rowCloseLoop)
  | .rowCloseLoop => OrClosure.loop (closurePorts slots) (labels .rowCloseLoop) (some (labels .rowFinish))
  | .rowFinish => .pop (slots 9) (fun s _ => s)
      (.push (slots 3) (fun _ => true) (.goto fun _ => labels .outerGuard))
  | .allCloseSeed => OrClosure.seed (closurePorts slots) (labels .allCloseLoop)
  | .allCloseLoop => OrClosure.loop (closurePorts slots) (labels .allCloseLoop) (some (labels .discardOuter))
  | .discardOuter => MachineLookup.discard (slots 3) (labels .discardOuter) (labels .finish)
  | .finish => .pop (slots 1) (fun s _ => s) (.pop (slots 9) (fun s _ => s)
      (Reduction.MachineTransfer.exitAt (slots 7) exit))

theorem copyTrace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (context : CopyContext) (base : K → List Bool) (q : Nat)
    (sourceWord : base (slots 0) = encodeWord q) (scratchEmpty : base (slots 5) = [])
    (targetEmpty : base (copyTarget slots context) = []) (ambient : σ) :
    (advance (TM2.step program))^[copySteps q]
      (some ⟨some (labels (.copy context .seed)), clean ambient, base⟩) =
      some ⟨some (copyExit labels context), clean ambient,
        Function.update base (copyTarget slots context) (encodeWord (q + 1))⟩ := by
  have hd : slots 0 ≠ copyTarget slots context := by
    cases context <;> simp [copyTarget, slots.injective.eq_iff]
  have hs : slots 5 ≠ copyTarget slots context := by
    cases context <;> simp [copyTarget, slots.injective.eq_iff]
  have h := MachineUnaryAffineAt.seededAffineTrace (slots 0) (slots 5) (copyTarget slots context)
    (slots.injective.ne (by decide)) hd hs 1 1 (labels (.copy context .seed))
    (labels (.copy context .scan)) (labels (.copy context .restore))
    (some (copyExit labels context)) program (atLabels _) (atLabels _) (atLabels _)
    base q [] (by simpa using sourceWord) scratchEmpty (ambient, false) none
  simpa only [copySteps, clean, one_mul, targetEmpty, List.append_nil] using h

theorem bodyTrace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q r i : Nat) (ready : Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[bodySteps q i]
      (some ⟨some (labels .rowSeed), clean ambient, frame slots base r i⟩) =
      some ⟨some (labels .outerGuard), clean ambient,
        frame slots (emitted (slots 7) (slots 8) base (clashRowTokens q i)) r (i + 1)⟩ := by
  let initial := frame slots base r i
  let seeded := Function.update initial (slots 4) (encodeWord 0)
  have hseed : (advance (TM2.step program))^[1]
      (some ⟨some (labels .rowSeed), clean ambient, initial⟩) =
      some ⟨some (labels (.copy .inner .seed)), clean ambient, seeded⟩ := by
    change some (TM2.stepAux (program (labels .rowSeed)) _ _) = _
    rw [atLabels, statement]
    simp [TM2.stepAux, seeded, initial, frame, slots.injective.eq_iff,
      ready.empty 4 (by decide) (by decide) (by decide), encodeWord]
  have hq : seeded (slots 0) = encodeWord q := by
    simpa [seeded, initial, frame, slots.injective.eq_iff] using ready.source
  have hs : seeded (slots 5) = [] := by
    simpa [seeded, initial, frame, slots.injective.eq_iff] using
      ready.empty 5 (by decide) (by decide) (by decide)
  have ht : seeded (copyTarget slots .inner) = [] := by
    simpa [copyTarget, seeded, initial, frame, slots.injective.eq_iff] using
      ready.empty 2 (by decide) (by decide) (by decide)
  have hcopy := copyTrace slots labels exit program atLabels .inner seeded q hq hs ht ambient
  have hstart : Function.update seeded (copyTarget slots .inner) (encodeWord (q + 1)) =
      Row.frame (rowMap.trans slots) initial (q + 1) 0 := by
    change Function.update (Function.update initial (slots 4) (encodeWord 0))
      (slots 2) (encodeWord (q + 1)) =
      Function.update (Function.update initial (slots 2) (encodeWord (q + 1)))
        (slots 4) (encodeWord 0)
    exact Function.update_comm (slots.injective.ne (by decide : (4 : Fin 10) ≠ 2)) _ _ _
  rw [hstart] at hcopy
  have hi : initial (slots 3) = encodeWord i := by simp [initial, frame]
  have hsl : initial (slots 5) = [] := by
    simpa [initial, frame, slots.injective.eq_iff] using
      ready.empty 5 (by decide) (by decide) (by decide)
  have hsr : initial (slots 6) = [] := by
    simpa [initial, frame, slots.injective.eq_iff] using
      ready.empty 6 (by decide) (by decide) (by decide)
  have hrow := Row.trace (rowMap.trans slots) (fun l => labels (.row l))
    (labels .discardInner) program (fun _ => atLabels _) initial (q + 1) i 0 hi hsl hsr ambient
  simp only [Nat.zero_add] at hrow
  let innerTokens := Row.tokens (q + 1) i 0
  let innerBase := emitted (slots 7) (slots 8) base innerTokens
  have innerReady : Ready slots innerBase q := ready.emitted innerTokens
  let afterRow := Row.frame (rowMap.trans slots) (frame slots innerBase r i) 0 (q + 1)
  change (advance (TM2.step program))^[Row.steps (q + 1) i 0]
    (some ⟨some (labels (.row .guard)), clean ambient, Row.frame (rowMap.trans slots) initial (q + 1) 0⟩) =
    some ⟨some (labels .discardInner), clean ambient,
      Row.frame (rowMap.trans slots) (emitted (slots 7) (slots 8) initial innerTokens) 0 (q + 1)⟩ at hrow
  have hemit : emitted (slots 7) (slots 8) initial innerTokens = frame slots innerBase r i :=
    emitted_frame slots base r i innerTokens
  rw [hemit] at hrow
  have hj : afterRow (slots 4) = encodeWord (q + 1) := by simp [afterRow, Row.frame, rowMap]
  have hdiscard := MachineLookup.discardTrace (slots 4) (labels .discardInner) (labels .afterInner)
    program (atLabels .discardInner) afterRow (q + 1) [] (by simpa using hj) (ambient, false) none
  have hclean : (advance (TM2.step program))^[1]
      (some ⟨some (labels .afterInner), clean ambient, Function.update afterRow (slots 4) []⟩) =
      some ⟨some (labels (.copy .rowClose .seed)), clean ambient, frame slots innerBase r i⟩ := by
    change some (TM2.stepAux (program (labels .afterInner)) _ _) = _
    rw [atLabels, statement]
    simp only [TM2.stepAux]
    congr 2
    apply ext_slots slots
    · intro k
      fin_cases k <;> simp [afterRow, Row.frame, rowMap, frame, slots.injective.eq_iff,
        encodeWord, innerReady.empty 2 (by decide) (by decide) (by decide),
        innerReady.empty 4 (by decide) (by decide) (by decide)]
    · intro k hk
      simp [afterRow, Row.frame, rowMap, frame, hk]
  have hcq : frame slots innerBase r i (slots 0) = encodeWord q := by
    simpa [frame, slots.injective.eq_iff] using innerReady.source
  have hcs : frame slots innerBase r i (slots 5) = [] := by
    simpa [frame, slots.injective.eq_iff] using innerReady.empty 5 (by decide) (by decide) (by decide)
  have hct : frame slots innerBase r i (copyTarget slots .rowClose) = [] := by
    simpa [frame, copyTarget, slots.injective.eq_iff] using
      innerReady.empty 9 (by decide) (by decide) (by decide)
  have hcCopy := copyTrace slots labels exit program atLabels .rowClose
    (frame slots innerBase r i) q hcq hcs hct ambient
  let closeStart := Function.update (frame slots innerBase r i) (slots 9) (encodeWord (q + 1))
  have hclose := closureTrace slots (labels .rowCloseSeed) (labels .rowCloseLoop)
    (some (labels .rowFinish)) program (atLabels .rowCloseSeed) (atLabels .rowCloseLoop)
    closeStart (q + 1) (by simp [closeStart]) ambient
  let closeEnd := Function.update (emitted (slots 7) (slots 8) closeStart (closeOr (q + 1)))
    (slots 9) (encodeWord 0)
  let closeBase := emitted (slots 7) (slots 8) innerBase (closeOr (q + 1))
  have hfinish : (advance (TM2.step program))^[1]
      (some ⟨some (labels .rowFinish), clean ambient, closeEnd⟩) =
      some ⟨some (labels .outerGuard), clean ambient, frame slots closeBase r (i + 1)⟩ := by
    change some (TM2.stepAux (program (labels .rowFinish)) _ _) = _
    rw [atLabels, statement]
    simp only [TM2.stepAux]
    congr 2
    apply ext_slots slots
    · intro k
      fin_cases k <;> simp [closeEnd, closeStart, closeBase, emitted, frame, slots.injective.eq_iff,
        encodeWord, List.replicate_succ, innerReady.empty 9 (by decide) (by decide) (by decide)]
    · intro k hk
      simp [closeEnd, closeStart, closeBase, emitted, frame, hk]
  have h := chain (chain (chain (chain (chain (chain (chain hseed hcopy) hrow) hdiscard) hclean)
    hcCopy) hclose) hfinish
  have hout : closeBase = emitted (slots 7) (slots 8) base (clashRowTokens q i) := by
    rw [show closeBase = emitted (slots 7) (slots 8)
      (emitted (slots 7) (slots 8) base innerTokens) (closeOr (q + 1)) from rfl,
      emitted_append (slots 7) (slots 8) (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8))]
    simp [clashRowTokens, innerTokens, Row.tokens]
  rw [hout] at h
  exact h

theorem loopTokens_succ (count q start : Nat) :
    loopTokens (count + 1) q start = clashRowTokens q start ++ loopTokens count q (start + 1) := by
  rw [loopTokens, forTokens_succ_first]
  simp only [Nat.add_zero]
  apply congrArg (List.append (clashRowTokens q start))
  apply forTokens_congr
  intro j _
  rw [show start + (j + 1) = start + 1 + j by omega]

theorem loopTrace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q count start : Nat) (ready : Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[loopSteps count q start]
      (some ⟨some (labels .outerGuard), clean ambient, frame slots base count start⟩) =
      some ⟨some (labels (.copy .allClose .seed)), clean ambient,
        frame slots (emitted (slots 7) (slots 8) base (loopTokens count q start)) 0 (start + count)⟩ := by
  induction count generalizing base start with
  | zero =>
    have h := MachineUnaryCounter.guardTrace_zero (slots 1) (labels .outerGuard)
      (labels .rowSeed) (labels (.copy .allClose .seed)) program (atLabels .outerGuard)
      (frame slots base 0 start) [] (ambient, false) none
    simpa only [counter_frame, loopSteps, loopTokens, forTokens, emitted_nil, Nat.add_zero, clean] using h
  | succ count ih =>
    have hg := MachineUnaryCounter.guardTrace_succ (slots 1) (labels .outerGuard)
      (labels .rowSeed) (labels (.copy .allClose .seed)) program (atLabels .outerGuard)
      (frame slots base count start) count [] (ambient, false) none
    simp only [counter_frame] at hg
    have hb := bodyTrace slots labels exit program atLabels base q count start ready ambient
    let nextBase := emitted (slots 7) (slots 8) base (clashRowTokens q start)
    have hr := ih nextBase (start + 1) (ready.emitted (clashRowTokens q start))
    have h := chain (chain hg hb) hr
    rw [show start + 1 + count = start + (count + 1) by omega] at h
    simp only [nextBase,
      emitted_append (slots 7) (slots 8) (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8)),
      ← loopTokens_succ] at h
    exact h

theorem trace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[steps q]
      (some ⟨some (labels .start), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (clashTokens q)⟩ := by
  let seeded := Function.update base (slots 3) (encodeWord 0)
  have hstart : (advance (TM2.step program))^[1]
      (some ⟨some (labels .start), clean ambient, base⟩) =
      some ⟨some (labels (.copy .outer .seed)), clean ambient, seeded⟩ := by
    change some (TM2.stepAux (program (labels .start)) _ _) = _
    rw [atLabels, statement]
    simp [TM2.stepAux, seeded, ready.empty 3 (by decide) (by decide) (by decide), encodeWord]
  have hs : seeded (slots 0) = encodeWord q := by
    simpa [seeded, slots.injective.eq_iff] using ready.source
  have hw : seeded (slots 5) = [] := by
    simpa [seeded, slots.injective.eq_iff] using ready.empty 5 (by decide) (by decide) (by decide)
  have hd : seeded (copyTarget slots .outer) = [] := by
    simpa [seeded, copyTarget, slots.injective.eq_iff] using
      ready.empty 1 (by decide) (by decide) (by decide)
  have hcopy := copyTrace slots labels exit program atLabels .outer seeded q hs hw hd ambient
  have hframe : Function.update seeded (copyTarget slots .outer) (encodeWord (q + 1)) =
      frame slots base (q + 1) 0 := by
    apply ext_slots slots
    · intro k
      fin_cases k <;> simp [seeded, copyTarget, frame, slots.injective.eq_iff]
    · intro k hk
      simp [seeded, copyTarget, frame, hk]
  rw [hframe] at hcopy
  have hloop := loopTrace slots labels exit program atLabels base q (q + 1) 0 ready ambient
  simp only [Nat.zero_add] at hloop
  let loopBase := emitted (slots 7) (slots 8) base (loopTokens (q + 1) q 0)
  have loopReady : Ready slots loopBase q := ready.emitted _
  let afterLoop := frame slots loopBase 0 (q + 1)
  have hcq : afterLoop (slots 0) = encodeWord q := by
    simpa [afterLoop, frame, slots.injective.eq_iff] using loopReady.source
  have hcw : afterLoop (slots 5) = [] := by
    simpa [afterLoop, frame, slots.injective.eq_iff] using loopReady.empty 5 (by decide) (by decide) (by decide)
  have hcd : afterLoop (copyTarget slots .allClose) = [] := by
    simpa [afterLoop, frame, copyTarget, slots.injective.eq_iff] using
      loopReady.empty 9 (by decide) (by decide) (by decide)
  have hcopyEnd := copyTrace slots labels exit program atLabels .allClose afterLoop q hcq hcw hcd ambient
  let closeStart := Function.update afterLoop (slots 9) (encodeWord (q + 1))
  have hclose := closureTrace slots (labels .allCloseSeed) (labels .allCloseLoop)
    (some (labels .discardOuter)) program (atLabels .allCloseSeed) (atLabels .allCloseLoop)
    closeStart (q + 1) (by simp [closeStart]) ambient
  let closeEnd := Function.update (emitted (slots 7) (slots 8) closeStart (closeOr (q + 1)))
    (slots 9) (encodeWord 0)
  have hi : closeEnd (slots 3) = encodeWord (q + 1) := by
    simp [closeEnd, closeStart, afterLoop, frame, emitted, slots.injective.eq_iff]
  have hdiscard := MachineLookup.discardTrace (slots 3) (labels .discardOuter) (labels .finish)
    program (atLabels .discardOuter) closeEnd (q + 1) [] (by simpa using hi) (ambient, false) none
  let finalBase := emitted (slots 7) (slots 8) loopBase (closeOr (q + 1))
  have hfinish : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean ambient, Function.update closeEnd (slots 3) []⟩) =
      some ⟨exit, clean ambient, finalBase⟩ := by
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels, statement]
    have ht : Function.update (Function.update (Function.update closeEnd (slots 3) [])
        (slots 1) []) (slots 9) [] = finalBase := by
      apply ext_slots slots
      · intro k
        fin_cases k <;> simp [closeEnd, closeStart, afterLoop, finalBase, frame, emitted,
          slots.injective.eq_iff, loopReady.empty 1 (by decide) (by decide) (by decide),
          loopReady.empty 3 (by decide) (by decide) (by decide),
          loopReady.empty 9 (by decide) (by decide) (by decide)]
      · intro k hk
        simp [closeEnd, closeStart, afterLoop, finalBase, frame, emitted, hk]
    have hr : (Function.update closeEnd (slots 3) []) (slots 1) = encodeWord 0 := by
      simp [closeEnd, closeStart, afterLoop, frame, emitted, slots.injective.eq_iff]
    have hc : (Function.update (Function.update closeEnd (slots 3) []) (slots 1) []) (slots 9) =
        encodeWord 0 := by simp [closeEnd, slots.injective.eq_iff]
    simp only [TM2.stepAux, hr, hc, encodeWord, List.replicate_zero,
      List.nil_append, List.tail_cons, ht]
    cases exit <;> rfl
  have h := chain (chain (chain (chain (chain (chain hstart hcopy) hloop) hcopyEnd) hclose) hdiscard) hfinish
  have hout : finalBase = emitted (slots 7) (slots 8) base (clashTokens q) := by
    rw [show finalBase = emitted (slots 7) (slots 8)
      (emitted (slots 7) (slots 8) base (loopTokens (q + 1) q 0)) (closeOr (q + 1)) from rfl,
      emitted_append (slots 7) (slots 8) (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8))]
    simp [clashTokens, loopTokens]
  rw [hout] at h
  exact h

end Full

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PayloadPresenceMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadPresenceMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted)

variable {K Λ σ : Type} [DecidableEq K]

theorem copyTrace (slots : Ports K) (labels : Label ↪ Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (context : CopyContext) (base : K → List Bool) (n : Nat)
    (sourceWord : base (copySource slots context) = encodeWord n)
    (scratchEmpty : base (slots 5) = []) (targetEmpty : base (copyTarget slots context) = [])
    (ambient : σ) :
    (advance (TM2.step program))^[2 * (n + 1) + 1]
      (some ⟨some (labels (.copy context .seed)), clean ambient, base⟩) =
      some ⟨some (copyExit labels context), clean ambient,
        Function.update base (copyTarget slots context) (encodeWord (n + 1))⟩ := by
  have hs : copySource slots context ≠ slots 5 := by
    cases context <;> exact slots.injective.ne (by decide)
  have hd : copySource slots context ≠ copyTarget slots context := by
    cases context <;> exact slots.injective.ne (by decide)
  have hsd : slots 5 ≠ copyTarget slots context := by
    cases context <;> exact slots.injective.ne (by decide)
  have h := MachineUnaryAffineAt.seededAffineTrace (copySource slots context) (slots 5)
    (copyTarget slots context) hs hd hsd 1 1
    (labels (.copy context .seed)) (labels (.copy context .scan)) (labels (.copy context .restore))
    (some (copyExit labels context)) program
    (atLabels (.copy context .seed)) (atLabels (.copy context .scan)) (atLabels (.copy context .restore))
    base n [] (by simpa using sourceWord) scratchEmpty (ambient, false) none
  simpa only [Nat.one_mul, targetEmpty, List.append_nil, clean] using h

theorem trace (slots : Ports K) (labels : Label ↪ Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q i : Nat) (hi : i < q)
    (ready : Ready slots base q i) (ambient : σ) :
    (advance (TM2.step program))^[steps q i]
      (some ⟨some (labels .initialize_), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (presenceTokens q i)⟩ := by
  have e₂ := ready.empty 2 (by decide) (by decide) (by decide) (by decide)
  have e₃ := ready.empty 3 (by decide) (by decide) (by decide) (by decide)
  have e₄ := ready.empty 4 (by decide) (by decide) (by decide) (by decide)
  have e₅ := ready.empty 5 (by decide) (by decide) (by decide) (by decide)
  have e₆ := ready.empty 6 (by decide) (by decide) (by decide) (by decide)
  let b₀ := Function.update base (slots 3) (encodeWord 0)
  let b₁ := Function.update b₀ (slots 2) (encodeWord (q + 1))
  let b₂ := Function.update b₁ (slots 4) (encodeWord (i + 1))
  let b₃ := Function.update b₂ (slots 6) (encodeWord (q + 1))
  have hinit : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize_), clean ambient, base⟩) =
      some ⟨some (labels (.copy .remaining .seed)), clean ambient, b₀⟩ := by
    change some (TM2.stepAux (program (labels .initialize_)) _ _) = _
    rw [atLabels, statement]
    simp [TM2.stepAux, e₃, b₀, encodeWord]
  have hr := copyTrace slots labels exit program atLabels .remaining b₀ q
    (by simpa [b₀, copySource, slots.injective.eq_iff] using ready.boundWord)
    (by simpa [b₀, slots.injective.eq_iff] using e₅)
    (by simpa [b₀, copyTarget, slots.injective.eq_iff] using e₂) ambient
  have ht := copyTrace slots labels exit program atLabels .threshold b₁ i
    (by simpa [b₁, b₀, copySource, slots.injective.eq_iff] using ready.indexWord)
    (by simpa [b₁, b₀, slots.injective.eq_iff] using e₅)
    (by simpa [b₁, b₀, copyTarget, slots.injective.eq_iff] using e₄) ambient
  have hc := copyTrace slots labels exit program atLabels .closing b₂ q
    (by simpa [b₂, b₁, b₀, copySource, slots.injective.eq_iff] using ready.boundWord)
    (by simpa [b₂, b₁, b₀, slots.injective.eq_iff] using e₅)
    (by simpa [b₂, b₁, b₀, copyTarget, slots.injective.eq_iff] using e₆) ambient
  let loopBase := Function.update base (slots 6) (encodeWord (q + 1))
  have hprepared : b₃ = InitializationMachineAt.tapes (presenceMap.trans slots)
      loopBase (q + 1) 0 (i + 1) (base (slots 7)) (base (slots 8)) := by
    apply ClashMachine.Full.ext_slots slots
    · intro j
      fin_cases j <;> simp [b₃, b₂, b₁, b₀, loopBase, InitializationMachineAt.tapes,
        InitializationMachineAt.frame, InitializationMachineAt.contents, presenceMap,
        slots.injective.eq_iff, e₅]
    · intro k hk
      simp [b₃, b₂, b₁, b₀, loopBase, InitializationMachineAt.tapes,
        InitializationMachineAt.frame, presenceMap, hk]
  have agrees : InitializationMachineAt.Agrees (presenceMap.trans slots)
      (presenceLabels.trans labels) program := by
    intro l hl
    change program (labels (.presence l)) =
      InitializationMachineAt.statement (presenceMap.trans slots) (presenceLabels.trans labels) l
    have h := atLabels (.presence l)
    cases l <;> try contradiction
    all_goals simpa only [statement] using h
  have hp := InitializationMachineAt.presenceTrace (presenceMap.trans slots) (presenceLabels.trans labels)
    (slots 6) (closing_distinct slots) (labels .orLoop) (some (labels .cleanup)) program agrees
    (atLabels (.presence .done)) (atLabels .orLoop) loopBase q i []
    (base (slots 7)) (base (slots 8)) (by simp [loopBase]) ambient
  dsimp only at hp
  let selected := InitializationMachineAt.tapes (presenceMap.trans slots) loopBase
    0 (q + 1) (i + 1 - (q + 1))
    ((tokenBits (selectorLoopTokens (q + 1) 0 (i + 1))).reverse ++ base (slots 7))
    (List.replicate (3 * (q + 1)) true ++ base (slots 8))
  let result := emitted (slots 7) (slots 8) base (presenceTokens q i)
  let produced := working slots result 0 (q + 1) 0 0
  have hsub : i + 1 - (q + 1) = 0 := by omega
  have hproduced : OrClosure.frame (closurePorts slots) selected (encodeWord 0 ++ [])
      ((tokenBits (presenceTokens q i)).reverse ++ base (slots 7))
      (List.replicate (4 * (q + 1) + 1) true ++ base (slots 8)) = produced := by
    apply ClashMachine.Full.ext_slots slots
    · intro j
      fin_cases j <;> simp [produced, working, result, emitted, OrClosure.frame,
        selected, closurePorts, InitializationMachineAt.closurePorts,
        InitializationMachineAt.tapes, InitializationMachineAt.frame,
        InitializationMachineAt.contents, presenceMap, loopBase, hsub,
        slots.injective.eq_iff, presenceTokens_length, e₅]
    · intro k hk
      simp [produced, working, result, emitted, OrClosure.frame,
        selected, closurePorts, InitializationMachineAt.closurePorts,
        InitializationMachineAt.tapes, InitializationMachineAt.frame, presenceMap, loopBase, hk]
  change (advance (TM2.step program))^[InitializationMachine.selectorSteps 0 (q + 1) + (q + 1 + 2)]
    (some ⟨some (labels (.presence .guard)), clean ambient,
      InitializationMachineAt.tapes (presenceMap.trans slots) loopBase
        (q + 1) 0 (i + 1) (base (slots 7)) (base (slots 8))⟩) =
    some ⟨some (labels .cleanup), clean ambient,
      OrClosure.frame (closurePorts slots) selected (encodeWord 0 ++ [])
        ((tokenBits (presenceTokens q i)).reverse ++ base (slots 7))
        (List.replicate (4 * (q + 1) + 1) true ++ base (slots 8))⟩ at hp
  rw [← hprepared, hproduced] at hp
  let cleared := Function.update (Function.update (Function.update produced (slots 2) [])
    (slots 4) []) (slots 6) []
  have hcleanup : (advance (TM2.step program))^[1]
      (some ⟨some (labels .cleanup), clean ambient, produced⟩) =
      some ⟨some (labels .drain), clean ambient, cleared⟩ := by
    change some (TM2.stepAux (program (labels .cleanup)) _ _) = _
    rw [atLabels, statement]
    simp [TM2.stepAux, produced, working, encodeWord, cleared, slots.injective.eq_iff]
  have hcurrent : cleared (slots 3) = encodeWord (q + 1) := by
    simp [cleared, produced, working, slots.injective.eq_iff]
  have hd := MachineDrain.drainTrace (slots 3) (labels .drain) exit program (atLabels .drain)
    cleared (encodeWord (q + 1)) (ambient, false) none
  rw [← hcurrent, Function.update_eq_self] at hd
  rw [hcurrent, encodeWord_length] at hd
  have hfinish : Function.update cleared (slots 3) [] = result := by
    apply ClashMachine.Full.ext_slots slots
    · intro j
      fin_cases j <;> simp [cleared, produced, working, result, emitted,
        slots.injective.eq_iff, e₂, e₃, e₄, e₆]
    · intro k hk
      simp [cleared, produced, working, hk]
  rw [hfinish] at hd
  exact chain (chain (chain (chain (chain (chain hinit hr) ht) hc) hp) hcleanup) hd

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadPresenceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CellsTokensAlignment
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted)
open PayloadPresenceMachine (Ports Ready)

variable {K Λ σ : Type} [DecidableEq K]

namespace Payload

theorem addressTrace (slots : Ports K) (labels : Label → Λ) (exit : Option Λ) (yes no : Bool)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit yes no l)
    (base : K → List Bool) (q i : Nat) (ready : Ready slots base q i) (ambient : σ) :
    (advance (TM2.step program))^[addressSteps q i]
      (some ⟨some (labels .seed), clean ambient, base⟩) =
      some ⟨some (labels (.inputTrue .tag)), clean ambient,
        Function.update base (slots 3) (encodeWord (q + 1 + i))⟩ := by
  have e₃ := ready.empty 3 (by decide) (by decide) (by decide) (by decide)
  have e₅ := ready.empty 5 (by decide) (by decide) (by decide) (by decide)
  have hq := MachineUnaryAffineAt.seededAffineTrace (slots 0) (slots 5) (slots 3)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
    (slots.injective.ne (by decide)) 1 1 (labels .seed) (labels .scanQ) (labels .restoreQ)
    (some (labels .scanI)) program (atLabels .seed) (atLabels .scanQ) (atLabels .restoreQ)
    base q [] (by simpa using ready.boundWord) e₅ (ambient, false) none
  simp only [Nat.one_mul, e₃, List.append_nil] at hq
  let addressed := Function.update base (slots 3) (encodeWord (q + 1))
  have hi := MachineUnaryAffineAt.affineTrace (slots 1) (slots 5) (slots 3)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
    (slots.injective.ne (by decide)) 1 (labels .scanI) (labels .restoreI)
    (some (labels (.inputTrue .tag))) program (atLabels .scanI) (atLabels .restoreI)
    addressed i (q + 1) [] [] (ambient, false) none
  have hframe (n : Nat) : MachineUnaryAffineAt.tapes (slots 1) (slots 5) (slots 3)
      addressed (encodeWord i ++ []) [] (encodeWord n ++ []) =
      Function.update base (slots 3) (encodeWord n) := by
    simp only [MachineUnaryAffineAt.tapes, MachineCopy.forkTapes, List.append_nil]
    apply ClashMachine.Full.ext_slots slots
    · intro j
      fin_cases j <;> simp [addressed, slots.injective.eq_iff, ready.indexWord, e₅]
    · intro k hk
      simp [addressed, hk]
  rw [hframe, hframe] at hi
  rw [show 1 * i + (q + 1) = q + 1 + i by omega] at hi
  exact chain hq hi

theorem trace (slots : Ports K) (labels : Label → Λ) (exit : Option Λ) (yes no : Bool)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit yes no l)
    (base : K → List Bool) (q i : Nat) (ready : Ready slots base q i) (ambient : σ) :
    (advance (TM2.step program))^[steps q i]
      (some ⟨some (labels .seed), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        emitted (slots 7) (slots 8) base (payloadTokens (q + 1 + i) yes no)⟩ := by
  have e₃ := ready.empty 3 (by decide) (by decide) (by decide) (by decide)
  have e₅ := ready.empty 5 (by decide) (by decide) (by decide) (by decide)
  let address := q + 1 + i
  let b₀ := Function.update base (slots 3) (encodeWord address)
  have ha := addressTrace slots labels exit yes no program atLabels base q i ready ambient
  have ht := ClashMachine.Input.trace (inputMap.trans slots) (fun l => labels (.inputTrue l))
    (some (labels .middle)) program (fun _ => atLabels _) b₀ address
    (by simp [b₀, inputMap]) (by simpa [b₀, inputMap, slots.injective.eq_iff] using e₅) ambient
  let b₁ := emitted (slots 7) (slots 8) b₀ [.input address]
  have hm : (advance (TM2.step program))^[1]
      (some ⟨some (labels .middle), clean ambient, b₁⟩) =
      some ⟨some (labels (.inputFalse .tag)), clean ambient,
        emitted (slots 7) (slots 8) b₁ [.const yes, .and]⟩ := by
    change some (TM2.stepAux (program (labels .middle)) _ _) = _
    rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
    rfl
  let b₂ := emitted (slots 7) (slots 8) b₁ [.const yes, .and]
  have hf := ClashMachine.Input.trace (inputMap.trans slots) (fun l => labels (.inputFalse l))
    (some (labels .suffix)) program (fun _ => atLabels _) b₂ address
    (by simp [b₂, b₁, b₀, inputMap, emitted, slots.injective.eq_iff])
    (by simpa [b₂, b₁, b₀, inputMap, emitted, slots.injective.eq_iff] using e₅) ambient
  let b₃ := emitted (slots 7) (slots 8) b₂ [.input address]
  have hs : (advance (TM2.step program))^[1]
      (some ⟨some (labels .suffix), clean ambient, b₃⟩) =
      some ⟨some (labels .drain), clean ambient,
        emitted (slots 7) (slots 8) b₃ [.not, .const no, .and, .or]⟩ := by
    change some (TM2.stepAux (program (labels .suffix)) _ _) = _
    rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
    rfl
  let b₄ := emitted (slots 7) (slots 8) b₃ [.not, .const no, .and, .or]
  have hword : b₄ (slots 3) = encodeWord address := by
    simp [b₄, b₃, b₂, b₁, b₀, emitted, slots.injective.eq_iff]
  have hd := MachineDrain.drainTrace (slots 3) (labels .drain) exit program (atLabels .drain)
    b₄ (encodeWord address) (ambient, false) none
  rw [← hword, Function.update_eq_self] at hd
  rw [hword, encodeWord_length] at hd
  have hfinish : Function.update b₄ (slots 3) [] =
      emitted (slots 7) (slots 8) base (payloadTokens address yes no) := by
    have hb : b₄ = emitted (slots 7) (slots 8) b₀ (payloadTokens address yes no) := by
      simp only [b₄, b₃, b₂, b₁, ClashMachine.emitted_append (slots 7) (slots 8)
        (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
      rfl
    rw [hb]
    apply ClashMachine.Full.ext_slots slots
    · intro j
      fin_cases j <;> simp [b₀, emitted, slots.injective.eq_iff, e₃]
    · intro k hk
      simp [b₀, emitted, hk]
  rw [hfinish] at hd
  exact chain (chain (chain (chain (chain ha ht) hm) hf) hs) hd

end Payload

namespace Symbol

theorem trace (slots : Ports K) (labels : Label ↪ Λ) (exit : Option Λ) (spec : SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit spec l)
    (base : K → List Bool) (q i : Nat) (hi : i < q)
    (ready : Ready slots base q i) (ambient : σ) :
    (advance (TM2.step program))^[steps spec q i]
      (some ⟨some (labels .start), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (symbolTokens spec q i)⟩ := by
  cases hspec : spec.isInput with
  | false =>
    simp only [steps, hspec, Bool.false_eq_true, ↓reduceIte]
    change some (TM2.stepAux (program (labels .start)) _ _) = _
    rw [atLabels, statement, hspec]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ClashMachine.stepAux_literal (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
    cases exit <;> simp [Reduction.MachineTransfer.exitAt, TM2.stepAux, symbolTokens, hspec]
  | true =>
    have hs : (advance (TM2.step program))^[1]
        (some ⟨some (labels .start), clean ambient, base⟩) =
        some ⟨some (labels (.first .initialize_)), clean ambient, base⟩ := by
      change some (TM2.stepAux (program (labels .start)) _ _) = _
      rw [atLabels, statement, hspec]
      rfl
    have h₁ := PayloadPresenceMachine.trace slots (firstLabels.trans labels)
      (some (labels (.payload .seed))) program (fun _ => atLabels _) base q i hi ready ambient
    let b₁ := emitted (slots 7) (slots 8) base (presenceTokens q i)
    have hp := Payload.trace slots (fun l => labels (.payload l)) (some (labels .conjunction))
      spec.trueValue spec.falseValue program (fun _ => atLabels _)
      b₁ q i (ready.emitted (presenceTokens q i)) ambient
    let b₂ := emitted (slots 7) (slots 8) b₁ (payloadTokens (q + 1 + i) spec.trueValue spec.falseValue)
    have hc : (advance (TM2.step program))^[1]
        (some ⟨some (labels .conjunction), clean ambient, b₂⟩) =
        some ⟨some (labels (.second .initialize_)), clean ambient,
          emitted (slots 7) (slots 8) b₂ [.and]⟩ := by
      change some (TM2.stepAux (program (labels .conjunction)) _ _) = _
      rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
        (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
      rfl
    let b₃ := emitted (slots 7) (slots 8) b₂ [.and]
    have r₃ : Ready slots b₃ q i :=
      ((ready.emitted (presenceTokens q i)).emitted
        (payloadTokens (q + 1 + i) spec.trueValue spec.falseValue)).emitted [.and]
    have h₂ := PayloadPresenceMachine.trace slots (secondLabels.trans labels)
      (some (labels .suffix)) program (fun _ => atLabels _) b₃ q i hi r₃ ambient
    let b₄ := emitted (slots 7) (slots 8) b₃ (presenceTokens q i)
    have hf : (advance (TM2.step program))^[1]
        (some ⟨some (labels .suffix), clean ambient, b₄⟩) =
        some ⟨exit, clean ambient,
          emitted (slots 7) (slots 8) b₄ [.not, .const spec.absentValue, .and, .or]⟩ := by
      change some (TM2.stepAux (program (labels .suffix)) _ _) = _
      rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
        (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))]
      cases exit <;> rfl
    have h := chain (chain (chain (chain (chain hs h₁) hp) hc) h₂) hf
    simpa only [steps, hspec, ↓reduceIte, b₄, b₃, b₂, b₁,
      ClashMachine.emitted_append (slots 7) (slots 8)
        (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8)), symbolTokens, muxTokens,
      List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using h

end Symbol

namespace Row

variable {A : Nat}

theorem traceFrom (slots : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit table l)
    (base : K → List Bool) (q i : Nat) (hi : i < q) (ready : Ready slots base q i)
    (ambient : σ) (start count : Nat) (hfinish : start + count = A) :
    (advance (TM2.step program))^[stepsFrom table q i start count]
      (some ⟨some (labels (.visit ⟨start, by omega⟩)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (tokensFrom table q i start count)⟩ := by
  induction count generalizing start base with
  | zero =>
    have hstart : start = A := by omega
    change some (TM2.stepAux (program (labels (.visit ⟨start, by omega⟩))) _ _) = _
    rw [atLabels, statement, dite_eq_right (show ¬ start < A by omega)]
    cases exit <;> simp [TM2.stepAux, Reduction.MachineTransfer.exitAt,
      tokensFrom, forTokens, ClashMachine.emitted_nil]
  | succ count ih =>
    have hstart : start < A := by omega
    let j : Fin A := ⟨start, hstart⟩
    have hv : (advance (TM2.step program))^[1]
        (some ⟨some (labels (.visit ⟨start, by omega⟩)), clean ambient, base⟩) =
        some ⟨some (labels (.symbol j .start)), clean ambient, base⟩ := by
      change some (TM2.stepAux (program (labels (.visit ⟨start, by omega⟩))) _ _) = _
      rw [atLabels, statement, dite_eq_left hstart]
      rfl
    have hs := Symbol.trace slots ((symbolLabels j).trans labels)
      (some (labels (.visit ⟨start + 1, by omega⟩))) (table j) program
      (fun l => atLabels (.symbol j l)) base q i hi ready ambient
    let nextBase := emitted (slots 7) (slots 8) base (symbolTokens (table j) q i)
    have hn := ih nextBase (ready.emitted (symbolTokens (table j) q i)) (start + 1) (by omega)
    have h := chain (chain hv hs) hn
    have ht : tableAt table start = table j := dite_eq_left hstart
    simpa only [stepsFrom, tokensFrom_succ, ht, nextBase,
      ClashMachine.emitted_append (slots 7) (slots 8)
        (slots.injective.ne (by decide : (7 : Fin 9) ≠ 8))] using h

theorem trace (slots : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit table l)
    (base : K → List Bool) (q i : Nat) (hi : i < q) (ready : Ready slots base q i) (ambient : σ) :
    (advance (TM2.step program))^[steps table q i]
      (some ⟨some (labels (.visit 0)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (tokens table q i)⟩ := by
  exact traceFrom slots labels exit table program atLabels base q i hi ready ambient 0 A (by omega)

end Row

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadRowsLoop

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted emitted_append)
open PayloadCellsMachine (SymbolSpec)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

theorem trace (p : Ports K) (label : Label A ↪ Λ) (exit : Λ) (table : Fin A → SymbolSpec)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (ha : Agrees p label exit table program) (base : K → List Bool) (q i m c : Nat)
    (hbound : i + m ≤ q) (ready : PayloadPresenceMachine.Ready (rowPorts p) base q 0)
    (ambient : σ) :
    (advance (TM2.step program))^[steps table q i m]
      (some ⟨some (label .guard), clean ambient, frame p base m i (c + m)⟩) =
      some ⟨some exit, clean ambient,
        emitted (p 7) (p 8) (frame p base 0 (i + m) c) (tokens table q i m)⟩ := by
  induction m generalizing base i with
  | zero =>
    simpa only [steps, Function.iterate_one, advance_some, Nat.add_zero,
      tokens, ClashMachine.emitted_nil] using guardStep_zero p label exit table program ha base i c ambient
  | succ m ih =>
    have hi : i < q := by omega
    have hguard : (advance (TM2.step program))^[1]
        (some ⟨some (label .guard), clean ambient, frame p base (m + 1) i (c + (m + 1))⟩) =
        some ⟨some (label (.row (.visit 0))), clean ambient, frame p base m i (c + (m + 1))⟩ := by
      simpa only [Function.iterate_one, advance_some] using
        guardStep_succ p label exit table program ha base m i (c + (m + 1)) ambient
    have hrow := PayloadCellsMachine.Row.trace (rowPorts p) (rowLabels label)
      (some (label .next)) table program (fun entry => ha (.row entry))
      (frame p base m i (c + (m + 1))) q i hi (frame_ready p base q m i _ ready) ambient
    change (advance (TM2.step program))^[PayloadCellsMachine.Row.steps table q i]
      (some ⟨some (label (.row (.visit 0))), clean ambient, frame p base m i (c + (m + 1))⟩) =
      some ⟨some (label .next), clean ambient,
        emitted (p 7) (p 8) (frame p base m i (c + (m + 1)))
          (PayloadCellsMachine.Row.tokens table q i)⟩ at hrow
    rw [frame_emitted] at hrow
    let nextBase := emitted (p 7) (p 8) base (PayloadCellsMachine.Row.tokens table q i)
    have hnext : (advance (TM2.step program))^[1]
        (some ⟨some (label .next), clean ambient, frame p nextBase m i (c + (m + 1))⟩) =
        some ⟨some (label .guard), clean ambient, frame p nextBase m (i + 1) (c + m)⟩ := by
      simpa only [Function.iterate_one, advance_some, Nat.add_assoc] using
        nextStep p label exit table program ha nextBase m i (c + m) ambient
    have hn : PayloadPresenceMachine.Ready (rowPorts p) nextBase q 0 :=
      ready.emitted (PayloadCellsMachine.Row.tokens table q i)
    have htail := ih nextBase (i + 1) (by omega) hn
    have h := ClashMachine.chain (ClashMachine.chain (ClashMachine.chain hguard hrow) hnext) htail
    have hend : i + 1 + m = i + (m + 1) := by omega
    simpa only [steps, tokens, hend, nextBase, ← frame_emitted,
      emitted_append (p 7) (p 8) (p.injective.ne (by decide : (7 : Fin 11) ≠ 8))] using h

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadRowsLoop

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitFinish
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

open Turing MachineComposition
open MachineCloudPadding

variable {σ : Type}

theorem finishTrace (n f root : Nat) (records : List Bool) (hf : f ≤ n)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[totalTime n f root records.length]
      (some ⟨some .copyOut, (ambient, register), initialTapes n f root records⟩) =
      some ⟨none, (ambient, none), finalTapes n f root records⟩ := by
  have copy := MachineCopy.copyTrace Tape.current Tape.gateCount Tape.scratch
    (by decide) (by decide) (by decide) false Label.copyOut Label.copyBack
    (some Label.cancel) program rfl rfl (initialTapes n f root records) rfl ambient register
  simp only [initialTapes, memory, encodeWord_length, List.append_nil, update_gateCount] at copy
  have cancel := cancelTrace (encodeWord n) (encodeWord root) records.reverse [] []
    f (n - f) ambient none
  rw [show f + (n - f) = n by omega] at cancel
  have reverse := Reduction.MachineTransfer.transferAt_fromTapes Tape.reversedRecords
    Tape.output (by decide) id false Label.records (some Label.rootOut) program rfl
    (memory (encodeWord n) [] (encodeWord root) records.reverse [] (encodeWord (n - f)) [])
    ambient none
  change (advance (TM2.step program))^[_]
    (some ⟨some .records, (ambient, none), _⟩) = _ at reverse
  simp only [memory, List.length_reverse, List.reverse_reverse, List.map_id,
    List.append_nil, Reduction.MachineTransfer.tapesAt, update_reversedRecords,
    update_output] at reverse
  have rootPhase := prependTrace Tape.root Tape.output Tape.scratch
    (by decide) (by decide) (by decide) Label.rootOut Label.rootBack (some Label.countOut)
    program rfl rfl
    (memory (encodeWord n) [] (encodeWord root) [] records (encodeWord (n - f)) [])
    rfl ambient none
  simp only [memory, encodeWord_length, Reduction.MachineTransfer.tapesAt,
    update_root, update_output] at rootPhase
  have countPhase := prependTrace Tape.gateCount Tape.output Tape.scratch
    (by decide) (by decide) (by decide) Label.countOut Label.countBack (some Label.currentOut)
    program rfl rfl
    (memory (encodeWord n) [] [] [] (encodeWord root ++ records) (encodeWord (n - f)) [])
    rfl ambient none
  simp only [memory, encodeWord_length, Reduction.MachineTransfer.tapesAt,
    update_gateCount, update_output] at countPhase
  have currentPhase := prependTrace Tape.current Tape.output Tape.scratch
    (by decide) (by decide) (by decide) Label.currentOut Label.currentBack none
    program rfl rfl
    (memory (encodeWord n) [] [] []
      (encodeWord (n - f) ++ (encodeWord root ++ records)) [] []) rfl ambient none
  simp only [memory, encodeWord_length, Reduction.MachineTransfer.tapesAt,
    update_current, update_output] at currentPhase
  have all := appendTrace _ (appendTrace _ (appendTrace _
    (appendTrace _ (appendTrace _ copy cancel) reverse) rootPhase) countPhase) currentPhase
  simpa only [totalTime, initialTapes, finalTapes, encodeWords,
    List.append_nil, List.append_assoc, Nat.add_assoc] using all

theorem circuitTrace (C : Circuit) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
      totalTime C.wires C.inputs C.output.val (recordsBits C.records).length]
      (some ⟨some .copyOut, (ambient, register),
        initialTapes C.wires C.inputs C.output.val (recordsBits C.records)⟩) =
      some ⟨none, (ambient, none), memory [] [] [] [] (circuitBits C) [] []⟩ := by
  rw [← circuit_finalTapes]
  exact finishTrace C.wires C.inputs C.output.val (recordsBits C.records)
    (Nat.le_add_right _ _) ambient register

def circuitInTime (C : Circuit) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register),
        initialTapes C.wires C.inputs C.output.val (recordsBits C.records)⟩
      (some ⟨none, (ambient, none), memory [] [] [] [] (circuitBits C) [] []⟩)
      (9 * C.wires + (recordsBits C.records).length + 18) where
  steps := totalTime C.wires C.inputs C.output.val (recordsBits C.records).length
  evals_in_steps := circuitTrace C ambient register
  steps_le_m := totalTime_le _ _ _ _ (Nat.le_add_right _ _) C.output.isLt

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitProducer
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.LiteralSlotGraph.instDecidableConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages

open Turing
open BinPackingGames.Reduction
open CircuitProducerModel

theorem drainStep_cons (tape : Tape) (again next : Label)
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (bit : Bool) (input : List Bool)
    (control : Unit × Context) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape (bit :: input)⟩ =
      some ⟨some again, (control, some bit), Function.update base tape input⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape (bit :: input))) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

theorem drainStep_nil (tape : Tape) (again next : Label)
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context) (register : Option Bool) :
    TM2.step program
      ⟨some again, (control, register), Function.update base tape []⟩ =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  change some (TM2.stepAux (program again) (control, register)
    (Function.update base tape [])) = _
  rw [atAgain]
  simp [drain, TM2.stepAux]

theorem drainTrace (tape : Tape) (again next : Label)
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (input : List Bool)
    (control : Unit × Context) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some again, (control, register), Function.update base tape input⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  induction input generalizing register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        MachineComposition.advance_some] using
        drainStep_nil tape again next atAgain base control register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[input.length + 1]
        (TM2.step program ⟨some again, (control, register),
          Function.update base tape (bit :: input)⟩) = _
      rw [drainStep_cons tape again next atAgain, ih]

theorem drainTrace_base (tape : Tape) (again next : Label)
    (atAgain : program again = drain tape again next)
    (base : Tape → List Bool) (control : Unit × Context) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[(base tape).length + 1]
      (some ⟨some again, (control, register), base⟩) =
      some ⟨some next, (control, none), Function.update base tape []⟩ := by
  simpa only [Function.update_eq_self] using
    drainTrace tape again next atAgain base (base tape) control register

theorem tagStep (tag : Fin 5) (base : Tape → List Bool) (state : State)
    (htag : base (.field 0) = encodeWord tag.val) :
    TM2.step program ⟨some .decodeTag, state, base⟩ =
      some ⟨some (.setup (.gate tag 0)), initialState,
        Function.update base (.field 0) []⟩ := by
  fin_cases tag <;>
    simp [TM2.step, TM2.stepAux, program, tagDecoder, resetGoto, initialState,
      encodeWord, htag]

def tagInTime (tag : Fin 5) (base : Tape → List Bool) (state : State)
    (htag : base (.field 0) = encodeWord tag.val) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .decodeTag, state, base⟩
      (some ⟨some (.setup (.gate tag 0)), initialState,
        Function.update base (.field 0) []⟩) 1 where
  steps := 1
  evals_in_steps := tagStep tag base state htag
  steps_le_m := Nat.le_refl _

theorem cleanupTrace (base : Tape → List Bool) (control : Unit × Context)
    (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[cleanupSteps base]
      (some ⟨some (.cleanup 0), (control, register), base⟩) =
      some ⟨some .guard, (control, none), clearFields base⟩ := by
  let b1 := Function.update base (.field 0) []
  let b2 := Function.update b1 (.field 1) []
  let b3 := Function.update b2 (.field 2) []
  have h0 := drainTrace_base (.field 0) (.cleanup 0) (.cleanup 1) rfl
    base control register
  have h1 := drainTrace_base (.field 1) (.cleanup 1) (.cleanup 2) rfl b1 control none
  have h2 := drainTrace_base (.field 2) (.cleanup 2) (.cleanup 3) rfl b2 control none
  have h3 := drainTrace_base (.field 3) (.cleanup 3) .guard rfl b3 control none
  have hn : cleanupSteps base = ((b3 (.field 3)).length + 1) +
      ((b2 (.field 2)).length + 1) + ((b1 (.field 1)).length + 1) +
      ((base (.field 0)).length + 1) := by
    simp [cleanupSteps, b1, b2, b3]
    omega
  rw [hn, Function.iterate_add_apply, h0, Function.iterate_add_apply, h1,
    Function.iterate_add_apply, h2, h3]
  rfl

def cleanupInTime (base : Tape → List Bool) (control : Unit × Context)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanup 0), (control, register), base⟩
      (some ⟨some .guard, (control, none), clearFields base⟩)
      (cleanupSteps base) where
  steps := cleanupSteps base
  evals_in_steps := cleanupTrace base control register
  steps_le_m := Nat.le_refl _

theorem finishTrace (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    (MachineComposition.advance (TM2.step program))^[
      (base .selected).length + (base .reversed).length + 3]
      (some ⟨some .finalCounter, initialState, base⟩) =
      some ⟨none, initialState, finishTapes base⟩ := by
  let b1 := Function.update base .counter []
  let b2 := Function.update b1 .selected []
  have first := counterStep base hcounter
  have second := drainTrace_base .selected .clearSelected .finalReverse rfl
    b1 ((), defaultControl) none
  have last := MachineTransfer.transferAt_fromTapes Tape.reversed Tape.output
    (by decide) id false Label.finalReverse none program rfl b2
    ((), defaultControl) none
  have hnext : MachineTransfer.nextAt Tape.output program =
      MachineComposition.advance (TM2.step program) := rfl
  rw [hnext] at last
  have last' : (MachineComposition.advance (TM2.step program))^[(base .reversed).length + 1]
      (some ⟨some .finalReverse, initialState, b2⟩) =
      some ⟨none, initialState, finishTapes base⟩ := by
    simpa [finishTapes, b1, b2,
      initialState] using last
  have second' : (MachineComposition.advance (TM2.step program))^[(base .selected).length + 1]
      (some ⟨some .clearSelected, initialState, b1⟩) =
      some ⟨some .finalReverse, initialState, b2⟩ := by
    simpa [b1, initialState] using second
  rw [show (base .selected).length + (base .reversed).length + 3 =
      ((base .reversed).length + 1) + ((base .selected).length + 1) + 1 by omega,
    Function.iterate_succ_apply, MachineComposition.advance_some, first,
    Function.iterate_add_apply, second', last']

def finishInTime (base : Tape → List Bool) (hcounter : base .counter = [false]) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .finalCounter, initialState, base⟩
      (some ⟨none, initialState, finishTapes base⟩)
      ((base .selected).length + (base .reversed).length + 3) where
  steps := (base .selected).length + (base .reversed).length + 3
  evals_in_steps := finishTrace base hcounter
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerStages

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders

open Turing
open BinPackingGames.Foundations.Hastad
open CircuitProducerModel CircuitEmission CircuitProducerStages

theorem headersTrace (base : Tape → List Bool) (n m output : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m, output] ++ suffix)
    (hn : base .header = []) (hm : base .counter = []) (ho : base .selected = [])
    (hs : base .scratch = []) (hr : base .reversed = []) :
    (MachineComposition.advance (TM2.step program))^[5 * n + 4 * m + output + 20]
      (some ⟨some (.headerStart 0), initialState, base⟩) =
      some ⟨some .guard, initialState, resultTapes base n m output suffix⟩ := by
  let b0 := SourceMachine.afterField .input .header base n
    (encodeWords [m, output] ++ suffix)
  let b1 := SourceMachine.afterField .input .counter b0 m (encodeWord output ++ suffix)
  let b2 := parsedTapes base n m output suffix
  let b3 := Function.update b2 .reversed (encodeWord n).reverse
  let b4 := Function.update b2 .reversed (encodeWords [n, 3 * m + 1]).reverse
  have h0 : base .input = encodeWord n ++ (encodeWords [m, output] ++ suffix) := by
    simpa only [encodeWords, List.append_nil, List.append_assoc] using hinput
  have h1 : b0 .input = encodeWord m ++ (encodeWord output ++ suffix) := by
    simp [b0, SourceMachine.afterField, encodeWords, List.append_assoc]
  have h2 : b1 .input = encodeWord output ++ suffix := by
    simp [b1, SourceMachine.afterField]
  have p0 := (SourceMachine.fieldInTime .input .header (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1)) program rfl rfl
    base n (encodeWords [m, output] ++ suffix) h0 ((), defaultControl) none).evals_in_steps
  have p1 := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some (.headerStart 2)) program rfl rfl
    b0 m (encodeWord output ++ suffix) h1 ((), defaultControl) none).evals_in_steps
  have p2 := (SourceMachine.fieldInTime .input .selected (by decide)
    (.headerStart 2) (.headerLoop 2) (some (.setup (.header 0))) program rfl rfl
    b1 output suffix h2 ((), defaultControl) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.headerStart 0), initialState, base⟩) =
    some ⟨some (.headerStart 1), initialState, b0⟩ at p0
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.headerStart 1), initialState, b0⟩) =
    some ⟨some (.headerStart 2), initialState, b1⟩ at p1
  change (MachineComposition.advance (TM2.step program))^[output + 2]
    (some ⟨some (.headerStart 2), initialState, b1⟩) =
    some ⟨some (.setup (.header 0)), initialState,
      SourceMachine.afterField .input .selected b1 output suffix⟩ at p2
  have hb2 : SourceMachine.afterField .input .selected b1 output suffix = b2 :=
    parsedTapes_eq base n m output suffix hn hm ho
  rw [hb2] at p2
  have p3 : (MachineComposition.advance (TM2.step program))^[3 * (n + 1) + 3]
      (some ⟨some (.setup (.header 0)), initialState, b2⟩) =
      some ⟨some (.setup (.header 1)), initialState, b3⟩ := by
    simpa [contextWords, contextNext, b3, b2, parsedTapes, hr, encodeWords] using
      contextTrace_word (.header 0) b2 (by simpa [b2, parsedTapes] using hs)
        initialState n rfl
  have p4 : (MachineComposition.advance (TM2.step program))^[3 * (m + 1) + 3]
      (some ⟨some (.setup (.header 1)), initialState, b3⟩) =
      some ⟨some .clearHeader, initialState, b4⟩ := by
    have p := contextTrace_word (.header 1) b3
      (by simpa [b3, b2, parsedTapes] using hs) initialState m (by
        simp [b3, b2, parsedTapes, contextSource])
    simpa [contextWords, contextNext, b4, b3, encodeWords, List.reverse_append] using p
  have p5 : (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some .clearHeader, initialState, b4⟩) =
      some ⟨some .guard, initialState, resultTapes base n m output suffix⟩ := by
    have p := drainTrace_base .header .clearHeader .guard rfl b4
      ((), defaultControl) none
    have he : Function.update b4 .header [] = resultTapes base n m output suffix := by
      funext tape
      cases tape <;> simp [b4, b2, parsedTapes, resultTapes]
    rw [he] at p
    simpa [b4, b2, parsedTapes, initialState] using p
  rw [show 5 * n + 4 * m + output + 20 = (n + 2) +
      (3 * (m + 1) + 3) + (3 * (n + 1) + 3) + (output + 2) +
      (m + 2) + (n + 2) by omega,
    Function.iterate_add_apply, p0, Function.iterate_add_apply, p1,
    Function.iterate_add_apply, p2, Function.iterate_add_apply, p3,
    Function.iterate_add_apply, p4, p5]

def headersInTime (base : Tape → List Bool) (n m output : Nat) (suffix : List Bool)
    (hinput : base .input = encodeWords [n, m, output] ++ suffix)
    (hn : base .header = []) (hm : base .counter = []) (ho : base .selected = [])
    (hs : base .scratch = []) (hr : base .reversed = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.headerStart 0), initialState, base⟩
      (some ⟨some .guard, initialState, resultTapes base n m output suffix⟩)
      (5 * n + 4 * m + output + 20) where
  steps := 5 * n + 4 * m + output + 20
  evals_in_steps := headersTrace base n m output suffix hinput hn hm ho hs hr
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerHeaders

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop

open Turing
open BinPackingGames.Foundations.Hastad
open CircuitProducerModel CircuitEmission CircuitProducerStages

def bodyInTime (base : Tape → List Bool) (r : Record) (suffix counter acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.fieldStart 0), initialState,
        tapes base (r.bits ++ suffix) counter acc (fun _ => [])⟩
      (some ⟨some .guard, initialState,
        tapes base suffix counter (r.outputBits.reverse ++ acc) (fun _ => [])⟩)
      (bodyCost r) := by
  let before := tapes base (r.bits ++ suffix) counter acc (fun _ => [])
  let parsed := tapes base suffix counter acc (parsedFields r)
  let decoded := tapes base suffix counter acc (decodedFields r)
  let out := r.outputBits.reverse ++ acc
  let emitted := tapes base suffix counter out (decodedFields r)
  let parse := SourceMachine.fourFieldsInTime .input Tape.field
    (by intro j h; cases h) Label.fieldStart Label.fieldLoop (some .decodeTag)
    program (by intro j; rfl) (by intro j; rfl)
    before r.tag.val r.output r.first r.second suffix rfl ((), defaultControl) none
  have hp : SourceMachine.fourTapes .input Tape.field before
      r.tag.val r.output r.first r.second suffix = parsed := fourTapes_eq _ _ _ _ _ _
  rw [hp] at parse
  let decode := tagInTime r.tag parsed initialState rfl
  have hd : Function.update parsed (.field 0) [] = decoded := decodeTapes_eq _ _ _ _ _
  rw [hd] at decode
  let table := gateInTime r decoded rfl initialState rfl rfl rfl
  have he : Function.update decoded .reversed (r.outputBits.reverse ++ decoded .reversed) =
      emitted := update_reversed _ _ _ _ _ _
  rw [he] at table
  let cleanup := cleanupInTime emitted ((), defaultControl) none
  have hc : clearFields emitted = tapes base suffix counter out (fun _ => []) :=
    clearFields_eq _ _ _ _ _
  rw [hc] at cleanup
  let p1 := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ parse decode
  let p2 := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p1 table
  let p3 := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p2 cleanup
  exact {
    toEvalsTo := p3.toEvalsTo
    steps_le_m := by
      have h := p3.steps_le_m
      have hcost : cleanupSteps emitted = r.output + r.first + r.second + 7 :=
        cleanupSteps_eq _ _ _ _ _
      unfold bodyCost
      omega }

def loopInTime (base : Tape → List Bool) (suffix : List Bool)
    (rs : List Record) (acc : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .guard, initialState,
        tapes base (recordsInput rs ++ suffix) (encodeWord rs.length) acc (fun _ => [])⟩
      (some ⟨some (.setup (.output 0)), initialState,
        tapes base suffix (encodeWord 0) ((recordsOutput rs).reverse ++ acc) (fun _ => [])⟩)
      (loopCost rs) := by
  induction rs generalizing acc with
  | nil =>
      let guard := MachineUnaryCounter.guardInTime_zero .counter Label.guard
        (.fieldStart 0) (.setup (.output 0)) program rfl
        (tapes base suffix (encodeWord 0) acc (fun _ => [])) []
        ((), defaultControl) none
      simpa only [counterTapes_eq, loopCost, recordsInput, recordsOutput,
        List.flatMap_nil, List.reverse_nil, List.nil_append, List.length_nil,
        initialState] using guard
  | cons r rs ih =>
      let before := tapes base (r.bits ++ (recordsInput rs ++ suffix))
        (encodeWord (rs.length + 1)) acc (fun _ => [])
      let guard := MachineUnaryCounter.guardInTime_succ .counter Label.guard
        (.fieldStart 0) (.setup (.output 0)) program rfl before rs.length []
        ((), defaultControl) none
      simp only [before, counterTapes_eq] at guard
      let body := bodyInTime base r (recordsInput rs ++ suffix) (encodeWord rs.length) acc
      let rest := ih (r.outputBits.reverse ++ acc)
      let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
      let full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first rest
      simpa only [loopCost, recordsInput, recordsOutput, List.flatMap_cons,
        List.length_cons, List.reverse_append, List.append_assoc, initialState,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerRuntime

open Turing
open CircuitProducerModel CircuitProducerLoop

theorem initList_eq (input : Input) :
    initList machine (inputBits input) =
      ⟨some (.headerStart 0), initialState, inputTapes input⟩ := by
  change (⟨some (.headerStart 0), initialState,
    (initList machine (inputBits input)).stk⟩ : machine.Cfg) = _
  apply congrArg (fun tapeContents =>
    (⟨some (.headerStart 0), initialState, tapeContents⟩ : machine.Cfg))
  funext tape
  (cases tape <;> simp [initList, machine, inputTapes]); rfl

theorem finish_eq (input : Input) :
    (⟨none, initialState,
      CircuitProducerStages.finishTapes (beforeFinishTapes input)⟩ : machine.Cfg) =
      haltList machine (producedBits input) := by
  apply congrArg (fun tapeContents => (⟨none, initialState, tapeContents⟩ : machine.Cfg))
  funext tape
  (cases tape <;>
    simp [CircuitProducerStages.finishTapes, Reduction.MachineTransfer.tapesAt,
      beforeFinishTapes, tapes, retainedTapes, machine]); rfl

def fullRunInTime (input : Input) :
    TM2OutputsInTime machine (inputBits input) (some (producedBits input))
      (100 * (inputBits input).length + 100) := by
  let first := CircuitProducerHeaders.headersInTime (inputTapes input) input.wireCount
    input.records.length input.selected (recordsInput input.records) rfl rfl rfl rfl rfl rfl
  have first' : StateTransition.EvalsToInTime (TM2.step program)
      (initList machine (inputBits input))
      (some ⟨some .guard, initialState, guardTapes input⟩)
      (5 * input.wireCount + 4 * input.records.length + input.selected + 20) := by
    simpa only [initList_eq, headers_result_eq] using! first
  let middle := loopInTime (retainedTapes input) [] input.records (outputHeaders input).reverse
  have middle' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .guard, initialState, guardTapes input⟩
      (some ⟨some (.setup (.output 0)), initialState, afterLoopTapes input⟩)
      (loopCost input.records) := by
    simpa only [List.append_nil, guardTapes, afterLoopTapes] using middle
  let unitClause := CircuitEmission.outputInTime input.selected (afterLoopTapes input)
    rfl initialState rfl
  have unitClause' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.setup (.output 0)), initialState, afterLoopTapes input⟩
      (some ⟨some .finalCounter, initialState, beforeFinishTapes input⟩)
      (9 * (input.selected + 1) + 9) := by
    simpa only [output_result_eq] using unitClause
  let last := CircuitProducerStages.finishInTime (beforeFinishTapes input) rfl
  have last' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .finalCounter, initialState, beforeFinishTapes input⟩
      (some (haltList machine (producedBits input)))
      (input.selected + (producedBits input).length + 4) := by
    erw [finish_eq] at last
    convert last using 1
    all_goals try with_reducible_and_instances rfl
    simp [beforeFinishTapes, tapes, retainedTapes]
    omega
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first' middle'
  let firstThree := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo unitClause'
  let complete := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstThree last'
  refine { toEvalsTo := complete.toEvalsTo, steps_le_m := complete.steps_le_m.trans ?_ }
  have hlo := loopCost_le input.records
  have hout := producedBits_length_le input
  rw [inputBits_length]
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerRuntime

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer

open Turing
open CircuitProducerModel

def fullRunInTime (C : Circuit) :
    TM2OutputsInTime machine (circuitBits C) (some (formulaBits C.toFormula))
      (100 * (circuitBits C).length + 100) := by
  simpa only [inputBits_asInput, producedBits_asInput] using
    CircuitProducerRuntime.fullRunInTime (asInput C)

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime circuitBits formulaBits Circuit.toFormula where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 100 * Polynomial.X + Polynomial.C 100
  outputsFun C := by
    change TM2OutputsInTime machine ((circuitBits C).map id)
      (some ((formulaBits C.toFormula).map id)) _
    have input_eq : @List.map (machine.Γ machine.k₀) (machine.Γ machine.k₀) id
        (circuitBits C) = circuitBits C := List.map_id _
    have output_eq : @List.map (machine.Γ machine.k₁) (machine.Γ machine.k₁) id
        (formulaBits C.toFormula) = formulaBits C.toFormula := List.map_id _
    simpa only [Equiv.refl, input_eq, output_eq,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      using fullRunInTime C

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducer

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PostfixBounds
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixMachine

open Turing PostfixModel Hastad

theorem readTrace (tag : Fin 6) (pass : Fin 2) (base : Tape → List Bool)
    (value : Nat) (suffix : List Bool)
    (hinput : base (readSource tag) = encodeWord value ++ suffix) :
    advance^[value + 2] (some ⟨some (.readStart tag pass), initialState, base⟩) =
      some ⟨some (readNext tag pass), initialState,
        SourceMachine.fieldTapes (readSource tag) (readDestination tag pass) base suffix
          (encodeWord value ++ base (readDestination tag pass))⟩ := by
  have h := (SourceMachine.fieldInTime (K := Tape) (Λ := Label) (σ := Unit)
    (readSource tag) (readDestination tag pass)
    (readSource_ne_destination tag pass) (.readStart tag pass) (.readLoop tag pass)
    (some (readNext tag pass)) program rfl rfl base value suffix hinput () none).evals_in_steps
  change advance^[value + 2]
    (some ⟨some (.readStart tag pass), initialState, base⟩) =
    some ⟨some (readNext tag pass), initialState,
      SourceMachine.fieldTapes (readSource tag) (readDestination tag pass) base suffix
        (encodeWord value ++ base (readDestination tag pass))⟩ at h
  exact h

theorem clearTrace (base : Tape → List Bool) :
    advance^[(base .left).length + (base .right).length + 2]
      (some ⟨some .clearLeft, initialState, base⟩) =
      some ⟨some .guard, initialState, clearTapes base⟩ := by
  let first := Function.update base .left []
  have h1 := (MachineDrain.drainInTime Tape.left .clearLeft (some .clearRight)
    program rfl base () none).evals_in_steps
  have h2 := (MachineDrain.drainInTime Tape.right .clearRight (some .guard)
    program rfl first () none).evals_in_steps
  change advance^[(base .left).length + 1]
    (some ⟨some .clearLeft, initialState, base⟩) =
    some ⟨some .clearRight, initialState, first⟩ at h1
  change advance^[(first .right).length + 1]
    (some ⟨some .clearRight, initialState, first⟩) =
    some ⟨some .guard, initialState, clearTapes base⟩ at h2
  have total := trace_trans _ h1 h2
  simpa only [first, Function.update_of_ne (by decide : Tape.right ≠ .left),
    show (base .left).length + 1 + ((base .right).length + 1) =
      (base .left).length + (base .right).length + 2 by omega] using total

theorem finishNodeTrace (base : Tape → List Bool) (current : Nat)
    (hcurrent : base .current = encodeWord current) (hscratch : base .scratch = []) :
    advance^[2 * current + (base .left).length + (base .right).length + 7]
      (some ⟨some .rootDrain, initialState, base⟩) =
      some ⟨some .guard, initialState, finishTapes base current⟩ := by
  let pushed := Function.update base .roots (encodeWord current ++ base .roots)
  let incremented := Function.update pushed .current (encodeWord (current + 1))
  have h1 := rootPushTrace base current hcurrent hscratch
  have h2 := incrementTrace pushed current (by simpa [pushed] using hcurrent)
  have h3 := clearTrace incremented
  have total := trace_trans _ (trace_trans _ h1 h2) h3
  simpa only [finishTapes, incremented, pushed,
    Function.update_of_ne (by decide : Tape.left ≠ .current),
    Function.update_of_ne (by decide : Tape.right ≠ .current),
    Function.update_of_ne (by decide : Tape.left ≠ .roots),
    Function.update_of_ne (by decide : Tape.right ≠ .roots),
    show (2 * current + 4) + 1 + ((base .left).length + (base .right).length + 2) =
      2 * current + (base .left).length + (base .right).length + 7 by omega] using total

theorem emitPreparedTrace (tag : Fin 6) (base : Tape → List Bool)
    (current : Nat) (gate : Gate)
    (htag : gateTag tag = (gateRecord current gate).tag.val)
    (ready : ∀ slot, FieldReady tag slot base ((gateRecord current gate).slot slot))
    (hcurrent : base .current = encodeWord current) (hscratch : base .scratch = []) :
    advance^[recordSteps tag (gateRecord current gate).slot +
      (2 * current + (base .left).length + (base .right).length + 7)]
      (some ⟨some (.emitTag tag), initialState, base⟩) =
      some ⟨some .guard, initialState,
        finishTapes (outputTapes base (gateRecord current gate).bits.reverse) current⟩ := by
  have hrecord := recordTrace tag base (gateRecord current gate).slot ready hscratch
  have hwords : [gateTag tag, (gateRecord current gate).slot 0,
      (gateRecord current gate).slot 1, (gateRecord current gate).slot 2] =
      (gateRecord current gate).words := by
    rw [htag]
    rfl
  rw [hwords] at hrecord
  let emitted := outputTapes base (gateRecord current gate).bits.reverse
  have hfinish := finishNodeTrace emitted current
    (by simpa [emitted, outputTapes] using hcurrent)
    (by simpa [emitted, outputTapes] using hscratch)
  have total := trace_trans _ hrecord hfinish
  simpa only [emitted, outputTapes_other base _ .left (by decide),
    outputTapes_other base _ .right (by decide)] using total

theorem prepareInputTrace (base : Tape → List Bool) (current wire : Nat)
    (roots : List Nat) (suffix : List Bool) :
    advance^[wire + 2]
      (some ⟨some (.readStart 5 0), initialState,
        boundaryTapes base current roots (encodeWord wire ++ suffix)⟩) =
      some ⟨some (.emitTag 5), initialState,
        preparedTapes base current roots suffix (encodeWord wire) []⟩ := by
  let first := boundaryTapes base current roots (encodeWord wire ++ suffix)
  have h := readTrace 5 0 first wire suffix rfl
  have hout : SourceMachine.fieldTapes (readSource 5) (readDestination 5 0) first suffix
      (encodeWord wire ++ first (readDestination 5 0)) =
      preparedTapes base current roots suffix (encodeWord wire) [] := by
    funext tape
    cases tape <;> simp [SourceMachine.fieldTapes, first, boundaryTapes, preparedTapes,
      readSource, readDestination, binary]
  rw [hout] at h
  exact h

theorem prepareUnaryTrace (base : Tape → List Bool) (current arg : Nat)
    (roots : List Nat) (suffix : List Bool) :
    advance^[arg + 2]
      (some ⟨some (.readStart 2 0), initialState,
        boundaryTapes base current (arg :: roots) suffix⟩) =
      some ⟨some (.emitTag 2), initialState,
        preparedTapes base current roots suffix (encodeWord arg) []⟩ := by
  let first := boundaryTapes base current (arg :: roots) suffix
  have h := readTrace 2 0 first arg (encodeWords roots) rfl
  have hout : SourceMachine.fieldTapes (readSource 2) (readDestination 2 0) first
      (encodeWords roots) (encodeWord arg ++ first (readDestination 2 0)) =
      preparedTapes base current roots suffix (encodeWord arg) [] := by
    funext tape
    cases tape <;> simp [SourceMachine.fieldTapes, first, boundaryTapes, preparedTapes,
      readSource, readDestination, binary]
  rw [hout] at h
  exact h

theorem prepareBinaryTrace (tag : Fin 6) (hb : binary tag = true) (hinput : tag.val ≠ 5)
    (base : Tape → List Bool) (current left right : Nat) (roots : List Nat) (suffix : List Bool) :
    advance^[left + right + 4]
      (some ⟨some (.readStart tag 0), initialState,
        boundaryTapes base current (right :: left :: roots) suffix⟩) =
      some ⟨some (.emitTag tag), initialState,
        preparedTapes base current roots suffix (encodeWord left) (encodeWord right)⟩ := by
  let first := boundaryTapes base current (right :: left :: roots) suffix
  let second := preparedTapes base current (left :: roots) suffix [] (encodeWord right)
  have h1 := readTrace tag 0 first right (encodeWords (left :: roots))
    (by simp [first, readSource, hinput, boundaryTapes, encodeWords])
  have frame1 : SourceMachine.fieldTapes (readSource tag) (readDestination tag 0) first
      (encodeWords (left :: roots)) (encodeWord right ++ first (readDestination tag 0)) = second := by
    funext tape
    cases tape <;> simp [SourceMachine.fieldTapes, first, second, boundaryTapes, preparedTapes,
      readSource, readDestination, hb, hinput]
  rw [frame1] at h1
  have h2 := readTrace tag 1 second left (encodeWords roots)
    (by simp [second, readSource, hinput, preparedTapes, encodeWords])
  have frame2 : SourceMachine.fieldTapes (readSource tag) (readDestination tag 1) second
      (encodeWords roots) (encodeWord left ++ second (readDestination tag 1)) =
      preparedTapes base current roots suffix (encodeWord left) (encodeWord right) := by
    funext tape
    cases tape <;> simp [SourceMachine.fieldTapes, second, preparedTapes,
      readSource, readDestination, hb, hinput]
  rw [frame2] at h2
  simp only [readNext, hb, Fin.val_zero, Fin.val_one, decide_true, Bool.and_true,
    Nat.one_ne_zero, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h1 h2
  have total := trace_trans _ h1 h2
  simpa only [show (right + 2) + (left + 2) = left + right + 4 by omega] using total

theorem prepareTrace (base : Tape → List Bool) (current : Nat) (token : Token)
    (roots rest : List Nat) (gate : Gate) (suffix : List Bool)
    (htake : token.takeGate roots = some (gate, rest)) :
    advance^[operandSteps token gate]
      (some ⟨some (prepare token.tag), initialState,
        boundaryTapes base current roots (argumentBits token ++ suffix)⟩) =
      some ⟨some (.emitTag token.tag), initialState,
        preparedTapes base current rest suffix
          (operandFields token gate).1 (operandFields token gate).2⟩ := by
  cases token with
  | const value =>
      simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
      rcases htake with ⟨rfl, rfl⟩
      cases value <;>
        simp [Token.tag, operandSteps, operandFields, argumentBits, prepare] <;>
        funext tape <;> cases tape <;> rfl
  | input wire =>
      simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
      rcases htake with ⟨rfl, rfl⟩
      simpa [Token.tag, operandSteps, operandFields, argumentBits, prepare] using
        prepareInputTrace base current wire roots suffix
  | not =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons arg roots =>
          simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
          rcases htake with ⟨rfl, rfl⟩
          simpa [Token.tag, operandSteps, operandFields, argumentBits, prepare] using
            prepareUnaryTrace base current arg roots suffix
  | and =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons right roots =>
          cases roots with
          | nil => simp [Token.takeGate] at htake
          | cons left roots =>
              simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
              rcases htake with ⟨rfl, rfl⟩
              simpa [Token.tag, operandSteps, operandFields, argumentBits, prepare] using
                prepareBinaryTrace 3 (by decide) (by decide) base current left right roots suffix
  | or =>
      cases roots with
      | nil => simp [Token.takeGate] at htake
      | cons right roots =>
          cases roots with
          | nil => simp [Token.takeGate] at htake
          | cons left roots =>
              simp only [Token.takeGate, Option.some.injEq, Prod.mk.injEq] at htake
              rcases htake with ⟨rfl, rfl⟩
              simpa [Token.tag, operandSteps, operandFields, argumentBits, prepare] using
                prepareBinaryTrace 4 (by decide) (by decide) base current left right roots suffix

theorem tokenTrace (base : Tape → List Bool) (current : Nat) (token : Token)
    (roots rest : List Nat) (gate : Gate) (suffix : List Bool)
    (htake : token.takeGate roots = some (gate, rest)) :
    advance^[tokenSteps current token gate]
      (some ⟨some .decode, initialState,
        boundaryTapes base current roots (token.bits ++ suffix)⟩) =
      some ⟨some .guard, initialState,
        boundaryTapes (outputTapes base (gateRecord current gate).bits.reverse)
          (current + 1) (current :: rest) suffix⟩ := by
  let first := boundaryTapes base current roots (token.bits ++ suffix)
  let decoded := boundaryTapes base current roots (argumentBits token ++ suffix)
  let prepared := preparedTapes base current rest suffix
    (operandFields token gate).1 (operandFields token gate).2
  have hd := decodeTrace token.tag first (argumentBits token ++ suffix)
    (by simp only [first, boundaryTapes, token_bits, List.append_assoc])
  have decodedFrame : Function.update first .input (argumentBits token ++ suffix) = decoded := by
    funext tape
    cases tape <;> simp [first, decoded, boundaryTapes]
  rw [decodedFrame] at hd
  have hp := prepareTrace base current token roots rest gate suffix htake
  have ready := preparedReady base current token roots rest gate suffix htake
  have he := emitPreparedTrace token.tag prepared current gate ready.1 ready.2 rfl rfl
  have total := trace_trans _ (trace_trans _ hd hp) he
  have finishedFrame : finishTapes (outputTapes prepared (gateRecord current gate).bits.reverse)
      current = boundaryTapes (outputTapes base (gateRecord current gate).bits.reverse)
        (current + 1) (current :: rest) suffix := by
    funext tape
    cases tape <;> simp [finishTapes, clearTapes, prepared, preparedTapes, boundaryTapes,
      outputTapes, encodeWords]
  rw [finishedFrame] at total
  simpa only [tokenSteps, first, prepared, preparedTapes, Nat.add_assoc] using total

theorem tokensTrace (tokens : List Token) (base : Tape → List Bool) (current : Nat)
    (roots : List Nat) (next : Nat) (finalRoots : List Nat) (gates : List Gate)
    (suffix : List Bool)
    (hcompile : compileTokens current roots tokens = some (next, finalRoots, gates))
    (hcount : base .remaining = encodeWord tokens.length) :
    advance^[tokensSteps current roots tokens]
      (some ⟨some .guard, initialState,
        boundaryTapes base current roots (tokenBits tokens ++ suffix)⟩) =
      some ⟨some .guard, initialState,
        boundaryTapes
          (outputTapes (Function.update base .remaining (encodeWord 0))
            (recordsBits (gateRecords current gates)).reverse)
          next finalRoots suffix⟩ := by
  induction tokens generalizing base current roots next finalRoots gates with
  | nil =>
      simp only [compileTokens, Option.some.injEq, Prod.mk.injEq] at hcompile
      rcases hcompile with ⟨rfl, rfl, rfl⟩
      have hsame : Function.update base .remaining (encodeWord 0) = base := by
        change base .remaining = encodeWord 0 at hcount
        rw [← hcount]
        exact Function.update_eq_self _ _
      simp [tokensSteps, tokenBits, tokenWords, gateRecords, recordsBits, recordsWords,
        encodeWords, hsame, outputTapes]
  | cons token tokens ih =>
      cases htake : token.takeGate roots with
      | none => simp [compileTokens, htake] at hcompile
      | some result =>
          rcases result with ⟨gate, rest⟩
          cases htail : compileTokens (current + 1) (current :: rest) tokens with
          | none => simp [compileTokens, htake, htail] at hcompile
          | some result =>
              rcases result with ⟨next', finalRoots', gates'⟩
              simp [compileTokens, htake, htail] at hcompile
              obtain ⟨hnext, hroots, hgates⟩ := hcompile
              subst next
              subst finalRoots
              subst gates
              let decremented := Function.update base .remaining (encodeWord tokens.length)
              let following := outputTapes decremented (gateRecord current gate).bits.reverse
              have hg := guardPositiveTrace
                (boundaryTapes base current roots (tokenBits (token :: tokens) ++ suffix))
                tokens.length (by simpa [boundaryTapes] using hcount)
              rw [boundary_remaining] at hg
              have ht := tokenTrace decremented current token roots rest gate
                (tokenBits tokens ++ suffix) htake
              have hi := ih following (current + 1) (current :: rest)
                next' finalRoots' gates' htail
                (by simp [following, decremented, outputTapes])
              have hg' : advance^[1]
                  (some ⟨some .guard, initialState,
                    boundaryTapes base current roots (tokenBits (token :: tokens) ++ suffix)⟩) =
                  some ⟨some .decode, initialState,
                    boundaryTapes decremented current roots (token.bits ++ (tokenBits tokens ++ suffix))⟩ := by
                simpa only [tokenBits_cons, List.append_assoc] using hg
              have total := trace_trans _ (trace_trans _ hg' ht) hi
              have frame :
                  outputTapes (Function.update following .remaining (encodeWord 0))
                    (recordsBits (gateRecords (current + 1) gates')).reverse =
                  outputTapes (Function.update base .remaining (encodeWord 0))
                    (recordsBits (gateRecords current (gate :: gates'))).reverse := by
                funext tape
                cases tape <;>
                  simp [following, decremented, outputTapes, gateRecords, recordsBits_cons,
                    List.reverse_append, List.append_assoc]
              rw [frame] at total
              simpa only [tokensSteps, htake] using total

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ForestStage
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.RootRefresh

open Turing MachineComposition
open BinPackingGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

theorem refreshTrace (source destination : K) (hne : source ≠ destination)
    (again start loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program again = guard source start exit)
    (atStart : program start = SourceMachine.fieldStart destination loopLabel)
    (atLoop : program loopLabel =
      SourceMachine.fieldLoop source destination loopLabel (some again))
    (base : K → List Bool) (values : List Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values]
      (some ⟨some again, (ambient, register),
        SourceMachine.fieldTapes source destination base (encodeWords values) output⟩) =
      some ⟨exit, (ambient, none),
        SourceMachine.fieldTapes source destination base [] (encodeWords values.reverse ++ output)⟩ := by
  induction values generalizing output register with
  | nil =>
    simpa only [steps_nil, Function.iterate_one, advance_some, encodeWords,
      List.reverse_nil, List.nil_append] using
      guardStep_nil source again start exit program atGuard
        (SourceMachine.fieldTapes source destination base [] output)
        (SourceMachine.fieldTapes_source source destination hne base [] output) ambient register
  | cons n values ih =>
    let initial := SourceMachine.fieldTapes source destination base
      (encodeWords (n :: values)) output
    have hinput : initial source = encodeWord n ++ encodeWords values := by
      simp only [initial, SourceMachine.fieldTapes_source source destination hne, encodeWords]
    have hnonempty : initial source ≠ [] := by
      intro h
      have hl := congrArg List.length h
      rw [hinput, List.length_append, encodeWord_length] at hl
      simp only [List.length_nil] at hl
      omega
    have hfield := (SourceMachine.fieldInTime source destination hne start loopLabel
      (some again) program atStart atLoop initial n (encodeWords values) hinput ambient
      (initial source).head?).evals_in_steps
    change (advance (TM2.step program))^[n + 2]
      (some ⟨some start, (ambient, (initial source).head?), initial⟩) =
        some ⟨some again, (ambient, none),
          SourceMachine.fieldTapes source destination initial (encodeWords values)
            (encodeWord n ++ initial destination)⟩ at hfield
    have hround :
        (advance (TM2.step program))^[n + 3]
          (some ⟨some again, (ambient, register), initial⟩) =
          some ⟨some again, (ambient, none),
            SourceMachine.fieldTapes source destination base (encodeWords values)
              (encodeWord n ++ output)⟩ := by
      change (advance (TM2.step program))^[(n + 2) + 1] _ = _
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [guardStep_nonempty source again start exit program atGuard initial hnonempty]
      simpa only [initial, SourceMachine.fieldTapes_destination,
        fieldTapes_overwrite source destination hne] using hfield
    rw [steps_cons, Function.iterate_add_apply, hround, ih]
    simp only [List.reverse_cons, encodeWords_append, encodeWords,
      List.append_nil, List.append_assoc]

end BinPackingGames.Foundations.Complexity.CookLevin.RootRefresh

namespace BinPackingGames.Foundations.Complexity.CookLevin.ForestStage

open Turing MachineComposition StatementCircuit CircuitBatch CircuitProducerModel
open PostfixModel PostfixAlignment

theorem coreTrace (tokens : List Token) (start next : Nat) (roots : List Nat)
    (gates : List Gate)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step PostfixMachine.program))^[
      PostfixMachine.tokensSteps start [] tokens +
        (recordsBits (gateRecords start gates)).length + 3]
      (some ⟨some .guard, PostfixMachine.initialState, coreInitial start tokens⟩) =
      some ⟨none, PostfixMachine.initialState,
        coreFinal next roots (recordsBits (gateRecords start gates))⟩ := by
  let bits := recordsBits (gateRecords start gates)
  let middle := PostfixMachine.boundaryTapes
    (PostfixMachine.outputTapes
      (Function.update (coreBase tokens) .remaining (encodeWord 0)) bits.reverse)
    next roots []
  have first := PostfixMachine.tokensTrace tokens (coreBase tokens) start [] next roots
    gates [] valid (by rfl)
  simp only [List.append_nil] at first
  have second := PostfixMachine.reverseTrace middle bits
    (by simp [middle, PostfixMachine.boundaryTapes, PostfixMachine.outputTapes])
    (by simp [middle, PostfixMachine.boundaryTapes, PostfixMachine.outputTapes, coreBase])
  have result := chain first second
  have frame : PostfixMachine.reversedTapes middle bits = coreFinal next roots bits := by
    funext tape
    cases tape <;> simp [PostfixMachine.reversedTapes, middle, coreFinal,
      PostfixMachine.finalTapes, PostfixMachine.boundaryTapes, PostfixMachine.outputTapes,
      coreBase]
  rw [frame] at result
  simpa only [coreInitial, bits, Nat.add_assoc] using result

theorem framed_coreTrace {σ : Type} (ambient : σ × Bool)
    (tokens : List Token) (start next : Nat) (roots : List Nat) (gates : List Gate)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step framedProgram))^[PostfixMachine.tokensSteps start [] tokens +
        (recordsBits (gateRecords start gates)).length + 3]
      (some ⟨some .guard, (ambient, none), coreInitial start tokens⟩) =
      some ⟨none, (ambient, none), coreFinal next roots (recordsBits (gateRecords start gates))⟩ :=
  liftSuccessfulTrace PostfixMachine.machine.step (TM2.step framedProgram)
    (framedCfg ambient) (framed_step ambient) _ _ _ (coreTrace tokens start next roots gates valid)

theorem localTrace {σ : Type} (ambient : σ × Bool)
    (tokens : List Token) (start next : Nat) (roots : List Nat) (gates : List Gate)
    (oldRecords oldRoots : List Bool)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step program))^[steps tokens start roots gates oldRoots]
      (some ⟨some .reverseTokens, (ambient, none), initialLocal start tokens oldRecords oldRoots⟩) =
      some ⟨none, (ambient, none),
        finalLocal next roots (recordsBits (gateRecords start gates)) oldRecords⟩ := by
  let bits := recordsBits (gateRecords start gates)
  let initial := initialLocal start tokens oldRecords oldRoots
  let ready := lowerFill (extras oldRecords oldRoots) (coreInitial start tokens)
  let compiled := lowerFill (extras oldRecords oldRoots) (coreFinal next roots bits)
  let merged := afterRecords next roots (bits.reverse ++ oldRecords) oldRoots
  let refreshed := afterRecords next roots (bits.reverse ++ oldRecords) []
  let unseeded := Function.update (finalLocal next roots bits oldRecords) (.lower .remaining) []
  have inputTransfer := (Reduction.MachineTransfer.transferAtInTime
    Tape.tokens (.lower .input) (by decide) id false .reverseTokens
    (some (.lower .guard)) program rfl initial ambient none).evals_in_steps
  have inputFrame : Reduction.MachineTransfer.tapesAt Tape.tokens (.lower .input) initial []
      ((initial .tokens).reverse.map id ++ initial (.lower .input)) = ready := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Reduction.MachineTransfer.tapesAt, initial,
        initialLocal, ready, lowerFill, coreInitial, PostfixMachine.boundaryTapes, coreBase, encodeWords]
    | tokens => simp [Reduction.MachineTransfer.tapesAt, initial, initialLocal, ready, lowerFill, extras]
    | records => simp [Reduction.MachineTransfer.tapesAt, initial, initialLocal, ready, lowerFill, extras]
    | rootTable => simp [Reduction.MachineTransfer.tapesAt, initial, initialLocal, ready, lowerFill, extras]
  change (advance (TM2.step program))^[(initial .tokens).length + 1]
    (some ⟨some .reverseTokens, (ambient, none), initial⟩) =
      some ⟨some (.lower .guard), (ambient, none), _⟩ at inputTransfer
  rw [inputFrame] at inputTransfer
  have hinputLength : (initial .tokens).length = (tokenBits tokens).length := by
    simp [initial, initialLocal]
  rw [hinputLength] at inputTransfer
  have lowering := ForestPlacement.trace localLowerPorts Label.lower (some .reverseRecords)
    (extras oldRecords oldRoots) framedProgram program (fun _ => rfl) _ _ _
    (framed_coreTrace ambient tokens start next roots gates valid)
  change (advance (TM2.step program))^[PostfixMachine.tokensSteps start [] tokens + bits.length + 3]
      (some ⟨some (.lower .guard), (ambient, none),
        ForestPlacement.fill localLowerPorts (extras oldRecords oldRoots) (coreInitial start tokens)⟩) =
      some ⟨some .reverseRecords, (ambient, none),
        ForestPlacement.fill localLowerPorts (extras oldRecords oldRoots) (coreFinal next roots bits)⟩ at lowering
  rw [fill_lower_eq, fill_lower_eq] at lowering
  have recordTransfer := (Reduction.MachineTransfer.transferAtInTime
    (Tape.lower .output) .records (by decide) id false .reverseRecords (some .drainRoots)
    program rfl compiled ambient none).evals_in_steps
  have recordFrame : Reduction.MachineTransfer.tapesAt (Tape.lower .output) .records compiled []
      ((compiled (.lower .output)).reverse.map id ++ compiled .records) = merged := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Reduction.MachineTransfer.tapesAt, compiled,
        lowerFill, extras, coreFinal, PostfixMachine.finalTapes, merged, afterRecords]
    | tokens => simp [Reduction.MachineTransfer.tapesAt, compiled, lowerFill, extras, merged, afterRecords]
    | records => simp [Reduction.MachineTransfer.tapesAt, compiled, lowerFill, extras,
        coreFinal, PostfixMachine.finalTapes, merged, afterRecords]
    | rootTable => simp [Reduction.MachineTransfer.tapesAt, compiled, lowerFill, extras, merged, afterRecords]
  change (advance (TM2.step program))^[(compiled (.lower .output)).length + 1]
    (some ⟨some .reverseRecords, (ambient, none), compiled⟩) =
      some ⟨some .drainRoots, (ambient, none), _⟩ at recordTransfer
  rw [recordFrame] at recordTransfer
  have hrecordLength : (compiled (.lower .output)).length = bits.length := by
    simp [compiled, lowerFill, coreFinal, PostfixMachine.finalTapes]
  rw [hrecordLength] at recordTransfer
  have draining := MachineDrain.drainTrace Tape.rootTable .drainRoots (some .rootGuard)
    program rfl merged (merged .rootTable) ambient none
  rw [Function.update_eq_self] at draining
  change (advance (TM2.step program))^[(merged .rootTable).length + 1]
    (some ⟨some .drainRoots, (ambient, none), merged⟩) =
      some ⟨some .rootGuard, (ambient, none), Function.update merged .rootTable []⟩ at draining
  have drainFrame : Function.update merged .rootTable [] = refreshed := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [merged, refreshed, afterRecords]
    | tokens => simp [merged, refreshed, afterRecords]
    | records => simp [merged, refreshed, afterRecords]
    | rootTable => simp [merged, refreshed, afterRecords]
  rw [drainFrame] at draining
  have hrootLength : (merged .rootTable).length = oldRoots.length := rfl
  rw [hrootLength] at draining
  have refresh := RootRefresh.refreshTrace (Tape.lower .roots) .rootTable (by decide)
    .rootGuard .rootStart .rootLoop (some .finish) program rfl rfl rfl
    refreshed roots [] ambient none
  have refreshInitial : Hastad.SourceMachine.fieldTapes (Tape.lower .roots) .rootTable
      refreshed (encodeWords roots) [] = refreshed := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
    | tokens => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
    | records => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
    | rootTable => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords]
  have refreshFinal : Hastad.SourceMachine.fieldTapes (Tape.lower .roots) .rootTable
      refreshed [] (encodeWords roots.reverse ++ []) = unseeded := by
    funext tape
    cases tape with
    | lower tape => cases tape <;> simp [Hastad.SourceMachine.fieldTapes, refreshed,
        afterRecords, unseeded, finalLocal]
    | tokens => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords, unseeded, finalLocal]
    | records => simp [Hastad.SourceMachine.fieldTapes, refreshed, afterRecords, unseeded, finalLocal]
    | rootTable => simp [Hastad.SourceMachine.fieldTapes, refreshed, unseeded, finalLocal]
  rw [refreshInitial, refreshFinal] at refresh
  have finish : (advance (TM2.step program))^[1]
      (some ⟨some .finish, (ambient, none), unseeded⟩) =
      some ⟨none, (ambient, none), finalLocal next roots bits oldRecords⟩ := by
    change some (TM2.stepAux (program .finish) (ambient, none) unseeded) = _
    simp [program, TM2.stepAux, unseeded, finalLocal, encodeWord, Function.update_idem]
  have total := chain (chain (chain (chain (chain inputTransfer lowering) recordTransfer) draining) refresh) finish
  have cost : (((((tokenBits tokens).length + 1 +
      (PostfixMachine.tokensSteps start [] tokens + bits.length + 3)) +
      (bits.length + 1)) + (oldRoots.length + 1)) + RootRefresh.steps roots) + 1 =
      steps tokens start roots gates oldRoots := by dsimp only [steps, bits]; omega
  simpa only [cost, initial, bits] using total

section Caller

variable {K Λ σ : Type} [DecidableEq K]

theorem traceAt (ports : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, target (labels label) = statement ports labels exit label)
    (base : K → List Bool) (ambient : σ × Bool) (tokens : List Token)
    (start next : Nat) (roots : List Nat) (gates : List Gate) (oldRecords oldRoots : List Bool)
    (valid : compileTokens start [] tokens = some (next, roots, gates)) :
    (advance (TM2.step target))^[steps tokens start roots gates oldRoots]
      (some ⟨some (labels .reverseTokens), (ambient, none),
        ForestPlacement.fill ports base (initialLocal start tokens oldRecords oldRoots)⟩) =
      some ⟨exit, (ambient, none), ForestPlacement.fill ports base
        (finalLocal next roots (recordsBits (gateRecords start gates)) oldRecords)⟩ :=
  ForestPlacement.trace ports labels exit base program target atLabels _ _ _
    (localTrace ambient tokens start next roots gates oldRecords oldRoots valid)

end Caller

end BinPackingGames.Foundations.Complexity.CookLevin.ForestStage

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TermMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.TermMachine

open Turing MachineComposition TransitionTemplate PostfixModel

theorem Frame.emit {input : Input} {base : Tape → List Bool}
    (frame : Frame input base) (tokens : List Token) : Frame input (emitTapes base tokens) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [emitTapes] using frame.cursorWord
  · simpa [emitTapes] using frame.capacityWord
  · simpa [emitTapes] using frame.rootsWord
  · intro tape ht
    have hc : tape ≠ .count := by intro h; subst tape; simp [work] at ht
    have ho : tape ≠ .reversed := by intro h; subst tape; simp [work] at ht
    rw [emitTapes_other base tokens tape hc ho]
    exact frame.clean tape ht

attribute [instance] Emitter.finite

namespace Emitter

variable {valid : Input → Prop} {output first second : Input → List Token}

def literalProgram (tokens : List Token) : Unit → TM2.Stmt Alphabet Unit State :=
  fun _ => Reduction.MachineSubstitution.pushWord .reversed (tokenBits tokens)
    (Reduction.MachineSubstitution.pushWord .count (List.replicate tokens.length true)
      (.load (fun _ => initialState) .halt))

theorem literalTrace (tokens : List Token) (base : Tape → List Bool) :
    (advance (TM2.step (literalProgram tokens)))^[1]
      (some ⟨some (), initialState, base⟩) =
      some ⟨none, initialState, emitTapes base tokens⟩ := by
  change some (TM2.stepAux (literalProgram tokens ()) initialState base) = _
  simp [literalProgram, Reduction.MachineSubstitution.stepAux_pushWord,
    TM2.stepAux, emitTapes]

def literal (valid : Input → Prop) (tokens : List Token) :
    Emitter valid (fun _ => tokens) where
  Label := Unit
  finite := inferInstance
  entry := ()
  program := literalProgram tokens
  steps := fun _ => 1
  constant := 1
  trace _ _ base _ := literalTrace tokens base
  bound input _ := by simp

def seqProgram (left : Emitter valid first) (right : Emitter valid second) :
    left.Label ⊕ right.Label → TM2.Stmt Alphabet (left.Label ⊕ right.Label) State
  | .inl l => MachineSubroutine.statement Sum.inl (some (.inr right.entry)) (left.program l)
  | .inr l => MachineSubroutine.statement Sum.inr none (right.program l)

def seq (left : Emitter valid first) (right : Emitter valid second) :
    Emitter valid (fun input => first input ++ second input) where
  Label := left.Label ⊕ right.Label
  finite := inferInstance
  entry := .inl left.entry
  program := seqProgram left right
  steps input := left.steps input + right.steps input
  constant := left.constant + right.constant
  trace input hv base frame := by
    have hl := MachineSubroutine.trace Sum.inl (some (.inr right.entry))
      left.program (seqProgram left right) (fun _ => rfl)
      (left.steps input) _ _ (left.trace input hv base frame)
    have hr := MachineSubroutine.trace Sum.inr none
      right.program (seqProgram left right) (fun _ => rfl)
      (right.steps input) _ _ (right.trace input hv (emitTapes base (first input))
        (frame.emit (first input)))
    simp only [MachineSubroutine.configuration, MachineSubroutine.label] at hl hr
    rw [Nat.add_comm (left.steps input), Function.iterate_add_apply, hl, hr,
      emitTapes_append]
  bound input hv := by
    have h := Nat.add_le_add (left.bound input hv) (right.bound input hv)
    simpa only [Nat.add_mul] using h

def congr (emitter : Emitter valid first) (equality : ∀ input, first input = second input) :
    Emitter valid second where
  Label := emitter.Label
  finite := emitter.finite
  entry := emitter.entry
  program := emitter.program
  steps := emitter.steps
  constant := emitter.constant
  trace input hv base frame := by
    simpa only [equality input] using emitter.trace input hv base frame
  bound := emitter.bound

theorem traceAt {Λ' : Type} (emitter : Emitter valid output)
    (labels : emitter.Label → Λ') (exit : Option Λ')
    (target : Λ' → TM2.Stmt Alphabet Λ' State)
    (code : ∀ label, target (labels label) =
      MachineSubroutine.statement labels exit (emitter.program label))
    (input : Input) (hv : valid input) (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step target))^[emitter.steps input]
      (some ⟨some (labels emitter.entry), initialState, base⟩) =
      some ⟨exit, initialState, emitTapes base (output input)⟩ := by
  have h := MachineSubroutine.trace labels exit emitter.program target code
    (emitter.steps input) _ _ (emitter.trace input hv base frame)
  simpa only [MachineSubroutine.configuration, MachineSubroutine.label] using h

end Emitter

attribute [instance] Selector.finite

def testProgram (within : Bool) (p : Position) :
    TestLabel → TM2.Stmt Alphabet TestLabel State
  | .position label => PositionMachine.statement .cursor .scratch .position p
      TestLabel.position (some (if within then .compare .scan else .atZero)) label
  | .compare label => MachineUnaryLessAt.statement compareSlots TestLabel.compare
      (some .drain) label
  | .atZero => .peek .position (fun _ head => (((), !(head.getD false)), none))
      (.goto fun _ => .drain)
  | .drain => MachineDrain.drain .position .drain none

def testSteps (within : Bool) (p : Position) (input : Input) : Nat :=
  PositionMachine.steps p input.cursor +
    (if within then MachineUnaryLessAt.steps (p.eval input.cursor) input.capacity else 1) +
    (p.eval input.cursor + 2)

theorem testSteps_le (within : Bool) (p : Position) (input : Input) :
    testSteps within p input ≤ (10 + 4 * positionDepth p) * (input.size + 1) := by
  have he := PositionMachine.steps_le_time p input.cursor
  simp only [PositionMachine.timePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at he
  have hp := position_le p input.cursor
  have hn := Nat.min_le_left (p.eval input.cursor) input.capacity
  have hs : input.cursor ≤ input.size := by simp [Input.size]; omega
  have hd : positionDepth p ≤ positionDepth p * (input.size + 1) := by
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  cases within <;> simp only [testSteps, Bool.false_eq_true,
    ite_false, ite_true, if_true, MachineUnaryLessAt.steps] <;> nlinarith

def affineAddress (p : Position) (coefficient offset : Nat) (input : Input) : Nat :=
  coefficient * p.eval input.cursor + offset

def affineSteps (p : Position) (coefficient offset : Nat) (input : Input) : Nat :=
  PositionMachine.steps p input.cursor + (2 * (p.eval input.cursor + 1) + 1) +
    (p.eval input.cursor + 2) +
      (MachinePreservingLookupClean.steps input.roots (affineAddress p coefficient offset input) +
        rootLookup input.roots (affineAddress p coefficient offset input) + 4)

theorem affineSteps_le (p : Position) (coefficient offset : Nat) (input : Input)
    (present : input.roots[affineAddress p coefficient offset input]? =
      some (rootLookup input.roots (affineAddress p coefficient offset input))) :
    affineSteps p coefficient offset input ≤ (30 + 3 * positionDepth p) * (input.size + 1) := by
  have he := PositionMachine.steps_le_time p input.cursor
  simp only [PositionMachine.timePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at he
  have hp := position_le p input.cursor
  have hl := MachinePreservingLookupClean.steps_le input.roots
    (affineAddress p coefficient offset input) _ present
  have hw := MachineLookupSpec.output_length_le input.roots
    (affineAddress p coefficient offset input) _ present
  rw [encodeWord_length] at hw
  have hs : input.cursor + (encodeWords input.roots).length ≤ input.size := by
    simp [Input.size]
  have hd : positionDepth p ≤ positionDepth p * (input.size + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold affineSteps
  nlinarith

namespace Emitter

variable {valid validLeft validRight : Input → Prop}
variable {yes no : Input → List Token} {predicate : Input → Bool}

abbrev ChoiceLabel (test : Selector predicate) (left : Emitter validLeft yes)
    (right : Emitter validRight no) := test.Label ⊕ (Unit ⊕ (left.Label ⊕ right.Label))

def choiceProgram (test : Selector predicate) (left : Emitter validLeft yes)
    (right : Emitter validRight no) : ChoiceLabel test left right →
      TM2.Stmt Alphabet (ChoiceLabel test left right) State
  | .inl l => MachineSubroutine.statement Sum.inl (some (.inr (.inl ()))) (test.program l)
  | .inr (.inl _) => .branch (fun s => s.1.2)
      (.load (fun _ => initialState) (.goto fun _ => .inr (.inr (.inl left.entry))))
      (.load (fun _ => initialState) (.goto fun _ => .inr (.inr (.inr right.entry))))
  | .inr (.inr (.inl l)) => MachineSubroutine.statement
      (fun label => .inr (.inr (.inl label))) none (left.program l)
  | .inr (.inr (.inr l)) => MachineSubroutine.statement
      (fun label => .inr (.inr (.inr label))) none (right.program l)

def choice (test : Selector predicate) (left : Emitter validLeft yes)
    (right : Emitter validRight no)
    (leftValid : ∀ input, valid input → predicate input = true → validLeft input)
    (rightValid : ∀ input, valid input → predicate input = false → validRight input) :
    Emitter valid (fun input => if predicate input then yes input else no input) where
  Label := ChoiceLabel test left right
  finite := inferInstance
  entry := .inl test.entry
  program := choiceProgram test left right
  steps input := test.steps input + 1 +
    (if predicate input then left.steps input else right.steps input)
  constant := test.constant + 1 + left.constant + right.constant
  trace input hv base frame := by
    have ht := MachineSubroutine.trace Sum.inl (some (.inr (.inl ())))
      test.program (choiceProgram test left right) (fun _ => rfl)
      (test.steps input) _ _ (test.trace input base frame)
    simp only [MachineSubroutine.configuration, MachineSubroutine.label] at ht
    cases hpred : predicate input with
    | false =>
      have dispatch : (advance (TM2.step (choiceProgram test left right)))^[1]
          (some ⟨some (.inr (.inl ())), (((), predicate input), none), base⟩) =
          some ⟨some (.inr (.inr (.inr right.entry))), initialState, base⟩ := by
        change some (TM2.stepAux _ _ _) = _
        simp [choiceProgram, TM2.stepAux, hpred]
      have body := MachineSubroutine.trace (fun label => .inr (.inr (.inr label))) none
        right.program (choiceProgram test left right) (fun _ => rfl)
        (right.steps input) _ _ (right.trace input (rightValid input hv hpred) base frame)
      simp only [MachineSubroutine.configuration, MachineSubroutine.label] at body
      simpa only [hpred, Bool.false_eq_true, ite_false] using
        trace_trans _ (trace_trans _ ht dispatch) body
    | true =>
      have dispatch : (advance (TM2.step (choiceProgram test left right)))^[1]
          (some ⟨some (.inr (.inl ())), (((), predicate input), none), base⟩) =
          some ⟨some (.inr (.inr (.inl left.entry))), initialState, base⟩ := by
        change some (TM2.stepAux _ _ _) = _
        simp [choiceProgram, TM2.stepAux, hpred]
      have body := MachineSubroutine.trace (fun label => .inr (.inr (.inl label))) none
        left.program (choiceProgram test left right) (fun _ => rfl)
        (left.steps input) _ _ (left.trace input (leftValid input hv hpred) base frame)
      simp only [MachineSubroutine.configuration, MachineSubroutine.label] at body
      simpa only [hpred, ite_true, if_true] using
        trace_trans _ (trace_trans _ ht dispatch) body
  bound input hv := by
    have ht := test.bound input
    have hs : 0 < input.size + 1 := Nat.succ_pos _
    cases hpred : predicate input with
    | false =>
      have hr := right.bound input (rightValid input hv hpred)
      simp only [Bool.false_eq_true, ite_false]
      nlinarith
    | true =>
      have hl := left.bound input (leftValid input hv hpred)
      simp only [ite_true, if_true]
      nlinarith

end Emitter

variable {K Λ σ : Type} {Γ : K → Type} [∀ k, DecidableEq (Γ k)]
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

def termTokens (indexing : ConfigIndex.Indexing Γ Λ σ) (term : Term Γ σ)
    (input : Input) : List Token :=
  term.tokens indexing input.roots input.capacity input.cursor

def globalTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (term : Global (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : List Token :=
  term.tokens indexing input.roots input.capacity input.cursor

end BinPackingGames.Foundations.Complexity.CookLevin.TermMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionArena
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

open StatementCircuit CircuitBatch PostfixModel PostfixAlignment

variable {inputs oldWidth newWidth width : Nat}

theorem recordsBits_append (first rest : List CircuitProducerModel.Record) :
    recordsBits (first ++ rest) = recordsBits first ++ recordsBits rest := by
  simp only [recordsBits, recordsWords, List.flatMap_append, encodeWords_append]

theorem step_roots (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth)) :
    (snapshot (f.step es)).roots =
      Batch.roots (snapshot f).current (List.ofFn es) := by
  apply List.ext_getElem
  · simp [snapshot]
  · intro i hi hj
    simp only [snapshot, List.getElem_ofFn, Frame.step, Batch.rootAt]

theorem compile_frameForest (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    compileTokens (next f) []
      (forestTokens (fun i => (f.wires i).val) (List.ofFn es)) =
      some (next (f.step es), (rootValues (f.step es)).reverse,
        Batch.gates (fun i => (f.wires i).val) (next f) (List.ofFn es)) := by
  have hr : rootValues (f.step es) = Batch.roots (next f) (List.ofFn es) :=
    step_roots f es
  rw [compile_forestTokens, hr]
  simp only [List.append_nil, next, Frame.step_gate_count, Nat.add_assoc]

theorem recordBits_step (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    recordBits (f.step es) = recordBits f ++
      recordsBits (gateRecords (next f)
        (Batch.gates (fun i => (f.wires i).val) (next f) (List.ofFn es))) := by
  simp only [recordBits, Frame.step, Fragment.append, gateRecords_append,
    recordsBits_append, next]

theorem snapshot_rootBits_length_le (f : Frame inputs width) :
    (snapshot f).rootBits.length ≤ width * ((snapshot f).current + 1) := by
  have h := encodeWords_length_le (snapshot f).roots (snapshot f).current
    (fun r hr => Nat.le_of_lt (snapshot_root_mem_lt f r hr))
  simpa only [Snapshot.rootBits, snapshot, List.length_ofFn] using h

theorem snapshot_records_length_le (f : Frame inputs width) :
    (snapshot f).reversedRecords.length ≤
      4 * f.fragment.gates.length * ((snapshot f).current + 5) := by
  have h := encodeWords_length_le
    (recordsWords (gateRecords inputs f.fragment.gates))
    (inputs + f.fragment.gates.length + 4)
    (gateRecords_fields_le inputs f.fragment.gates f.fragment.ordered)
  simpa only [snapshot, List.length_reverse, recordsBits, recordsWords_length,
    gateRecords_length, Nat.add_assoc] using h

theorem snapshot_lengths_le (f : Frame inputs width) (B : Nat)
    (hc : (snapshot f).current ≤ B) (hg : f.fragment.gates.length ≤ B)
    (hw : width ≤ B) :
    (snapshot f).currentBits.length ≤ 4 * (B + 6)^2 ∧
    (snapshot f).rootBits.length ≤ 4 * (B + 6)^2 ∧
    (snapshot f).reversedRecords.length ≤ 4 * (B + 6)^2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Snapshot.currentBits, encodeWord_length]
    nlinarith
  · apply (snapshot_rootBits_length_le f).trans
    have hm := Nat.mul_le_mul hw (Nat.add_le_add_right hc 1)
    nlinarith
  · apply (snapshot_records_length_le f).trans
    have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hg) (Nat.add_le_add_right hc 5)
    nlinarith

theorem stage_tokenBits_length_le (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) (B : Nat)
    (hc : (snapshot f).current ≤ B) (he : Batch.cost (List.ofFn es) ≤ B) :
    (tokenBits (forestTokens (fun i => (f.wires i).val) (List.ofFn es))).length ≤
      4 * (B + 6)^2 := by
  apply (forest_tokenBits_length_le _ _ (snapshot f).current
    (fun i => (f.wires i).isLt)).trans
  have hmax : max 5 (snapshot f).current + 1 ≤ B + 6 := by omega
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 2 he) hmax
  nlinarith

theorem timeFrame_gate_count (V : NPVerifier) (input : List Bool) (t : Nat) :
    (VerifierCircuit.timeFrame V input t).fragment.gates.length =
      Batch.cost (List.ofFn (VerifierCircuit.initialExpressions V input)) +
      t * Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input)) := by
  simp only [VerifierCircuit.timeFrame, Frame.repeat_gate_count,
    VerifierCircuit.initialFrame, Frame.step_gate_count, Frame.initial,
    Fragment.empty, List.length_nil, Nat.zero_add]

theorem timeFrame_gates_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    (VerifierCircuit.timeFrame V input t).fragment.gates.length ≤
      (VerifierCircuit.gatePolynomial V).eval input.length := by
  apply le_trans ?_ (VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input)
  rw [timeFrame_gate_count, VerifierCircuit.circuitOfVerifier_gate_count]
  have hm := Nat.mul_le_mul_right
    (Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input))) ht
  omega

theorem timeFrame_current_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    next (VerifierCircuit.timeFrame V input t) ≤ (budgetPolynomial V).eval input.length := by
  have hg := timeFrame_gates_le V input t ht
  have hb := budgetPolynomial_eval V input
  unfold next
  omega

theorem timeFrame_lengths_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    let s := snapshot (VerifierCircuit.timeFrame V input t)
    s.currentBits.length ≤ (tapePolynomial V).eval input.length ∧
    s.rootBits.length ≤ (tapePolynomial V).eval input.length ∧
    s.reversedRecords.length ≤ (tapePolynomial V).eval input.length := by
  dsimp only
  rw [tapePolynomial_eval]
  have hg := timeFrame_gates_le V input t ht
  have hb := budgetPolynomial_eval V input
  apply snapshot_lengths_le
  · change _ + _ ≤ _
    omega
  · omega
  · omega

theorem acceptance_tokens_length_le (V : NPVerifier) (input : List Bool) :
    (tokenBits (forestTokens
      (fun i => ((VerifierCircuit.timeFrame V input (V.horizon input.length)).wires i).val)
      (List.ofFn (fun _ : Fin 1 => VerifierCircuit.acceptanceExpr V input)))).length ≤
      (tapePolynomial V).eval input.length := by
  rw [tapePolynomial_eval]
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  rw [VerifierCircuit.circuitOfVerifier_gate_count] at hg
  have hp := timeFrame_gates_le V input (V.horizon input.length) le_rfl
  have hb := budgetPolynomial_eval V input
  apply stage_tokenBits_length_le
  · change _ + _ ≤ _
    omega
  · simp only [List.ofFn_succ, List.ofFn_zero, Batch.cost_cons, Batch.cost_nil,
      Nat.add_zero]
    omega

theorem finalFrame_lengths_le (V : NPVerifier) (input : List Bool) :
    let s := snapshot (finalFrame V input)
    s.currentBits.length ≤ (tapePolynomial V).eval input.length ∧
    s.rootBits.length ≤ (tapePolynomial V).eval input.length ∧
    s.reversedRecords.length ≤ (tapePolynomial V).eval input.length := by
  dsimp only
  rw [tapePolynomial_eval]
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  change (finalFrame V input).fragment.gates.length ≤ _ at hg
  have hb := budgetPolynomial_eval V input
  apply snapshot_lengths_le
  · change _ + _ ≤ _
    omega
  · omega
  · omega

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

end

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionArena

open Turing MachineComposition

abbrev Alphabet (_ : Tape) := Bool
abbrev State := TermMachine.State

def forestPorts : ForestStage.Tape ↪ Tape :=
  ⟨Sum.inl, Sum.inl_injective⟩

def termInput (S : Nat) (snapshot : ProducerInvariant.Snapshot) : TermMachine.Input :=
  ⟨0, S, snapshot.roots⟩

theorem termFrame (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) :
    TermMachine.Frame (termInput S snapshot)
      (fun tape => tapes base S remaining snapshot (termPorts tape)) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro tape ht
  cases tape <;> simp_all [TermMachine.work, termTape, tapes]

theorem fill_forest (base : Tape → List Bool) (contents : ForestStage.Tape → List Bool) :
    ForestPlacement.fill forestPorts base contents =
      fun tape => match tape with
      | .inl t => contents t
      | .inr t => base (.inr t) := by
  funext tape
  cases tape with
  | inl t => exact ForestPlacement.fill_at forestPorts base contents t
  | inr t =>
    exact ForestPlacement.fill_other forestPorts base contents (.inr t)
      (by intro i; simp [forestPorts])

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionArena

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

theorem clear_result (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (base : K → List Bool) (result : Nat)
    (hcoeff : ∀ i : Fin (width p), base (slots (.inr i)) = []) :
    clearFieldsTapes (fun k => (word p slots k).length) (indices p slots)
      (MachineHorner.resultTapes slots (prepared p slots base) result) =
      MachineHorner.resultTapes slots base result := by
  funext k
  rw [clearFieldsTapes_apply _ _ (indices_nodup p slots)]
  by_cases h : k ∈ indices p slots
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp [MachineHorner.resultTapes, slots.injective.eq_iff, prepared_digit,
      fieldWord, hcoeff]
  · by_cases hd : k = slots (.inl 3)
    · subst k
      simp [MachineHorner.resultTapes]
    · simp [h, MachineHorner.resultTapes, hd, prepared,
        prependFieldsTapes_apply _ _ (indices_nodup p slots)]

def steps (p : Polynomial Nat) (n : Nat) : Nat :=
  MachineHorner.steps n (digit p) (width p) + 2

end Eval

end BinPackingGames.Foundations.Hastad.SourceHeaderCounts

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierFront
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

variable {K Λ σ : Type}

variable [DecidableEq K]

def steps : List (Polynomial Nat) → Nat → Nat
  | [], _ => 0
  | p :: ps, n => Eval.steps p n + steps ps n

end BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation

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

namespace BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine

open Turing MachineComposition PostfixModel
open ClashMachine (State clean emitted emitted_append chain)
open PayloadCellsMachine (SymbolSpec)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

structure Ready (p : Ports K) (base : K → List Bool) (input : List Bool) (q S : Nat) : Prop where
  inputWord : base (p 0) = input
  boundWord : base (p 1) = encodeWord q
  capacityWord : base (p 2) = encodeWord S
  empty : WorkEmpty p base

theorem workEmpty_emitted (p : Ports K) (base : K → List Bool) (tokens : List Token)
    (h : WorkEmpty p base) : WorkEmpty p (emitted (p 3) (p 4) base tokens) := by
  intro j hj
  have h3 : j ≠ 3 := by intro h; subst j; norm_num at hj
  have h4 : j ≠ 4 := by intro h; subst j; norm_num at hj
  simpa [emitted, p.injective.eq_iff, h3, h4] using h j hj

theorem frame_emitted (p : Ports K) (base : K → List Bool) (m i c : Nat) (ts : List Token) :
    emitted (p 3) (p 4) (frame p base m i c) ts =
      frame p (emitted (p 3) (p 4) base ts) m i c :=
  PayloadRowsLoop.frame_emitted (loopPorts p) base m i c ts

theorem frame_seed (p : Ports K) (base : K → List Bool) (m i c : Nat) :
    frame p (Function.update base (p 8) (encodeWord 0)) m i c = frame p base m i c := by
  apply ext_ports p
  · intro j
    fin_cases j <;> simp [frame, PayloadRowsLoop.frame, loopPorts, loopMap, p.injective.eq_iff]
  · intro k hk
    simp [frame, PayloadRowsLoop.frame, loopPorts, loopMap, hk]

theorem seed_ready (p : Ports K) (base : K → List Bool) (q : Nat)
    (hq : base (p 1) = encodeWord q) (empty : WorkEmpty p base) :
    PayloadPresenceMachine.Ready (PayloadRowsLoop.rowPorts (loopPorts p))
      (Function.update base (p 8) (encodeWord 0)) q 0 := by
  have rowPort (j : Fin 9) : PayloadRowsLoop.rowPorts (loopPorts p) j =
      p (![1, 8, 9, 10, 11, 7, 12, 3, 4] j) := by
    simp only [PayloadRowsLoop.rowPorts, PayloadRowsLoop.rowMap]
    fin_cases j <;> rfl
  constructor
  · simpa [rowPort, p.injective.eq_iff] using hq
  · change Function.update base (p 8) (encodeWord 0) (p 8) = encodeWord 0
    exact Function.update_self _ _ _
  · intro j h0 h1 h7 h8
    fin_cases j <;> try contradiction
    · simpa [rowPort, p.injective.eq_iff] using empty 9 (by decide)
    · simpa [rowPort, p.injective.eq_iff] using empty 10 (by decide)
    · simpa [rowPort, p.injective.eq_iff] using empty 11 (by decide)
    · simpa [rowPort, p.injective.eq_iff] using empty 7 (by decide)
    · simpa [rowPort, p.injective.eq_iff] using empty 12 (by decide)

def statement (p : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (prefixTable : InputCellsMachine.TruthTable A) (payload : Fin A → SymbolSpec) (blank : List Token) :
    Label A → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .prefix l => CellsPrefixStage.statement (prefixPorts p) (prefixLabels labels)
      (some (labels .copyFirst)) prefixTable l
  | .copyFirst => Reduction.MachineTransfer.loopAt (p 1) (p 7) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (p 7) (p 1) (p 13) false
      (labels .copySecond) (some (labels .seed))
  | .seed => .push (p 8) (fun _ => false) (.goto fun _ => labels (.payload .guard))
  | .payload l => PayloadRowsLoop.statement (loopPorts p) (payloadLabels labels)
      (labels .padding) payload l
  | .padding => PaddingCellsMachine.statement (paddingPorts p) blank (labels .padding)
      (some (labels .cleanup))
  | .cleanup => .pop (p 13) (fun s _ => s)
      (.pop (p 6) (fun s _ => s) (.goto fun _ => labels .drain))
  | .drain => MachineDrain.drain (p 8) (labels .drain) exit

def Agrees (p : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
    (prefixTable : InputCellsMachine.TruthTable A) (payload : Fin A → SymbolSpec) (blank : List Token)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ)) : Prop :=
  ∀ l, program (labels l) = statement p labels exit prefixTable payload blank l

variable (p : Ports K) (labels : Label A ↪ Λ) (exit : Option Λ)
  (prefixTable : InputCellsMachine.TruthTable A) (payload : Fin A → SymbolSpec) (blank : List Token)
  (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
  (ha : Agrees p labels exit prefixTable payload blank program)

include ha

theorem prefixTrace (base : K → List Bool) (input : List Bool) (q S : Nat)
    (hS : input.length ≤ S) (ready : Ready p base input q S) (ambient : σ) :
    (advance (TM2.step program))^[2 * (S + 2) + ((A + 4) * input.length + 3)]
      (some ⟨some (labels (.prefix .capacityFirst)), clean ambient, base⟩) =
      some ⟨some (labels .copyFirst), clean ambient,
        Function.update (emitted (p 3) (p 4) base (InputCellsMachine.streamTokens prefixTable input))
          (p 6) (encodeWord (S - input.length))⟩ := by
  have h := CellsPrefixStage.trace (prefixPorts p) (prefixLabels labels)
    (some (labels .copyFirst)) prefixTable program (fun l => ha (.prefix l)) base input S hS
    ready.inputWord ready.capacityWord (ready.empty 5 (by decide))
    (ready.empty 6 (by decide)) (ready.empty 7 (by decide)) (ambient, false) none
  have ht : InputCellsCapacity.tapes (CellsPrefixStage.capacityPorts (prefixPorts p)) base
      (S - input.length) []
      ((tokenBits (InputCellsMachine.streamTokens prefixTable input)).reverse ++ base (p 3))
      (List.replicate (A * input.length) true ++ base (p 4)) =
      Function.update (emitted (p 3) (p 4) base (InputCellsMachine.streamTokens prefixTable input))
        (p 6) (encodeWord (S - input.length)) := by
    simp only [InputCellsCapacity.tapes, InputCellsCapacity.corePorts,
      CellsPrefixStage.capacityPorts, prefixPorts, prefixMap]
    change Function.update (Function.update (Function.update
      (Function.update base (p 6) (encodeWord (S - input.length))) (p 5) [])
        (p 3) ((tokenBits (InputCellsMachine.streamTokens prefixTable input)).reverse ++ base (p 3)))
      (p 4) (List.replicate (A * input.length) true ++ base (p 4)) = _
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [emitted, p.injective.eq_iff, ready.empty 5 (by decide)]
    · intro k hk
      simp [emitted, hk]
  rw [show prefixPorts p 2 = p 3 from rfl, show prefixPorts p 3 = p 4 from rfl, ht] at h
  exact h

theorem preparePayloadTrace (base : K → List Bool) (q c : Nat)
    (hq : base (p 1) = encodeWord q) (empty : WorkEmpty p base) (ambient : σ) :
    (advance (TM2.step program))^[2 * (q + 2) + 1]
      (some ⟨some (labels .copyFirst), clean ambient,
        Function.update base (p 6) (encodeWord c)⟩) =
      some ⟨some (labels (.payload .guard)), clean ambient, frame p base q 0 c⟩ := by
  let start := Function.update base (p 6) (encodeWord c)
  have hc := MachineCopy.copyTrace (p 1) (p 13) (p 7)
    (p.injective.ne (by decide)) (p.injective.ne (by decide)) (p.injective.ne (by decide))
    false (labels .copyFirst) (labels .copySecond) (some (labels .seed)) program
    (ha .copyFirst) (ha .copySecond) start
    (by simpa [start, p.injective.eq_iff] using empty 7 (by decide)) (ambient, false) none
  have hs : start (p 1) = encodeWord q := by simpa [start, p.injective.eq_iff] using hq
  have he : start (p 13) = [] := by simpa [start, p.injective.eq_iff] using empty 13 (by decide)
  rw [hs, he, List.append_nil, encodeWord_length] at hc
  have hseed : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seed), clean ambient,
        Function.update start (p 13) (encodeWord q)⟩) =
      some ⟨some (labels (.payload .guard)), clean ambient, frame p base q 0 c⟩ := by
    change some (TM2.stepAux (program (labels .seed)) _ _) = _
    rw [ha .seed]
    simp only [statement, TM2.stepAux]
    congr 1
    apply congrArg (fun tapes => (⟨some (labels (.payload .guard)), clean ambient, tapes⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ)))
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [start, frame, PayloadRowsLoop.frame, loopPorts, loopMap,
        p.injective.eq_iff, empty 8 (by decide), encodeWord] <;> first | done | (rw [Function.update_apply, if_pos (by rfl)])
    · intro k hk
      simp [start, frame, PayloadRowsLoop.frame, loopPorts, loopMap, hk]
  exact _root_.OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.chain hc hseed

theorem payloadTrace (base : K → List Bool) (q c : Nat)
    (hq : base (p 1) = encodeWord q) (empty : WorkEmpty p base) (ambient : σ) :
    (advance (TM2.step program))^[PayloadRowsLoop.steps payload q 0 q]
      (some ⟨some (labels (.payload .guard)), clean ambient, frame p base q 0 (c + q)⟩) =
      some ⟨some (labels .padding), clean ambient,
        frame p (emitted (p 3) (p 4) base (PayloadRowsLoop.tokens payload q 0 q)) 0 q c⟩ := by
  have h := PayloadRowsLoop.trace (loopPorts p) (payloadLabels labels) (labels .padding)
    payload program (fun l => ha (.payload l)) (Function.update base (p 8) (encodeWord 0))
    q 0 q c (by omega) (seed_ready p base q hq empty) ambient
  change (advance (TM2.step program))^[PayloadRowsLoop.steps payload q 0 q]
      (some ⟨some (labels (.payload .guard)), clean ambient,
        frame p (Function.update base (p 8) (encodeWord 0)) q 0 (c + q)⟩) =
      some ⟨some (labels .padding), clean ambient,
        emitted (p 3) (p 4) (frame p (Function.update base (p 8) (encodeWord 0)) 0 (0 + q) c)
          (PayloadRowsLoop.tokens payload q 0 q)⟩ at h
  simpa only [frame_seed, Nat.zero_add, frame_emitted] using h

theorem paddingTrace (base : K → List Bool) (q c : Nat) (ambient : σ) :
    (advance (TM2.step program))^[c + 1]
      (some ⟨some (labels .padding), clean ambient, frame p base 0 q c⟩) =
      some ⟨some (labels .cleanup), clean ambient,
        frame p (emitted (p 3) (p 4) base (PaddingCellsMachine.repeatedRows blank c)) 0 q 0⟩ := by
  have h := PaddingCellsMachine.trace (paddingPorts p) blank (labels .padding)
    (some (labels .cleanup)) program (ha .padding) (frame p base 0 q c) c []
    (base (p 3)) (base (p 4)) (ambient, false) none
  have hstart : PaddingCellsMachine.frame (paddingPorts p) (frame p base 0 q c)
      (encodeWord c ++ []) (base (p 3)) (base (p 4)) = frame p base 0 q c := by
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [PaddingCellsMachine.frame, OrClosure.frame,
        PaddingCellsMachine.corePorts, paddingPorts, paddingMap, frame, PayloadRowsLoop.frame,
        loopPorts, loopMap, p.injective.eq_iff] <;> first | done | (rw [Function.update_apply, if_pos (by rfl)])
    · intro k hk
      simp [PaddingCellsMachine.frame, OrClosure.frame, PaddingCellsMachine.corePorts,
        paddingPorts, paddingMap, frame, PayloadRowsLoop.frame, loopPorts, loopMap, hk]
  have hend : PaddingCellsMachine.frame (paddingPorts p) (frame p base 0 q c)
      (encodeWord 0 ++ [])
      ((tokenBits (PaddingCellsMachine.repeatedRows blank c)).reverse ++ base (p 3))
      (List.replicate (c * blank.length) true ++ base (p 4)) =
      frame p (emitted (p 3) (p 4) base (PaddingCellsMachine.repeatedRows blank c)) 0 q 0 := by
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [PaddingCellsMachine.frame, OrClosure.frame,
        PaddingCellsMachine.corePorts, paddingPorts, paddingMap, frame, PayloadRowsLoop.frame,
        loopPorts, loopMap, p.injective.eq_iff, emitted] <;> first | done | (rw [Function.update_apply, if_pos (by rfl)])
    · intro k hk
      simp [PaddingCellsMachine.frame, OrClosure.frame, PaddingCellsMachine.corePorts,
        paddingPorts, paddingMap, frame, PayloadRowsLoop.frame, loopPorts, loopMap, emitted, hk]
  simpa only [hstart, hend, clean] using h

theorem cleanupTrace (base : K → List Bool) (q : Nat) (empty : WorkEmpty p base) (ambient : σ) :
    (advance (TM2.step program))^[1 + (q + 2)]
      (some ⟨some (labels .cleanup), clean ambient, frame p base 0 q 0⟩) =
      some ⟨exit, clean ambient, base⟩ := by
  have hc : (advance (TM2.step program))^[1]
      (some ⟨some (labels .cleanup), clean ambient, frame p base 0 q 0⟩) =
      some ⟨some (labels .drain), clean ambient, Function.update base (p 8) (encodeWord q)⟩ := by
    change some (TM2.stepAux (program (labels .cleanup)) _ _) = _
    rw [ha .cleanup]
    simp only [statement, TM2.stepAux]
    congr 1
    apply congrArg (fun tapes => (⟨some (labels .drain), clean ambient, tapes⟩ :
      TM2.Cfg (Alphabet (K := K)) Λ (State σ)))
    apply ext_ports p
    · intro j
      fin_cases j <;> simp [frame, PayloadRowsLoop.frame, loopPorts, loopMap,
        p.injective.eq_iff, encodeWord, empty 6 (by decide), empty 13 (by decide)]
    · intro k hk
      simp [frame, PayloadRowsLoop.frame, loopPorts, loopMap, hk]
  have hd := MachineDrain.drainTrace (p 8) (labels .drain) exit program (ha .drain)
    base (encodeWord q) (ambient, false) none
  rw [encodeWord_length] at hd
  have hb : Function.update base (p 8) [] = base := by
    rw [← empty 8 (by decide), Function.update_eq_self]
  rw [hb] at hd
  exact _root_.OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.chain hc hd

omit ha in
def tokens (prefixTable : InputCellsMachine.TruthTable A) (payload : Fin A → SymbolSpec)
    (blank : List Token) (input : List Bool) (q S : Nat) : List Token :=
  InputCellsMachine.streamTokens prefixTable input ++ PayloadRowsLoop.tokens payload q 0 q ++
    PaddingCellsMachine.repeatedRows blank (S - input.length - q)

theorem trace (base : K → List Bool) (input : List Bool) (q S : Nat)
    (hS : input.length + q ≤ S) (ready : Ready p base input q S) (ambient : σ) :
    (advance (TM2.step program))^[steps payload input.length q S]
      (some ⟨some (labels (.prefix .capacityFirst)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (p 3) (p 4) base (tokens prefixTable payload blank input q S)⟩ := by
  let pre := InputCellsMachine.streamTokens prefixTable input
  let mid := PayloadRowsLoop.tokens payload q 0 q
  let post := PaddingCellsMachine.repeatedRows blank (S - input.length - q)
  let b₁ := emitted (p 3) (p 4) base pre
  let b₂ := emitted (p 3) (p 4) b₁ mid
  let b₃ := emitted (p 3) (p 4) b₂ post
  have e₁ : WorkEmpty p b₁ := workEmpty_emitted p base pre ready.empty
  have e₂ : WorkEmpty p b₂ := workEmpty_emitted p b₁ mid e₁
  have e₃ : WorkEmpty p b₃ := workEmpty_emitted p b₂ post e₂
  have q₁ : b₁ (p 1) = encodeWord q := by
    simpa [b₁, emitted, p.injective.eq_iff] using ready.boundWord
  have hp := prefixTrace p labels exit prefixTable payload blank program ha base input q S
    (by omega) ready ambient
  have hprep := preparePayloadTrace p labels exit prefixTable payload blank program ha b₁ q
    (S - input.length) q₁ e₁ ambient
  have hm := payloadTrace p labels exit prefixTable payload blank program ha b₁ q
    (S - input.length - q) q₁ e₁ ambient
  rw [show S - input.length - q + q = S - input.length by omega] at hm
  have hpad := paddingTrace p labels exit prefixTable payload blank program ha b₂ q
    (S - input.length - q) ambient
  have hc := cleanupTrace p labels exit prefixTable payload blank program ha b₃ q e₃ ambient
  have h := _root_.OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.chain (_root_.OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.chain (_root_.OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.chain (_root_.OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.chain hp hprep) hm) hpad) hc
  simpa only [steps, b₃, b₂, b₁, pre, mid, post,
    emitted_append (p 3) (p 4) (p.injective.ne (by decide : (3 : Fin 14) ≠ 4)), tokens,
    List.append_assoc] using h

end BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

open Turing

abbrev State := TermMachine.State
abbrev initialState : State := TermMachine.initialState

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionIteration
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceTemplate

open StatementCircuit VerifierCircuit PostfixModel PostfixAlignment InitializationTemplate

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceTemplate.instDecidableEqΛTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceTemplate.instDecidableEqσTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceTemplate.instDecidableEqΓTmBoolComputation
def mismatchTokens (expected : Bool) (wire : Nat) : List Token :=
  if expected then [.input wire, .not] else [.input wire]

def tokens (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) : List Token :=
  [.input (wire (Fin.last (width V input)))] ++
    (List.ofFn fun j : Fin (width V input) =>
      mismatchTokens (targetBit V input j) (wire j.castSucc)).flatten ++
    closeOr (width V input) ++ [.not, .and]

theorem mismatchTokens_eq (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) (j : Fin (width V input)) :
    mismatchTokens (targetBit V input j) (wire j.castSucc) =
      exprTokens wire (mismatchExpr V input j) := by
  by_cases h : configEncoding (capacity V input.length) (accepting V)
      ((bitEquiv V input).symm j) = true
  · simp [mismatchTokens, targetBit, mismatchExpr, exprTokens, h]
  · simp [mismatchTokens, targetBit, mismatchExpr, exprTokens, h]

theorem tokens_eq (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    tokens V input wire = exprTokens wire (acceptanceExpr V input) := by
  simp only [acceptanceExpr, exprTokens, exprTokens_disjoin,
    forestTokens_ofFn, List.length_ofFn]
  simp [tokens, mismatchTokens_eq, List.append_assoc]

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceTemplate

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionMachine

open Turing MachineComposition TransitionTemplate TermMachine PostfixModel

variable {K Λ σ : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

def listTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (terms : List (Template (Γ := Γ) (Λ := Λ) (σ := σ))) (input : Input) : List Token :=
  terms.flatMap fun term => globalTokens indexing term input

def prefixTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (terms : List (Template (Γ := Γ) (Λ := Λ) (σ := σ) × Bool))
    (input : Input) : List Token :=
  terms.flatMap fun term => globalTokens indexing term.1 input ++
    (if term.2 then [.not] else [])

def withCursor (input : Input) (cursor : Nat) : Input := { input with cursor := cursor }

def cursorTapes (base : Tape → List Bool) (cursor : Nat) : Tape → List Bool :=
  Function.update base .cursor (encodeWord cursor)

@[simp] theorem withCursor_cursor (input : Input) (cursor : Nat) :
    (withCursor input cursor).cursor = cursor := rfl

@[simp] theorem withCursor_capacity (input : Input) (cursor : Nat) :
    (withCursor input cursor).capacity = input.capacity := rfl

@[simp] theorem withCursor_roots (input : Input) (cursor : Nat) :
    (withCursor input cursor).roots = input.roots := rfl

@[simp] theorem withCursor_withCursor (input : Input) (first second : Nat) :
    withCursor (withCursor input first) second = withCursor input second := rfl

theorem Frame.cursor {input : Input} {base : Tape → List Bool}
    (frame : Frame input base) (cursor : Nat) :
    Frame (withCursor input cursor) (cursorTapes base cursor) := by
  refine ⟨by simp [cursorTapes], ?_, ?_, ?_⟩
  · simpa [cursorTapes] using frame.capacityWord
  · simpa [cursorTapes] using frame.rootsWord
  · intro tape ht
    have hc : tape ≠ .cursor := by intro h; subst tape; simp [work] at ht
    simpa [cursorTapes, hc] using frame.clean tape ht

@[simp] theorem cursorTapes_same {input : Input} {base : Tape → List Bool}
    (frame : Frame input base) : cursorTapes base input.cursor = base := by
  simp only [cursorTapes, ← frame.cursorWord, Function.update_eq_self]

@[simp] theorem cursorTapes_twice (base : Tape → List Bool) (first second : Nat) :
    cursorTapes (cursorTapes base first) second = cursorTapes base second := by
  simp [cursorTapes]

theorem emitTapes_cursor (base : Tape → List Bool) (cursor : Nat) (tokens : List Token) :
    emitTapes (cursorTapes base cursor) tokens = cursorTapes (emitTapes base tokens) cursor := by
  funext tape
  cases tape <;> simp [cursorTapes, emitTapes]

def Valid (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Prop :=
  indexing.width input.capacity + (if plan.carry then 1 else 0) ≤ input.roots.length

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem Valid.withCursor {indexing : ConfigIndex.Indexing Γ Λ σ}
    {plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)} {input : Input}
    (h : Valid indexing plan input) (cursor : Nat) :
    Valid indexing plan (withCursor input cursor) := h

def finalValid (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Prop :=
  Valid indexing plan input ∧ input.cursor = input.capacity

def finalTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : List Token :=
  if plan.carry then [.input (rootLookup input.roots
    (affineAddress .current indexing.symbolCount (indexing.labelCount + indexing.stateCount) input))]
  else []

def dataSize (input : Input) : Nat := input.capacity + (encodeWords input.roots).length

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan

open StatementCircuit TransitionTemplate AcceptanceTemplate
open PostfixModel VerifierCircuit TermMachine

local instance instFintypeΛTmBoolComputation_r27320e_1 (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance instFintypeσTmBoolComputation_r27320e_1 (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance instFintypeΓTmBoolComputation_r27320e_1 (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan.instDecidableEqΛTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan.instDecidableEqσTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan.instDecidableEqΓTmBoolComputation
def mismatchForest (V : NPVerifier) (roots : List Nat) (S : Nat) : List Token :=
  (outputOrder (indexing V) S).flatMap fun bit =>
    mismatchTokens (configEncoding S (accepting V) bit)
      (configWire (indexing V) roots S bit)

theorem mismatchForest_circuit (V : NPVerifier) (input : List Bool) (roots : List Nat) :
    mismatchForest V roots (capacity V input.length) =
      (List.ofFn fun j : Fin (width V input) =>
        mismatchTokens (targetBit V input j) (rootLookup roots j.val)).flatten := by
  simp only [mismatchForest, outputOrder, List.flatMap_def,
    Function.comp_def, configWire, Equiv.apply_symm_apply, targetBit,
    ← List.ofFn_eq_map, List.map_ofFn, bitEquiv]

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionIterationTime
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

open Turing MachineComposition TermMachine TransitionTemplate PostfixModel

def widthAddress (coefficient offset : Nat) (input : Input) : Nat :=
  coefficient * input.capacity + offset

def rootSteps (coefficient offset : Nat) (input : Input) : Nat :=
  (2 * (input.capacity + 1) + 1) +
    (MachinePreservingLookupClean.steps input.roots (widthAddress coefficient offset input) +
      rootLookup input.roots (widthAddress coefficient offset input) + 4)

def closurePorts : OrClosure.Ports Tape :=
  ⟨.position, .reversed, .count, by decide, by decide, by decide⟩

def closureProgram (coefficient offset : Nat) :
    ClosureLabel → TM2.Stmt Alphabet ClosureLabel State
  | .seed => MachineUnaryAffineAt.seed .position offset .scan
  | .scan => MachineUnaryAffineAt.scan .capacity .scratch .position coefficient .scan .restore
  | .restore => Reduction.MachineTransfer.loopAt .scratch .capacity id false .restore (some .orSeed)
  | .orSeed => OrClosure.seed closurePorts .orLoop
  | .orLoop => OrClosure.loop closurePorts .orLoop (some .finish)
  | .finish => .pop .position (fun _ _ => initialState) .halt

def closureSteps (coefficient offset : Nat) (input : Input) : Nat :=
  (2 * (input.capacity + 1) + 1) + (widthAddress coefficient offset input + 2) + 1

theorem closureSteps_le (coefficient offset : Nat) (input : Input) :
    closureSteps coefficient offset input ≤ (coefficient + offset + 8) * (input.size + 1) := by
  have hs : input.capacity ≤ input.size := by simp [Input.size]; omega
  have hmul := Nat.mul_le_mul_left coefficient hs
  unfold closureSteps widthAddress
  nlinarith

section Indexed

end Indexed

open VerifierCircuit AcceptanceTemplate

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerTime

open CircuitBatch StatementCircuit PostfixModel PostfixAlignment ProducerInvariant
open MachineComposition VerifierCircuit
open scoped BigOperators

variable {inputs oldWidth newWidth : Nat}

local instance iterationTimeVerifierLabelFintype_r27320e_1 (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype_r27320e_1 (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype_r27320e_1 (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq_r27320e_1 (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq_r27320e_1 (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq_r27320e_1 (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _
def forestSteps (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth))
    (oldRoots : List Bool) : Nat :=
  ForestStage.steps (forestTokens (fun i => (f.wires i).val) (List.ofFn es))
    (next f) (Batch.roots (next f) (List.ofFn es)).reverse
    (Batch.gates (fun i => (f.wires i).val) (next f) (List.ofFn es)) oldRoots

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerTime

end

end OAI
end


