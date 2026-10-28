-- Prove2me | Definitions.Def_OAIQ082C013
-- name    : OAIQ082C013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:34:21.276811+00:00
-- url     : https://prove2.me/theorems/b2a9e27f-58cb-4d8e-b810-4608f2139970
-- title:
--   Definitions bundle OAIQ082C013 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 394 declarations of OpenAI's Lean: 171 definitions, 10 inductive types or structures, 3 instances and 210 theorems. The definitions and types are `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Full.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Full.Ready`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Full.closurePorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Full.copyExit`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Full.frame`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Full.loopTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Pair.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Row.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine.Row.tokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly.CodeLabel`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly.placedControl`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.alphabetDecidable`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.clashRowTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.clashTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.labelDecidable`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.nonemptyTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.stateDecidable`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate.validityTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InputFrame.cfg`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InputFrame.machine`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.PolynomialMachine.timePolynomial`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.alphabetDecidable`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.alphabetFinite`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.labelDecidable`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.labelFinite`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.stateDecidable`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant.stateFinite`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.DataBits.Realizes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.ResultBits.Realizes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate.Data.Matches`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate.Result.Matches`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate.forestTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Nonempty.Ready`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Nonempty.closurePorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.SelectorLoop.tokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding.pairCell`, `OAI.BinPackingGames.Foundations.Hastad.SourceGap.ClauseGap`, `OAI.BinPackingGames.Foundations.Hastad.SourceMachine.fourTapes` and 141 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_BinaryOrderMachine`, `BinPacking_Arithmetic_BinaryPowerMachine`, `BinPacking_Arithmetic_BinaryTallyMachine`, `BinPacking_Arithmetic_BinaryToTallyMachine`, `BinPacking_Arithmetic_NatExpressionBounds`, `BinPacking_Arithmetic_NatExpressionBranch`, `BinPacking_Computation_MachineFiniteAlphabet`, `BinPacking_Computation_MachineHorner`, `BinPacking_CookLevin_CircuitProducer`, `BinPacking_CookLevin_ClashMachine`, `BinPacking_CookLevin_ConfigIndex`, `BinPacking_CookLevin_MachineCircuit`, `BinPacking_CookLevin_OutputOrder`, `BinPacking_CookLevin_PolynomialMachine`, `BinPacking_CookLevin_ProducerFrontStage`, `BinPacking_CookLevin_TransitionArena`, `BinPacking_CookLevin_ValidityComposition`, `BinPacking_CookLevin_ValidityMachine`, `BinPacking_CookLevin_VerifierCircuit`, `BinPacking_CookLevin_VerifierFront`, `BinPacking_Information_SourceFieldArray`, `BinPacking_Information_SourceNonempty`, `BinPacking_Machines_DropPackingBoundMachine`, `BinPacking_Machines_PackingPowerProgram`, `BinPacking_PCP_CloudRounding`, `BinPacking_PCP_PCPIteration`, `BinPacking_PCP_PoweringFinalConstants`, `BinPacking_PCP_PoweringMomentBound`, `BinPacking_PCP_PoweringTableSemantics`, `BinPacking_PCP_PreprocessingRegularSoundness`, `BinPacking_PCP_Queries`, `BinPacking_Packing_CapacityScan`, `BinPacking_Search_ExtensionAgreementMachine`, `BinPacking_Search_ExtensionCapacityBounds`, `BinPacking_Search_ExtensionMachineSpace`, `BinPacking_Search_ExtensionShapeMachine`, `BinPacking_Search_ExtensionValidationMachine`, `BinPacking_Search_ExtensionVerifierPipeline`, `BinPacking_Search_SearchInitialItemsMachine`, `BinPacking_Search_SearchInitializeEncoding`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C005`, `OAIQ082C006`, `OAIQ082C007` and `OAIQ082C008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C017`, `OAIQ082C019`, `OAIQ082C020`, `OAIQ082C021` and `OAIQ082C022`.
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

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_CloudRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

def rightFromPivot (G : PortGraph V D) :
    (n : Nat) → Fin (n + 1) → Edge V D → (Fin n → D) → V
  | 0, _, e, _ => next G e.1 e.2
  | n + 1, k, e, r => Fin.cases
      (wordEnd G (n + 1) (next G e.1 e.2) r)
      (fun j => rightFromPivot G n j e (fun m => r m.succ)) k

end BinPackingGames.Foundations.PCP.PoweringWalks

namespace BinPackingGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

instance finiteBall [Finite D] (G : PortGraph V D) (t : Nat) (v : V) :
    Finite (Ball G t v) :=
  Finite.of_surjective (wordToBall G t v) (wordToBall_surjective G t v)

def encode (G : PortGraph V D) (t : Nat) (v : V) (ℓ : Ball G t v → A) :
    PaddedLabel D t A := fun w => ℓ (wordToBall G t v w)

end BinPackingGames.Foundations.PCP.PoweringLabels

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineFiniteAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

theorem sequential_machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (hfirst : FiniteAlphabet first) (hsecond : FiniteAlphabet second) :
    FiniteAlphabet (MachineSequential.machine first second relabel fallback) := by
  intro tape
  rcases tape with tape | tape | tape
  · exact hfirst tape
  · exact hsecond tape
  · exact input_finite second

theorem compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.compose first second fallback).tm := by
  exact sequential_machine first.tm second.tm
    (fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol))
    (second.inputAlphabet.symm fallback) hfirst hsecond

theorem composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.composeBits first second).tm :=
  compose first second false hfirst hsecond

theorem repeat_machine (body : FinTM2)
    (input : body.Γ body.k₀ ≃ Bool) (output : body.Γ body.k₁ ≃ Bool)
    (hbody : FiniteAlphabet body) :
    FiniteAlphabet (MachineRepeat.machine body input output) := by
  intro tape
  cases tape with
  | inl tape => exact hbody tape
  | inr _ => exact input_finite body

end BinPackingGames.Foundations.Complexity.MachineFiniteAlphabet

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryOrderMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryOrderMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinPackingCompleteness.BinaryEncoding (bitsValue bitsValue_bits)

section Preserving

variable {K Λ σ : Type} [DecidableEq K]

def preservingInstruction (slots : Fin 5 ↪ K) (labels : PreserveLabel → Λ)
    (exits : Ordering → Option Λ) : PreserveLabel → TM2.Stmt (Alphabet K) Λ (State σ)
  | .leftOut => loopAt (slots 0) (slots 4) id false
      (labels .leftOut) (some (labels .leftBack))
  | .leftBack => MachineCopy.forkLoop (slots 4) (slots 0) (slots 2) false
      (labels .leftBack) (some (labels .rightOut))
  | .rightOut => loopAt (slots 1) (slots 4) id false
      (labels .rightOut) (some (labels .rightBack))
  | .rightBack => MachineCopy.forkLoop (slots 4) (slots 1) (slots 3) false
      (labels .rightBack) (some (labels .compare))
  | .compare => loop (slots 2) (slots 3) (labels .compare) exits

theorem preservingTrace (slots : Fin 5 ↪ K) (labels : PreserveLabel → Λ)
    (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = preservingInstruction slots labels exits label)
    (base : K → List Bool) (leftEmpty : base (slots 2) = [])
    (rightEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[
        preservingSteps (base (slots 0)).length (base (slots 1)).length]
      (some ⟨some (labels .leftOut), clean ambient, base⟩) =
      some ⟨exits (orderNat (bitsValue (base (slots 0))) (bitsValue (base (slots 1))) .eq),
        clean ambient, base⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  let afterLeft := Function.update base (slots 2) (base (slots 0))
  let afterBoth := Function.update afterLeft (slots 3) (base (slots 1))
  have leftRun : (MachineComposition.advance (TM2.step program))^[
      2 * ((base (slots 0)).length + 1)]
      (some ⟨some (labels .leftOut), clean ambient, base⟩) =
      some ⟨some (labels .rightOut), clean ambient, afterLeft⟩ := by
    have run := MachineCopy.copyTrace (slots 0) (slots 2) (slots 4)
      (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
      (labels .leftOut) (labels .leftBack) (some (labels .rightOut)) program
      (atLabels .leftOut) (atLabels .leftBack) base scratchEmpty ((ambient, .eq), none) none
    simpa only [leftEmpty, List.append_nil, clean, afterLeft] using run
  have rightWord : afterLeft (slots 1) = base (slots 1) := by
    simp [afterLeft, hd 1 2 (by decide)]
  have rightCopyEmpty : afterLeft (slots 3) = [] := by
    simp [afterLeft, hd 3 2 (by decide), rightEmpty]
  have scratchStillEmpty : afterLeft (slots 4) = [] := by
    simp [afterLeft, hd 4 2 (by decide), scratchEmpty]
  have rightRun : (MachineComposition.advance (TM2.step program))^[
      2 * ((base (slots 1)).length + 1)]
      (some ⟨some (labels .rightOut), clean ambient, afterLeft⟩) =
      some ⟨some (labels .compare), clean ambient, afterBoth⟩ := by
    have run := MachineCopy.copyTrace (slots 1) (slots 3) (slots 4)
      (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) false
      (labels .rightOut) (labels .rightBack) (some (labels .compare)) program
      (atLabels .rightOut) (atLabels .rightBack) afterLeft scratchStillEmpty
      ((ambient, .eq), none) none
    simpa only [rightWord, rightCopyEmpty, List.append_nil, clean, afterBoth] using run
  have leftCopied : afterBoth (slots 2) = base (slots 0) := by
    simp [afterBoth, afterLeft, hd 2 3 (by decide)]
  have rightCopied : afterBoth (slots 3) = base (slots 1) := by
    simp [afterBoth]
  have restored : tapesAt (slots 2) (slots 3) afterBoth [] [] = base := by
    funext k
    by_cases hl : k = slots 2
    · subst k
      simp [tapesAt, hd 2 3 (by decide), leftEmpty]
    · by_cases hr : k = slots 3
      · subst k
        simp [tapesAt, rightEmpty]
      · simp [tapesAt, afterBoth, afterLeft, hl, hr]
  have comparisonRun := compareTrace_fromTapes (slots 2) (slots 3)
    (hd 2 3 (by decide)) (labels .compare) exits program (atLabels .compare) afterBoth ambient
  rw [leftCopied, rightCopied, restored] at comparisonRun
  have combined := joinTrace (joinTrace leftRun rightRun) comparisonRun
  simpa only [preservingSteps, Nat.add_assoc] using combined

def preservingInTime (slots : Fin 5 ↪ K) (labels : PreserveLabel → Λ)
    (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = preservingInstruction slots labels exits label)
    (base : K → List Bool) (leftEmpty : base (slots 2) = [])
    (rightEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exits (orderNat (bitsValue (base (slots 0))) (bitsValue (base (slots 1))) .eq),
        clean ambient, base⟩)
      (preservingSteps (base (slots 0)).length (base (slots 1)).length) where
  steps := preservingSteps (base (slots 0)).length (base (slots 1)).length
  evals_in_steps := preservingTrace slots labels exits program atLabels base
    leftEmpty rightEmpty scratchEmpty ambient
  steps_le_m := Nat.le_refl _

def preservingNatInTime (slots : Fin 5 ↪ K) (labels : PreserveLabel → Λ)
    (exits : Ordering → Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLabels : ∀ label, program (labels label) = preservingInstruction slots labels exits label)
    (base : K → List Bool) (a b : Nat)
    (leftWord : base (slots 0) = a.bits) (rightWord : base (slots 1) = b.bits)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (scratchEmpty : base (slots 4) = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exits (orderNat a b .eq), clean ambient, base⟩)
      (preservingSteps a.size b.size) := by
  simpa only [leftWord, rightWord, bitsValue_bits, Nat.size_eq_bits_len] using
    preservingInTime slots labels exits program atLabels base leftEmpty rightEmpty scratchEmpty ambient

end Preserving

end BinPackingGap.BinaryOrderMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryTallyMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.UnaryToBinaryMachine

open Turing BinPackingGames.Foundations.Complexity
open MachineComposition BinaryArithmetic
open BinPackingGames.Reduction.MachineTransfer

theorem increment_ne_nil (bits : List Bool) : increment bits ≠ [] := by
  cases bits with
  | nil => simp [increment]
  | cons bit bits => cases bit <;> simp [increment]

theorem bitValue_increment (bits : List Bool) :
    bitValue (increment bits) = bitValue bits + 1 := by
  induction bits with
  | nil => simp [increment, Nat.bit]
  | cons bit bits ih =>
      cases bit <;> simp [increment, Nat.bit, ih]
      omega

theorem canonical_increment {bits : List Bool} (h : Canonical bits) :
    Canonical (increment bits) := by
  revert h
  induction bits with
  | nil => intro h; simp [increment, Canonical]
  | cons bit bits ih =>
      intro h
      cases bit with
      | false => exact ⟨h.1, fun _ => rfl⟩
      | true => exact ⟨ih h.1, fun hnil => False.elim (increment_ne_nil bits hnil)⟩

theorem increment_bits (n : Nat) : increment n.bits = (n + 1).bits := by
  have h := bits_bitValue (canonical_increment (canonical_bits n))
  simpa only [bitValue_increment, bitValue_bits] using h.symm

theorem incrementCost_le (bits : List Bool) :
    incrementCost bits ≤ 2 * bits.length + 2 := by
  induction bits with
  | nil => simp [incrementCost]
  | cons bit bits ih =>
      cases bit <;> simp [incrementCost]
      omega

theorem steps_le (n initial : Nat) :
    steps n initial ≤ n * (2 * (initial + n) + 3) + 1 := by
  induction n generalizing initial with
  | zero => simp [steps]
  | succ n ih =>
      have hcost := incrementCost_le initial.bits
      have hsize := size_le_self initial
      have hnext := ih (initial + 1)
      rw [Nat.size_eq_bits_len] at hcost
      simp only [steps]
      nlinarith

variable {K Λ A : Type} [DecidableEq K]

variable (source output scratch : K)
variable (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)

include hOC in
@[simp] theorem tapes_output (base : K → List Bool) (input binary work : List Bool) :
    tapes source output scratch base input binary work output = binary := by
  simp [tapes, hOC]

@[simp] theorem tapes_scratch (base : K → List Bool) (input binary work : List Bool) :
    tapes source output scratch base input binary work scratch = work := by
  simp [tapes]

include hSO hSC hOC in
theorem update_source (base : K → List Bool) (input binary work next : List Bool) :
    Function.update (tapes source output scratch base input binary work) source next =
      tapes source output scratch base next binary work := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapes, hSO, hSC]
  · by_cases ho : k = output
    · subst k; simp [tapes, hs, hOC]
    · by_cases hc : k = scratch
      · subst k; simp [tapes, hs]
      · simp [tapes, hs, ho, hc]

include hOC in
theorem update_output (base : K → List Bool) (input binary work next : List Bool) :
    Function.update (tapes source output scratch base input binary work) output next =
      tapes source output scratch base input next work := by
  funext k
  by_cases ho : k = output
  · subst k; simp [tapes, hOC]
  · by_cases hc : k = scratch
    · subst k; simp [tapes, ho]
    · simp [tapes, ho, hc]

theorem update_scratch (base : K → List Bool) (input binary work next : List Bool) :
    Function.update (tapes source output scratch base input binary work) scratch next =
      tapes source output scratch base input binary next := by
  simp [tapes]

variable (labels : Label → Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
variable (base : K → List Bool) (ambient : A)

include hSO hSC hOC atLabels

theorem scanStep (bit : Bool) (input binary work : List Bool) :
    TM2.step program
      ⟨some (labels .scan), (ambient, none),
        tapes source output scratch base (bit :: input) binary work⟩ =
      some ⟨if bit then some (labels .carry) else exit, (ambient, none),
        tapes source output scratch base input binary work⟩ := by
  change some (TM2.stepAux (program (labels .scan)) _ _) = _
  rw [atLabels .scan]
  cases bit <;> cases exit <;>
    simp [instruction, finish, TM2.stepAux,
      tapes_source, hSO, hSC, hOC, update_source]

omit hSO hSC in
theorem carryStep_nil (input work : List Bool) :
    TM2.step program
      ⟨some (labels .carry), (ambient, none),
        tapes source output scratch base input [] work⟩ =
      some ⟨some (labels .restore), (ambient, none),
        tapes source output scratch base input [true] work⟩ := by
  change some (TM2.stepAux (program (labels .carry)) _ _) = _
  rw [atLabels .carry]
  simp [instruction, finish, TM2.stepAux, tapes_output, hOC, update_output]

omit hSO hSC in
theorem carryStep_false (input binary work : List Bool) :
    TM2.step program
      ⟨some (labels .carry), (ambient, none),
        tapes source output scratch base input (false :: binary) work⟩ =
      some ⟨some (labels .restore), (ambient, none),
        tapes source output scratch base input (true :: binary) work⟩ := by
  change some (TM2.stepAux (program (labels .carry)) _ _) = _
  rw [atLabels .carry]
  simp [instruction, finish, TM2.stepAux, tapes_output, hOC, update_output]

omit hSO hSC in
theorem carryStep_true (input binary work : List Bool) :
    TM2.step program
      ⟨some (labels .carry), (ambient, none),
        tapes source output scratch base input (true :: binary) work⟩ =
      some ⟨some (labels .carry), (ambient, none),
        tapes source output scratch base input binary (false :: work)⟩ := by
  change some (TM2.stepAux (program (labels .carry)) _ _) = _
  rw [atLabels .carry]
  simp [instruction, finish, TM2.stepAux, tapes_output, tapes_scratch,
    hOC, update_output, update_scratch]

omit hSO hSC in
theorem restoreTrace (input binary work : List Bool) :
    (advance (TM2.step program))^[work.length + 1]
      (some ⟨some (labels .restore), (ambient, none),
        tapes source output scratch base input binary work⟩) =
      some ⟨some (labels .scan), (ambient, none),
        tapes source output scratch base input (work.reverse ++ binary) []⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet (K := K)) scratch output hOC.symm
    id false (labels .restore) (some (labels .scan)) program (atLabels .restore)
    (tapes source output scratch base input binary work) ambient none
  have next_eq : nextAt output program = advance (TM2.step program) := by
    funext state
    rfl
  rw [next_eq] at h
  simpa only [tapes_scratch, tapes_output source output scratch hOC,
    List.map_id_fun, id_eq, tapesAt, update_scratch,
    update_output source output scratch hOC] using h

omit hSO hSC in
theorem incrementTrace (input binary work : List Bool) :
    (advance (TM2.step program))^[incrementCost binary + work.length]
      (some ⟨some (labels .carry), (ambient, none),
        tapes source output scratch base input binary work⟩) =
      some ⟨some (labels .scan), (ambient, none),
        tapes source output scratch base input (work.reverse ++ increment binary) []⟩ := by
  induction binary generalizing work with
  | nil =>
      have first := carryStep_nil source output scratch hOC
        labels exit program atLabels base ambient input work
      have second := restoreTrace source output scratch hOC
        labels exit program atLabels base ambient input [true] work
      have full := joinTrace (oneStepTrace first) second
      have clock : 1 + (work.length + 1) = 2 + work.length := by omega
      rw [clock] at full
      simpa only [incrementCost, increment] using full
  | cons bit binary ih =>
      cases bit with
      | false =>
          have first := carryStep_false source output scratch hOC
            labels exit program atLabels base ambient input binary work
          have second := restoreTrace source output scratch hOC
            labels exit program atLabels base ambient input (true :: binary) work
          have full := joinTrace (oneStepTrace first) second
          have clock : 1 + (work.length + 1) = 2 + work.length := by omega
          rw [clock] at full
          simpa only [incrementCost, increment] using full
      | true =>
          have first := carryStep_true source output scratch hOC
            labels exit program atLabels base ambient input binary work
          have second := ih (false :: work)
          have full := joinTrace (oneStepTrace first) second
          have clock : 1 + (incrementCost binary + (false :: work).length) =
              (incrementCost binary + 2) + work.length := by
            simp only [List.length_cons]
            omega
          rw [clock] at full
          simpa only [incrementCost, increment, List.reverse_cons,
            List.append_assoc, List.singleton_append] using full

theorem convertTrace (n initial : Nat) (suffix : List Bool) :
    (advance (TM2.step program))^[steps n initial]
      (some ⟨some (labels .scan), (ambient, none),
        tapes source output scratch base (encodeWord n ++ suffix) initial.bits []⟩) =
      some ⟨exit, (ambient, none),
        tapes source output scratch base suffix (initial + n).bits []⟩ := by
  induction n generalizing initial with
  | zero =>
      simpa only [steps, encodeWord, List.replicate_zero, List.nil_append,
        List.singleton_append, Nat.add_zero, Bool.false_eq_true, ↓reduceIte,
        Function.iterate_one, advance_some] using
        scanStep source output scratch hSO hSC hOC labels exit program atLabels base ambient
          false suffix initial.bits []
  | succ n ih =>
      have first := scanStep source output scratch hSO hSC hOC
        labels exit program atLabels base ambient true (encodeWord n ++ suffix) initial.bits []
      have second := incrementTrace source output scratch hOC
        labels exit program atLabels base ambient (encodeWord n ++ suffix) initial.bits []
      simp only [↓reduceIte] at first
      simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append,
        increment_bits] at second
      have third := ih (initial + 1)
      have full := joinTrace (joinTrace
        (oneStepTrace first) second) third
      simpa only [steps, encodeWord, List.replicate_succ, List.cons_append,
        Nat.add_assoc, Nat.add_comm 1 n] using full

end BinPackingGap.UnaryToBinaryMachine

namespace BinPackingGap.BinaryTallyMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinaryAddMachine (State clean)

variable {K Λ A : Type} [DecidableEq K]

theorem tally_steps_le (n : ℕ) :
    UnaryToBinaryMachine.steps n 0 ≤ 3 * (n + 1) ^ 2 := by
  have h := UnaryToBinaryMachine.steps_le n 0
  nlinarith

theorem plainScanEmpty (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (binary work : List Bool) :
    TM2.step program
      ⟨some (labels .scan), clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base [] binary work⟩ =
      some ⟨exit, clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base [] binary work⟩ := by
  let frame := UnaryToBinaryMachine.tapes source output scratch base [] binary work
  have hs : frame source = [] :=
    UnaryToBinaryMachine.tapes_source source output scratch hSO hSC base [] binary work
  have hu : Function.update frame source [] = frame := by
    rw [← hs, Function.update_eq_self]
  change some (TM2.stepAux (program (labels .scan)) (clean ambient) frame) = _
  rw [atLabels .scan]
  cases exit <;>
    simp [instruction, UnaryToBinaryMachine.instruction, UnaryToBinaryMachine.finish,
      TM2.stepAux, BinaryAddMachine.clean, BinaryAddMachine.state, hs, hu] <;> rfl

theorem plainConvertTrace (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (n initial : Nat) :
    (advance (TM2.step program))^[UnaryToBinaryMachine.steps n initial]
      (some ⟨some (labels .scan), clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base
          (List.replicate n true) initial.bits []⟩) =
      some ⟨exit, clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base [] (initial + n).bits []⟩ := by
  induction n generalizing initial with
  | zero =>
      simpa only [UnaryToBinaryMachine.steps, List.replicate_zero, Nat.add_zero,
        Function.iterate_one, advance_some] using
        plainScanEmpty source output scratch hSO hSC labels exit program atLabels
          base ambient initial.bits []
  | succ n ih =>
      have first := UnaryToBinaryMachine.scanStep source output scratch hSO hSC hOC
        labels exit program atLabels base ((ambient, false), none)
        true (List.replicate n true) initial.bits []
      have second := UnaryToBinaryMachine.incrementTrace source output scratch hOC
        labels exit program atLabels base ((ambient, false), none)
        (List.replicate n true) initial.bits []
      simp only [↓reduceIte] at first
      simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append,
        UnaryToBinaryMachine.increment_bits] at second
      have third := ih (initial + 1)
      have full := joinPlainTrace (joinPlainTrace (stepAsPlainTrace first) second) third
      simpa only [UnaryToBinaryMachine.steps, List.replicate_succ,
        BinaryAddMachine.clean, BinaryAddMachine.state,
        Nat.add_assoc, Nat.add_comm 1 n] using full

theorem plainTallyTrace (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (n : Nat) :
    (advance (TM2.step program))^[UnaryToBinaryMachine.steps n 0]
      (some ⟨some (labels .scan), clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base (List.replicate n true) [] []⟩) =
      some ⟨exit, clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base [] n.bits []⟩ := by
  simpa only [Nat.zero_bits, Nat.zero_add] using
    plainConvertTrace source output scratch hSO hSC hOC labels exit program atLabels
      base ambient n 0

def plainTallyInTime (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (n : Nat) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base (List.replicate n true) [] []⟩
      (some ⟨exit, clean ambient,
        UnaryToBinaryMachine.tapes source output scratch base [] n.bits []⟩)
      (3 * (n + 1) ^ 2) where
  steps := UnaryToBinaryMachine.steps n 0
  evals_in_steps := plainTallyTrace source output scratch hSO hSC hOC
    labels exit program atLabels base ambient n
  steps_le_m := tally_steps_le n

def plainTallyFromTapesInTime (source output scratch : K)
    (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
    (base : K → List Bool) (ambient : A) (n : Nat)
    (sourceWord : base source = List.replicate n true)
    (outputEmpty : base output = []) (scratchEmpty : base scratch = []) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .scan), clean ambient, base⟩
      (some ⟨exit, clean ambient, Function.update (Function.update base source []) output n.bits⟩)
      (3 * (n + 1) ^ 2) := by
  have hs : Function.update base source (List.replicate n true) = base := by
    rw [← sourceWord, Function.update_eq_self]
  have ho : Function.update base output [] = base := by
    rw [← outputEmpty, Function.update_eq_self]
  have hc : Function.update base scratch [] = base := by
    rw [← scratchEmpty, Function.update_eq_self]
  have hstart : UnaryToBinaryMachine.tapes source output scratch base
      (List.replicate n true) [] [] = base := by
    rw [UnaryToBinaryMachine.tapes, hs, ho, hc]
  have hfinish : UnaryToBinaryMachine.tapes source output scratch base [] n.bits [] =
      Function.update (Function.update base source []) output n.bits := by
    let done := Function.update (Function.update base source []) output n.bits
    have hwork : done scratch = [] := by
      simp [done, Ne.symm hSC, Ne.symm hOC, scratchEmpty]
    change Function.update done scratch [] = done
    rw [← hwork, Function.update_eq_self]
  have run := plainTallyInTime source output scratch hSO hSC hOC
    labels exit program atLabels base ambient n
  simpa only [hstart, hfinish] using run

end BinPackingGap.BinaryTallyMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryPowerMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryMulMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {K Λ A : Type} [DecidableEq K]

def statement (slots : Fin 9 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .copyLeft => MachineTransfer.loopAt (slots 0) (slots 8) id false
      (labels .copyLeft) (some (labels .forkLeft))
  | .forkLeft => MachineCopy.forkLoop (slots 8) (slots 0) (slots 3) false
      (labels .forkLeft) (some (labels .copyRight))
  | .copyRight => MachineTransfer.loopAt (slots 1) (slots 8) id false
      (labels .copyRight) (some (labels .forkRight))
  | .forkRight => MachineCopy.forkLoop (slots 8) (slots 1) (slots 4) false
      (labels .forkRight) (some (labels .guard))
  | .guard => .pop (slots 4) (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.branch (fun state => state.2.getD false)
          (.load (fun state => clean state.1.1.1) (.goto fun _ => labels .copyAddend))
          (.load (fun state => clean state.1.1.1) (.goto fun _ => labels .shift)))
        (.load (fun state => clean state.1.1.1) (.goto fun _ => labels .clearShift)))
  | .copyAddend => MachineTransfer.loopAt (slots 3) (slots 8) id false
      (labels .copyAddend) (some (labels .forkAddend))
  | .forkAddend => MachineCopy.forkLoop (slots 8) (slots 3) (slots 6) false
      (labels .forkAddend) (some (labels .add))
  | .add => BinaryAddMachine.addLoop (slots 6) (slots 5) (slots 7)
      (labels .add) (some (labels .restoreSum))
  | .restoreSum => MachineTransfer.loopAt (slots 7) (slots 5) id false
      (labels .restoreSum) (some (labels .shift))
  | .shift => .peek (slots 3) (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.push (slots 3) (fun _ => false)
          (.load (fun state => clean state.1.1.1) (.goto fun _ => labels .guard)))
        (.load (fun state => clean state.1.1.1) (.goto fun _ => labels .guard)))
  | .clearShift => MachineDrain.drain (slots 3) (labels .clearShift)
      (some (labels .reverseOutput))
  | .reverseOutput => MachineTransfer.loopAt (slots 5) (slots 7) id false
      (labels .reverseOutput) (some (labels .output))
  | .output => MachineTransfer.loopAt (slots 7) (slots 2) id false
      (labels .output) exit

section Traces

variable (slots : Fin 9 ↪ K) (labels : Label → Λ) (exit : Option Λ)
variable (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, p (labels l) = statement slots labels exit l)
variable (base : K → List Bool) (left right out : List Bool) (ambient : A)

include atLabels

theorem copyInputsTrace :
    (MachineComposition.advance (TM2.step p))^[2 * (right.length + 1) + 2 * (left.length + 1)]
      (some ⟨some (labels .copyLeft), clean ambient,
        tapes slots base left right out [] [] [] [] [] []⟩) =
      some ⟨some (labels .guard), clean ambient,
        tapes slots base left right out left right [] [] [] []⟩ := by
  have hleft :
      (MachineComposition.advance (TM2.step p))^[2 * (left.length + 1)]
        (some ⟨some (labels .copyLeft), clean ambient,
          tapes slots base left right out [] [] [] [] [] []⟩) =
        some ⟨some (labels .copyRight), clean ambient,
          tapes slots base left right out left [] [] [] [] []⟩ := by
    simpa [clean] using MachineCopy.copyTrace (slots 0) (slots 3) (slots 8)
      (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
      (slots.injective.ne (by decide)) false (labels .copyLeft) (labels .forkLeft)
      (some (labels .copyRight)) p (atLabels .copyLeft) (atLabels .forkLeft)
      (tapes slots base left right out [] [] [] [] [] []) (by simp)
      ((ambient, false), none) none
  have hright :
      (MachineComposition.advance (TM2.step p))^[2 * (right.length + 1)]
        (some ⟨some (labels .copyRight), clean ambient,
          tapes slots base left right out left [] [] [] [] []⟩) =
        some ⟨some (labels .guard), clean ambient,
          tapes slots base left right out left right [] [] [] []⟩ := by
    simpa [clean] using MachineCopy.copyTrace (slots 1) (slots 4) (slots 8)
      (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
      (slots.injective.ne (by decide)) false (labels .copyRight) (labels .forkRight)
      (some (labels .guard)) p (atLabels .copyRight) (atLabels .forkRight)
      (tapes slots base left right out left [] [] [] [] []) (by simp)
      ((ambient, false), none) none
  exact composeTrace hleft hright

theorem guardEmptyTrace (xs acc : List Bool) :
    (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .guard), clean ambient,
        tapes slots base left right out xs [] acc [] [] []⟩) =
      some ⟨some (labels .clearShift), clean ambient,
        tapes slots base left right out xs [] acc [] [] []⟩ := by
  change some (TM2.stepAux (p (labels .guard)) _ _) = _
  rw [atLabels .guard]
  simp [statement, TM2.stepAux, clean]

theorem guardConsTrace (xs ys acc : List Bool) (bit : Bool) :
    (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .guard), clean ambient,
        tapes slots base left right out xs (bit :: ys) acc [] [] []⟩) =
      some ⟨some (labels (if bit then .copyAddend else .shift)), clean ambient,
        tapes slots base left right out xs ys acc [] [] []⟩ := by
  change some (TM2.stepAux (p (labels .guard)) _ _) = _
  rw [atLabels .guard]
  cases bit <;> simp [statement, TM2.stepAux, clean]

theorem shiftTrace (xs ys acc : List Bool) :
    (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .shift), clean ambient,
        tapes slots base left right out xs ys acc [] [] []⟩) =
      some ⟨some (labels .guard), clean ambient,
        tapes slots base left right out (BinaryArithmetic.shift xs) ys acc [] [] []⟩ := by
  change some (TM2.stepAux (p (labels .shift)) _ _) = _
  rw [atLabels .shift]
  cases xs <;> simp [statement, TM2.stepAux, clean, BinaryArithmetic.shift]

theorem addPhaseTrace (xs ys acc : List Bool) :
    (MachineComposition.advance (TM2.step p))^[
        ((BinaryArithmetic.addCarry xs acc false).length + 1) +
          ((max xs.length acc.length + 1) + 2 * (xs.length + 1))]
      (some ⟨some (labels .copyAddend), clean ambient,
        tapes slots base left right out xs ys acc [] [] []⟩) =
      some ⟨some (labels .shift), clean ambient,
        tapes slots base left right out xs ys (BinaryArithmetic.addCarry xs acc false)
          [] [] []⟩ := by
  have hcopy :
      (MachineComposition.advance (TM2.step p))^[2 * (xs.length + 1)]
        (some ⟨some (labels .copyAddend), clean ambient,
          tapes slots base left right out xs ys acc [] [] []⟩) =
        some ⟨some (labels .add), clean ambient,
          tapes slots base left right out xs ys acc xs [] []⟩ := by
    simpa [clean] using MachineCopy.copyTrace (slots 3) (slots 6) (slots 8)
      (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
      (slots.injective.ne (by decide)) false (labels .copyAddend) (labels .forkAddend)
      (some (labels .add)) p (atLabels .copyAddend) (atLabels .forkAddend)
      (tapes slots base left right out xs ys acc [] [] []) (by simp)
      ((ambient, false), none) none
  have hadd :
      (MachineComposition.advance (TM2.step p))^[max xs.length acc.length + 1]
        (some ⟨some (labels .add), clean ambient,
          tapes slots base left right out xs ys acc xs [] []⟩) =
        some ⟨some (labels .restoreSum), clean ambient,
          tapes slots base left right out xs ys [] []
            (BinaryArithmetic.addCarry xs acc false).reverse []⟩ := by
    simpa [BinaryAddMachine.tapes, BinaryAddMachine.clean, BinaryAddMachine.state, clean]
      using BinaryAddMachine.addTrace (slots 6) (slots 5) (slots 7)
        (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
        (slots.injective.ne (by decide)) (labels .add) (some (labels .restoreSum))
        p (atLabels .add) (tapes slots base left right out xs ys acc xs [] [])
        ambient xs acc [] false none none
  have hrestore :
      (MachineComposition.advance (TM2.step p))^[(BinaryArithmetic.addCarry xs acc false).length + 1]
        (some ⟨some (labels .restoreSum), clean ambient,
          tapes slots base left right out xs ys [] []
            (BinaryArithmetic.addCarry xs acc false).reverse []⟩) =
        some ⟨some (labels .shift), clean ambient,
          tapes slots base left right out xs ys (BinaryArithmetic.addCarry xs acc false)
            [] [] []⟩ := by
    have hnext : MachineTransfer.nextAt (Γ := fun _ : K => Bool) (slots 5) p =
        MachineComposition.advance (TM2.step p) := rfl
    simpa [MachineTransfer.tapesAt, hnext, clean]
      using MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (slots 7) (slots 5)
        (slots.injective.ne (by decide)) id false (labels .restoreSum)
        (some (labels .shift)) p (atLabels .restoreSum)
        (tapes slots base left right out xs ys [] []
          (BinaryArithmetic.addCarry xs acc false).reverse [])
        ((ambient, false), none) none
  exact composeTrace (composeTrace hcopy hadd) hrestore

theorem cleanupTrace (xs acc : List Bool) :
    (MachineComposition.advance (TM2.step p))^[xs.length + 2 * acc.length + 3]
      (some ⟨some (labels .clearShift), clean ambient,
        tapes slots base left right out xs [] acc [] [] []⟩) =
      some ⟨exit, clean ambient,
        tapes slots base left right (acc ++ out) [] [] [] [] [] []⟩ := by
  have hclear :
      (MachineComposition.advance (TM2.step p))^[xs.length + 1]
        (some ⟨some (labels .clearShift), clean ambient,
          tapes slots base left right out xs [] acc [] [] []⟩) =
        some ⟨some (labels .reverseOutput), clean ambient,
          tapes slots base left right out [] [] acc [] [] []⟩ := by
    simpa [clean] using MachineDrain.drainTrace (slots 3) (labels .clearShift)
      (some (labels .reverseOutput)) p (atLabels .clearShift)
      (tapes slots base left right out xs [] acc [] [] []) xs ((ambient, false), none) none
  have hreverse :
      (MachineComposition.advance (TM2.step p))^[acc.length + 1]
        (some ⟨some (labels .reverseOutput), clean ambient,
          tapes slots base left right out [] [] acc [] [] []⟩) =
        some ⟨some (labels .output), clean ambient,
          tapes slots base left right out [] [] [] [] acc.reverse []⟩ := by
    have hnext : MachineTransfer.nextAt (Γ := fun _ : K => Bool) (slots 7) p =
        MachineComposition.advance (TM2.step p) := rfl
    simpa [MachineTransfer.tapesAt, hnext, clean]
      using MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (slots 5) (slots 7)
        (slots.injective.ne (by decide)) id false (labels .reverseOutput)
        (some (labels .output)) p (atLabels .reverseOutput)
        (tapes slots base left right out [] [] acc [] [] []) ((ambient, false), none) none
  have houtput :
      (MachineComposition.advance (TM2.step p))^[acc.length + 1]
        (some ⟨some (labels .output), clean ambient,
          tapes slots base left right out [] [] [] [] acc.reverse []⟩) =
        some ⟨exit, clean ambient,
          tapes slots base left right (acc ++ out) [] [] [] [] [] []⟩ := by
    have hnext : MachineTransfer.nextAt (Γ := fun _ : K => Bool) (slots 2) p =
        MachineComposition.advance (TM2.step p) := rfl
    simpa [MachineTransfer.tapesAt, hnext, clean]
      using MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool) (slots 7) (slots 2)
        (slots.injective.ne (by decide)) id false (labels .output) exit p (atLabels .output)
        (tapes slots base left right out [] [] [] [] acc.reverse [])
        ((ambient, false), none) none
  rw [show xs.length + 2 * acc.length + 3 =
    (acc.length + 1) + ((acc.length + 1) + (xs.length + 1)) by omega]
  exact composeTrace (composeTrace hclear hreverse) houtput

theorem loopTrace (xs ys acc : List Bool) :
    (MachineComposition.advance (TM2.step p))^[loopSteps xs ys acc]
      (some ⟨some (labels .guard), clean ambient,
        tapes slots base left right out xs ys acc [] [] []⟩) =
      some ⟨exit, clean ambient,
        tapes slots base left right (BinaryArithmetic.mulAcc xs ys acc ++ out)
          [] [] [] [] [] []⟩ := by
  induction ys generalizing xs acc with
  | nil =>
      rw [show loopSteps xs [] acc = (xs.length + 2 * acc.length + 3) + 1 by
        simp only [loopSteps]]
      exact composeTrace
        (guardEmptyTrace slots labels exit p atLabels base left right out ambient xs acc)
        (cleanupTrace slots labels exit p atLabels base left right out ambient xs acc)
  | cons bit ys ih =>
      cases bit with
      | false =>
          rw [show loopSteps xs (false :: ys) acc =
            (loopSteps (BinaryArithmetic.shift xs) ys acc + 1) + 1 by
              simp only [loopSteps]]
          exact composeTrace
            (guardConsTrace slots labels exit p atLabels base left right out ambient xs ys acc false)
            (composeTrace
              (shiftTrace slots labels exit p atLabels base left right out ambient xs ys acc)
              (ih (BinaryArithmetic.shift xs) acc))
      | true =>
          rw [show loopSteps xs (true :: ys) acc =
            ((loopSteps (BinaryArithmetic.shift xs) ys (BinaryArithmetic.addCarry xs acc false) + 1) +
              (((BinaryArithmetic.addCarry xs acc false).length + 1) +
                ((max xs.length acc.length + 1) + 2 * (xs.length + 1)))) + 1 by
                  simp only [loopSteps]
                  omega]
          exact composeTrace
            (guardConsTrace slots labels exit p atLabels base left right out ambient xs ys acc true)
            (composeTrace
              (addPhaseTrace slots labels exit p atLabels base left right out ambient xs ys acc)
              (composeTrace
                (shiftTrace slots labels exit p atLabels base left right out ambient xs ys
                  (BinaryArithmetic.addCarry xs acc false))
                (ih (BinaryArithmetic.shift xs) (BinaryArithmetic.addCarry xs acc false))))

theorem multiplyTrace :
    (MachineComposition.advance (TM2.step p))^[steps left right]
      (some ⟨some (labels .copyLeft), clean ambient,
        tapes slots base left right out [] [] [] [] [] []⟩) =
      some ⟨exit, clean ambient,
        tapes slots base left right (BinaryArithmetic.mulAcc left right [] ++ out)
          [] [] [] [] [] []⟩ :=
  composeTrace (copyInputsTrace slots labels exit p atLabels base left right out ambient)
    (loopTrace slots labels exit p atLabels base left right out ambient left right [])

end Traces

def multiplyInPolynomialTime (slots : Fin 9 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, p (labels l) = statement slots labels exit l)
    (base : K → List Bool) (left right out : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .copyLeft), clean ambient,
        tapes slots base left right out [] [] [] [] [] []⟩
      (some ⟨exit, clean ambient,
        tapes slots base left right (BinaryArithmetic.mulAcc left right [] ++ out)
          [] [] [] [] [] []⟩)
      (timePolynomial.eval (left.length + right.length)) where
  steps := steps left right
  evals_in_steps := multiplyTrace slots labels exit p atLabels base left right out ambient
  steps_le_m := steps_le_timePolynomial left right

theorem initialTapes_eq (slots : Fin 9 ↪ K) (base : K → List Bool)
    (left right : List Bool) (hleft : base (slots 0) = left) (hright : base (slots 1) = right)
    (workspace : ∀ i : Fin 9, 3 ≤ i.val → base (slots i) = []) :
    tapes slots base left right (base (slots 2)) [] [] [] [] [] [] = base := by
  have h3 := workspace 3 (by decide)
  have h4 := workspace 4 (by decide)
  have h5 := workspace 5 (by decide)
  have h6 := workspace 6 (by decide)
  have h7 := workspace 7 (by decide)
  have h8 := workspace 8 (by decide)
  funext k
  by_cases hk : ∃ i, slots i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [tapes_slot]
    fin_cases i <;> simp_all
  · exact framedTapes_other slots base _ k hk

def multiplyNatInPolynomialTime (slots : Fin 9 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, p (labels l) = statement slots labels exit l)
    (base : K → List Bool) (a b : Nat)
    (operandA : base (slots 0) = a.bits) (operandB : base (slots 1) = b.bits)
    (workspace : ∀ i : Fin 9, 3 ≤ i.val → base (slots i) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .copyLeft), clean ambient, base⟩
      (some ⟨exit, clean ambient,
        Function.update base (slots 2) ((a * b).bits ++ base (slots 2))⟩)
      (timePolynomial.eval (a.size + b.size)) := by
  have hbase := initialTapes_eq slots base a.bits b.bits operandA operandB workspace
  have hfinish : tapes slots base a.bits b.bits ((a * b).bits ++ base (slots 2))
      [] [] [] [] [] [] = Function.update base (slots 2) ((a * b).bits ++ base (slots 2)) := by
    rw [← tapes_update2 slots base a.bits b.bits (base (slots 2)) [] [] [] [] [] [], hbase]
  have h := multiplyInPolynomialTime slots labels exit p atLabels base a.bits b.bits
    (base (slots 2)) ambient
  simpa only [BinaryArithmetic.mulAcc_bits, hbase, hfinish, ← Nat.size_eq_bits_len] using h

end BinPackingGap.BinaryMulMachine

namespace BinPackingGap.BinaryPowerMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinaryAddMachine (State clean)

variable {K Λ A : Type} [DecidableEq K]

def instruction (slots : Fin 11 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A)
  | .initialize_ => .push (slots 1) (fun _ => true)
      (.load (fun s => clean s.1.1.1) (.goto fun _ => labels .guard))
  | .guard => .pop (slots 9) (fun s head => (s.1, head))
      (.branch (fun s => s.2.isSome)
        (.load (fun s => clean s.1.1.1)
          (.goto fun _ => labels (.multiply .copyLeft)))
        (BinaryAddMachine.finish exit))
  | .multiply phase => BinaryMulMachine.statement (mulSlots slots)
      (fun phase => labels (.multiply phase)) (some (labels .clearAccumulator)) phase
  | .clearAccumulator => MachineDrain.drain (slots 1) (labels .clearAccumulator)
      (some (labels .reverseProduct))
  | .reverseProduct => loopAt (slots 2) (slots 10) id false
      (labels .reverseProduct) (some (labels .restoreAccumulator))
  | .restoreAccumulator => loopAt (slots 10) (slots 1) id false
      (labels .restoreAccumulator) (some (labels .guard))

def program (slots : Fin 11 ↪ K) :
    Label → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Label (State A) :=
  instruction slots id none

end BinPackingGap.BinaryPowerMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpressionBranch
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryAddPreserving

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinaryAddMachine (State clean)

variable {K Λ A : Type} [DecidableEq K]

def instruction (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A)
  | .leftOut => loopAt (slots 0) (slots 6) id false
      (labels .leftOut) (some (labels .leftBack))
  | .leftBack => MachineCopy.forkLoop (slots 6) (slots 0) (slots 2) false
      (labels .leftBack) (some (labels .rightOut))
  | .rightOut => loopAt (slots 1) (slots 6) id false
      (labels .rightOut) (some (labels .rightBack))
  | .rightBack => MachineCopy.forkLoop (slots 6) (slots 1) (slots 3) false
      (labels .rightBack) (some (labels .add))
  | .add => BinaryAddMachine.addLoop (slots 2) (slots 3) (slots 4)
      (labels .add) (some (labels .transfer))
  | .transfer => loopAt (slots 4) (slots 5) id false (labels .transfer) exit

theorem addTrace (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a b : Nat)
    (leftWord : base (slots 0) = a.bits) (rightWord : base (slots 1) = b.bits)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (sumEmpty : base (slots 4) = []) (outputEmpty : base (slots 5) = [])
    (scratchEmpty : base (slots 6) = []) (ambient : A) :
    (MachineComposition.advance (TM2.step program))^[steps a b]
      (some ⟨some (labels .leftOut), clean ambient, base⟩) =
      some ⟨exit, clean ambient, resultTapes slots base a b⟩ := by
  have hd (i j : Fin 7) (hne : i ≠ j) : slots i ≠ slots j := slots.injective.ne hne
  let afterLeft := Function.update base (slots 2) a.bits
  let afterBoth := Function.update afterLeft (slots 3) b.bits
  let afterAdd := Function.update base (slots 4) (a + b).bits.reverse
  have leftRun : (MachineComposition.advance (TM2.step program))^[2 * (a.size + 1)]
      (some ⟨some (labels .leftOut), clean ambient, base⟩) =
      some ⟨some (labels .rightOut), clean ambient, afterLeft⟩ := by
    have run := MachineCopy.copyTrace (slots 0) (slots 2) (slots 6)
      (hd 0 2 (by decide)) (hd 0 6 (by decide)) (hd 2 6 (by decide)) false
      (labels .leftOut) (labels .leftBack) (some (labels .rightOut)) program
      (atLabels .leftOut) (atLabels .leftBack) base scratchEmpty
      ((ambient, false), none) none
    simpa only [leftWord, leftEmpty, List.append_nil, Nat.size_eq_bits_len,
      clean, BinaryAddMachine.state, afterLeft] using run
  have rightStill : afterLeft (slots 1) = b.bits := by
    simp [afterLeft, hd 1 2 (by decide), rightWord]
  have rightCopyEmpty : afterLeft (slots 3) = [] := by
    simp [afterLeft, hd 3 2 (by decide), rightEmpty]
  have scratchStill : afterLeft (slots 6) = [] := by
    simp [afterLeft, hd 6 2 (by decide), scratchEmpty]
  have rightRun : (MachineComposition.advance (TM2.step program))^[2 * (b.size + 1)]
      (some ⟨some (labels .rightOut), clean ambient, afterLeft⟩) =
      some ⟨some (labels .add), clean ambient, afterBoth⟩ := by
    have run := MachineCopy.copyTrace (slots 1) (slots 3) (slots 6)
      (hd 1 3 (by decide)) (hd 1 6 (by decide)) (hd 3 6 (by decide)) false
      (labels .rightOut) (labels .rightBack) (some (labels .add)) program
      (atLabels .rightOut) (atLabels .rightBack) afterLeft scratchStill
      ((ambient, false), none) none
    simpa only [rightStill, rightCopyEmpty, List.append_nil, Nat.size_eq_bits_len,
      clean, BinaryAddMachine.state, afterBoth] using run
  have leftCopied : afterBoth (slots 2) = a.bits := by
    simp [afterBoth, afterLeft, hd 2 3 (by decide)]
  have rightCopied : afterBoth (slots 3) = b.bits := by simp [afterBoth]
  have sumStillEmpty : afterBoth (slots 4) = [] := by
    simp [afterBoth, afterLeft, hd 4 3 (by decide), hd 4 2 (by decide), sumEmpty]
  have addStart : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4)
      afterBoth a.bits b.bits [] = afterBoth := by
    have self : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4) afterBoth
        (afterBoth (slots 2)) (afterBoth (slots 3)) (afterBoth (slots 4)) = afterBoth := by
      simp [BinaryAddMachine.tapes]
    simpa only [leftCopied, rightCopied, sumStillEmpty] using self
  have addFinish : BinaryAddMachine.tapes (slots 2) (slots 3) (slots 4)
      afterBoth [] [] (a + b).bits.reverse = afterAdd := by
    funext k
    by_cases hl : k = slots 2
    · subst k
      simp [BinaryAddMachine.tapes, afterAdd, hd 2 3 (by decide),
        hd 2 4 (by decide), leftEmpty]
    · by_cases hr : k = slots 3
      · subst k
        simp [BinaryAddMachine.tapes, afterAdd, hd 3 4 (by decide), rightEmpty]
      · by_cases hs : k = slots 4
        · subst k
          simp [BinaryAddMachine.tapes, afterAdd]
        · simp [BinaryAddMachine.tapes, afterAdd, afterBoth, afterLeft, hl, hr, hs]
  have sumRun : (MachineComposition.advance (TM2.step program))^[max a.size b.size + 1]
      (some ⟨some (labels .add), clean ambient, afterBoth⟩) =
      some ⟨some (labels .transfer), clean ambient, afterAdd⟩ := by
    have run := BinaryAddMachine.addTrace (slots 2) (slots 3) (slots 4)
      (hd 2 3 (by decide)) (hd 2 4 (by decide)) (hd 3 4 (by decide))
      (labels .add) (some (labels .transfer)) program (atLabels .add) afterBoth ambient
      a.bits b.bits [] false none none
    simpa only [BinaryArithmetic.addCarry_bits, List.append_nil, Nat.size_eq_bits_len,
      addStart, addFinish, clean] using run
  have sumWord : afterAdd (slots 4) = (a + b).bits.reverse := by simp [afterAdd]
  have outputStillEmpty : afterAdd (slots 5) = [] := by
    simp [afterAdd, hd 5 4 (by decide), outputEmpty]
  have transferred : tapesAt (slots 4) (slots 5) afterAdd [] (a + b).bits =
      resultTapes slots base a b := by
    funext k
    by_cases ho : k = slots 5
    · subst k
      simp [tapesAt, resultTapes]
    · by_cases hs : k = slots 4
      · subst k
        simp [tapesAt, resultTapes, hd 4 5 (by decide), sumEmpty]
      · simp [tapesAt, resultTapes, afterAdd, ho, hs]
  have transferRun : (MachineComposition.advance (TM2.step program))^[(a + b).size + 1]
      (some ⟨some (labels .transfer), clean ambient, afterAdd⟩) =
      some ⟨exit, clean ambient, resultTapes slots base a b⟩ := by
    have run := transferAt_fromTapes (Γ := fun _ : K => Bool) (slots 4) (slots 5)
      (hd 4 5 (by decide)) id false (labels .transfer) exit program (atLabels .transfer)
      afterAdd ((ambient, false), none) none
    have hnext : nextAt (Γ := fun _ : K => Bool) (slots 5) program =
        MachineComposition.advance (TM2.step program) := rfl
    simpa only [hnext,
      sumWord, outputStillEmpty, List.reverse_reverse, List.length_reverse,
      List.map_id, List.append_nil, Nat.size_eq_bits_len, transferred,
      clean, BinaryAddMachine.state] using run
  exact joinTrace (joinTrace (joinTrace leftRun rightRun) sumRun) transferRun

def addInLinearTime (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction slots labels exit label)
    (base : K → List Bool) (a b : Nat)
    (leftWord : base (slots 0) = a.bits) (rightWord : base (slots 1) = b.bits)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (sumEmpty : base (slots 4) = []) (outputEmpty : base (slots 5) = [])
    (scratchEmpty : base (slots 6) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftOut), clean ambient, base⟩
      (some ⟨exit, clean ambient, resultTapes slots base a b⟩)
      (4 * (a.size + b.size) + 7) where
  steps := steps a b
  evals_in_steps := addTrace slots labels exit program atLabels base a b leftWord rightWord
    leftEmpty rightEmpty sumEmpty outputEmpty scratchEmpty ambient
  steps_le_m := steps_le a b

end BinPackingGap.BinaryAddPreserving

namespace BinPackingGap.BinaryMonusPreserving

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer
open BinaryAddMachine (State clean)
open BinaryArithmetic

variable {K Λ A : Type} [DecidableEq K]

def instruction (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A)
  | .leftOut => loopAt (slots 0) (slots 6) id false
      (labels .leftOut) (some (labels .leftBack))
  | .leftBack => MachineCopy.forkLoop (slots 6) (slots 0) (slots 2) false
      (labels .leftBack) (some (labels .rightOut))
  | .rightOut => loopAt (slots 1) (slots 6) id false
      (labels .rightOut) (some (labels .rightBack))
  | .rightBack => MachineCopy.forkLoop (slots 6) (slots 1) (slots 3) false
      (labels .rightBack) (some (labels .subtract))
  | .subtract => BinaryMonusMachine.subtractLoop (slots 2) (slots 3) (slots 4)
      (labels .subtract) (fun borrow => some (labels (if borrow then .drain else .trim)))
  | .trim => BinaryMonusMachine.trimLoop (slots 4) (labels .trim) (some (labels .transfer))
  | .transfer => loopAt (slots 4) (slots 5) id false (labels .transfer) exit
  | .drain => MachineDrain.drain (slots 4) (labels .drain) exit

end BinPackingGap.BinaryMonusPreserving

namespace BinPackingGap.BinaryRegisterProgram

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {Reg K Λ A : Type}

@[simp] theorem resultOf_cons [DecidableEq Reg] (command : Command Reg)
    (commands : List (Command Reg)) (values : Reg → Nat) :
    resultOf (command :: commands) values = resultOf commands (result command values) := rfl

theorem resultOf_append [DecidableEq Reg] (first second : List (Command Reg))
    (values : Reg → Nat) :
    resultOf (first ++ second) values = resultOf second (resultOf first values) := by
  induction first generalizing values with
  | nil => rfl
  | cons command commands ih => exact ih (result command values)

theorem Ready_append [DecidableEq Reg] (first second : List (Command Reg))
    (values : Reg → Nat) :
    Ready (first ++ second) values ↔ Ready first values ∧ Ready second (resultOf first values) := by
  induction first generalizing values with
  | nil => simp [Ready]
  | cons command commands ih =>
      simp only [List.cons_append, Ready, resultOf_cons, ih, and_assoc]

def cost (command : Command Reg) (values : Reg → Nat) : Nat :=
  match command with
  | .add op => 4 * ((values op.left).size + (values op.right).size) + 7
  | .mul op =>
      let width := (values op.left).size + (values op.right).size
      4 * width ^ 2 + 14 * width + 12
  | .monus op => 5 * ((values op.left).size + (values op.right).size) + 7
  | .constant _ _ => 1
  | .clear dst => (values dst).size + 1
  | .copy _ src _ => 2 * ((values src).size + 1)

def budget [DecidableEq Reg] : List (Command Reg) → (Reg → Nat) → Nat :=
  MachineFiniteSequence.steps result cost

def LocalLabel : Command Reg → Type
  | .add _ => BinaryAddPreserving.Label
  | .mul _ => BinaryMulMachine.Label
  | .monus _ => BinaryMonusPreserving.Label
  | .constant _ _ | .clear _ => Unit
  | .copy _ _ _ => Bool

instance instFintypeLocalLabel (command : Command Reg) : Fintype (LocalLabel command) := by
  cases command <;> dsimp [LocalLabel] <;> infer_instance

instance instDecidableEqLocalLabel (command : Command Reg) : DecidableEq (LocalLabel command) := by
  cases command <;> dsimp [LocalLabel] <;> infer_instance

def main : (command : Command Reg) → LocalLabel command
  | .add _ => .leftOut
  | .mul _ => .copyLeft
  | .monus _ => .leftOut
  | .constant _ _ | .clear _ => ()
  | .copy _ _ _ => false

def localInstruction [DecidableEq K] (slot : (Reg ⊕ Fin 6) ↪ K) :
    (command : Command Reg) → (LocalLabel command → Λ) → Option Λ →
    LocalLabel command → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A)
  | .add op, labels, exit => BinaryAddPreserving.instruction (addSlots slot op) labels exit
  | .mul op, labels, exit => BinaryMulMachine.statement (mulSlots slot op) labels exit
  | .monus op, labels, exit => BinaryMonusPreserving.instruction (addSlots slot op) labels exit
  | .constant dst n, _, exit => fun _ =>
      MachineSubstitution.pushWord (slot (.inl dst)) n.bits.reverse
        (MachineTransfer.exitAt (slot (.inl dst)) exit)
  | .clear dst, labels, exit => fun _ =>
      MachineDrain.drain (slot (.inl dst)) (labels ()) exit
  | .copy dst src _, labels, exit => fun label =>
      bif label then
        MachineCopy.forkLoop (slot (.inr 0)) (slot (.inl src)) (slot (.inl dst))
          false (labels true) exit
      else
        MachineTransfer.loopAt (slot (.inl src)) (slot (.inr 0)) id false
          (labels false) (some (labels true))

abbrev Label (commands : List (Command Reg)) := MachineFiniteSequence.Label LocalLabel commands

def entry (commands : List (Command Reg)) (labels : Label commands → Λ) (exit : Option Λ) :=
  MachineFiniteSequence.entry LocalLabel main commands labels exit

def instruction [DecidableEq K] (slot : (Reg ⊕ Fin 6) ↪ K)
    (commands : List (Command Reg)) (labels : Label commands → Λ) (exit : Option Λ) :=
  MachineFiniteSequence.instruction LocalLabel main (localInstruction (A := A) slot)
    commands labels exit

end BinPackingGap.BinaryRegisterProgram

namespace BinPackingGap.NatExpressionCompiler

open BinaryRegisterProgram

variable {α Reg L R N : Type}

def command : BinaryOp → Operands Reg → Command Reg
  | .add, operands => .add operands
  | .mul, operands => .mul operands
  | .monus, operands => .monus operands

@[simp] theorem destination_command (op : BinaryOp) (operands : Operands Reg) :
    destination (command op operands) = operands.destination := by
  cases op <;> rfl

@[simp] theorem value_command (op : BinaryOp) (operands : Operands Reg)
    (regs : Reg → Nat) :
    value (command op operands) regs =
      applyOp op (regs operands.left) (regs operands.right) := by
  cases op <;> rfl

@[simp] theorem commandReady_command (op : BinaryOp) (operands : Operands Reg)
    (regs : Reg → Nat) :
    commandReady (command op operands) regs ↔ regs operands.destination = 0 := by
  cases op <;> rfl

@[simp] theorem leftReg_apply (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (node : L) :
    leftReg loc node = loc (.inr (.inl node)) := rfl

@[simp] theorem rightReg_apply (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (node : R) :
    rightReg loc node = loc (.inr (.inr node)) := rfl

theorem leftReg_ne_rightReg (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (left : L) (right : R) :
    leftReg loc left ≠ rightReg loc right := by
  intro h
  change loc (.inr (.inl left)) = loc (.inr (.inr right)) at h
  have htag := loc.injective h
  cases htag

theorem root_ne_leftReg (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (left : L) :
    loc (.inl ()) ≠ leftReg loc left := by
  intro h
  change loc (.inl ()) = loc (.inr (.inl left)) at h
  have htag := loc.injective h
  cases htag

theorem root_ne_rightReg (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (right : R) :
    loc (.inl ()) ≠ rightReg loc right := by
  intro h
  change loc (.inl ()) = loc (.inr (.inr right)) at h
  have htag := loc.injective h
  cases htag

def branchOperands (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) (leftRoot : L) (rightRoot : R) :
    Operands Reg where
  destination := loc (.inl ())
  left := leftReg loc leftRoot
  right := rightReg loc rightRoot
  left_ne_right := leftReg_ne_rightReg loc leftRoot rightRoot
  left_ne_destination := Ne.symm (root_ne_leftReg loc leftRoot)
  right_ne_destination := Ne.symm (root_ne_rightReg loc rightRoot)

@[simp] theorem branchOperands_destination (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg)
    (leftRoot : L) (rightRoot : R) :
    (branchOperands loc leftRoot rightRoot).destination = loc (.inl ()) := rfl

@[simp] theorem branchOperands_left (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg)
    (leftRoot : L) (rightRoot : R) :
    (branchOperands loc leftRoot rightRoot).left = leftReg loc leftRoot := rfl

@[simp] theorem branchOperands_right (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg)
    (leftRoot : L) (rightRoot : R) :
    (branchOperands loc leftRoot rightRoot).right = rightReg loc rightRoot := rfl

variable [DecidableEq Reg]

@[simp] theorem result_command_destination (op : BinaryOp) (operands : Operands Reg)
    (regs : Reg → Nat) :
    result (command op operands) regs operands.destination =
      applyOp op (regs operands.left) (regs operands.right) := by
  simpa only [destination_command, value_command] using
    result_destination (command op operands) regs

end BinPackingGap.NatExpressionCompiler

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpressionBounds
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

noncomputable def addCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg)
    (labels : LocalLabel (.add op) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ label,
      p (labels label) = localInstruction slot (.add op) labels exit label)
    (base : K → List Bool) (values : Reg → Nat)
    (ready : commandReady (.add op) values) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.add op))), BinaryAddMachine.clean ambient,
        registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base (result (.add op) values)⟩)
      (cost (.add op) values) := by
  have hd : values op.destination = 0 := ready
  have run := BinaryAddPreserving.addInLinearTime (addSlots slot op) labels exit p
    (fun label => atLabels label) (registerTapes slot base values)
    (values op.left) (values op.right)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [hd]) (by simp) ambient
  have hresult : BinaryAddPreserving.resultTapes (addSlots slot op)
      (registerTapes slot base values) (values op.left) (values op.right) =
      registerTapes slot base (result (.add op) values) := by
    simpa only [BinaryAddPreserving.resultTapes, addSlots_five, result, destination, value]
      using registerTapes_update slot base values op.destination
        (values op.left + values op.right)
  simpa only [hresult, main, cost] using run

noncomputable def mulCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg)
    (labels : LocalLabel (.mul op) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (BinaryAddMachine.State A))
    (atLabels : ∀ label,
      p (labels label) = localInstruction slot (.mul op) labels exit label)
    (base : K → List Bool) (values : Reg → Nat)
    (ready : commandReady (.mul op) values) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.mul op))), BinaryAddMachine.clean ambient,
        registerTapes slot base values⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        registerTapes slot base (result (.mul op) values)⟩)
      (cost (.mul op) values) := by
  have hd : values op.destination = 0 := ready
  have hout : registerTapes slot base values (mulSlots slot op 2) = [] := by simp [hd]
  have run := BinaryMulMachine.multiplyNatInPolynomialTime (mulSlots slot op) labels exit p
    (fun label => atLabels label) (registerTapes slot base values)
    (values op.left) (values op.right) (by simp) (by simp)
    (registerTapes_mul_workspace slot op base values) ambient
  have hresult : Function.update (registerTapes slot base values) (mulSlots slot op 2)
      ((values op.left * values op.right).bits ++
        registerTapes slot base values (mulSlots slot op 2)) =
      registerTapes slot base (result (.mul op) values) := by
    rw [hout, List.append_nil, mulSlots_two]
    exact registerTapes_update slot base values op.destination
      (values op.left * values op.right)
  simpa only [hresult, main, cost, BinaryMulMachine.clean,
    BinaryAddMachine.clean, BinaryAddMachine.state, BinaryMulMachine.timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] using run

end

section

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction
open BinaryAddMachine (State clean)

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

noncomputable def constantCommandInTime (slot : (Reg ⊕ Fin 6) ↪ K) (dst : Reg) (n : ℕ)
    (labels : LocalLabel (.constant dst n) → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l,
      p (labels l) = localInstruction slot (.constant dst n) labels exit l)
    (base : K → List Bool) (vals : Reg → ℕ)
    (ready : commandReady (.constant dst n) vals) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (main (.constant dst n))), clean ambient, registerTapes slot base vals⟩
      (some ⟨exit, clean ambient, registerTapes slot base (result (.constant dst n) vals)⟩)
      (cost (.constant dst n) vals) := by
  have hzero : vals dst = 0 := ready
  have hempty : registerTapes slot base vals (slot (.inl dst)) = [] := by
    simp only [registerTapes_reg, hzero, Nat.zero_bits]
  refine { steps := 1, evals_in_steps := ?_, steps_le_m := le_rfl }
  change some (TM2.stepAux (p (labels ())) (clean ambient) (registerTapes slot base vals)) =
    some ⟨exit, clean ambient, registerTapes slot base (result (.constant dst n) vals)⟩
  rw [atLabels ()]
  simp only [localInstruction]
  rw [MachineSubstitution.stepAux_pushWord]
  simp only [List.reverse_reverse, hempty, List.append_nil, registerTapes_update]
  cases exit <;> rfl

end

open Turing
open BinPackingGames.Foundations.Complexity

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

def program (slot : (Reg ⊕ Fin 6) ↪ K) (commands : List (Command Reg)) :
    Label commands → TM2.Stmt (BinaryAddMachine.Alphabet (K := K)) (Label commands)
      (BinaryAddMachine.State A) := instruction slot commands id none

def BitBounded (width : Nat) : List (Command Reg) → (Reg → Nat) → Prop
  | [], values => ∀ r, (values r).size ≤ width
  | command :: commands, values =>
      (∀ r, (values r).size ≤ width) ∧ BitBounded width commands (result command values)

omit [DecidableEq Reg] in
theorem cost_le (command : Command Reg) (values : Reg → Nat) (width : Nat)
    (bounded : ∀ r, (values r).size ≤ width) : cost command values ≤ commandBound width := by
  cases command with
  | add op =>
      have hl := bounded op.left
      have hr := bounded op.right
      simp only [cost, commandBound]
      omega
  | mul op =>
      have hsum : (values op.left).size + (values op.right).size ≤ 2 * width := by
        have hl := bounded op.left
        have hr := bounded op.right
        omega
      have hsquare := Nat.mul_le_mul hsum hsum
      simp only [cost, commandBound]
      nlinarith
  | monus op =>
      have hl := bounded op.left
      have hr := bounded op.right
      simp only [cost, commandBound]
      omega
  | constant dst n => simp only [cost, commandBound]; omega
  | clear dst =>
      have hd := bounded dst
      simp only [cost, commandBound]
      omega
  | copy dst src different =>
      have hs := bounded src
      simp only [cost, commandBound]
      omega

theorem budget_le (commands : List (Command Reg)) (values : Reg → Nat) (width : Nat)
    (bounded : BitBounded width commands values) :
    budget commands values ≤ commands.length * commandBound width := by
  induction commands generalizing values with
  | nil => simp [budget, MachineFiniteSequence.steps]
  | cons command commands ih =>
      have headBound := cost_le command values width bounded.1
      have tailBound := ih (result command values) bounded.2
      change cost command values + budget commands (result command values) ≤
        (commands.length + 1) * commandBound width
      calc
        _ ≤ commandBound width + commands.length * commandBound width :=
          Nat.add_le_add headBound tailBound
        _ = _ := by simp [Nat.add_mul, Nat.add_comm]

end BinPackingGap.BinaryRegisterProgram

namespace BinPackingGap.BinaryRegisterProgram

open Turing
open BinPackingGames.Foundations.Complexity

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

def constantSize : Command Reg → Nat
  | .constant _ n => n.size
  | _ => 0

def maxConstantSize : List (Command Reg) → Nat
  | [] => 0
  | command :: commands => max (constantSize command) (maxConstantSize commands)

omit [DecidableEq Reg] in
theorem constantSize_le_maxConstantSize (commands : List (Command Reg))
    (command : Command Reg) (member : command ∈ commands) :
    constantSize command ≤ maxConstantSize commands := by
  induction commands with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | ht
      · exact Nat.le_max_left _ _
      · exact (ih ht).trans (Nat.le_max_right _ _)

theorem result_size_le (command : Command Reg) (values : Reg → Nat) (width : Nat)
    (positive : 0 < width) (initial : ∀ r, (values r).size ≤ width)
    (literal : constantSize command ≤ width) :
    ∀ r, (result command values r).size ≤ 2 * width := by
  have hv : (value command values).size ≤ 2 * width := by
    cases command with
    | add op =>
        have ha := nat_size_add_le_max (values op.left) (values op.right)
        have hl := initial op.left
        have hr := initial op.right
        change (values op.left + values op.right).size ≤ 2 * width
        omega
    | mul op =>
        have hm := nat_size_mul_le (values op.left) (values op.right)
        have hl := initial op.left
        have hr := initial op.right
        change (values op.left * values op.right).size ≤ 2 * width
        omega
    | monus op =>
        have hm := nat_size_sub_le (values op.left) (values op.right)
        have hl := initial op.left
        change (values op.left - values op.right).size ≤ 2 * width
        omega
    | constant dst n =>
        change n.size ≤ width at literal
        change n.size ≤ 2 * width
        omega
    | clear dst => simp [value, Nat.size_zero]
    | copy dst src different =>
        have hs := initial src
        change (values src).size ≤ 2 * width
        omega
  intro r
  by_cases heq : r = destination command
  · subst r
    simpa only [result_destination] using hv
  · rw [result_other command values r heq]
    exact (initial r).trans (by omega)

theorem bitBounded_of_positive_width (commands : List (Command Reg))
    (values : Reg → Nat) (width : Nat) (positive : 0 < width)
    (initial : ∀ r, (values r).size ≤ width)
    (constants : ∀ command ∈ commands, constantSize command ≤ width) :
    BitBounded (2 ^ commands.length * width) commands values := by
  induction commands generalizing values width with
  | nil => simpa [BitBounded] using initial
  | cons command commands ih =>
      have nextInitial := result_size_le command values width positive initial
        (constants command (by simp))
      have nextConstants : ∀ c ∈ commands, constantSize c ≤ 2 * width := by
        intro c hc
        have h := constants c (by simp [hc])
        omega
      have tailBound := ih (result command values) (2 * width) (by omega)
        nextInitial nextConstants
      have scale : 2 ^ commands.length * (2 * width) =
          2 ^ (commands.length + 1) * width := by
        rw [Nat.pow_succ]
        ring
      change (∀ r, (values r).size ≤ 2 ^ (commands.length + 1) * width) ∧ _
      constructor
      · intro r
        have hp : 0 < (2 : Nat) ^ (commands.length + 1) := pow_pos (by decide) _
        have hr := initial r
        nlinarith
      · simpa only [scale, List.length_cons] using tailBound

def staticWidth (commands : List (Command Reg)) (inputWidth : Nat) : Nat :=
  2 ^ commands.length * (inputWidth + maxConstantSize commands + 1)

theorem bitBounded_from_input (commands : List (Command Reg)) (values : Reg → Nat)
    (inputWidth : Nat) (initial : ∀ r, (values r).size ≤ inputWidth) :
    BitBounded (staticWidth commands inputWidth) commands values := by
  apply bitBounded_of_positive_width commands values
    (inputWidth + maxConstantSize commands + 1)
  · omega
  · intro r
    have hr := initial r
    omega
  · intro command hc
    have h := constantSize_le_maxConstantSize commands command hc
    omega

noncomputable def runtimePolynomial (commands : List (Command Reg)) : Polynomial Nat :=
  let scale : Polynomial Nat := Polynomial.C (2 ^ commands.length) *
    (Polynomial.X + Polynomial.C (maxConstantSize commands + 1))
  Polynomial.C commands.length *
    (Polynomial.C 16 * scale ^ 2 + Polynomial.C 28 * scale + Polynomial.C 12)

omit [DecidableEq Reg] in
theorem runtimePolynomial_eval (commands : List (Command Reg)) (inputWidth : Nat) :
    (runtimePolynomial commands).eval inputWidth =
      commands.length * commandBound (staticWidth commands inputWidth) := by
  simp only [runtimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, commandBound, staticWidth]
  ring

end BinPackingGap.BinaryRegisterProgram

end OAI
end

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

def fourTapes (source : K) (destination : Fin 4 → K) (base : K → List Bool)
    (a b c d : Nat) (suffix : List Bool) : K → List Bool :=
  let t₀ := afterField source (destination 0) base a (encodeWords [b, c, d] ++ suffix)
  let t₁ := afterField source (destination 1) t₀ b (encodeWords [c, d] ++ suffix)
  let t₂ := afterField source (destination 2) t₁ c (encodeWords [d] ++ suffix)
  afterField source (destination 3) t₂ d suffix

end BinPackingGames.Foundations.Hastad.SourceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Queries
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open BinPackingGames.Foundations.Hastad

theorem exists_nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (f : Cube A → Bool) :
    ∃ a : A, ∀ b : A, relativeDistance f (codeword a) ≤ relativeDistance f (codeword b) := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ
    (fun a : A => relativeDistance f (codeword a)) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

def nearest {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] (f : Cube A → Bool) : A :=
  Classical.choose (exists_nearest f)

end BinPackingGames.Foundations.PCP.CodeComposition

namespace BinPackingGames.Foundations.PCP.AssignmentTester

open BinPackingGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def blrReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, disagree (F f ^^ F g) (F (cubeXor f g))

def selfCorrect (F : Cube A → Bool) (x r : Cube A) : Bool :=
  F r ^^ F (cubeXor r x)

def andLawFailure (s f g : Cube A) : Bool :=
  parity s (cubeAnd f g) ^^ (parity s f && parity s g)

def andReject (F : Cube A → Bool) : ℝ :=
  𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    disagree (selfCorrect F (cubeAnd f g) r₀)
      (selfCorrect F f r₁ && selfCorrect F g r₂)

def unitReject (F : Cube A → Bool) : ℝ :=
  𝔼 r, disagree (selfCorrect F (fun _ => true) r) true

variable {K : Type*} [Fintype K] [Nonempty K]

def inputReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 k, 𝔼 r, disagree (σ k) (selfCorrect F (fun a => label a k) r)

def testerReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  (blrReject F + andReject F + unitReject F + inputReject label σ F) / 4

def oracleAnswer (σ : K → Bool) (F : Cube A → Bool) : K ⊕ Cube A → Bool :=
  Sum.elim σ F

def eventReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool)
    (kind : Fin 4) (k : K) (f g r₀ r₁ r₂ : Cube A) : ℝ :=
  truth (!(eventAccepts kind (fun slot =>
    oracleAnswer σ F (eventQueries label kind k f g r₀ r₁ r₂ slot))))

def explicitTesterReject (label : A → K → Bool) (σ : K → Bool) (F : Cube A → Bool) : ℝ :=
  𝔼 kind : Fin 4, 𝔼 k, 𝔼 f, 𝔼 g, 𝔼 r₀, 𝔼 r₁, 𝔼 r₂,
    eventReject label σ F kind k f g r₀ r₁ r₂

end BinPackingGames.Foundations.PCP.AssignmentTester

namespace BinPackingGames.Foundations.PCP.AlphabetReduction

open BinPackingGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def edgeTesterReject (accepts : A → A → Bool) (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool) : ℝ :=
  AssignmentTester.explicitTesterReject (pairEncoding accepts) (pairWord left right) F

end BinPackingGames.Foundations.PCP.AlphabetReduction

namespace BinPackingGames.Foundations.PCP.AlphabetGraph

open BinPackingGames.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def edgeOracle (G : ConstraintGraph V E A) (assignment : Address V E A → Bool) (e : E) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) → Bool :=
  fun tape => assignment (.inr (e, extendTape G e tape))

def eventReject (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (event : Event E A) : ℝ :=
  AssignmentTester.truth (!((verifier G).accepts event (QueryIncidence.response (verifier G) assignment event)))

def localAverage (G : ConstraintGraph V E A) (assignment : Address V E A → Bool)
    (e : E) : ℝ := 𝔼 sample : LocalEvent A, eventReject G assignment (e, sample)

def average [Fintype E] (G : ConstraintGraph V E A)
    (assignment : Address V E A → Bool) : ℝ :=
  𝔼 event : Event E A, eventReject G assignment event

def decodedLabeling (assignment : Address V E A → Bool) : V → A :=
  fun v => CodeComposition.nearest (vertexBlock assignment v)

end BinPackingGames.Foundations.PCP.AlphabetGraph

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PreprocessingRegularSoundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

def liftedLabel (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (labels : Fin t.vertices → GraphTables.Label) :
    Fin (vertexCount t padding) → GraphTables.Label :=
  fun z => labels (paddedOwner (GraphTables.semantics t) (fun v => Fin (padding v))
    ((vertexOrder t padding).symm z))

end BinPackingGames.Foundations.PCP.PreprocessingRegularTables

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PoweringMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PoweringWitness

open PoweringWalks SpectralReturn PoweringReturn
open PoweringMoment (bit)

variable {V D : Type*}

noncomputable def endpointWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (φ ψ : Edge V D → V → ℝ) (n : Nat) (k : Fin (n + 1))
    (w : Walk V D (n + 1)) : ℝ :=
  bit (bad (edgeAt G n w k) = true) *
    φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)

noncomputable def vertexWitness (G : PortGraph V D) (bad : Edge V D → Bool)
    (f : V → V → ℝ) (n : Nat) (k : Fin (n + 1)) :
    Walk V D (n + 1) → ℝ :=
  endpointWitness G bad (fun e => f e.1) (fun e => f (next G e.1 e.2)) n k

end BinPackingGames.Foundations.PCP.PoweringWitness

namespace BinPackingGames.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open PoweringWalks SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

variable {V D : Type*} [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]

def windowEvent (G : PortGraph V D) (bad : V × D → Bool)
    (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) (w : Walk V D (n + 1)) : Prop :=
  bad (edgeAt G n w (windowIndex n start m h i)) = true

end BinPackingGames.Foundations.PCP.PoweringMomentBound

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineHorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

theorem drainTrace (tape : K) (loopLabel : Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLoop : p loopLabel = drainLoop tape loopLabel exit)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[n + 1]
      (some ⟨some loopLabel, ((ambient, ()), register),
        Function.update base tape (encodeWord n ++ suffix)⟩) =
      some ⟨exit, ((ambient, ()), none), Function.update base tape suffix⟩ := by
  induction n generalizing register with
  | zero =>
    change some (TM2.stepAux (p loopLabel) _ _) = _
    rw [atLoop]
    cases exit <;> simp [drainLoop, TM2.stepAux, encodeWord, Reduction.MachineTransfer.exitAt]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step p))^[n + 1]
      (some (TM2.stepAux (p loopLabel) _ _)) = _
    rw [atLoop]
    simp only [drainLoop, TM2.stepAux, Function.update_self, encodeWord,
      List.replicate_succ, List.cons_append, List.head?_cons, List.tail_cons,
      Option.getD_some, Function.update_idem]
    exact ih (some true)

open scoped BigOperators

end BinPackingGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ConfigIndex
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

open Turing
open StackEncoding BoundedExecution

section Statements

variable {K : Type} {Γ : K → Type} {Λ σ ι : Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [DecidableEq Λ]

def DataBits.Realizes {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (state : σ) (tapes : ∀ k, List (Γ k)) : Prop :=
  (∀ v, (bits.state v).eval input = decide (state = v)) ∧
  ∀ k i a, (bits.cells k i a).eval input = decide (encode S (tapes k) i = a)

def ResultBits.Realizes {S : Nat} (bits : ResultBits ι Γ Λ σ S) (input : ι → Bool)
    (cfg : TM2.Cfg Γ Λ σ) : Prop :=
  bits.toDataBits.Realizes input cfg.var cfg.stk ∧
  ∀ label, (bits.label label).eval input = decide (cfg.l = label)

theorem eval_readBits {A : Type} [DecidableEq A] {S : Nat}
    (input : ι → Bool) (bits : Fin S → Option A → Expr ι) (xs : List A)
    (hlen : xs.length ≤ S)
    (hbits : ∀ i a, (bits i a).eval input = decide (encode S xs i = a))
    (n : Nat) (a : Option A) :
    (readBits bits n a).eval input = decide (xs[n]? = a) := by
  by_cases hn : n < S
  · simp only [readBits, dite_eq_left hn]
    exact hbits ⟨n, hn⟩ a
  · have hx : xs[n]? = none := List.getElem?_eq_none (by omega)
    simp only [readBits, dite_eq_right hn, Expr.eval, hx]

omit [∀ stack, Fintype (Γ stack)] in
theorem realizes_pushBits {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (v : σ) (tapes : ∀ k, List (Γ k)) (h : bits.Realizes input v tapes)
    (k : K) (f : σ → Γ k) :
    (pushBits bits k f).Realizes input v (Function.update tapes k (f v :: tapes k)) := by
  refine ⟨h.1, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    simp only [pushBits, Function.update_self]
    by_cases hi : i.val = 0
    · rw [dite_eq_left hi, eval_table input _ _ v h.1]
      simp [encode, hi]
    · rw [dite_eq_right hi, h.2]
      apply bool_ext
      simp [encode, List.getElem?_cons, hi]
      exact ⟨of_decide_eq_true, decide_eq_true⟩
  · simpa only [pushBits, Function.update_of_ne hj] using h.2 j i a

omit [DecidableEq K] in
theorem realizes_peekBits {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (v : σ) (tapes : ∀ k, List (Γ k)) (h : bits.Realizes input v tapes)
    (k : K) (f : σ → Option (Γ k) → σ) (hlen : (tapes k).length ≤ S) :
    (peekBits bits k f).Realizes input (f v (tapes k).head?) tapes := by
  refine ⟨?_, h.2⟩
  intro w
  apply eval_table₂ input _ _ _ v (tapes k).head? h.1
  intro a
  simpa [List.head?_eq_getElem?] using
    eval_readBits input (bits.cells k) (tapes k) hlen (h.2 k) 0 a

theorem realizes_popBits {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (v : σ) (tapes : ∀ k, List (Γ k)) (h : bits.Realizes input v tapes)
    (k : K) (f : σ → Option (Γ k) → σ) (hlen : (tapes k).length ≤ S) :
    (popBits bits k f).Realizes input (f v (tapes k).head?)
      (Function.update tapes k (tapes k).tail) := by
  refine ⟨(realizes_peekBits bits input v tapes h k f hlen).1, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    simp only [popBits, Function.update_self]
    rw [eval_readBits input (bits.cells k) (tapes k) hlen (h.2 k)]
    simp [encode, List.getElem?_tail]
  · simpa only [popBits, Function.update_of_ne hj] using h.2 j i a

omit [DecidableEq K] [∀ stack, Fintype (Γ stack)] in
theorem realizes_loadBits {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (v : σ) (tapes : ∀ k, List (Γ k)) (h : bits.Realizes input v tapes)
    (f : σ → σ) : (loadBits bits f).Realizes input (f v) tapes := by
  exact ⟨fun w => eval_table input f bits.state v h.1 w, h.2⟩

omit [DecidableEq K] [Fintype σ] [∀ stack, Fintype (Γ stack)] in
theorem realizes_muxResult {S : Nat} (input : ι → Bool) (condition : Expr ι)
    (yes no : ResultBits ι Γ Λ σ S) (decision : Bool) (hc : condition.eval input = decision)
    (yesCfg noCfg : TM2.Cfg Γ Λ σ)
    (hy : decision = true → yes.Realizes input yesCfg)
    (hn : decision = false → no.Realizes input noCfg) :
    (muxResult condition yes no).Realizes input (if decision then yesCfg else noCfg) := by
  cases decision with
  | false =>
    rcases hn rfl with ⟨⟨hv, hs⟩, hl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true, if_true] using hv v
    · intro k i a; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true, if_true] using hs k i a
    · intro l; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true, if_true] using hl l
  | true =>
    rcases hy rfl with ⟨⟨hv, hs⟩, hl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true, if_true] using hv v
    · intro k i a; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true, if_true] using hs k i a
    · intro l; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true, if_true] using hl l

theorem compileAux_correct {S : Nat} (stmt : TM2.Stmt Γ Λ σ)
    (bits : DataBits ι Γ σ S) (input : ι → Bool) (v : σ) (tapes : ∀ k, List (Γ k))
    (safe : StatementSafe S stmt v tapes) (h : bits.Realizes input v tapes) :
    (compileAux stmt bits).Realizes input (TM2.stepAux stmt v tapes) := by
  induction stmt generalizing bits v tapes with
  | push k f next ih =>
    exact ih _ _ _ safe.2.2 (realizes_pushBits bits input v tapes h k f)
  | peek k f next ih =>
    exact ih _ _ _ safe.2 (realizes_peekBits bits input v tapes h k f (safe.1 k))
  | pop k f next ih =>
    exact ih _ _ _ safe.2 (realizes_popBits bits input v tapes h k f (safe.1 k))
  | load f next ih =>
    exact ih _ _ _ safe.2 (realizes_loadBits bits input v tapes h f)
  | branch guard yes no ihy ihn =>
    have hc : (table guard bits.state true).eval input = guard v := by
      rw [eval_table input guard bits.state v h.1]
      cases guard v <;> rfl
    have hy : guard v = true → (compileAux yes bits).Realizes input (TM2.stepAux yes v tapes) := by
      intro hg
      apply ihy bits v tapes _ h
      simpa [StatementSafe, hg] using safe.2
    have hn : guard v = false → (compileAux no bits).Realizes input (TM2.stepAux no v tapes) := by
      intro hg
      apply ihn bits v tapes _ h
      simpa [StatementSafe, hg] using safe.2
    have hm := realizes_muxResult input _ _ _ (guard v) hc _ _ hy hn
    cases hg : guard v <;> simpa [compileAux, TM2.stepAux, hg] using hm
  | goto label =>
    exact ⟨h, fun l => eval_table input _ bits.state v h.1 l⟩
  | halt => exact ⟨h, fun _ => rfl⟩

end Statements

section Encoding

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [DecidableEq Λ]

omit [DecidableEq K] [Fintype σ] [∀ stack, Fintype (Γ stack)] in
theorem inputBits_realizes (S : Nat) (v : σ) (tapes : ∀ k, List (Γ k)) :
    (inputBits S).Realizes (inputEncoding S v tapes) v tapes := by
  exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩

omit [DecidableEq K] [Fintype σ] [∀ stack, Fintype (Γ stack)] in
theorem resultExpr_eval {ι : Type} {S : Nat} (bits : ResultBits ι Γ Λ σ S)
    (input : ι → Bool) (cfg : TM2.Cfg Γ Λ σ) (h : bits.Realizes input cfg)
    (bit : ConfigBit Γ Λ σ S) :
    (resultExpr bits bit).eval input = configEncoding S cfg bit := by
  rcases bit with label | (v | ⟨k, i, a⟩)
  · exact h.2 label
  · exact h.1.1 v
  · exact h.1.2 k i a

theorem transitionExpr_eval (S : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (v : σ) (tapes : ∀ k, List (Γ k)) (safe : StatementSafe S stmt v tapes)
    (bit : ConfigBit Γ Λ σ S) :
    (transitionExpr S stmt bit).eval (inputEncoding S v tapes) =
      configEncoding S (TM2.stepAux stmt v tapes) bit :=
  resultExpr_eval _ _ _ (compileAux_correct stmt _ _ v tapes safe
    (inputBits_realizes S v tapes)) bit

end Encoding

end BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_MachineCircuit
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.MachineCircuit

open Turing StatementCircuit BoundedExecution
open scoped BigOperators

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
variable [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]

omit [Fintype Λ] in
theorem liveCase_eval (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ)
    (cfg : TM2.Cfg Γ Λ σ) (safe : StepSafe S program cfg)
    (bit : ConfigBit Γ Λ σ S) (label : Λ) :
    (liveCase S program bit label).eval (configEncoding S cfg) =
      (decide (cfg.l = some label) &&
        configEncoding S (absorbingNext (TM2.step program) cfg) bit) := by
  by_cases live : cfg.l = some label
  · simp only [liveCase, Expr.eval, Expr.eval_rename, configEncoding, live,
      decide_true, Bool.true_and]
    rw [transitionExpr_eval S (program label) cfg.var cfg.stk (safe label live),
      absorbing_live program cfg label live]
    rfl
  · simp [liveCase, Expr.eval, configEncoding, live]

theorem stickyExpr_eval (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ)
    (cfg : TM2.Cfg Γ Λ σ) (safe : StepSafe S program cfg)
    (bit : ConfigBit Γ Λ σ S) :
    (stickyExpr S program bit).eval (configEncoding S cfg) =
      configEncoding S (absorbingNext (TM2.step program) cfg) bit := by
  have hactive :
      (Expr.disjoin (Finset.univ.toList.map (liveCase S program bit))).eval
        (configEncoding S cfg) = true ↔
      ∃ label, cfg.l = some label ∧
        configEncoding S (absorbingNext (TM2.step program) cfg) bit = true := by
    rw [Expr.eval_disjoin_true]
    simp only [List.mem_map]
    constructor
    · rintro ⟨e, ⟨label, _, rfl⟩, he⟩
      rw [liveCase_eval S program cfg safe] at he
      exact ⟨label, by simpa only [Bool.and_eq_true, decide_eq_true_eq] using he⟩
    · rintro ⟨label, hl, hb⟩
      refine ⟨liveCase S program bit label, ?_, ?_⟩
      · exact ⟨label, by simp, rfl⟩
      · rw [liveCase_eval S program cfg safe]
        simp [hl, hb]
  apply bool_ext
  simp only [stickyExpr, Expr.eval, Bool.or_eq_true, Bool.and_eq_true, hactive]
  cases hl : cfg.l with
  | none =>
    rw [absorbing_halted program cfg hl]
    simp [configEncoding, hl]
  | some label => simp [configEncoding, hl]

end BinPackingGames.Foundations.Complexity.CookLevin.MachineCircuit

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_OutputOrder
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

open Turing StatementCircuit

variable {K : Type} (Γ : K → Type) (σ : Type)

variable {Γ σ} [∀ k, DecidableEq (Γ k)]

def Data.Matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) : Prop :=
  (∀ v, (bits.state v).instantiate S cursor = actual.state v) ∧
    ∀ k p a (h : p.eval cursor < S),
      (bits.cells k p a).instantiate S cursor = actual.cells k ⟨p.eval cursor, h⟩ a

def Result.Matches {Λ : Type} (S cursor : Nat) (bits : Result (Γ := Γ) (σ := σ) Λ)
    (actual : ResultBits (InputBit Γ σ S) Γ Λ σ S) : Prop :=
  bits.toData.Matches S cursor actual.toDataBits ∧
    ∀ label, (bits.label label).instantiate S cursor = actual.label label

omit [∀ tape, DecidableEq (Γ tape)] in
theorem initial_matches (S cursor : Nat) :
    (initial : Data (Γ := Γ) (σ := σ)).Matches S cursor (inputBits S) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro k p a hp
  simp [initial, Term.instantiate, hp, inputBits]

theorem instantiate_read (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (k : K) (p : Position) (a : Option (Γ k)) :
    (read bits k p a).instantiate S cursor = readBits (actual.cells k) (p.eval cursor) a := by
  by_cases hp : p.eval cursor < S
  · simpa [read, Term.instantiate, readBits, hp] using h.2 k p a hp
  · simp [read, Term.instantiate, readBits, hp]

variable {Λ : Type} [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [DecidableEq Λ]

omit [DecidableEq σ] [∀ tape, Fintype (Γ tape)] in
theorem push_matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (k : K) (f : σ → Γ k) :
    (push bits k f).Matches S cursor (pushBits actual k f) := by
  refine ⟨h.1, ?_⟩
  intro j p a hp
  by_cases hj : j = k
  · subst j
    simp only [push, pushBits, Function.update_self]
    by_cases hz : p.eval cursor = 0
    · simp [Term.instantiate, hz, h.1]
    · have hpred : (Position.pred p).eval cursor < S := by
        simp only [Position.eval]
        omega
      simpa [Term.instantiate, Position.eval, hz] using h.2 k (.pred p) a hpred
  · simpa [push, pushBits, Function.update_of_ne hj] using h.2 j p a hp

omit [DecidableEq K] in
theorem peek_matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (k : K) (f : σ → Option (Γ k) → σ) :
    (peek bits k f).Matches S cursor (peekBits actual k f) := by
  refine ⟨?_, h.2⟩
  intro v
  simp only [peek, peekBits, instantiate_table₂]
  have hs : (fun a => (bits.state a).instantiate S cursor) = actual.state := funext h.1
  have hc : (fun a => (read bits k .zero a).instantiate S cursor) =
      readBits (actual.cells k) 0 := by
    funext a
    exact instantiate_read S cursor bits actual h k .zero a
  rw [hs, hc]

theorem pop_matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (k : K) (f : σ → Option (Γ k) → σ) :
    (pop bits k f).Matches S cursor (popBits actual k f) := by
  refine ⟨(peek_matches S cursor bits actual h k f).1, ?_⟩
  intro j p a hp
  by_cases hj : j = k
  · subst j
    simpa [pop, popBits, Position.eval] using instantiate_read S cursor bits actual h k (.succ p) a
  · simpa [pop, popBits, Function.update_of_ne hj] using h.2 j p a hp

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [∀ tape, Fintype (Γ tape)] in
theorem load_matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (f : σ → σ) : (load bits f).Matches S cursor (loadBits actual f) := by
  refine ⟨?_, h.2⟩
  intro v
  simp [load, loadBits, h.1]

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] in
theorem mux_matches (S cursor : Nat) (condition : Term Γ σ)
    (yes no : Result (Γ := Γ) (σ := σ) Λ)
    (actualYes actualNo : ResultBits (InputBit Γ σ S) Γ Λ σ S)
    (hy : yes.Matches S cursor actualYes) (hn : no.Matches S cursor actualNo) :
    (mux condition yes no).Matches S cursor
      (muxResult (condition.instantiate S cursor) actualYes actualNo) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v
    simp [mux, muxResult, hy.1.1, hn.1.1]
  · intro k p a hp
    simp [mux, muxResult, hy.1.2 k p a hp, hn.1.2 k p a hp]
  · intro l
    simp [mux, muxResult, hy.2, hn.2]

theorem compile_matches (S cursor : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (bits : Data (Γ := Γ) (σ := σ)) (actual : DataBits (InputBit Γ σ S) Γ σ S)
    (h : bits.Matches S cursor actual) :
    (compile stmt bits).Matches S cursor (compileAux stmt actual) := by
  induction stmt generalizing bits actual with
  | push k f next ih =>
      exact ih (push bits k f) (pushBits actual k f) (push_matches S cursor bits actual h k f)
  | peek k f next ih =>
      exact ih (peek bits k f) (peekBits actual k f) (peek_matches S cursor bits actual h k f)
  | pop k f next ih =>
      exact ih (pop bits k f) (popBits actual k f) (pop_matches S cursor bits actual h k f)
  | load f next ih =>
      exact ih (load bits f) (loadBits actual f) (load_matches S cursor bits actual h f)
  | branch guard yes no ihy ihn =>
      have hm := mux_matches S cursor (finiteTable guard bits.state true)
        (compile yes bits) (compile no bits) (compileAux yes actual) (compileAux no actual)
        (ihy bits actual h) (ihn bits actual h)
      simpa [compile, compileAux, h.1] using hm
  | goto label =>
      refine ⟨h, ?_⟩
      intro l
      simp [compile, compileAux, h.1]
  | halt => exact ⟨h, fun _ => rfl⟩

theorem transition_instantiate (S : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) :
    (transition stmt (bitKind bit)).instantiate S (bitCursor bit) = transitionExpr S stmt bit := by
  have h := compile_matches S (bitCursor bit) stmt initial (inputBits S)
    (initial_matches S (bitCursor bit))
  rcases bit with l | (v | ⟨k, i, a⟩)
  · exact h.2 l
  · exact h.1.1 v
  · exact h.1.2 k .current a i.isLt

variable [Fintype Λ]

theorem sticky_instantiate (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) :
    (sticky program (bitKind bit)).instantiate S (bitCursor bit) =
      MachineCircuit.stickyExpr S program bit := by
  simp only [sticky, Global.instantiate, instantiate_global_disjoin, List.map_map,
    Function.comp_def, self_instantiate, transition_instantiate,
    MachineCircuit.stickyExpr]
  rfl

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem Term.tokens_eq (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S cursor : Nat) (term : Term Γ σ) :
    term.tokens indexing roots S cursor =
      PostfixAlignment.exprTokens (fun bit => configWire indexing roots S (.inr bit))
        (term.instantiate S cursor) := by
  induction term with
  | state v => simp [tokens, instantiate, PostfixAlignment.exprTokens, configWire]
  | cell k p a =>
      by_cases h : p.eval cursor < S <;>
        simp [tokens, instantiate, h, PostfixAlignment.exprTokens, configWire]
  | const b => rfl
  | not e ih => simp only [tokens, instantiate, PostfixAlignment.exprTokens, ih]
  | and e f ihe ihf => simp only [tokens, instantiate, PostfixAlignment.exprTokens, ihe, ihf]
  | or e f ihe ihf => simp only [tokens, instantiate, PostfixAlignment.exprTokens, ihe, ihf]
  | atZero p e f ihe ihf =>
      by_cases h : p.eval cursor = 0 <;> simp [tokens, instantiate, h, ihe, ihf]
  | within p e f ihe ihf =>
      by_cases h : p.eval cursor < S <;> simp [tokens, instantiate, h, ihe, ihf]

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem Global.tokens_eq (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S cursor : Nat) (term : Global (Γ := Γ) (Λ := Λ) (σ := σ)) :
    term.tokens indexing roots S cursor =
      PostfixAlignment.exprTokens (configWire indexing roots S) (term.instantiate S cursor) := by
  induction term with
  | label l => simp [tokens, instantiate, PostfixAlignment.exprTokens, configWire]
  | data e =>
      simp only [tokens, instantiate, PostfixAlignment.exprTokens_rename]
      exact e.tokens_eq indexing roots S cursor
  | const b => rfl
  | and e f ihe ihf => simp only [tokens, instantiate, PostfixAlignment.exprTokens, ihe, ihf]
  | or e f ihe ihf => simp only [tokens, instantiate, PostfixAlignment.exprTokens, ihe, ihf]

theorem sticky_tokens_eq (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ) (bit : ConfigBit Γ Λ σ S) :
    (sticky program (bitKind bit)).tokens indexing roots S (bitCursor bit) =
      PostfixAlignment.exprTokens (configWire indexing roots S)
        (MachineCircuit.stickyExpr S program bit) := by
  rw [Global.tokens_eq, sticky_instantiate]

noncomputable def forestTokens (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ) : List PostfixModel.Token :=
  (outputOrder indexing S).flatMap fun bit =>
    (sticky program (bitKind bit)).tokens indexing roots S (bitCursor bit)

theorem forestTokens_eq (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ) :
    forestTokens indexing roots S program =
      PostfixAlignment.forestTokens (configWire indexing roots S)
        ((outputOrder indexing S).map (MachineCircuit.stickyExpr S program)) := by
  simp only [forestTokens, PostfixAlignment.forestTokens, List.flatMap_map]
  apply List.flatMap_congr
  intro bit _
  exact sticky_tokens_eq indexing roots S program bit

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierCircuit
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding

open scoped BigOperators

def pairCell {q : Nat} (input : List Bool) (bits : Bits q) (n : Nat) : Option Bool :=
  if n < (inputPrefix input).length then (inputPrefix input)[n]?
  else witnessCell bits (n - (inputPrefix input).length)

theorem pairCell_eq_getElem? {q : Nat} (input : List Bool) (bits : Bits q)
    (hv : Valid bits) (n : Nat) :
    pairCell input bits n = (pairBits (input, decode bits))[n]? := by
  rw [pairBits]
  change pairCell input bits n = (inputPrefix input ++ decode bits)[n]?
  rw [List.getElem?_append]
  simp only [pairCell, witnessCell_eq_getElem? bits hv]

end BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding

namespace BinPackingGames.Foundations.Complexity.CookLevin.WitnessCircuit

open StatementCircuit WitnessEncoding

theorem eval_nonemptyExpr {q : Nat} (bits : Bits q) :
    (nonemptyExpr q).eval bits = true ↔ ∃ i, selector bits i = true := by
  simp only [nonemptyExpr, eval_disjoin_ofFn_true, eval_selectorExpr]

theorem eval_clashPairExpr {q : Nat} (bits : Bits q) (i j : Fin (q + 1)) :
    (clashPairExpr q i j).eval bits = true ↔
      i ≠ j ∧ selector bits i = true ∧ selector bits j = true := by
  by_cases h : i = j <;> simp [clashPairExpr, h, Expr.eval]

theorem eval_clashExpr {q : Nat} (bits : Bits q) :
    (clashExpr q).eval bits = true ↔
      ∃ i j, i ≠ j ∧ selector bits i = true ∧ selector bits j = true := by
  simp only [clashExpr, eval_disjoin_ofFn_true, eval_clashPairExpr]

theorem eval_validityExpr {q : Nat} (bits : Bits q) :
    (validityExpr q).eval bits = true ↔ Valid bits := by
  rw [valid_iff_local]
  simp only [validityExpr, Expr.eval, Bool.and_eq_true, Bool.not_eq_true']
  rw [eval_nonemptyExpr]
  have hc := eval_clashExpr bits
  constructor
  · rintro ⟨hne, hclash⟩
    refine ⟨hne, fun i j hi hj => ?_⟩
    by_contra hij
    have ht := hc.mpr ⟨i, j, hij, hi, hj⟩
    simp [hclash] at ht
  · rintro ⟨hne, hu⟩
    refine ⟨hne, ?_⟩
    cases hb : (clashExpr q).eval bits
    · rfl
    · obtain ⟨i, j, hij, hi, hj⟩ := hc.mp hb
      exact False.elim (hij (hu i j hi hj))

theorem eval_presenceExpr {q : Nat} (bits : Bits q) (n : Nat) :
    (presenceExpr q n).eval bits = present bits n := by
  apply bool_ext
  simp only [presenceExpr, eval_disjoin_ofFn_true, Expr.eval, eval_selectorExpr,
    Bool.and_eq_true, present, decide_eq_true_eq]

section Symbols

variable {A : Type*} [DecidableEq A]

theorem eval_payloadSymbolExpr {q : Nat} (bits : Bits q) (f : Bool → A)
    (i : Fin q) (a : Option A) :
    (payloadSymbolExpr q f i a).eval bits = decide (some (f (payload bits i)) = a) := by
  rw [payloadSymbolExpr, Expr.eval_mux, eval_payloadExpr]
  cases payload bits i <;> simp [Expr.eval]

theorem eval_inputCellExpr {q : Nat} (bits : Bits q) (input : List Bool)
    (f : Bool → A) (n : Nat) (a : Option A) :
    (inputCellExpr q input f n a).eval bits = decide ((pairCell input bits n).map f = a) := by
  by_cases hp : n < (inputPrefix input).length
  · simp only [inputCellExpr, pairCell, ite_eq_left hp, Expr.eval]
  · by_cases hq : n - (inputPrefix input).length < q
    · simp only [inputCellExpr, hp, ite_false, hq, dite_eq_left, Expr.eval_mux,
        eval_presenceExpr, eval_payloadSymbolExpr, Expr.eval, pairCell, witnessCell]
      cases present bits (n - (inputPrefix input).length) <;> simp
    · simp only [inputCellExpr, pairCell, witnessCell, ite_eq_right hp, dite_eq_right hq,
        Expr.eval, Option.map_none]

end Symbols

section Initial

variable (verifier : NPVerifier)
variable [DecidableEq verifier.computation.tm.Λ]
variable [DecidableEq verifier.computation.tm.σ]
variable [∀ k, DecidableEq (verifier.computation.tm.Γ k)]

omit [DecidableEq verifier.computation.tm.Λ] [DecidableEq verifier.computation.tm.σ] in
theorem eval_initialCellExpr (input : List Bool) (S : Nat)
    (bits : Bits (verifier.witnessBound.eval input.length)) (hv : Valid bits)
    (k : verifier.computation.tm.K) (i : Fin S) (a : Option (verifier.computation.tm.Γ k)) :
    (initialCellExpr verifier input S k i a).eval bits =
      decide (StackEncoding.encode S ((initial verifier input bits).stk k) i = a) := by
  by_cases hk : k = verifier.computation.tm.k₀
  · subst k
    simpa [initialCellExpr, StackEncoding.encode,
      pairCell_eq_getElem? input bits hv i.val] using
        eval_inputCellExpr bits input verifier.computation.inputAlphabet.invFun i.val a
  · simp [initialCellExpr, hk, initial_other_stack verifier input bits k hk,
      StackEncoding.encode, Expr.eval]

theorem eval_initExpr (input : List Bool) (S : Nat)
    (bits : Bits (verifier.witnessBound.eval input.length)) (hv : Valid bits)
    (bit : ConfigBit verifier.computation.tm.Γ verifier.computation.tm.Λ
      verifier.computation.tm.σ S) :
    (initExpr verifier input S bit).eval bits =
      configEncoding S (initial verifier input bits) bit := by
  rcases bit with label | (state | ⟨k, i, a⟩)
  · rfl
  · rfl
  · exact eval_initialCellExpr verifier input S bits hv k i a

end Initial

end BinPackingGames.Foundations.Complexity.CookLevin.WitnessCircuit

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

open Turing StatementCircuit CircuitBatch
open scoped BigOperators

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.alphabetFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.labelFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.stateFinite
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.labelDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.stateDecidable
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit.alphabetDecidable
theorem accepting_stack_le (V : NPVerifier) (input : List Bool) (k : V.computation.tm.K) :
    ((accepting V).stk k).length ≤ capacity V input.length := by
  by_cases hk : k = V.computation.tm.k₁
  · subst k
    simpa [accepting, haltList] using capacity_pos V input.length
  · simp [accepting, haltList, hk]

theorem actualRun_accepting_iff (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :
    actualRun V input bits (V.horizon input.length) = accepting V ↔
      V.verify (input, WitnessEncoding.decode bits) = true := by
  have hr := BoundedExecution.run_eq_halt_of_outputs V.computation.tm
    (machineInput V input bits)
    ([V.verify (input, WitnessEncoding.decode bits)].map V.computation.outputAlphabet.invFun)
    (V.horizon input.length)
    (V.runWithinHorizon input (WitnessEncoding.decode bits) (WitnessEncoding.decode_length_le bits))
  change actualRun V input bits (V.horizon input.length) = _ at hr
  rw [hr]
  constructor
  · intro h
    have hs := congrArg (fun c : V.computation.tm.Cfg => c.stk V.computation.tm.k₁) h
    have he : V.computation.outputAlphabet.invFun (V.verify (input, WitnessEncoding.decode bits)) =
        V.computation.outputAlphabet.invFun true := by
      simpa [accepting, haltList] using hs
    exact V.computation.outputAlphabet.symm.injective he
  · intro h
    simp [h, accepting]

theorem initialExpressions_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (hv : WitnessEncoding.Valid bits) :
    (fun j => (initialExpressions V input j).eval bits) =
      stateEncoding V input (WitnessEncoding.initial V input bits)
        ((WitnessCircuit.validityExpr _).eval bits) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [initialExpressions, stateEncoding]
  · simpa [initialExpressions, stateEncoding] using
      WitnessCircuit.eval_initExpr V input (capacity V input.length) bits hv
        ((bitEquiv V input).symm i)

theorem stepExpressions_eval (V : NPVerifier) (input : List Bool) (cfg : V.computation.tm.Cfg)
    (safe : MachineCircuit.StepSafe (capacity V input.length) V.computation.tm.m cfg)
    (valid : Bool) :
    Frame.network (stepExpressions V input) (stateEncoding V input cfg valid) =
      stateEncoding V input (BoundedExecution.stickyNext V.computation.tm cfg) valid := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [Frame.network, stepExpressions, Expr.eval, stateEncoding]
  · simp only [Frame.network, stepExpressions, Fin.lastCases_castSucc, Expr.eval_rename]
    have he : (fun b => stateEncoding V input cfg valid (bitWire V input b)) =
        configEncoding (capacity V input.length) cfg := by funext b; simp
    rw [he, MachineCircuit.stickyExpr_eval _ _ cfg safe]
    simp only [stateEncoding, Fin.lastCases_castSucc]
    rfl

theorem initialFrame_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (hv : WitnessEncoding.Valid bits) :
    (initialFrame V input).eval bits = stateEncoding V input
      (WitnessEncoding.initial V input bits) ((WitnessCircuit.validityExpr _).eval bits) := by
  rw [initialFrame, Frame.step_eval_fun]
  have hi : (Frame.initial id).eval bits = bits := by funext i; simp
  rw [hi]
  exact initialExpressions_eval V input bits hv

theorem timeFrame_validity (V : NPVerifier) (input : List Bool) (bits : FreeBits V input)
    (t : Nat) :
    (timeFrame V input t).eval bits (Fin.last (width V input)) =
      (WitnessCircuit.validityExpr (V.witnessBound.eval input.length)).eval bits := by
  induction t with
  | zero =>
    simp only [timeFrame, Frame.repeat, initialFrame, Frame.step_eval,
      initialExpressions, Fin.lastCases_last]
    apply Expr.eval_congr
    intro i
    exact Frame.initial_eval id bits i
  | succ t ih =>
    simpa only [timeFrame, Frame.repeat, Frame.step_eval, stepExpressions,
      Fin.lastCases_last, Expr.eval] using ih

theorem mismatchExpr_eval (V : NPVerifier) (input : List Bool)
    (state : Fin (width V input + 1) → Bool) (j : Fin (width V input)) :
    (mismatchExpr V input j).eval state = true ↔
      state j.castSucc ≠ configEncoding (capacity V input.length) (accepting V)
        ((bitEquiv V input).symm j) := by
  cases ht : configEncoding (capacity V input.length) (accepting V)
      ((bitEquiv V input).symm j) <;> cases hs : state j.castSucc <;>
    simp [mismatchExpr, Expr.eval, ht, hs]

theorem acceptanceExpr_eval (V : NPVerifier) (input : List Bool)
    (state : Fin (width V input + 1) → Bool) :
    (acceptanceExpr V input).eval state = true ↔
      state (Fin.last (width V input)) = true ∧
      ∀ j : Fin (width V input), state j.castSucc =
        configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j) := by
  have hd : (Expr.disjoin (List.ofFn (mismatchExpr V input))).eval state = true ↔
      ∃ j : Fin (width V input), state j.castSucc ≠
        configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j) := by
    rw [Expr.eval_disjoin_true]
    constructor
    · rintro ⟨e, he, hv⟩
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
      exact ⟨j, (mismatchExpr_eval V input state j).mp hv⟩
    · rintro ⟨j, hj⟩
      exact ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, (mismatchExpr_eval V input state j).mpr hj⟩
  have hz : (Expr.disjoin (List.ofFn (mismatchExpr V input))).eval state = false ↔
      ∀ j : Fin (width V input), state j.castSucc =
        configEncoding (capacity V input.length) (accepting V) ((bitEquiv V input).symm j) := by
    constructor
    · intro h j
      by_contra hj
      have ht := hd.mpr ⟨j, hj⟩
      rw [h] at ht
      contradiction
    · intro h
      cases ht : (Expr.disjoin (List.ofFn (mismatchExpr V input))).eval state with
      | false => rfl
      | true =>
        obtain ⟨j, hj⟩ := hd.mp ht
        exact False.elim (hj (h j))
  simp only [acceptanceExpr, Expr.eval, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false]
  exact and_congr_right (fun _ => hz)

theorem acceptanceExpr_stateEncoding (V : NPVerifier) (input : List Bool)
    (cfg : V.computation.tm.Cfg) (valid : Bool)
    (hcfg : ∀ k, (cfg.stk k).length ≤ capacity V input.length) :
    (acceptanceExpr V input).eval (stateEncoding V input cfg valid) = true ↔
      valid = true ∧ cfg = accepting V := by
  rw [acceptanceExpr_eval]
  constructor
  · rintro ⟨hv, hbits⟩
    refine ⟨by simpa using hv, ?_⟩
    apply MachineCircuit.configEncoding_injective (capacity V input.length)
      cfg (accepting V) hcfg (accepting_stack_le V input)
    funext b
    have h := hbits (bitEquiv V input b)
    simpa [stateEncoding] using h
  · rintro ⟨hv, rfl⟩
    simp [stateEncoding, hv]

theorem circuitOfVerifier_eval (V : NPVerifier) (input : List Bool) (bits : FreeBits V input) :
    (circuitOfVerifier V input).eval bits =
      (acceptanceExpr V input).eval ((timeFrame V input (V.horizon input.length)).eval bits) := by
  change (((timeFrame V input (V.horizon input.length)).step
    (fun _ : Fin 1 => acceptanceExpr V input)).toCircuit 0).eval bits = _
  rw [Frame.toCircuit_eval, Frame.step_eval]

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitializeEncoding
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionQuery

def Ext (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) : Prop :=
  items.Valid ∧ ∃ assignments : List Nat,
    (RawPacking.mk bins assignments).Feasible items ∧ Agrees fixed assignments

theorem ext_none_iff (bins : Nat) (items : RawInstance) :
    Ext bins items (List.replicate items.length none) ↔
      items.Valid ∧ ∃ assignments : List Nat,
        (RawPacking.mk bins assignments).Feasible items := by
  constructor
  · rintro ⟨valid, assignments, feasible, _⟩
    exact ⟨valid, assignments, feasible⟩
  · rintro ⟨valid, assignments, feasible⟩
    refine ⟨valid, assignments, feasible, ?_⟩
    exact (agrees_replicate_none items.length assignments).mpr feasible.1.symm

end BinPackingGap.ExtensionQuery

namespace BinPackingGap.SearchSemantics

open ExtensionQuery

structure State where
  items : RawInstance
  phase : Phase
  bins : Nat
  item : Nat
  label : Nat
  fixed : List (Option Nat)
  deriving DecidableEq, Repr

def initial (r : RawInstance) (valid : Bool) : State :=
  if valid then
    if r.length = 0 then ⟨r, .done, 0, 0, 0, []⟩
    else ⟨r, .find, 1, 0, 0, List.replicate r.length none⟩
  else ⟨r, .invalid, 0, 0, 0, []⟩

def query (s : State) : List Bool :=
  match s.phase with
  | .find => BinaryEncoding.extensionBits s.bins s.items s.fixed
  | .fill => BinaryEncoding.extensionBits s.bins s.items
      (s.fixed.set s.item (some s.label))
  | .done | .invalid => []

def update (s : State) (answer : Bool) : State :=
  match s.phase with
  | .find =>
      if answer then { s with phase := .fill, item := 0, label := 0 }
      else { s with bins := s.bins + 1 }
  | .fill =>
      if answer then
        { s with phase := if s.item + 1 = s.items.length then .done else .fill
                 item := s.item + 1, label := 0
                 fixed := s.fixed.set s.item (some s.label) }
      else { s with label := s.label + 1 }
  | .done | .invalid => s

def step (D : List Bool → Bool) (s : State) : State := update s (D (query s))

def run (D : List Bool → Bool) : Nat → State → State
  | 0, s => s
  | t + 1, s => run D t (step D s)

theorem run_eq_iterate (D : List Bool → Bool) (t : Nat) (s : State) :
    run D t s = (step D)^[t] s := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
      simpa only [run, Function.iterate_succ_apply] using ih (step D s)

def fuel (r : RawInstance) : Nat := r.length * (r.length + 1)

def output (s : State) : Option RawPacking :=
  match s.phase with
  | .done => some ⟨s.bins, labels s.fixed⟩
  | _ => none

def search (D : List Bool → Bool) (r : RawInstance) (valid : Bool) : Option RawPacking :=
  output (run D (if valid then fuel r else 0) (initial r valid))

@[simp] theorem update_items (s : State) (answer : Bool) :
    (update s answer).items = s.items := by
  cases h : s.phase <;> cases answer <;> simp [update, h]

@[simp] theorem step_done (D : List Bool → Bool) (s : State) (h : s.phase = .done) :
    step D s = s := by simp [step, update, h]

@[simp] theorem step_invalid (D : List Bool → Bool) (s : State) (h : s.phase = .invalid) :
    step D s = s := by simp [step, update, h]

@[simp] theorem search_empty (D : List Bool → Bool) :
    search D [] true = some ⟨0, []⟩ := by
  simp [search, initial, fuel, run, output, labels]

@[simp] theorem search_invalid (D : List Bool → Bool) (r : RawInstance) :
    search D r false = none := by
  simp [search, initial, run, output]

end BinPackingGap.SearchSemantics

namespace BinPackingGap.ExtensionCertificate

open ExtensionQuery

def validItems (items : RawInstance) : Bool :=
  items.all fun q => decide (0 < q.1 ∧ q.1 ≤ q.2)

def capacityCheck (items : RawInstance) (assignments : List Nat) (label : Nat) : Bool :=
  let total := RawPacking.loadFraction items assignments label
  decide (total.1 ≤ total.2)

def check (bins : Nat) (items : RawInstance) (fixed : List (Option Nat))
    (assignments : List Nat) : Bool :=
  validItems items &&
    (decide (assignments.length = items.length) &&
      (assignments.all (fun label => decide (label < bins)) &&
        (agreesBool fixed assignments &&
          assignments.all (capacityCheck items assignments))))

def verify (inputWitness : List Bool × List Bool) : Bool :=
  match BinaryEncoding.decodeExtension inputWitness.1,
      BinaryEncoding.decodeAssignments inputWitness.2 with
  | some (bins, items, fixed), some assignments => check bins items fixed assignments
  | _, _ => false

def language (input : List Bool) : Prop :=
  match BinaryEncoding.decodeExtension input with
  | some (bins, items, fixed) => Ext bins items fixed
  | none => False

@[simp] theorem validItems_eq_true_iff (items : RawInstance) :
    validItems items = true ↔ items.Valid := by
  simp [validItems, RawInstance.Valid]

@[simp] theorem capacityCheck_eq_true_iff (items : RawInstance)
    (assignments : List Nat) (label : Nat) :
    capacityCheck items assignments label = true ↔
      (RawPacking.loadFraction items assignments label).1 ≤
        (RawPacking.loadFraction items assignments label).2 := by
  simp [capacityCheck]

theorem check_eq_true_iff (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) (assignments : List Nat) :
    check bins items fixed assignments = true ↔
      items.Valid ∧ (RawPacking.mk bins assignments).Feasible items ∧
        Agrees fixed assignments := by
  simp only [check, Bool.and_eq_true, validItems_eq_true_iff,
    List.all_eq_true, decide_eq_true_eq, agreesBool_eq_true_iff,
    capacityCheck_eq_true_iff]
  constructor
  · rintro ⟨valid, lengths, range, agrees, capacities⟩
    refine ⟨valid, ?_, agrees⟩
    apply (RawPacking.feasible_iff_mem_capacity items ⟨bins, assignments⟩).mpr
    refine ⟨lengths, range, ?_⟩
    intro label mem
    exact (RawPacking.load_le_one_iff items valid assignments label).mpr
      (capacities label mem)
  · rintro ⟨valid, feasible, agrees⟩
    obtain ⟨lengths, range, capacities⟩ :=
      (RawPacking.feasible_iff_mem_capacity items ⟨bins, assignments⟩).mp feasible
    refine ⟨valid, lengths, range, agrees, ?_⟩
    intro label mem
    exact (RawPacking.load_le_one_iff items valid assignments label).mp
      (capacities label mem)

@[simp] theorem verify_encoded (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) (assignments : List Nat) :
    verify (BinaryEncoding.extensionBits bins items fixed,
      BinaryEncoding.assignmentBits assignments) = check bins items fixed assignments := by
  simp [verify]

@[simp] theorem language_extensionBits (bins : Nat) (items : RawInstance)
    (fixed : List (Option Nat)) :
    language (BinaryEncoding.extensionBits bins items fixed) ↔ Ext bins items fixed := by
  simp [language]

theorem verify_sound (input witness : List Bool) (accepted : verify (input, witness) = true) :
    language input := by
  cases parsed : BinaryEncoding.decodeExtension input with
  | none => simp [verify, parsed] at accepted
  | some query =>
      rcases query with ⟨bins, items, fixed⟩
      cases certificate : BinaryEncoding.decodeAssignments witness with
      | none => simp [verify, parsed, certificate] at accepted
      | some assignments =>
          have checked : check bins items fixed assignments = true := by
            simpa [verify, parsed, certificate] using accepted
          obtain ⟨valid, feasible, agrees⟩ :=
            (check_eq_true_iff bins items fixed assignments).mp checked
          change (match BinaryEncoding.decodeExtension input with
            | some (b, r, p) => Ext b r p
            | none => False)
          rw [parsed]
          exact ⟨valid, assignments, feasible, agrees⟩

end BinPackingGap.ExtensionCertificate

namespace BinPackingGap.SearchEncoding

open SearchSemantics BinaryEncoding BinPackingGames.Foundations.Complexity

def phaseBits : Phase → List Bool
  | .find => [false, false]
  | .fill => [false, true]
  | .done => [true, false]
  | .invalid => [true, true]

@[simp] theorem phaseBits_length (phase : Phase) : (phaseBits phase).length = 2 := by
  cases phase <;> rfl

def fixedBits (fixed : List (Option Nat)) : List Bool :=
  listBits (optionBits natBits) fixed

def stateBits (s : State) : List Bool :=
  phaseBits s.phase ++ encodeWord s.bins ++ encodeWord s.item ++ encodeWord s.label ++
    rawInstanceBits s.items ++ fixedBits s.fixed

@[simp] theorem stateBits_length (s : State) :
    (stateBits s).length = 5 + s.bins + s.item + s.label +
      (rawInstanceBits s.items).length + (fixedBits s.fixed).length := by
  simp only [stateBits, List.length_append, phaseBits_length, encodeWord_length]
  omega

end BinPackingGap.SearchEncoding

namespace BinPackingGap.SearchMachineComposition

open Turing BinPackingGames.Foundations.Complexity
open SearchSemantics SearchEncoding

def «initialize_» (input : List Bool) : Nat × State :=
  match BinaryEncoding.decodeRawInstance input with
  | none => (0, initial [] false)
  | some items =>
      let valid := ExtensionCertificate.validItems items
      (if valid then fuel items else 0, initial items valid)

def algorithm (D : List Bool → Bool) (input : List Bool) : Option RawPacking :=
  output (MachineBoundedIteration.iterate (step D) («initialize_» input))

theorem algorithm_eq_search (D : List Bool → Bool) (input : List Bool) :
    algorithm D input =
      match BinaryEncoding.decodeRawInstance input with
      | none => none
      | some items => search D items (ExtensionCertificate.validItems items) := by
  cases parsed : BinaryEncoding.decodeRawInstance input with
  | none => simp [algorithm, «initialize_», parsed, MachineBoundedIteration.iterate,
      initial, output]
  | some items =>
      simp only [algorithm, «initialize_», parsed, MachineBoundedIteration.iterate,
        search, run_eq_iterate]

@[simp] theorem algorithm_encoded (D : List Bool → Bool) (items : RawInstance) :
    algorithm D (BinaryEncoding.rawInstanceBits items) =
      search D items (ExtensionCertificate.validItems items) := by
  simp [algorithm_eq_search]

@[simp] theorem algorithm_malformed (D : List Bool → Bool) (input : List Bool)
    (malformed : BinaryEncoding.decodeRawInstance input = none) :
    algorithm D input = none := by
  simp [algorithm_eq_search, malformed]

@[simp] theorem algorithm_empty (D : List Bool → Bool) :
    algorithm D (BinaryEncoding.rawInstanceBits []) = some ⟨0, []⟩ := by
  simp [ExtensionCertificate.validItems]

end BinPackingGap.SearchMachineComposition

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialItemsMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionNatMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

theorem natTrace (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (accepted rejected : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = statement slots labels accepted rejected label)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (input : base (slots 0) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base (slots 2) = []) (ambient : A) :
    (MachineComposition.advance (TM2.step p))^[2 * n.size + 2]
      (some ⟨some (labels .scan), BinaryAddMachine.clean ambient, base⟩) =
      some ⟨accepted, BinaryAddMachine.clean ambient, resultTapes slots base n suffix⟩ := by
  let source := ExtensionMachineRegisters.program
    (ExtensionMachineRegisters.Lens.ofEquiv (scannerEquiv A).symm) p
  have atScan : source (labels .scan) =
      BinPackingCompleteness.BinaryNameMachine.scan (slots 0) (slots 2)
        (labels .scan) (some (labels .restore)) rejected := by
    change ExtensionMachineRegisters.statement
      (ExtensionMachineRegisters.Lens.ofEquiv (scannerEquiv A).symm) (p (labels .scan)) = _
    rw [atLabels .scan]
    exact ExtensionMachineRegisters.statement_ofEquiv_symm (scannerEquiv A).symm _
  have hd (i j : Fin 3) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
  have first := BinPackingCompleteness.BinaryNameMachine.framedTrace
    (slots 0) (slots 2) (hd 0 2 (by decide)) (labels .scan)
    (some (labels .restore)) rejected source atScan base (ambient, false)
    n.bits suffix [] none
  have canonical := BinPackingCompleteness.BinaryParsing.canonical_nat_bits n
  rw [canonical] at first
  simp only [↓reduceIte, List.append_nil] at first
  have translated := ExtensionMachineRegisters.equivTrace (scannerEquiv A) p _ _ _ first
  let afterScan := tapesAt (slots 0) (slots 2) base suffix n.bits.reverse
  have initial : tapesAt (slots 0) (slots 2) base
      (BinPackingCompleteness.BinaryNameMachine.frame n.bits ++ suffix) [] = base := by
    rw [BinPackingCompleteness.BinaryParsing.frame_eq]
    change tapesAt (slots 0) (slots 2) base (BinaryEncoding.natBits n ++ suffix) [] = base
    rw [← input, ← scratchEmpty]
    exact tapesAt_self _ _ _
  have translated' : (MachineComposition.advance (TM2.step p))^[n.size + 1]
      (some ⟨some (labels .scan), BinaryAddMachine.clean ambient, base⟩) =
      some ⟨some (labels .restore), BinaryAddMachine.clean ambient, afterScan⟩ := by
    simpa only [ExtensionMachineRegisters.equivConfiguration, scannerEquiv,
      Equiv.coe_fn_mk, BinPackingCompleteness.BinaryNameMachine.clean,
      BinaryAddMachine.clean, BinaryAddMachine.state, initial, afterScan,
      ← Nat.size_eq_bits_len] using translated
  have saved : afterScan (slots 2) = n.bits.reverse := by simp [afterScan, tapesAt]
  have destination : afterScan (slots 1) = base (slots 1) := by
    simp [afterScan, tapesAt, hd 1 0 (by decide), hd 1 2 (by decide)]
  have second := transferAt_fromTapes (slots 2) (slots 1) (hd 2 1 (by decide))
    (id : Bool → Bool) false (labels .restore) accepted p
    (by simpa only [statement] using atLabels .restore) afterScan
    ((ambient, false), none) none
  rw [saved, destination] at second
  have final : tapesAt (slots 2) (slots 1) afterScan []
      (n.bits ++ base (slots 1)) = resultTapes slots base n suffix := by
    funext k
    by_cases hout : k = slots 1
    · subst k; simp [tapesAt, resultTapes]
    by_cases hscratch : k = slots 2
    · subst k
      simp [tapesAt, resultTapes, hd 2 1 (by decide), hd 2 0 (by decide), scratchEmpty]
    simp [tapesAt, afterScan, resultTapes, hout, hscratch]
  have second' : (MachineComposition.advance (TM2.step p))^[n.size + 1]
      (some ⟨some (labels .restore), BinaryAddMachine.clean ambient, afterScan⟩) =
      some ⟨accepted, BinaryAddMachine.clean ambient, resultTapes slots base n suffix⟩ := by
    change (nextAt (Γ := Alphabet) (slots 1) p)^[n.size + 1]
      (some ⟨some (labels .restore), BinaryAddMachine.clean ambient, afterScan⟩) =
      some ⟨accepted, BinaryAddMachine.clean ambient, resultTapes slots base n suffix⟩
    simpa only [List.length_reverse, List.reverse_reverse, List.map_id_fun,
      id_eq, ← Nat.size_eq_bits_len, final, BinaryAddMachine.clean,
      BinaryAddMachine.state] using second
  rw [show 2 * n.size + 2 = (n.size + 1) + (n.size + 1) by omega,
    Function.iterate_add_apply, translated', second']

def natInTime (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (accepted rejected : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = statement slots labels accepted rejected label)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (input : base (slots 0) = BinaryEncoding.natBits n ++ suffix)
    (scratchEmpty : base (slots 2) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .scan), BinaryAddMachine.clean ambient, base⟩
      (some ⟨accepted, BinaryAddMachine.clean ambient, resultTapes slots base n suffix⟩)
      (2 * n.size + 2) where
  steps := 2 * n.size + 2
  evals_in_steps := natTrace slots labels accepted rejected p atLabels base n suffix
    input scratchEmpty ambient
  steps_le_m := Nat.le_refl _

def orderStatement (slots : Fin 5 ↪ K) (labels : BinaryOrderMachine.PreserveLabel → Λ)
    (exits : Ordering → Option Λ) (label : BinaryOrderMachine.PreserveLabel) :
    TM2.Stmt (Alphabet (K := K)) Λ (State (A × Ordering)) :=
  ExtensionMachineRegisters.statement
    (ExtensionMachineRegisters.Lens.ofEquiv (orderEquiv A))
    (BinaryOrderMachine.preservingInstruction slots labels exits label)

def preservingOrderInTime (slots : Fin 5 ↪ K)
    (labels : BinaryOrderMachine.PreserveLabel → Λ) (exits : Ordering → Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State (A × Ordering)))
    (atLabels : ∀ label, p (labels label) = orderStatement slots labels exits label)
    (base : K → List Bool) (a b : Nat)
    (leftWord : base (slots 0) = a.bits) (rightWord : base (slots 1) = b.bits)
    (leftEmpty : base (slots 2) = []) (rightEmpty : base (slots 3) = [])
    (scratchEmpty : base (slots 4) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .leftOut), BinaryAddMachine.clean (ambient, .eq), base⟩
      (some ⟨exits (BinaryOrderMachine.orderNat a b .eq),
        BinaryAddMachine.clean (ambient, .eq), base⟩)
      (BinaryOrderMachine.preservingSteps a.size b.size) := by
  let source := ExtensionMachineRegisters.program
    (ExtensionMachineRegisters.Lens.ofEquiv (orderEquiv A).symm) p
  have atSource : ∀ label, source (labels label) =
      BinaryOrderMachine.preservingInstruction slots labels exits label := by
    intro label
    change ExtensionMachineRegisters.statement
      (ExtensionMachineRegisters.Lens.ofEquiv (orderEquiv A).symm) (p (labels label)) = _
    rw [atLabels]
    exact ExtensionMachineRegisters.statement_ofEquiv_symm (orderEquiv A).symm _
  have run := BinaryOrderMachine.preservingNatInTime slots labels exits source atSource
    base a b leftWord rightWord leftEmpty rightEmpty scratchEmpty (ambient, false)
  have lifted := ExtensionMachineRegisters.equivExecution (orderEquiv A) p run
  simpa only [ExtensionMachineRegisters.equivConfiguration, orderEquiv,
    Equiv.coe_fn_mk, BinaryOrderMachine.clean, BinaryAddMachine.clean,
    BinaryAddMachine.state, Option.map_some] using lifted

end BinPackingGap.ExtensionNatMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPowerProgram
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BooleanTapeCode

open Turing FiniteTapeProgram BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {K A : Type} [DecidableEq K]

def copyProgram (source destination scratch : K) :
    Bool → TM2.Stmt (fun _ : K => Bool) Bool (State A)
  | false => MachineTransfer.loopAt source scratch id false false (some true)
  | true => MachineCopy.forkLoop scratch source destination false true none

def copy (source destination scratch : K) : Program K A :=
  .routine Bool inferInstance false (copyProgram source destination scratch)

theorem copy_exec (source destination scratch : K)
    (hSD : source ≠ destination) (hSW : source ≠ scratch) (hDW : destination ≠ scratch)
    (base : K → List Bool) (hW : base scratch = []) (s : State A) :
    Exec (copy source destination scratch) ⟨s, base⟩ (2 * ((base source).length + 1))
      ⟨(s.1, none), Function.update base destination (base source ++ base destination)⟩ := by
  apply Exec.routine
  exact MachineCopy.copyTrace source destination scratch hSD hSW hDW false false true none
    (copyProgram source destination scratch) rfl rfl base hW s.1 s.2

def drain (source : K) : Program K A :=
  .routine Unit inferInstance () (fun _ => MachineDrain.drain source () none)

theorem drain_exec (source : K) (base : K → List Bool) (s : State A) :
    Exec (drain source) ⟨s, base⟩ ((base source).length + 1)
      ⟨(s.1, none), Function.update base source []⟩ := by
  apply Exec.routine
  simpa only [Function.update_eq_self] using
    MachineDrain.drainTrace source () none (fun _ : Unit => MachineDrain.drain source () none)
      rfl base (base source) s.1 s.2

theorem convert_exec (source destination scratch : K)
    (hSD : source ≠ destination) (hSW : source ≠ scratch) (hDW : destination ≠ scratch)
    (base : K → List Bool) (a : A) (n initial : Nat) (suffix : List Bool) :
    Exec (convert source destination scratch)
      ⟨clean a, UnaryToBinaryMachine.tapes source destination scratch base
        (encodeWord n ++ suffix) initial.bits []⟩
      (UnaryToBinaryMachine.steps n initial)
      ⟨clean a, UnaryToBinaryMachine.tapes source destination scratch base
        suffix (initial + n).bits []⟩ := by
  apply Exec.routine
  exact UnaryToBinaryMachine.convertTrace source destination scratch hSD hSW hDW id none
    (UnaryToBinaryMachine.instruction source destination scratch id none) (fun _ => rfl)
    base (a, ()) n initial suffix

theorem increment_exec {n : Nat} (binary unary scratch : K)
    (hUB : unary ≠ binary) (hUW : unary ≠ scratch) (hBW : binary ≠ scratch)
    (base : K → List Bool) (hU : base unary = []) (hW : base scratch = [])
    (hB : base binary = n.bits) (a : A) (register : Option Bool) :
    Exec (increment binary unary scratch) ⟨((a, ()), register), base⟩
      (1 + UnaryToBinaryMachine.steps 1 n)
      ⟨clean a, Function.update base binary (n + 1).bits⟩ := by
  have first := Exec.atom (.push unary (fun _ => false)
    (.push unary (fun _ => true) (.load (fun s => (s.1, none)) .done)))
    (Data.mk ((a, ()), register) base)
  have second := convert_exec unary binary scratch hUB hUW hBW base a 1 n []
  have startEq : UnaryToBinaryMachine.tapes unary binary scratch base
      (encodeWord 1 ++ []) n.bits [] = Function.update base unary [true, false] := by
    funext k
    by_cases hk : k = unary
    · subst k; simp [UnaryToBinaryMachine.tapes, encodeWord, hUB, hUW]
    · by_cases hb : k = binary
      · subst k; simp [UnaryToBinaryMachine.tapes, hBW, hB, hk]
      · by_cases hw : k = scratch
        · subst k; simp [UnaryToBinaryMachine.tapes, hW, hk]
        · simp [UnaryToBinaryMachine.tapes, hk, hb, hw]
  have endEq : UnaryToBinaryMachine.tapes unary binary scratch base [] (n + 1).bits [] =
      Function.update base binary (n + 1).bits := by
    funext k
    by_cases hk : k = unary
    · subst k; simp [UnaryToBinaryMachine.tapes, hUB, hUW, hU]
    · by_cases hb : k = binary
      · subst k; simp [UnaryToBinaryMachine.tapes, hBW]
      · by_cases hw : k = scratch
        · subst k; simp [UnaryToBinaryMachine.tapes, hW, hBW.symm]
        · simp [UnaryToBinaryMachine.tapes, hk, hb, hw]
  rw [startEq, endEq] at second
  exact Exec.seq (by simpa [Action.eval, hU, clean] using first) second

end BinPackingGap.BooleanTapeCode

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryToTallyMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
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

def code (slot : (Reg ⊕ Fin 6) ↪ K) :
    List (Command Reg) → Code (K := K) (S := BinaryAddMachine.State A)
  | [] => .atom .done
  | command :: tail =>
    .seq (.routine (LocalLabel command) inferInstance (main command)
      (localInstruction slot command id none)) (code slot tail)

theorem final_width (commands : List (Command Reg)) (values : Reg → Nat)
    (width : Nat) (hwidth : ∀ r, (values r).size ≤ width) :
    ∀ r, (resultOf commands values r).size ≤ staticWidth commands width := by
  have hb := bitBounded_from_input commands values width hwidth
  generalize hw : staticWidth commands width = bound at hb ⊢
  clear hw hwidth
  induction commands generalizing values with
  | nil => exact hb
  | cons command tail ih => exact ih (result command values) hb.2

end BinPackingGap.BinaryRegisterStructured

namespace BinPackingGap.BinaryToTallyMachine

open BinPackingGames.Foundations.Complexity BinaryRegisterProgram FiniteTapeProgram

def subtractOperands : Operands Reg where
  destination := .temporary
  left := .counter
  right := .one
  left_ne_right := by decide
  left_ne_destination := by decide
  right_ne_destination := by decide

def prepareCommands : List (Command Reg) :=
  [.copy .counter .source (by decide), .constant .one 1]

def decrementCommands : List (Command Reg) :=
  [.monus subtractOperands, .clear .counter,
    .copy .counter .temporary (by decide), .clear .temporary]

def finishCommands : List (Command Reg) := [.clear .one]

theorem prepare_ready (n : Nat) : Ready prepareCommands (initial n) := by
  simp [prepareCommands, Ready, commandReady, result, destination, value, initial]

theorem prepare_result (n : Nat) :
    resultOf prepareCommands (initial n) = running n n := by
  funext r
  cases r <;> simp [prepareCommands, resultOf, MachineFiniteSequence.resultOf,
    result, destination, value, initial, running]

theorem prepare_budget (n : Nat) :
    budget prepareCommands (initial n) + 1 = 2 * n.size + 4 := by
  simp [prepareCommands, budget, MachineFiniteSequence.steps, cost, initial]
  omega

theorem decrement_ready (n r : Nat) : Ready decrementCommands (running n (r + 1)) := by
  simp [decrementCommands, Ready, commandReady, result, destination, value,
    subtractOperands, running]

theorem decrement_result (n r : Nat) :
    resultOf decrementCommands (running n (r + 1)) = running n r := by
  funext q
  cases q <;> simp [decrementCommands, resultOf, MachineFiniteSequence.resultOf,
    result, destination, value, subtractOperands, running]

theorem decrement_budget (n r : Nat) :
    budget decrementCommands (running n (r + 1)) + 1 =
      6 * (r + 1).size + 3 * r.size + 17 := by
  simp [decrementCommands, budget, MachineFiniteSequence.steps, cost, result,
    destination, value, subtractOperands, running, Nat.size_one]
  omega

theorem finish_ready (n : Nat) : Ready finishCommands (running n 0) := by
  simp [finishCommands, Ready, commandReady]

theorem finish_result (n : Nat) :
    resultOf finishCommands (running n 0) = initial n := by
  funext r
  cases r <;> simp [finishCommands, resultOf, MachineFiniteSequence.resultOf,
    result, destination, value, running, initial]

theorem finish_budget (n : Nat) : budget finishCommands (running n 0) + 1 = 3 := by
  simp [finishCommands, budget, MachineFiniteSequence.steps, cost, running, Nat.size_one]

variable {K A : Type} [DecidableEq K]

def body (slot : (Reg ⊕ Fin 6) ↪ K) (output : K) : Code (K := K) (S := State A) :=
  .seq (.atom reset) (.seq (BinaryRegisterStructured.code slot decrementCommands)
    (.atom (.push output (fun _ => true) .done)))

def loop (slot : (Reg ⊕ Fin 6) ↪ K) (output : K) : Code (K := K) (S := State A) :=
  .loop (guard slot) more (body slot output)

def code (slot : (Reg ⊕ Fin 6) ↪ K) (output : K) : Code (K := K) (S := State A) :=
  .seq (BinaryRegisterStructured.code slot prepareCommands)
    (.seq (loop slot output) (BinaryRegisterStructured.code slot finishCommands))

theorem bits_succ_nonempty (r : Nat) : (r + 1).bits ≠ [] := by
  intro h
  have hv := congrArg BinaryArithmetic.bitValue h
  simp only [BinaryArithmetic.bitValue_bits, BinaryArithmetic.bitValue_nil] at hv
  omega

theorem guard_more (slot : (Reg ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (n r : Nat) (ambient : A) :
    more ((guard slot).eval
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n (r + 1))⟩).state =
      true := by
  have h := bits_succ_nonempty r
  simp only [guard, Action.eval, registerTapes_reg, running, more]
  cases hb : (r + 1).bits with
  | nil => exact False.elim (h hb)
  | cons b bs => rfl

end BinPackingGap.BinaryToTallyMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitProducer
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop

open Turing
open BinPackingGames.Foundations.Hastad
open CircuitProducerModel CircuitEmission CircuitProducerStages

theorem fourTapes_eq (base : Tape → List Bool) (input counter acc suffix : List Bool)
    (r : Record) :
    SourceMachine.fourTapes .input Tape.field
      (tapes base input counter acc (fun _ => [])) r.tag.val r.output r.first r.second suffix =
      tapes base suffix counter acc (parsedFields r) := by
  funext tape
  cases tape with
  | field j =>
      fin_cases j <;>
        simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
          tapes, parsedFields, Record.fieldValue]
  | _ =>
      simp [SourceMachine.fourTapes, SourceMachine.afterField, SourceMachine.fieldTapes,
        tapes]

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerLoop

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ClashMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate

section

open PostfixModel

def nonemptyTokens (q : Nat) : List Token :=
  forTokens (q + 1) (fun i => [.input i]) ++ closeOr (q + 1)

def clashRowTokens (q i : Nat) : List Token :=
  forTokens (q + 1) (clashPairTokens i) ++ closeOr (q + 1)

def clashTokens (q : Nat) : List Token :=
  forTokens (q + 1) (clashRowTokens q) ++ closeOr (q + 1)

def validityTokens (q : Nat) : List Token :=
  nonemptyTokens q ++ clashTokens q ++ [.not, .and]

end

open StatementCircuit WitnessCircuit WitnessEncoding PostfixModel PostfixAlignment CircuitBatch

theorem clashPairTokens_eq (q : Nat) (i j : Fin (q + 1)) :
    clashPairTokens i.val j.val = exprTokens Fin.val (clashPairExpr q i j) := by
  by_cases h : i = j
  · subst j; simp [clashPairTokens, clashPairExpr, exprTokens]
  · have hv : i.val ≠ j.val := fun hval => h (Fin.ext hval)
    simp [clashPairTokens, clashPairExpr, h, hv, selectorExpr, exprTokens]

section Symbols

variable {A : Type*} [DecidableEq A]

theorem payloadSymbolTokens_eq (q : Nat) (f : Bool → A) (i : Fin q) (a : Option A) :
    payloadSymbolTokens q f i.val a = exprTokens Fin.val (payloadSymbolExpr q f i a) := by
  simp [payloadSymbolExpr, payloadSymbolTokens, exprTokens_mux, payloadExpr,
    exprTokens, muxTokens]

end Symbols

noncomputable section Frame

open VerifierCircuit

local instance labelDecidable (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance stateDecidable (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

end Frame

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationTemplate

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

theorem emitted_other (output count k : K) (ho : k ≠ output) (hc : k ≠ count)
    (base : K → List Bool) (tokens : List Token) : emitted output count base tokens k = base k := by
  simp [emitted, ho, hc]

namespace Pair

inductive Label where
  | left (l : MachineUnaryLessAt.Label)
  | right (l : MachineUnaryLessAt.Label)
  | branchLeft | branchRight | diagonal
  | inputLeft (l : Input.Label)
  | inputRight (l : Input.Label)
  | conjunction
  deriving DecidableEq, Fintype

end Pair

namespace Row

inductive Label where
  | guard
  | pair (l : Pair.Label)
  | increment
  deriving DecidableEq, Fintype

theorem counter_frame (slots : Fin 7 ↪ K) (base : K → List Bool) (r r' j : Nat) :
    MachineUnaryCounter.counterTapes (slots 0) (frame slots base r j) r' [] =
      frame slots base r' j := by
  funext k
  by_cases h₀ : k = slots 0
  · subst k; simp [MachineUnaryCounter.counterTapes, frame, slots.injective.eq_iff]
  · by_cases h₂ : k = slots 2 <;> simp [MachineUnaryCounter.counterTapes, frame, h₀, h₂]

theorem emitted_frame (slots : Fin 7 ↪ K) (base : K → List Bool) (r j : Nat) (tokens : List Token) :
    emitted (slots 5) (slots 6) (frame slots base r j) tokens =
      frame slots (emitted (slots 5) (slots 6) base tokens) r j := by
  funext k
  by_cases h₀ : k = slots 0
  · subst k; simp [emitted, frame, slots.injective.eq_iff]
  · by_cases h₂ : k = slots 2
    · subst k; simp [emitted, frame, slots.injective.eq_iff]
    · by_cases h₅ : k = slots 5
      · subst k; simp [emitted, frame, slots.injective.eq_iff]
      · by_cases h₆ : k = slots 6
        · subst k; simp [emitted, frame, slots.injective.eq_iff]
        · simp [emitted, frame, h₀, h₂, h₅, h₆]

theorem increment_frame (slots : Fin 7 ↪ K) (base : K → List Bool) (r j : Nat) :
    Function.update (frame slots base r j) (slots 2) (true :: encodeWord j) =
      frame slots base r (j + 1) := by
  simp [frame, encodeWord, List.replicate_succ]

def tokens (count i start : Nat) : List Token :=
  forTokens count (fun j => clashPairTokens i (start + j))

theorem tokens_zero (i start : Nat) : tokens 0 i start = [] := rfl

end Row

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PolynomialMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PolynomialMachine

section LiteralFields

open Turing
open BinPackingGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

theorem stepAux_prependFields (word : K → List Bool) (indices : List K)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (prependFields word indices continuation) state tapes =
      TM2.stepAux continuation state (prependFieldsTapes word indices tapes) := by
  induction indices generalizing tapes with
  | nil => rfl
  | cons k rest ih =>
    simp only [prependFields, stepAux_pushWord, List.reverse_reverse, prependFieldsTapes]
    exact ih _

theorem stepAux_clearFields (count : K → Nat) (indices : List K)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (clearFields count indices continuation) state tapes =
      TM2.stepAux continuation state (clearFieldsTapes count indices tapes) := by
  induction indices generalizing tapes with
  | nil => rfl
  | cons k rest ih =>
    simp only [clearFields, stepAux_popN, clearFieldsTapes]
    exact ih _

end LiteralFields

noncomputable section

def timePolynomial (p : Polynomial Nat) : Polynomial Nat :=
  prefixCostPolynomial (digit p) (width p) +
    Polynomial.C 2 * prefixValuePolynomial (digit p) (width p) + Polynomial.X + Polynomial.C 8

theorem timePolynomial_eval (p : Polynomial Nat) (n : Nat) :
    (timePolynomial p).eval n = MachineHorner.steps n (digit p) (width p) + n + 3 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, prefixValuePolynomial_eval,
    prefixCostPolynomial_eval, MachineHorner.steps]
  omega

theorem hornerValue_eq_eval (p : Polynomial Nat) (n : Nat) :
    MachineHorner.value n (digit p) (width p) = p.eval n := by
  rw [MachineHorner.value_eq_foldl, range_map_digit]
  have hh := highCoefficients_foldl p n
  simpa only [Nat.mul_comm] using hh

end

end BinPackingGames.Foundations.Complexity.CookLevin.PolynomialMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted emitted_other emitted_nil)

variable {K Λ σ : Type} [DecidableEq K]

namespace SelectorLoop

theorem counter_frame (slots : Fin 5 ↪ K) (base : K → List Bool) (r r' j : Nat) :
    MachineUnaryCounter.counterTapes (slots 0) (frame slots base r j) r' [] =
      frame slots base r' j := by
  funext k
  by_cases h₀ : k = slots 0
  · subst k; simp [MachineUnaryCounter.counterTapes, frame, slots.injective.eq_iff]
  · by_cases h₁ : k = slots 1 <;> simp [MachineUnaryCounter.counterTapes, frame, h₀, h₁]

theorem emitted_frame (slots : Fin 5 ↪ K) (base : K → List Bool) (r j : Nat) (tokens : List Token) :
    emitted (slots 3) (slots 4) (frame slots base r j) tokens =
      frame slots (emitted (slots 3) (slots 4) base tokens) r j := by
  funext k
  by_cases h₀ : k = slots 0
  · subst k; simp [emitted, frame, slots.injective.eq_iff]
  · by_cases h₁ : k = slots 1
    · subst k; simp [emitted, frame, slots.injective.eq_iff]
    · by_cases h₃ : k = slots 3
      · subst k; simp [emitted, frame, slots.injective.eq_iff]
      · by_cases h₄ : k = slots 4
        · subst k; simp [emitted, frame, slots.injective.eq_iff]
        · simp [emitted, frame, h₀, h₁, h₃, h₄]

theorem increment_frame (slots : Fin 5 ↪ K) (base : K → List Bool) (r j : Nat) :
    Function.update (frame slots base r j) (slots 1) (true :: encodeWord j) =
      frame slots base r (j + 1) := by
  simp [frame, encodeWord, List.replicate_succ]

def tokens (count start : Nat) : List Token :=
  forTokens count (fun j => [.input (start + j)])

theorem tokens_zero (start : Nat) : tokens 0 start = [] := rfl

theorem steps_le (count start : Nat) :
    steps count start ≤ count * (3 * (start + count + 1) + 5) + 1 := by
  induction count generalizing start with
  | zero => simp [steps]
  | succ count ih =>
    have hr := ih (start + 1)
    have he : start + 1 + count + 1 = start + (count + 1) + 1 := by omega
    rw [he] at hr
    rw [steps, Nat.succ_mul]
    unfold ClashMachine.Input.steps
    omega

end SelectorLoop

namespace Nonempty

def closurePorts (slots : Fin 7 ↪ K) : OrClosure.Ports K where
  remaining := slots 4
  reversed := slots 5
  count := slots 6
  remaining_ne_reversed := slots.injective.ne (by decide)
  remaining_ne_count := slots.injective.ne (by decide)
  reversed_ne_count := slots.injective.ne (by decide)

structure Ready (slots : Fin 7 ↪ K) (base : K → List Bool) (q : Nat) : Prop where
  boundWord : base (slots 0) = encodeWord q
  remainingEmpty : base (slots 1) = []
  currentEmpty : base (slots 2) = []
  scratchEmpty : base (slots 3) = []
  closureEmpty : base (slots 4) = []

theorem emitted_update (output count work : K) (ho : work ≠ output) (hc : work ≠ count)
    (base : K → List Bool) (replacement : List Bool) (tokens : List Token) :
    emitted output count (Function.update base work replacement) tokens =
      Function.update (emitted output count base tokens) work replacement := by
  funext k
  by_cases hw : k = work
  · subst k; simp [emitted, ho, hc]
  · by_cases houtput : k = output
    · subst k
      by_cases hoc : output = count
      · subst count; simp [emitted, Ne.symm ho]
      · simp [emitted, Ne.symm ho, Ne.symm hc, hoc]
    · by_cases hcount : k = count
      · subst k; simp [emitted, Ne.symm hc]
      · simp [emitted, hw, houtput, hcount]

theorem frame_updates (slots : Fin 7 ↪ K) (base : K → List Bool) (r i : Nat) :
    SelectorLoop.frame (loopMap.trans slots) base r i =
      Function.update (Function.update base (slots 1) (encodeWord r)) (slots 2) (encodeWord i) := rfl

theorem tokens_nonempty (q : Nat) :
    SelectorLoop.tokens (q + 1) 0 ++ closeOr (q + 1) = nonemptyTokens q := by
  simp [SelectorLoop.tokens, nonemptyTokens]

theorem closed_frame (p : OrClosure.Ports K) (base : K → List Bool) (n : Nat) :
    OrClosure.frame p base (encodeWord 0)
      ((tokenBits (closeOr n)).reverse ++ base p.reversed)
      (List.replicate (n + 1) true ++ base p.count) =
      emitted p.reversed p.count (Function.update base p.remaining (encodeWord 0)) (closeOr n) := by
  simp only [OrClosure.frame, emitted, closeOr, List.length_append, List.length_singleton,
    List.length_replicate]
  rw [Nat.add_comm 1 n]
  simp only [Function.update_of_ne (Ne.symm p.remaining_ne_reversed),
    Function.update_of_ne (Ne.symm p.remaining_ne_count)]

theorem steps_le (q : Nat) : steps q ≤ 20 * (q + 2) ^ 2 := by
  have h := SelectorLoop.steps_le (q + 1) 0
  simp only [Nat.zero_add] at h
  unfold steps
  nlinarith

end Nonempty

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityComposition
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
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

structure Ready (slots : Fin 10 ↪ K) (base : K → List Bool) (q : Nat) : Prop where
  source : base (slots 0) = encodeWord q
  empty : ∀ k : Fin 10, k ≠ 0 → k ≠ 7 → k ≠ 8 → base (slots k) = []

theorem Ready.emitted {slots : Fin 10 ↪ K} {base : K → List Bool} {q : Nat}
    (h : Ready slots base q) (tokens : List Token) :
    Ready slots (emitted (slots 7) (slots 8) base tokens) q := by
  constructor
  · simpa [ClashMachine.emitted, slots.injective.eq_iff] using h.source
  · intro k hk ho hc
    simpa [ClashMachine.emitted, slots.injective.eq_iff, ho, hc] using h.empty k hk ho hc

def frame (slots : Fin 10 ↪ K) (base : K → List Bool) (remaining current : Nat) : K → List Bool :=
  Function.update (Function.update base (slots 1) (encodeWord remaining)) (slots 3) (encodeWord current)

def closurePorts (slots : Fin 10 ↪ K) : OrClosure.Ports K where
  remaining := slots 9
  reversed := slots 7
  count := slots 8
  remaining_ne_reversed := slots.injective.ne (by decide)
  remaining_ne_count := slots.injective.ne (by decide)
  reversed_ne_count := slots.injective.ne (by decide)

inductive Label where
  | start
  | copy (context : CopyContext) (l : CopyLabel)
  | outerGuard | rowSeed
  | row (l : Row.Label)
  | discardInner | afterInner | rowCloseSeed | rowCloseLoop | rowFinish
  | allCloseSeed | allCloseLoop | discardOuter | finish
  deriving DecidableEq, Fintype

def copyExit (labels : Label → Λ) : CopyContext → Λ
  | .outer => labels .outerGuard
  | .inner => labels (.row .guard)
  | .rowClose => labels .rowCloseSeed
  | .allClose => labels .allCloseSeed

theorem closureTrace (slots : Fin 10 ↪ K) (entry again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atSeed : program entry = OrClosure.seed (closurePorts slots) again)
    (atLoop : program again = OrClosure.loop (closurePorts slots) again exit)
    (base : K → List Bool) (n : Nat) (word : base (slots 9) = encodeWord n) (ambient : σ) :
    (advance (TM2.step program))^[n + 2]
      (some ⟨some entry, clean ambient, base⟩) =
      some ⟨exit, clean ambient, Function.update
        (emitted (slots 7) (slots 8) base (closeOr n)) (slots 9) (encodeWord 0)⟩ := by
  have h := OrClosure.closureTrace (closurePorts slots) entry again exit program atSeed atLoop
    base n [] (base (slots 7)) (base (slots 8)) (ambient, false) none
  have hi : OrClosure.frame (closurePorts slots) base (encodeWord n ++ [])
      (base (slots 7)) (base (slots 8)) = base := by
    rw [List.append_nil, ← word]
    exact OrClosure.frame_self _ _
  have ho : OrClosure.frame (closurePorts slots) base (encodeWord 0 ++ [])
      ((tokenBits (closeOr n)).reverse ++ base (slots 7))
      (List.replicate (n + 1) true ++ base (slots 8)) =
      Function.update (emitted (slots 7) (slots 8) base (closeOr n)) (slots 9) (encodeWord 0) := by
    apply ext_slots slots
    · intro i
      fin_cases i <;> simp [OrClosure.frame, closurePorts, emitted, closeOr, slots.injective.eq_iff]
    · intro k hk
      simp [OrClosure.frame, closurePorts, emitted, hk]
  rw [hi, ho] at h
  exact h

theorem emitted_frame (slots : Fin 10 ↪ K) (base : K → List Bool) (r i : Nat) (tokens : List Token) :
    emitted (slots 7) (slots 8) (frame slots base r i) tokens =
      frame slots (emitted (slots 7) (slots 8) base tokens) r i := by
  apply ext_slots slots
  · intro k
    fin_cases k <;> simp [frame, emitted, slots.injective.eq_iff]
  · intro k hk
    simp [frame, emitted, hk]

theorem counter_frame (slots : Fin 10 ↪ K) (base : K → List Bool) (r r' i : Nat) :
    MachineUnaryCounter.counterTapes (slots 1) (frame slots base r i) r' [] = frame slots base r' i := by
  apply ext_slots slots
  · intro k
    fin_cases k <;> simp [MachineUnaryCounter.counterTapes, frame, slots.injective.eq_iff]
  · intro k hk
    simp [MachineUnaryCounter.counterTapes, frame, hk]

def loopTokens (count q start : Nat) : List Token :=
  forTokens count (fun j => clashRowTokens q (start + j))

end Full

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted)

variable {K Λ σ : Type} [DecidableEq K]

inductive Label where
  | nonempty (l : Nonempty.Label)
  | clash (l : ClashMachine.Full.Label)
  | finish
  deriving DecidableEq, Fintype

theorem steps_le_time (q : Nat) : steps q ≤ timePolynomial.eval q := by
  rw [timePolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nonempty.steps_le q) (ClashMachine.Full.steps_le_time q)) 1

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full

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

local instance alphabetFinite (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) :=
  V.finiteAlphabet
local instance labelFinite (V : NPVerifier) : Fintype V.computation.tm.Λ :=
  V.computation.tm.ΛFin
local instance stateFinite (V : NPVerifier) : Fintype V.computation.tm.σ :=
  V.computation.tm.σFin
local instance labelDecidable (V : NPVerifier) : DecidableEq V.computation.tm.Λ :=
  Classical.decEq _
local instance stateDecidable (V : NPVerifier) : DecidableEq V.computation.tm.σ :=
  Classical.decEq _
local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Information_SourceNonempty
attribute [-instance] _root_.OAI.BinPackingGap.LiteralSlotGraph.instDecidableConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Hastad.SourceGap

open Target SourceContexts SourceOccurrences
open BinPackingGames.Reduction

def ClauseGap (F : Formula) (η : ℚ) : Prop :=
  F.clauses ≠ [] ∧ ∀ assignment : Fin F.variables → Bool,
    (η : ℝ) * F.clauses.length ≤
      (PCP.failureCount F assignment (PCP.allIndices F) : ℝ)

end BinPackingGames.Foundations.Hastad.SourceGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierFront
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InputFrame

open Turing MachineComposition
open BinPackingGames.Reduction.MachineTransfer

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := 0
  σ := State
  initialState := ((), none)
  m := program

def cfg (label : Option Label) (input saved counter : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input saved counter⟩

theorem scanStep_nil (saved counter : List Bool) (register : Option Bool) :
    machine.step (cfg (some 1) [] saved counter register) =
      some (cfg (some 2) [] saved counter) := by
  change some (TM2.stepAux (program 1) _ _) = _
  simp [program, scan, cfg, TM2.stepAux, tapes, update_zero]
  rfl

theorem scanStep_cons (bit : Bool) (input saved counter : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some 1) (bit :: input) saved counter register) =
      some (cfg (some 1) input (bit :: saved) (true :: counter) (some bit)) := by
  change some (TM2.stepAux (program 1) _ _) = _
  simp [program, scan, cfg, TM2.stepAux, tapes, update_zero, update_one, update_two]
  rfl

theorem scanTrace (input saved counter : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 1) input saved counter register)) =
        some (cfg (some 2) [] (input.reverse ++ saved)
          (List.replicate input.length true ++ counter)) := by
  induction input generalizing saved counter register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
      List.reverse_nil, List.replicate_zero, List.nil_append] using
      scanStep_nil saved counter register
  | cons bit input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [advance_some]
    rw [scanStep_cons, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [List.replicate_succ']
    simp only [List.append_assoc, List.singleton_append]

theorem startStep (input : List Bool) :
    machine.step (initList machine input) = some (cfg (some 1) input [] [false]) := by
  change some (TM2.stepAux (program 0) ((),none) _) = _
  simp [program, TM2.stepAux, cfg]
  apply congrArg (fun contents => some (⟨some 1, ((), none), contents⟩ : machine.Cfg))
  funext k
  fin_cases k <;> simp [tapes]

theorem stopped_eq_haltList (output : List Bool) :
    cfg none output [] [] = haltList machine output := by
  unfold cfg haltList
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

end BinPackingGames.Foundations.Complexity.CookLevin.InputFrame

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ProducerFrontStage
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def statement (p : Ports K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (State σ)
  | .copy => Reduction.MachineTransfer.loopAt (p 0) (p 2) id false
      (labels .copy) (some (labels .restore))
  | .restore => MachineCopy.forkLoop (p 2) (p 0) (p 1) false
      (labels .restore) (some (labels .seed))
  | .seed => .push (p 3) (fun _ => false)
      (.push (p 4) (fun _ => false) (Reduction.MachineTransfer.exitAt (p 4) exit))

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly

open Turing PostfixModel

open MachineComposition
open ClashMachine (State clean emitted)

inductive CodeLabel (A : Nat) where
  | control
  | cells (label : CellsMachine.Label A)
  | validity (label : ValidityMachine.Full.Label)
  deriving DecidableEq, Fintype

variable {K Λ σ : Type} [DecidableEq K]

def placedControl (slots : Tape 9 ↪ K) : InitializationControl.Ports K where
  reversed := slots .reversed
  count := slots .count
  distinct := slots.injective.ne (by decide)

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_DropPackingBoundMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.DropPackingBoundMachine

open Turing BinPackingGames.Foundations.Complexity BinPackingGames.Reduction
open BinaryEncoding

theorem output_encoded (out : RawReductionOutput) :
    output .name (rawReductionOutputBits out) = rawInstanceBits out.2 :=
  output_frame out.1.bits (rawInstanceBits out.2)

def reversedMachine : FinTM2 := MachineTransducer.machine Mode.name transition emit

def reversedRun (out : RawReductionOutput) :
    TM2OutputsInTime reversedMachine (rawReductionOutputBits out)
      (some (rawInstanceBits out.2).reverse) (2 * (rawReductionOutputBits out).length + 1) where
  steps := 2 * (rawReductionOutputBits out).length + 1
  evals_in_steps := by
    have run := MachineTransducer.transduce_init_steps Mode.name transition emit
      (rawReductionOutputBits out)
    change (MachineTransducer.next Mode.name transition emit)^[2 * (rawReductionOutputBits out).length + 1]
      (some (initList reversedMachine (rawReductionOutputBits out))) =
      some (haltList reversedMachine (rawInstanceBits out.2).reverse)
    change (MachineTransducer.next Mode.name transition emit)^[2 * (rawReductionOutputBits out).length + 1]
      (some (initList reversedMachine (rawReductionOutputBits out))) =
      some (haltList reversedMachine (output .name (rawReductionOutputBits out)).reverse) at run
    rw [output_encoded] at run
    exact run
  steps_le_m := Nat.le_refl _

def machine : FinTM2 :=
  MachineSequential.machine reversedMachine MachineReverse.machine id false

def run (out : RawReductionOutput) :
    TM2OutputsInTime machine (rawReductionOutputBits out) (some (rawInstanceBits out.2))
      (5 * (rawReductionOutputBits out).length + 4) := by
  have second : TM2OutputsInTime MachineReverse.machine
      ((rawInstanceBits out.2).reverse.map id) (some (rawInstanceBits out.2))
      ((rawInstanceBits out.2).length + 1) := by
    simpa only [List.map_id, List.map_id_fun, List.reverse_reverse, List.length_reverse] using!
      MachineReverse.outputsInTime (rawInstanceBits out.2).reverse
  have full := MachineSequential.execute reversedMachine MachineReverse.machine id false
    (rawReductionOutputBits out) (rawInstanceBits out.2).reverse (rawInstanceBits out.2)
    (2 * (rawReductionOutputBits out).length + 1) ((rawInstanceBits out.2).length + 1)
    (reversedRun out) second
  refine { toEvalsTo := full.toEvalsTo, steps_le_m := ?_ }
  have h := full.steps_le_m
  have hlen : (rawInstanceBits out.2).length ≤ (rawReductionOutputBits out).length := by
    simp only [rawReductionOutputBits, List.length_append]
    omega
  change full.steps ≤ 2 * (rawReductionOutputBits out).length + 1 +
    2 * ((rawInstanceBits out.2).reverse.length + 1) + ((rawInstanceBits out.2).length + 1) at h
  rw [List.length_reverse] at h
  omega

noncomputable def computation :
    TM2ComputableInPolyTime rawReductionOutputBits rawInstanceBits
      (fun out : RawReductionOutput => out.2) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 5 * Polynomial.X + Polynomial.C 4
  outputsFun out := by
    change TM2OutputsInTime machine ((rawReductionOutputBits out).map id)
      (some ((rawInstanceBits out.2).map id)) _
    simpa only [List.map_id, List.map_id_fun, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using! run out

end BinPackingGap.DropPackingBoundMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PoweringTableSemantics
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.PCP.AlphabetGraph.legalDecidable _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.PoweringOpinions

open PoweringWalks PoweringLabels SpectralReturn
open PoweringMoment (bit)

variable {V D A : Type*}

def opinionAt (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : A := by
  classical
  exact if h : ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u then
    decode (selectors v) (labels v) ⟨u, h⟩ else fallback

def honestLabels (G : PortGraph V D) (t : Nat) (assignment : V → A) :
    V → PaddedLabel D t A := fun v => encode G t v (fun u => assignment u.val)

variable [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]

def sampleOpinion (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) (p : Fin N → D) : A :=
  opinionAt G t selectors labels fallback u (wordEnd G N u p)

def decoded (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) : A :=
  PoweringDecoding.mode (sampleOpinion G t N selectors labels fallback u)

def matchFn (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : ℝ :=
  bit (opinionAt G t selectors labels fallback u v = decoded G t N selectors labels fallback u)

end BinPackingGames.Foundations.PCP.PoweringOpinions

end

namespace BinPackingGames.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

def baseGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b) :
    ConstraintGraph V (Edge V D) A where
  reverse := G.rot
  reverse_involutive := G.rot_involutive
  tail := Prod.fst
  accepts := accepts
  reverse_accepts := reverse_accepts

def decodedBad (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (assignment : V → A) (e : Edge V D) : Bool :=
  !(accepts e (assignment e.1) (assignment (G.rot e).1))

noncomputable def witness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1)) : Prop :=
  decodedBad G accepts assignment (edgeAt G n w k) = true ∧
    opinionAt G (n + 1) selectors labels fallback (edgeAt G n w k).1 w.1 =
      assignment (edgeAt G n w k).1 ∧
    opinionAt G (n + 1) selectors labels fallback
      (G.rot (edgeAt G n w k)).1 (endpoint G w) =
        assignment (G.rot (edgeAt G n w k)).1

end BinPackingGames.Foundations.PCP.PoweringTest

namespace BinPackingGames.Foundations.PCP.PoweringTableSemantics

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration PoweringTables

abbrev RawLabeling (vertices d n : Nat) :=
  Fin vertices → PaddedLabel (Fin d) (n + 1) (Fin 64)

abbrev EncodedLabeling (vertices d n : Nat) :=
  Fin vertices → Fin (labelCount d n)

def encodeLabeling {vertices : Nat} (d n : Nat) (labels : RawLabeling vertices d n) :
    EncodedLabeling vertices d n :=
  fun v => encodeLabel d (n + 1) 64 (labels v)

def decodeLabeling {vertices : Nat} (d n : Nat) (labels : EncodedLabeling vertices d n) :
    RawLabeling vertices d n :=
  fun v => decodeLabel d (n + 1) 64 (labels v)

@[simp] theorem decodeLabeling_encodeLabeling {vertices : Nat} (d n : Nat)
    (labels : RawLabeling vertices d n) :
    decodeLabeling d n (encodeLabeling d n labels) = labels := by
  funext v
  exact decodeLabel_encodeLabel d (n + 1) 64 (labels v)

@[simp] theorem encodeLabeling_decodeLabeling {vertices : Nat} (d n : Nat)
    (labels : EncodedLabeling vertices d n) :
    encodeLabeling d n (decodeLabeling d n labels) = labels := by
  funext v
  exact encodeLabel_decodeLabel d (n + 1) 64 (labels v)

end BinPackingGames.Foundations.PCP.PoweringTableSemantics

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PoweringFinalConstants
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open PoweringWalks PoweringLabels PoweringOpinions PoweringTest
open SpectralReturn PoweringWitness PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

variable [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
  [Fintype A] [Nonempty A]

def decodedError (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n N : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A) : ℝ :=
  edgeDensity (decodedBad G accepts (decoded G (n + 1) N selectors labels fallback))

def poweredRejection (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) : ℝ :=
  mean (fun d : Dart V D n => bit ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false))

end BinPackingGames.Foundations.PCP.PoweringSoundness

namespace BinPackingGames.Foundations.PCP.PoweringPortReindex
open PoweringWalks PoweringLabels PoweringReach PoweringTest
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def walkEquiv (ports : D ≃ E) (n : Nat) : Walk V D n ≃ Walk V E n :=
  Equiv.prodCongr (Equiv.refl V) (wordEquiv ports n)

def addressEquiv (ports : D ≃ E) (t : Nat) : PortWords D t ≃ PortWords E t where
  toFun w := ⟨w.1, wordEquiv ports w.1.val w.2⟩
  invFun w := ⟨w.1, (wordEquiv ports w.1.val).symm w.2⟩
  left_inv w := by rcases w with ⟨n,p⟩; simp
  right_inv w := by rcases w with ⟨n,p⟩; simp

def labelEquiv (ports : D ≃ E) (t : Nat) : PaddedLabel E t A ≃ PaddedLabel D t A where
  toFun a := fun w => a (addressEquiv ports t w)
  invFun a := fun w => a ((addressEquiv ports t).symm w)
  left_inv a := by funext w; simp
  right_inv a := by funext w; simp

variable (G : PortGraph V D) (H : PortGraph V E) (ports : D ≃ E)
variable (rotation : ∀ v d, H.rot (v, ports d) =
  ((G.rot (v,d)).1, ports (G.rot (v,d)).2))

include rotation

theorem wordEnd_map (n : Nat) (v : V) (p : Fin n → D) :
    wordEnd H n v (wordEquiv ports n p) = wordEnd G n v p := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    simp only [wordEnd, next, wordEquiv, Equiv.coe_fn_mk, rotation]
    exact ih _ _

theorem reach_iff (t : Nat) (v u : V) :
    (∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u) ↔
    (∃ n, n ≤ t ∧ ∃ p : Fin n → E, wordEnd H n v p = u) := by
  constructor
  · rintro ⟨n,hn,p,hp⟩
    exact ⟨n,hn,wordEquiv ports n p,(wordEnd_map G H ports rotation n v p).trans hp⟩
  · rintro ⟨n,hn,p,hp⟩
    refine ⟨n,hn,(wordEquiv ports n).symm p,?_⟩
    rw [← wordEnd_map G H ports rotation, Equiv.apply_symm_apply]
    exact hp

def ballEquiv (t : Nat) (v : V) : Ball G t v ≃ Ball H t v where
  toFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mp u.property⟩
  invFun u := ⟨u.val,(reach_iff G H ports rotation t v u.val).mpr u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem wordToBall_map (t : Nat) (v : V) (w : PortWords D t) :
    wordToBall H t v (addressEquiv ports t w) =
      ballEquiv G H ports rotation t v (wordToBall G t v w) := by
  apply Subtype.ext
  exact wordEnd_map G H ports rotation w.1.val v w.2

def pullSelector {t : Nat} {v : V} (S : AddressSelector H t v) :
    AddressSelector G t v where
  address u := (addressEquiv ports t).symm
    (S.address (ballEquiv G H ports rotation t v u))
  correct u := by
    apply (ballEquiv G H ports rotation t v).injective
    rw [← wordToBall_map, Equiv.apply_symm_apply, S.correct]

variable (accepts : Edge V E → A → A → Bool)

def pullAccepts : Edge V D → A → A → Bool :=
  fun e => accepts (e.1, ports e.2)

def dartEquiv (n : Nat) : Dart V D n ≃ Dart V E n :=
  Equiv.prodCongr (Equiv.refl Bool) (walkEquiv ports (n+1))

theorem pullReverse
    (reverse_accepts : ∀ e a b, accepts (H.rot e) b a = accepts e a b)
    (e : Edge V D) (a b : A) :
    pullAccepts ports accepts (G.rot e) b a = pullAccepts ports accepts e a b := by
  simpa only [pullAccepts, rotation] using reverse_accepts (e.1,ports e.2) a b

end BinPackingGames.Foundations.PCP.PoweringPortReindex

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PCPIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

abbrev OutputVertex (V E A : Type*) :=
  QueryIncidence.Vertex (AlphabetGraph.Event E A) (AlphabetGraph.Address V E A)

abbrev OutputDart (E A : Type*) := QueryIncidence.Dart (AlphabetGraph.Event E A) 6

end BinPackingGames.Foundations.PCP.AlphabetGraphBounds

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_CapacityScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.CapacityScan

def scan (label : Nat) : RawInstance → List Nat → (Nat × Nat) → Bool
  | [], _, accumulator => decide (accumulator.1 ≤ accumulator.2)
  | _, [], accumulator => decide (accumulator.1 ≤ accumulator.2)
  | item :: items, assigned :: assignments, accumulator =>
      if accumulator.1 ≤ accumulator.2 then
        scan label items assignments (step label accumulator (item, assigned))
      else false

theorem scan_eq_true_iff (label : Nat) (items : RawInstance)
    (valid : items.Valid) (assignments : List Nat) (accumulator : Nat × Nat) :
    scan label items assignments accumulator = true ↔
      ((items.zip assignments).foldl (step label) accumulator).1 ≤
        ((items.zip assignments).foldl (step label) accumulator).2 := by
  induction items generalizing assignments accumulator with
  | nil => simp [scan]
  | cons item items ih =>
      have validTail : RawInstance.Valid items :=
        fun q mem => valid q (List.mem_cons_of_mem item mem)
      cases assignments with
      | nil => simp [scan]
      | cons assigned assignments =>
          by_cases accepted : accumulator.1 ≤ accumulator.2
          · simpa only [scan, ite_eq_left accepted, List.zip_cons_cons, List.foldl_cons] using
              ih validTail assignments (step label accumulator (item, assigned))
          · have overflow := FractionWidth.fold_overflow
              (item :: items) (assigned :: assignments) label accumulator valid
              (Nat.lt_of_not_ge accepted)
            have final_rejected :
                ¬(( (item :: items).zip (assigned :: assignments)).foldl
                    (step label) accumulator).1 ≤
                  (((item :: items).zip (assigned :: assignments)).foldl
                    (step label) accumulator).2 := by
              change (((item :: items).zip (assigned :: assignments)).foldl
                  (step label) accumulator).2 <
                (((item :: items).zip (assigned :: assignments)).foldl
                  (step label) accumulator).1 at overflow
              exact Nat.not_le_of_lt overflow
            simp only [scan, ite_eq_right accepted, Bool.false_eq_true, final_rejected]

theorem scan_initial_eq_capacityCheck (label : Nat) (items : RawInstance)
    (valid : items.Valid) (assignments : List Nat) :
    scan label items assignments (0, 1) =
      ExtensionCertificate.capacityCheck items assignments label := by
  apply Bool.eq_iff_iff.mpr
  rw [scan_eq_true_iff label items valid assignments,
    ExtensionCertificate.capacityCheck_eq_true_iff]
  rfl

end BinPackingGap.CapacityScan

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionAgreementMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionAgreementMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition

abbrev fixedBits (fixed : List (Option Nat)) : List Bool :=
  BinaryEncoding.listBits (BinaryEncoding.optionBits BinaryEncoding.natBits) fixed

theorem run_encoded (fixed : List (Option Nat)) (assignments : List Nat) :
    run ⟨.entry, fixedBits fixed, BinaryEncoding.assignmentBits assignments⟩ =
      resultView (ExtensionCertificate.agreesBool fixed assignments) := by
  induction fixed generalizing assignments with
  | nil =>
      cases assignments with
      | nil =>
          rw [run_step _ (by simp [Terminal])]
          exact run_checkEnd_empty
      | cons value assignments =>
          rw [run_step _ (by simp [Terminal])]
          simp [next, bothView, fixedBits, BinaryEncoding.assignmentBits,
            BinaryEncoding.listBits, ExtensionCertificate.agreesBool, run_drainFixed]
  | cons entry fixed ih =>
      cases assignments with
      | nil =>
          rw [run_step _ (by simp [Terminal])]
          simp [next, bothView, fixedBits, BinaryEncoding.assignmentBits,
            BinaryEncoding.listBits, ExtensionCertificate.agreesBool, run_drainFixed]
      | cons value assignments =>
          rw [run_step _ (by simp [Terminal])]
          change run ⟨.option,
            BinaryEncoding.optionBits BinaryEncoding.natBits entry ++ fixedBits fixed,
            BinaryEncoding.natBits value ++ BinaryEncoding.assignmentBits assignments⟩ = _
          cases entry with
          | none =>
              rw [run_step _ (by simp [Terminal])]
              change run ⟨.skipFlag, fixedBits fixed,
                BinPackingCompleteness.BinaryEncoding.frame value.bits ++
                  BinaryEncoding.assignmentBits assignments⟩ =
                resultView (ExtensionCertificate.agreesBool fixed assignments)
              rw [run_skipFrame]
              exact ih assignments
          | some label =>
              rw [run_step _ (by simp [Terminal])]
              change run ⟨.compareFlag,
                BinPackingCompleteness.BinaryEncoding.frame label.bits ++ fixedBits fixed,
                BinPackingCompleteness.BinaryEncoding.frame value.bits ++
                  BinaryEncoding.assignmentBits assignments⟩ =
                resultView (decide (label = value) &&
                  ExtensionCertificate.agreesBool fixed assignments)
              rw [run_compareFrame]
              have bits_iff : label.bits = value.bits ↔ label = value := by
                constructor
                · intro h
                  have values := congrArg BinPackingCompleteness.BinaryEncoding.bitsValue h
                  simpa only [BinPackingCompleteness.BinaryEncoding.bitsValue_bits] using values
                · rintro rfl
                  rfl
              by_cases equal : label = value
              · subst value
                simpa using ih assignments
              · simp [bits_iff, equal]

noncomputable def agreementInTime (fixed : List (Option Nat)) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg .entry (fixedBits fixed) (BinaryEncoding.assignmentBits assignments))
      (some (cfg (if ExtensionCertificate.agreesBool fixed assignments then
        .accept else .reject) [] []))
      (agreementTime.eval
        ((fixedBits fixed).length + (BinaryEncoding.assignmentBits assignments).length)) := by
  have trace := (rawInTime (fixedBits fixed) (BinaryEncoding.assignmentBits assignments)).execution
  change StateTransition.EvalsToInTime machine.step _
    (some (run ⟨.entry, fixedBits fixed, BinaryEncoding.assignmentBits assignments⟩).cfg) _ at trace
  rw [run_encoded] at trace
  simpa only [resultView, View.cfg] using trace

noncomputable def agreementFlagInTime (fixed : List (Option Nat)) (assignments : List Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg .entry (fixedBits fixed) (BinaryEncoding.assignmentBits assignments))
      (some ⟨none, (none, none), tapes [ExtensionCertificate.agreesBool fixed assignments] []⟩)
      (agreementTime.eval
        ((fixedBits fixed).length + (BinaryEncoding.assignmentBits assignments).length) + 1) := by
  let stage := agreementInTime fixed assignments
  let finish : machine.Cfg :=
    ⟨none, (none, none), tapes [ExtensionCertificate.agreesBool fixed assignments] []⟩
  have last : StateTransition.EvalsToInTime machine.step
      (cfg (if ExtensionCertificate.agreesBool fixed assignments then .accept else .reject) [] [])
      (some finish) 1 := {
    steps := 1
    evals_in_steps := by
      change machine.step
        (cfg (if ExtensionCertificate.agreesBool fixed assignments then .accept else .reject) [] []) =
        some finish
      exact flagStep (ExtensionCertificate.agreesBool fixed assignments)
    steps_le_m := Nat.le_refl _ }
  simpa only [Nat.add_comm] using StateTransition.EvalsToInTime.trans machine.step
    _ 1 _ _ (some finish) stage last

end BinPackingGap.ExtensionAgreementMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionCapacityBounds
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionWitness

open BinaryEncoding

theorem denominatorBits_le_rawInstanceBits (items : RawInstance) :
    FractionWidth.denominatorBits items ≤ (rawInstanceBits items).length := by
  induction items with
  | nil => simp [FractionWidth.denominatorBits, rawInstanceBits_length]
  | cons q items ih =>
      simp only [FractionWidth.denominatorBits, rawInstanceBits_length,
        List.map_cons, List.sum_cons] at *
      omega

end BinPackingGap.ExtensionWitness

namespace BinPackingGap.ExtensionFractionMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {K Λ A : Type} [DecidableEq K]

def statement (slots : Tape ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .multiply product localLabel =>
      BinaryMulMachine.statement ((productTapes product).trans slots)
        (fun localLabel => labels (.multiply product localLabel))
        (productExit labels product) localLabel
  | .add =>
      BinaryAddMachine.addLoop (slots 6) (slots 7) (slots 8)
        (labels .add) (some (labels .restore))
  | .restore =>
      MachineTransfer.loopAt (slots 8) (slots 4) id false (labels .restore) exit

noncomputable def arithmeticInTime (slots : Tape ↪ K) (labels : Label → Λ)
    (exit : Option Λ) (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (num den itemNum itemDen : Nat)
    (hnum : base (slots 0) = num.bits) (hden : base (slots 1) = den.bits)
    (hitemNum : base (slots 2) = itemNum.bits) (hitemDen : base (slots 3) = itemDen.bits)
    (emptyWorkspace : ∀ i : Tape, 4 ≤ i.val → base (slots i) = []) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .leftNumerator .copyLeft)), BinaryAddMachine.clean ambient, base⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        resultTapes slots base num den itemNum itemDen⟩)
      (arithmeticBudget num den itemNum itemDen) := by
  have hd (i j : Tape) (h : i ≠ j) : slots i ≠ slots j := slots.injective.ne h
  have h4 := emptyWorkspace 4 (by decide)
  have h5 := emptyWorkspace 5 (by decide)
  have h6 := emptyWorkspace 6 (by decide)
  have h7 := emptyWorkspace 7 (by decide)
  have h8 := emptyWorkspace 8 (by decide)
  have work : ∀ i : Tape, 9 ≤ i.val → base (slots i) = [] :=
    fun i hi => emptyWorkspace i (by omega)
  let afterLeft := Function.update base (slots 6) (num * itemDen).bits
  let afterRight := Function.update afterLeft (slots 7) (itemNum * den).bits
  let afterDen := Function.update afterRight (slots 5) (den * itemDen).bits
  let afterAdd := BinaryAddMachine.tapes (slots 6) (slots 7) (slots 8)
    afterDen [] [] (num * itemDen + itemNum * den).bits.reverse
  have leftRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .leftNumerator .copyLeft)), BinaryAddMachine.clean ambient, base⟩
      (some ⟨some (labels (.multiply .rightNumerator .copyLeft)),
        BinaryAddMachine.clean ambient, afterLeft⟩)
      (BinaryMulMachine.timePolynomial.eval (num.size + itemDen.size)) := by
    have h := BinaryMulMachine.multiplyNatInPolynomialTime
      ((productTapes .leftNumerator).trans slots)
      (fun l => labels (.multiply .leftNumerator l))
      (productExit labels .leftNumerator) p
      (fun l => atLabels (.multiply .leftNumerator l))
      base num itemDen hnum hitemDen (workspace_multiply slots base work .leftNumerator) ambient
    change StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .leftNumerator .copyLeft)), BinaryAddMachine.clean ambient, base⟩
      (some ⟨some (labels (.multiply .rightNumerator .copyLeft)), BinaryAddMachine.clean ambient,
        Function.update base (slots 6) ((num * itemDen).bits ++ base (slots 6))⟩) _ at h
    simpa only [h6, List.append_nil, afterLeft] using h
  have workLeft := workspace_update slots base work 6 (by decide) (num * itemDen).bits
  have rightRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .rightNumerator .copyLeft)),
        BinaryAddMachine.clean ambient, afterLeft⟩
      (some ⟨some (labels (.multiply .denominator .copyLeft)),
        BinaryAddMachine.clean ambient, afterRight⟩)
      (BinaryMulMachine.timePolynomial.eval (itemNum.size + den.size)) := by
    have h := BinaryMulMachine.multiplyNatInPolynomialTime
      ((productTapes .rightNumerator).trans slots)
      (fun l => labels (.multiply .rightNumerator l))
      (productExit labels .rightNumerator) p
      (fun l => atLabels (.multiply .rightNumerator l))
      afterLeft itemNum den
      (by
        change afterLeft (slots 2) = itemNum.bits
        simpa [afterLeft, hd 2 6 (by decide)] using hitemNum)
      (by
        change afterLeft (slots 1) = den.bits
        simpa [afterLeft, hd 1 6 (by decide)] using hden)
      (workspace_multiply slots afterLeft workLeft .rightNumerator) ambient
    have hout : afterLeft (slots 7) = [] := by simp [afterLeft, hd 7 6 (by decide), h7]
    change StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .rightNumerator .copyLeft)), BinaryAddMachine.clean ambient, afterLeft⟩
      (some ⟨some (labels (.multiply .denominator .copyLeft)), BinaryAddMachine.clean ambient,
        Function.update afterLeft (slots 7) ((itemNum * den).bits ++ afterLeft (slots 7))⟩) _ at h
    simpa only [hout, List.append_nil, afterRight] using h
  have workRight := workspace_update slots afterLeft workLeft 7 (by decide) (itemNum * den).bits
  have denominatorRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .denominator .copyLeft)),
        BinaryAddMachine.clean ambient, afterRight⟩
      (some ⟨some (labels .add), BinaryAddMachine.clean ambient, afterDen⟩)
      (BinaryMulMachine.timePolynomial.eval (den.size + itemDen.size)) := by
    have h := BinaryMulMachine.multiplyNatInPolynomialTime
      ((productTapes .denominator).trans slots)
      (fun l => labels (.multiply .denominator l))
      (productExit labels .denominator) p
      (fun l => atLabels (.multiply .denominator l))
      afterRight den itemDen
      (by
        change afterRight (slots 1) = den.bits
        simpa [afterRight, afterLeft, hd 1 6 (by decide), hd 1 7 (by decide)] using hden)
      (by
        change afterRight (slots 3) = itemDen.bits
        simpa [afterRight, afterLeft, hd 3 6 (by decide), hd 3 7 (by decide)] using hitemDen)
      (workspace_multiply slots afterRight workRight .denominator) ambient
    have hout : afterRight (slots 5) = [] := by
      simp [afterRight, afterLeft, hd 5 6 (by decide), hd 5 7 (by decide), h5]
    change StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (.multiply .denominator .copyLeft)), BinaryAddMachine.clean ambient, afterRight⟩
      (some ⟨some (labels .add), BinaryAddMachine.clean ambient,
        Function.update afterRight (slots 5) ((den * itemDen).bits ++ afterRight (slots 5))⟩) _ at h
    simpa only [hout, List.append_nil, afterDen] using h
  have den6 : afterDen (slots 6) = (num * itemDen).bits := by
    simp [afterDen, afterRight, afterLeft, hd 6 5 (by decide), hd 6 7 (by decide)]
  have den7 : afterDen (slots 7) = (itemNum * den).bits := by
    simp [afterDen, afterRight, hd 7 5 (by decide)]
  have den8 : afterDen (slots 8) = [] := by
    simp [afterDen, afterRight, afterLeft, hd 8 5 (by decide), hd 8 6 (by decide),
      hd 8 7 (by decide), h8]
  have addRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .add), BinaryAddMachine.clean ambient, afterDen⟩
      (some ⟨some (labels .restore), BinaryAddMachine.clean ambient, afterAdd⟩)
      (max (num * itemDen).size (itemNum * den).size + 1) := by
    have h := BinaryAddMachine.addNatInTime (slots 6) (slots 7) (slots 8)
      (hd 6 7 (by decide)) (hd 6 8 (by decide)) (hd 7 8 (by decide))
      (labels .add) (some (labels .restore)) p (atLabels .add)
      afterDen ambient (num * itemDen) (itemNum * den) []
    have initial : BinaryAddMachine.tapes (slots 6) (slots 7) (slots 8) afterDen
        (num * itemDen).bits (itemNum * den).bits [] = afterDen := by
      rw [← den6, ← den7, ← den8]
      simp [BinaryAddMachine.tapes]
    simpa only [initial, List.append_nil, afterAdd] using h
  have add8 : afterAdd (slots 8) = (num * itemDen + itemNum * den).bits.reverse := by
    simp [afterAdd, BinaryAddMachine.tapes]
  have add4 : afterAdd (slots 4) = [] := by
    simp [afterAdd, BinaryAddMachine.tapes, afterDen, afterRight, afterLeft,
      hd 4 5 (by decide), hd 4 6 (by decide), hd 4 7 (by decide), hd 4 8 (by decide), h4]
  have finalTapes : MachineTransfer.tapesAt (slots 8) (slots 4) afterAdd []
      (num * itemDen + itemNum * den).bits = resultTapes slots base num den itemNum itemDen := by
    funext k
    by_cases h4k : k = slots 4
    · subst k; simp [MachineTransfer.tapesAt, resultTapes]
    by_cases h5k : k = slots 5
    · subst k
      simp [MachineTransfer.tapesAt, afterAdd, BinaryAddMachine.tapes, afterDen,
        resultTapes, hd 5 4 (by decide), hd 5 6 (by decide), hd 5 7 (by decide),
        hd 5 8 (by decide)]
    by_cases h6k : k = slots 6
    · subst k
      simp [MachineTransfer.tapesAt, afterAdd, BinaryAddMachine.tapes, resultTapes,
        hd 6 4 (by decide), hd 6 5 (by decide), hd 6 7 (by decide), hd 6 8 (by decide), h6]
    by_cases h7k : k = slots 7
    · subst k
      simp [MachineTransfer.tapesAt, afterAdd, BinaryAddMachine.tapes, resultTapes,
        hd 7 4 (by decide), hd 7 5 (by decide), hd 7 8 (by decide), h7]
    by_cases h8k : k = slots 8
    · subst k
      simp [MachineTransfer.tapesAt, resultTapes, hd 8 4 (by decide), hd 8 5 (by decide), h8]
    simp [MachineTransfer.tapesAt, afterAdd, BinaryAddMachine.tapes, afterDen,
      afterRight, afterLeft, resultTapes, h4k, h5k, h6k, h7k, h8k]
  have restoreRun : StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .restore), BinaryAddMachine.clean ambient, afterAdd⟩
      (some ⟨exit, BinaryAddMachine.clean ambient,
        resultTapes slots base num den itemNum itemDen⟩)
      ((num * itemDen + itemNum * den).size + 1) := by
    have h := MachineTransfer.transferAtInTime (slots 8) (slots 4)
      (hd 8 4 (by decide)) (id : Bool → Bool) false (labels .restore) exit p
      (by simpa only [statement] using atLabels .restore)
      afterAdd ((ambient, false), none) none
    simpa only [add8, add4, List.length_reverse, List.reverse_reverse,
      List.map_id_fun, id_eq, List.append_nil, ← Nat.size_eq_bits_len, finalTapes,
      BinaryAddMachine.clean, BinaryAddMachine.state] using h
  have firstTwo := StateTransition.EvalsToInTime.trans (TM2.step p) _ _ _ _ _ leftRun rightRun
  have firstThree := StateTransition.EvalsToInTime.trans (TM2.step p) _ _ _ _ _ firstTwo denominatorRun
  have firstFour := StateTransition.EvalsToInTime.trans (TM2.step p) _ _ _ _ _ firstThree addRun
  have full := StateTransition.EvalsToInTime.trans (TM2.step p) _ _ _ _ _ firstFour restoreRun
  exact { toEvalsTo := full.toEvalsTo
          steps_le_m := by
            have bound := full.steps_le_m
            unfold arithmeticBudget
            omega }

theorem arithmeticBudget_le (A D a d : Nat) :
    arithmeticBudget A D a d ≤ timePolynomial.eval (A.size + D.size + a.size + d.size) := by
  let s := A.size + D.size + a.size + d.size
  have hm₁ := MachineComposition.natPolynomial_eval_mono BinaryMulMachine.timePolynomial
    (show A.size + d.size ≤ s by dsimp [s]; omega)
  have hm₂ := MachineComposition.natPolynomial_eval_mono BinaryMulMachine.timePolynomial
    (show a.size + D.size ≤ s by dsimp [s]; omega)
  have hm₃ := MachineComposition.natPolynomial_eval_mono BinaryMulMachine.timePolynomial
    (show D.size + d.size ≤ s by dsimp [s]; omega)
  have hp₁ := BinaryArithmetic.size_mul_le A d
  have hp₂ := BinaryArithmetic.size_mul_le a D
  have hs := BinaryArithmetic.size_add_le (A * d) (a * D)
  have hprod : max (A * d).size (a * D).size ≤ s := by dsimp [s]; omega
  have hsum : (A * d + a * D).size ≤ s + 1 := by omega
  unfold arithmeticBudget
  have hbound :
      BinaryMulMachine.timePolynomial.eval (A.size + d.size) +
        BinaryMulMachine.timePolynomial.eval (a.size + D.size) +
        BinaryMulMachine.timePolynomial.eval (D.size + d.size) +
        (max (A * d).size (a * D).size + 1) + ((A * d + a * D).size + 1) ≤
      3 * BinaryMulMachine.timePolynomial.eval s + 2 * s + 3 := by omega
  apply hbound.trans
  simp only [timePolynomial, BinaryMulMachine.timePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  dsimp [s]
  omega

end BinPackingGap.ExtensionFractionMachine

namespace BinPackingGap.ExtensionCapacityMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {K Λ A : Type} [DecidableEq K]

def statement (slots : Tape ↪ K) (labels : Label → Λ)
    (accepted rejected : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .guard =>
      .pop (slots 2) (fun state head => ((state.1.1, head), state.2))
        (.pop (slots 3) (fun state head => (state.1, head))
          (.branch (fun state => decide (state.1.2 = some true ∧ state.2 = some true))
            (finish (some (labels (.number .numerator .scan))))
            (.branch (fun state => decide (state.1.2 = some false ∧ state.2 = some false))
              (finish accepted) (finish rejected))))
  | .number field phase =>
      ExtensionNatMachine.statement ((numberTapes field).trans slots)
        (fun phase => labels (.number field phase)) (afterNumber labels field) rejected phase
  | .compare which phase =>
      ExtensionNatMachine.orderStatement ((compareTapes which).trans slots)
        (fun phase => labels (.compare which phase))
        (comparisonExits labels rejected which) phase
  | .fraction phase =>
      ExtensionFractionMachine.statement (fractionTapes.trans slots)
        (fun phase => labels (.fraction phase))
        (some (labels (.compare .capacity .leftOut))) phase
  | .clearOldNumerator =>
      MachineDrain.drain (slots 0) (labels .clearOldNumerator)
        (some (labels .clearOldDenominator))
  | .clearOldDenominator =>
      MachineDrain.drain (slots 1) (labels .clearOldDenominator)
        (some (labels .numeratorOut))
  | .numeratorOut =>
      MachineTransfer.loopAt (slots 11) (slots 10) id false
        (labels .numeratorOut) (some (labels .numeratorBack))
  | .numeratorBack =>
      MachineTransfer.loopAt (slots 10) (slots 0) id false
        (labels .numeratorBack) (some (labels .denominatorOut))
  | .denominatorOut =>
      MachineTransfer.loopAt (slots 12) (slots 10) id false
        (labels .denominatorOut) (some (labels .denominatorBack))
  | .denominatorBack =>
      MachineTransfer.loopAt (slots 10) (slots 1) id false
        (labels .denominatorBack) (some (labels .clearItemNumerator))
  | .clearItemNumerator =>
      MachineDrain.drain (slots 5) (labels .clearItemNumerator)
        (some (labels .clearItemDenominator))
  | .clearItemDenominator =>
      MachineDrain.drain (slots 6) (labels .clearItemDenominator)
        (some (labels .clearItemLabel))
  | .clearItemLabel =>
      MachineDrain.drain (slots 7) (labels .clearItemLabel) (some (labels .guard))

inductive FullLabel
  | initialize_
  | core (label : Label)
  | clear (result : Bool) (phase : MachineDrainMany.Label allTapes)
  | emit (result : Bool)
  deriving DecidableEq, Fintype

def inputTapes (base : Tape → List Bool) (numerator denominator selected : Nat)
    (items : RawInstance) (assignments : List Nat) : Tape → List Bool := fun k =>
  if k = 0 then numerator.bits
  else if k = 1 then denominator.bits
  else if k = 2 then BinaryEncoding.rawInstanceBits items
  else if k = 3 then BinaryEncoding.assignmentBits assignments
  else if k = 4 then selected.bits
  else base k

def initialTapes (items : RawInstance) (assignments : List Nat) (selected : Nat) :
    Tape → List Bool := fun k =>
  if k = 2 then BinaryEncoding.rawInstanceBits items
  else if k = 3 then BinaryEncoding.assignmentBits assignments
  else if k = 4 then selected.bits
  else []

def inputLength (items : RawInstance) (assignments : List Nat) (selected : Nat) : Nat :=
  (BinaryEncoding.rawInstanceBits items).length +
    (BinaryEncoding.assignmentBits assignments).length + selected.size

theorem cleanup_tapes (base : Tape → List Bool) :
    MachineDrainMany.finalTapes allTapes base = fun _ => [] := by
  funext k
  apply MachineDrainMany.finalTapes_mem
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

end BinPackingGap.ExtensionCapacityMachine

namespace BinPackingGap.ExtensionCapacityMachine

section

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

def ready (numerator denominator selected : Nat) (items : RawInstance)
    (assignments : List Nat) : Tape → List Bool :=
  work numerator.bits denominator.bits (BinaryEncoding.rawInstanceBits items)
    (BinaryEncoding.assignmentBits assignments) selected.bits [] [] [] [] []

end

theorem rowCost_le (num den a d assigned selected B : Nat)
    (accepted : num ≤ den) (itemBound : a ≤ d)
    (denominatorBound : den.size + d.size ≤ B + 1)
    (assignedBound : assigned.size ≤ B) (selectedBound : selected.size ≤ B) :
    rowCost num den a d assigned selected ≤ 1024 * (B + 1) ^ 2 := by
  have numeratorWidth := FractionWidth.size_mono accepted
  have itemWidth := FractionWidth.size_mono itemBound
  have productWidth := (FractionWidth.size_mul_le den d).trans denominatorBound
  have leftWidth : (num * d).size ≤ B + 1 :=
    (FractionWidth.addFraction_left_product_size_le
      (x := (num, den)) (q := (a, d)) accepted).trans denominatorBound
  have rightWidth : (a * den).size ≤ B + 1 :=
    (FractionWidth.addFraction_right_product_size_le
      (x := (num, den)) (q := (a, d)) itemBound).trans denominatorBound
  have sumWidth : (num * d + a * den).size ≤ B + 2 :=
    FractionWidth.size_add_le leftWidth rightWidth
  have arithmeticBound := (ExtensionFractionMachine.arithmeticBudget_le num den a d).trans
    (ExtensionArithmeticBounds.fractionTime_le
      (num.size + den.size + a.size + d.size) B (by omega))
  rw [ExtensionArithmeticBounds.timePolynomial_eval] at arithmeticBound
  have labelComparison := BinaryOrderMachine.preservingSteps_le assigned.size selected.size
  have capacityComparison := BinaryOrderMachine.preservingSteps_le
    (num * d + a * den).size (den * d).size
  unfold rowCost
  nlinarith [Nat.zero_le (B ^ 2)]

end BinPackingGap.ExtensionCapacityMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionMachineSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionMachineSpace

open Turing BinPackingGames.Foundations.Complexity

theorem execution_stackLength (tm : FinTM2) (k : tm.K)
    {start finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step start (some finish) budget) :
    (finish.stk k).length ≤ (start.stk k).length + budget * Runtime.programPushBound tm :=
  Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) run

theorem execution_lengthSum (tm : FinTM2) (chosen : List tm.K)
    {start finish : tm.Cfg} {budget : Nat}
    (run : StateTransition.EvalsToInTime tm.step start (some finish) budget) :
    lengthSum chosen finish.stk ≤
      lengthSum chosen start.stk + chosen.length * (budget * Runtime.programPushBound tm) := by
  induction chosen with
  | nil => simp [lengthSum]
  | cons k chosen ih =>
      have stepBound := execution_stackLength tm k run
      simp only [lengthSum, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.one_mul] at ih ⊢
      omega

end BinPackingGap.ExtensionMachineSpace

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

theorem run_name (next : Continuation) (name : Nat) (rest : List Bool) :
    run (.name next true) (natBits name ++ rest) = run (afterName next) rest := by
  apply run_frame
  exact (finalDigit_true_iff name.bits).mpr
    (BinPackingCompleteness.BinaryParsing.canonical_nat_bits name)

theorem run_items (r : RawInstance) (rest : List Bool) :
    run .items (rawInstanceBits r ++ rest) = run .fixedList rest := by
  induction r with
  | nil => simp [rawInstanceBits, listBits, run, nextMode]
  | cons q r ih =>
      simp only [rawInstanceBits, listBits, List.cons_append, run, nextMode,
        pairBits, List.append_assoc, run_name, afterName]
      exact ih

theorem run_fixed (fixed : List (Option Nat)) (rest : List Bool) :
    run .fixedList (listBits (optionBits natBits) fixed ++ rest) = run .done rest := by
  induction fixed with
  | nil => simp [listBits, run, nextMode]
  | cons value fixed ih =>
      cases value with
      | none => simpa only [listBits, optionBits, List.cons_append, List.singleton_append,
          List.nil_append, run, nextMode] using ih
      | some n =>
          simpa only [listBits, optionBits, List.cons_append, List.append_assoc,
            run, nextMode, run_name, afterName] using ih

theorem run_assignments (a : List Nat) (rest : List Bool) :
    run .assignments (assignmentBits a ++ rest) = run .done rest := by
  induction a with
  | nil => simp [assignmentBits, listBits, run, nextMode]
  | cons n a ih =>
      simpa only [assignmentBits, listBits, List.cons_append, List.append_assoc,
        run, nextMode, run_name, afterName] using ih

theorem run_extension (bins : Nat) (r : RawInstance) (fixed : List (Option Nat)) :
    run (start .extension) (extensionBits bins r fixed) = .done := by
  simp only [start, extensionBits, List.append_assoc, run_name, afterName,
    run_items]
  simpa only [List.append_nil, run] using run_fixed fixed []

theorem run_assignmentBits (a : List Nat) :
    run (start .assignments) (assignmentBits a) = .done := by
  simpa only [start, List.append_nil, run] using run_assignments a []

theorem name_inverse (next : Continuation) (input : List Bool)
    (accepted : run (.name next true) input = .done) :
    ∃ name rest, input = natBits name ++ rest ∧ run (afterName next) rest = .done := by
  obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := frame_inverse next true input accepted
  have hcanonical := (finalDigit_true_iff bits).mp hvalid
  have hbits := (BinPackingCompleteness.BinaryParsing.canonical_iff bits).mp hcanonical
  refine ⟨BinPackingCompleteness.BinaryEncoding.bitsValue bits, rest, ?_, hrest⟩
  simpa only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits, hbits] using hinput

theorem fixed_inverse_aux (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .fixedList input = .done) :
    ∃ fixed, input = listBits (optionBits natBits) fixed := by
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
              cases input with
              | nil => simp [run, nextMode] at accepted
              | cons present input =>
                  cases present with
                  | false =>
                      have haccepted : run .fixedList input = .done := accepted
                      have henough : input.length < fuel := by
                        simp only [List.length_cons] at enough
                        omega
                      obtain ⟨fixed, hfixed⟩ := ih input henough haccepted
                      exact ⟨none :: fixed, by simp [listBits, optionBits, hfixed]⟩
                  | true =>
                      have haccepted : run (.name .fixed true) input = .done := accepted
                      obtain ⟨n, rest, hinput, hrest⟩ := name_inverse .fixed input haccepted
                      have hlength := congrArg List.length hinput
                      simp only [List.length_append] at hlength
                      have henough : rest.length < fuel := by
                        simp only [List.length_cons] at enough
                        omega
                      obtain ⟨fixed, hfixed⟩ := ih rest henough hrest
                      exact ⟨some n :: fixed, by
                        simp [listBits, optionBits, hinput, hfixed]⟩

theorem assignments_inverse_aux (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .assignments input = .done) :
    ∃ a, input = assignmentBits a := by
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
              have haccepted : run (.name .assignment true) input = .done := accepted
              obtain ⟨n, rest, hinput, hrest⟩ := name_inverse .assignment input haccepted
              have hlength := congrArg List.length hinput
              simp only [List.length_append] at hlength
              have henough : rest.length < fuel := by
                simp only [List.length_cons] at enough
                omega
              obtain ⟨a, ha⟩ := ih rest henough hrest
              exact ⟨n :: a, by simp [assignmentBits, listBits, hinput, ha]⟩

theorem items_inverse_aux (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .items input = .done) :
    ∃ r fixed, input = rawInstanceBits r ++ listBits (optionBits natBits) fixed := by
  induction fuel generalizing input with
  | zero => omega
  | succ fuel ih =>
      cases input with
      | nil => simp [run] at accepted
      | cons flag input =>
          cases flag with
          | false =>
              have haccepted : run .fixedList input = .done := accepted
              obtain ⟨fixed, hfixed⟩ :=
                fixed_inverse_aux (input.length + 1) input (by omega) haccepted
              exact ⟨[], fixed, by simp [rawInstanceBits, listBits, hfixed]⟩
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
              obtain ⟨r, fixed, htail⟩ := ih rest henough hrest
              refine ⟨(num, den) :: r, fixed, ?_⟩
              simp [rawInstanceBits, listBits, pairBits, hnum, hden, htail, List.append_assoc]

theorem run_extension_iff (input : List Bool) :
    run (start .extension) input = .done ↔
      ∃ bins r fixed, input = extensionBits bins r fixed := by
  constructor
  · intro accepted
    obtain ⟨bins, rest, hinput, hrest⟩ := name_inverse .bins input accepted
    obtain ⟨r, fixed, htail⟩ := items_inverse_aux (rest.length + 1) rest (by omega) hrest
    exact ⟨bins, r, fixed, by simp [extensionBits, hinput, htail, List.append_assoc]⟩
  · rintro ⟨bins, r, fixed, rfl⟩
    exact run_extension bins r fixed

theorem run_assignments_iff (input : List Bool) :
    run (start .assignments) input = .done ↔ ∃ a, input = assignmentBits a := by
  constructor
  · intro accepted
    exact assignments_inverse_aux (input.length + 1) input (by omega) accepted
  · rintro ⟨a, rfl⟩
    exact run_assignmentBits a

def decodeAccepts : Kind → List Bool → Bool
  | .extension, input => (decodeExtension input).isSome
  | .assignments, input => (decodeAssignments input).isSome

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution

end BinPackingGap.ExtensionShapeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionValidationMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionValidationMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition

def controlInstruction : Control → TM2.Stmt Alphabet Label State
  | .boundEnd => .pop 0 (fun state head => (state.1, head))
      (.branch (fun state => state.2.isNone)
        (jump (.control .marker)) (jump (.control .reject)))
  | .marker => .pop 1 (fun state head => ((state.1.1, head), state.2))
      (.pop 2 (fun state head => (state.1, head))
        (.branch (fun state => state.1.2.isSome && state.2.isSome)
          (.branch (fun state => decide (state.1.2 = state.2))
            (.branch (fun state => state.2.getD false)
              (jump (.number .numerator .scan)) (jump (.control .endCheck)))
            (jump (.control .reject)))
          (jump (.control .reject))))
  | .positive => .pop 4 (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.push 4 (fun state => state.2.getD false) (jump (.number .denominator .scan)))
        (jump (.control .reject)))
  | .clearNumerator => MachineDrain.drain 4 (.control .clearNumerator)
      (some (.control .clearDenominator))
  | .clearDenominator => MachineDrain.drain 5 (.control .clearDenominator)
      (some (.control .clearAssigned))
  | .clearAssigned => MachineDrain.drain 6 (.control .clearAssigned)
      (some (.control .marker))
  | .endCheck => .pop 1 (fun state head => ((state.1.1, head), state.2))
      (.pop 2 (fun state head => (state.1, head))
        (.branch (fun state => state.1.2.isNone && state.2.isNone)
          (jump (.control .accept)) (jump (.control .reject))))
  | .accept => .push 0 (fun _ => true) .halt
  | .reject => .push 0 (fun _ => false) .halt

def loopTime (bins : Nat) : RawInstance → List Nat → Nat
  | (a, d) :: items, j :: assignments => rowBudget bins a d j + loopTime bins items assignments
  | _, _ => 2

end BinPackingGap.ExtensionValidationMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionVerifierPipeline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionCapacityMachine

open Turing
open BinPackingGames.Foundations.Complexity

theorem scan_overfull (items : RawInstance) (assignments : List Nat) (selected num den : Nat)
    (overfull : den < num) : CapacityScan.scan selected items assignments (num, den) = false := by
  cases items <;> cases assignments <;> simp [CapacityScan.scan, Nat.not_le_of_lt overfull]

end BinPackingGap.ExtensionCapacityMachine

namespace BinPackingGap.ExtensionCapacityOuterMachine

open Turing BinPackingGames.Foundations.Complexity BinPackingGames.Reduction

inductive Label
  | copyOut (kind : CopyKind)
  | copyBack (kind : CopyKind)
  | guard
  | number (phase : ExtensionNatMachine.Label)
  | inner (phase : ExtensionCapacityMachine.FullLabel)
  | afterInner
  | cleanup (result : Bool) (phase : MachineDrainMany.Label allTapes)
  | emit (result : Bool)
  deriving DecidableEq, Fintype

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => clean) (.goto fun _ => label)

def finish (exit : Option Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => clean) (match exit with
    | some label => .goto fun _ => label
    | none => .halt)

def stageTapes (items : RawInstance) (assignments remaining : List Nat) : Tape → List Bool :=
  fun k =>
    if k = 22 then BinaryEncoding.rawInstanceBits items
    else if k = 23 then BinaryEncoding.assignmentBits assignments
    else if k = 24 then BinaryEncoding.assignmentBits remaining
    else []

def initialTapes (items : RawInstance) (assignments : List Nat) : Tape → List Bool :=
  Function.update (stageTapes items assignments []) 24 []

def inputLength (items : RawInstance) (assignments : List Nat) : Nat :=
  (BinaryEncoding.rawInstanceBits items).length + (BinaryEncoding.assignmentBits assignments).length

def scanResult (items : RawInstance) (assignments remaining : List Nat) : Bool :=
  remaining.all (fun selected => CapacityScan.scan selected items assignments (0, 1))

theorem scanResult_eq_capacityChecks (items : RawInstance) (valid : items.Valid)
    (assignments remaining : List Nat) :
    scanResult items assignments remaining =
      remaining.all (ExtensionCertificate.capacityCheck items assignments) := by
  induction remaining with
  | nil => rfl
  | cons selected remaining ih =>
      simpa only [scanResult, List.all_cons,
        CapacityScan.scan_initial_eq_capacityCheck selected items valid assignments] using
        congrArg (fun answer => ExtensionCertificate.capacityCheck items assignments selected && answer) ih

theorem selected_size_le_encoding (selected : Nat) (assignments : List Nat)
    (member : selected ∈ assignments) :
    selected.size ≤ (BinaryEncoding.assignmentBits assignments).length := by
  induction assignments with
  | nil => simp at member
  | cons value assignments ih =>
      have length : (BinaryEncoding.assignmentBits (value :: assignments)).length =
          2 * value.size + 2 + (BinaryEncoding.assignmentBits assignments).length := by
        simp [BinaryEncoding.assignmentBits, BinaryEncoding.listBits]
        omega
      rw [length]
      rcases List.mem_cons.mp member with same | member
      · subst selected
        omega
      · have bound := ih member
        omega

theorem suffix_encoding_length_le (before after : List Nat) :
    (BinaryEncoding.assignmentBits after).length ≤
      (BinaryEncoding.assignmentBits (before ++ after)).length := by
  induction before with
  | nil => exact Nat.le_refl _
  | cons value before ih =>
      simp only [List.cons_append]
      have length : (BinaryEncoding.assignmentBits (value :: (before ++ after))).length =
          2 * value.size + 2 + (BinaryEncoding.assignmentBits (before ++ after)).length := by
        simp [BinaryEncoding.assignmentBits, BinaryEncoding.listBits]
        omega
      rw [length]
      omega

theorem stage_lengthSum (items : RawInstance) (assignments remaining : List Nat) :
    MachineDrainMany.lengthSum allTapes (stageTapes items assignments remaining) =
      (BinaryEncoding.rawInstanceBits items).length +
      (BinaryEncoding.assignmentBits assignments).length +
      (BinaryEncoding.assignmentBits remaining).length := by
  simp [MachineDrainMany.lengthSum, allTapes, List.ofFn_succ, stageTapes, Nat.add_assoc]

theorem ended_lengthSum (items : RawInstance) (assignments : List Nat) :
    MachineDrainMany.lengthSum allTapes
      (Function.update (stageTapes items assignments []) 24 []) =
      (BinaryEncoding.rawInstanceBits items).length +
      (BinaryEncoding.assignmentBits assignments).length := by
  simp [MachineDrainMany.lengthSum, allTapes, List.ofFn_succ, stageTapes]

theorem cleanup_tapes (base : Tape → List Bool) :
    MachineDrainMany.finalTapes allTapes base = fun _ => [] := by
  funext k
  apply MachineDrainMany.finalTapes_mem
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

noncomputable def loopBudget (items : RawInstance) (assignments remaining : List Nat) : Nat :=
  remaining.length * roundBudget ((BinaryEncoding.rawInstanceBits items).length +
    (BinaryEncoding.assignmentBits assignments).length) +
    (BinaryEncoding.rawInstanceBits items).length +
    2 * (BinaryEncoding.assignmentBits assignments).length + 28

end BinPackingGap.ExtensionCapacityOuterMachine

namespace BinPackingGap.ExtensionVerifierMachine

open Turing BinPackingGames.Foundations.Complexity
open ExtensionMachineRegisters (Lens)

abbrev LocalLabel : Helper → Type
  | .pair => ExtensionPairMachine.Label
  | .query | .witness => ExtensionShapeMachine.Label
  | .fields => Fields.Label
  | .validation => ExtensionValidationMachine.Label
  | .agreement => ExtensionAgreementMachine.Label
  | .capacity => ExtensionCapacityOuterMachine.Label

end BinPackingGap.ExtensionVerifierMachine

end OAI
end


