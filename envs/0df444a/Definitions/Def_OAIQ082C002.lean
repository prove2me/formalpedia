-- Prove2me | Definitions.Def_OAIQ082C002
-- name    : OAIQ082C002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:22:00.726773+00:00
-- url     : https://prove2.me/theorems/3a0f0eb3-fe89-4c65-b432-5a9e76d8f0f7
-- title:
--   Definitions bundle OAIQ082C002 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 683 declarations of OpenAI's Lean: 366 definitions, 41 inductive types or structures, 16 instances and 260 theorems. The definitions and types are `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.ClosureLabel`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.ClosureLabel.enumList`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution.StackBound`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution.StatementSafe`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution.absorbingNext`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution.advance`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution.executionToAbsorbing`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution.run`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution.stickyNext`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.Alphabet`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.Ports`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.WorkEmpty`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.loopMap`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.loopPorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.paddingMap`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.paddingPorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.prefixMap`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.prefixPorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine.steps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsPrefixStage.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsPrefixStage.Ports`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CellsPrefixStage.streamLabels`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission.contextSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.Alphabet`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.Label.enumList`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.State`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.Tape`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.Tape.enumList`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.cancelLoop`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.memory`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.totalTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.Alphabet`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.Context`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.State`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.Tape`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.cleanupNext`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.contextNext`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel.contextSource` and 367 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_BinaryOrderMachine`, `BinPacking_Arithmetic_BinaryPowerMachine`, `BinPacking_Arithmetic_BinaryTallyMachine`, `BinPacking_Arithmetic_GraphTallyMachine`, `BinPacking_Arithmetic_NatExpressionBranch`, `BinPacking_Computation_FinalCNFRowPlan`, `BinPacking_Computation_FinalCNFRowTrace`, `BinPacking_Computation_GraphCounterStart`, `BinPacking_Computation_GraphIterationBounds`, `BinPacking_Computation_MachineFiniteAlphabet`, `BinPacking_Computation_MachineHorner`, `BinPacking_Computation_MachineInitialHeaders`, `BinPacking_Computation_TableIterationFiniteAlphabet`, `BinPacking_CookLevin_BoundedExecution`, `BinPacking_CookLevin_CellsTokensAlignment`, `BinPacking_CookLevin_CircuitEncodingBridge`, `BinPacking_CookLevin_CircuitFinish`, `BinPacking_CookLevin_ClashMachine`, `BinPacking_CookLevin_Completeness`, `BinPacking_CookLevin_ConfigIndex`, `BinPacking_CookLevin_ForestStage`, `BinPacking_CookLevin_InitializationMachine`, `BinPacking_CookLevin_InitializationMachineAt`, `BinPacking_CookLevin_MachineCircuit`, `BinPacking_CookLevin_OutputOrder`, `BinPacking_CookLevin_PaddingCellsMachine`, `BinPacking_CookLevin_PayloadPresenceMachine`, `BinPacking_CookLevin_PolynomialMachine`, `BinPacking_CookLevin_PostfixBounds`, `BinPacking_CookLevin_ProducerFrontStage`, `BinPacking_CookLevin_TermMachine`, `BinPacking_CookLevin_TransitionArena`, `BinPacking_CookLevin_TransitionIteration`, `BinPacking_CookLevin_TransitionIterationTime`, `BinPacking_CookLevin_ValidityComposition`, `BinPacking_CookLevin_ValidityMachine`, `BinPacking_CookLevin_VerifierFront`, `BinPacking_Expanders_LazySmoothing`, `BinPacking_Expanders_SpectralCut`, `BinPacking_Expanders_ZigzagSpectral`, `BinPacking_Information_SourceFieldArray`, `BinPacking_PCP_CloudRounding`, `BinPacking_PCP_CompareLoop`, `BinPacking_PCP_FiniteGraph`, `BinPacking_PCP_Initialization`, `BinPacking_PCP_Lookup`, `BinPacking_PCP_MachineRawInitialTable`, `BinPacking_PCP_PCPSource`, `BinPacking_PCP_PoweringFinalConstants`, `BinPacking_PCP_PoweringMomentBound`, `BinPacking_PCP_Queries`, `BinPacking_PCP_RawInitialMachineBody`, `BinPacking_PCP_RawInitialMachineBudget`, `BinPacking_PCP_RawInitialMachineCleanup`, `BinPacking_PCP_RawInitialMachineFinish`, `BinPacking_PCP_RawInitialMachineLoop`, `BinPacking_PCP_RawInitialMachineLoopData`, `BinPacking_PCP_RawInitialMachineReadClause`, `BinPacking_PCP_RawInitialMachineRows`, `BinPacking_PCP_RawInitialPredicate`, `BinPacking_PCP_RoundTableGap`, `BinPacking_Packing_FractionWidth`, `BinPacking_Reductions_MachineReverse`, `BinPacking_Reductions_MachineTransducer`, `BinPacking_Search_ApproximationImpliesP`, `BinPacking_Search_ExtensionCapacityBounds`, `BinPacking_Trees_IntegerTreeGeometry`, `BinPacking_Trees_TreeAttachment`, `BinPacking_Trees_TreeAvoidance`, `BinPacking_Trees_TreeColorCounts`, `BinPacking_Trees_TreePruning`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C006`, `OAIQ082C007`, `OAIQ082C008` and `OAIQ082C009`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_CloudRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PoweringDecoding

open scoped BigOperators

variable {Ω A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A]

noncomputable def mass (opinion : Ω → A) (a : A) : ℝ := by
  classical
  exact Finset.univ.expect (fun ω => if opinion ω = a then 1 else 0)

omit [Nonempty Ω] in
theorem exists_mode (opinion : Ω → A) :
    ∃ a : A, ∀ b : A, mass opinion b ≤ mass opinion a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A)
    (mass opinion) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

noncomputable def mode (opinion : Ω → A) : A := Classical.choose (exists_mode opinion)

end BinPackingGames.Foundations.PCP.PoweringDecoding

namespace BinPackingGames.Foundations.PCP.CloudRounding

open scoped BigOperators

section CloudCounts

variable {X A D : Type*} [Fintype X] [Fintype A] [Fintype D]
variable [DecidableEq X] [DecidableEq A]

def colorSet (ell : X → A) (a : A) : Finset X :=
  Finset.univ.filter (fun x => ell x = a)

def minoritySet (ell : X → A) (m : A) : Finset X :=
  Finset.univ.filter (fun x => ell x ≠ m)

def directedCut (next : X × D → X) (S : Finset X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => xd.1 ∈ S ∧ next xd ∉ S)

def disagreementSet (ell : X → A) (next : X × D → X) : Finset (X × D) :=
  Finset.univ.filter (fun xd => ell xd.1 ≠ ell (next xd))

abbrev Nonmajor (m : A) := {a : A // a ≠ m}

omit [DecidableEq X] in
theorem exists_max_color (ell : X → A) [Nonempty A] :
    ∃ m : A, ∀ a, (colorSet ell a).card ≤ (colorSet ell m).card := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : A => (colorSet ell a).card) Finset.univ_nonempty
  exact ⟨m, fun a => hm a (Finset.mem_univ a)⟩

noncomputable def majority (ell : X → A) [Nonempty A] : A :=
  Classical.choose (exists_max_color ell)

end CloudCounts

end BinPackingGames.Foundations.PCP.CloudRounding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_FiniteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

variable {W D B : Type*}

def labelingEquiv (vertices : V ≃ W) (labels : A ≃ B) : (V → A) ≃ (W → B) where
  toFun := fun labeling w => labels (labeling (vertices.symm w))
  invFun := fun labeling v => labels.symm (labeling (vertices v))
  left_inv := by intro labeling; funext v; simp
  right_inv := by intro labeling; funext w; simp

end BinPackingGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialPredicate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialRows

def dummyWords (n m : Nat) : List Nat :=
  [n + m, 6 * m] ++ List.replicate 4096 1

end BinPackingGames.Foundations.PCP.RawInitialRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.GraphTableComplexity

open BinPackingGames.Foundations.Complexity
open Polynomial

noncomputable def encodingPolynomial (q : Nat) : Polynomial Nat :=
  X ^ 2 + C (2 * (q * q) + 1) * X + C 2

end BinPackingGames.Foundations.PCP.GraphTableComplexity

namespace BinPackingGames.Foundations.PCP.RawInitialMachineBudget

open Complexity

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * Polynomial.X ^ 2 + Polynomial.C 60000 * Polynomial.X +
    Polynomial.C 100

end BinPackingGames.Foundations.PCP.RawInitialMachineBudget

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineFiniteAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRepeat
open Turing

inductive ExtraTape
  | counter | temporary | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.counter, .temporary, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Phase
  | parse | guard | bodyToTemp | tempToBody | finalToTemp | tempToOutput
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.parse, .guard, .bodyToTemp, .tempToBody,
  .finalToTemp, .tempToOutput]

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance instFintypePhase : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (counter temporary output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .counter => counter
  | .temporary => temporary
  | .output => output

def oneStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := le_refl _

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

def loopBudget : Nat → (Nat → List Bool) → (Nat → Nat) → Nat
  | 0, words, _ => 2*(words 0).length+3
  | count+1, words, budgets => budgets 0 + 2*(words 1).length+3 +
      loopBudget count (fun i => words (i+1)) (fun i => budgets (i+1))

end BinPackingGames.Foundations.Complexity.MachineRepeat

namespace BinPackingGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

theorem input_finite (M : FinTM2) : Finite (M.Γ M.k₀) := by
  let := M.Γk₀Fin
  infer_instance

end BinPackingGames.Foundations.Complexity.MachineFiniteAlphabet

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryOrderMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryOrderMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingCompleteness.BinaryEncoding (bitsValue )

def updateOrder (prior : Ordering) (left right : Bool) : Ordering :=
  if left = right then prior else if left then .gt else .lt

def scanOrder (left right : List Bool) (prior : Ordering) : Ordering :=
  match left, right with
  | [], [] => prior
  | [], b :: bs => scanOrder [] bs (updateOrder prior false b)
  | a :: as, [] => scanOrder as [] (updateOrder prior a false)
  | a :: as, b :: bs => scanOrder as bs (updateOrder prior a b)
termination_by left.length + right.length
decreasing_by all_goals simp_wf <;> omega

def orderNat (left right : Nat) (prior : Ordering := .eq) : Ordering :=
  if left < right then .lt else if right < left then .gt else prior

@[simp] theorem orderNat_self (n : Nat) (prior : Ordering) :
    orderNat n n prior = prior := by simp [orderNat]

theorem orderNat_bit (a b : Nat) (left right : Bool) (prior : Ordering) :
    orderNat a b (updateOrder prior left right) =
      orderNat (Nat.bit left a) (Nat.bit right b) prior := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have hb : Nat.bit left a < Nat.bit right b := by
      cases left <;> cases right <;> simp only [Nat.bit_false, Nat.bit_true] <;> omega
    simp [orderNat, hlt, hb]
  · subst b
    cases left <;> cases right <;> simp [orderNat, updateOrder, Nat.bit]
  · have hb : Nat.bit right b < Nat.bit left a := by
      cases left <;> cases right <;> simp only [Nat.bit_false, Nat.bit_true] <;> omega
    simp [orderNat, hgt, Nat.not_lt.mpr hgt.le, hb, Nat.not_lt.mpr hb.le]

section Program

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := ((σ × Ordering) × Option Bool) × Option Bool

def clean (ambient : σ) : State σ := (((ambient, .eq), none), none)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => clean state.1.1.1) (exitAt exit)

def loop (left right : K) (again : Λ) (exits : Ordering → Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => ((state.1.1, head), state.2))
    (.pop right (fun state head => (state.1, head))
      (.branch (fun state => state.1.2.isNone && state.2.isNone)
        (.branch (fun state => decide (state.1.1.2 = .lt))
          (finish (exits .lt))
          (.branch (fun state => decide (state.1.1.2 = .gt))
            (finish (exits .gt)) (finish (exits .eq))))
        (.load (fun state =>
          (((state.1.1.1, updateOrder state.1.1.2
            (state.1.2.getD false) (state.2.getD false)), none), none))
          (.goto fun _ => again))))

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes = ⟨exit, clean state.1.1.1, tapes⟩ := by
  simp [finish, TM2.stepAux]

end Program

end BinPackingGap.BinaryOrderMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryTallyMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryArithmetic

def Canonical : List Bool → Prop
  | [] => True
  | b :: bs => Canonical bs ∧ (bs = [] → b = true)

def sumBit (a b c : Bool) : Bool := (a != b) != c

def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def addCarry : List Bool → List Bool → Bool → List Bool
  | [], [], c => if c then [true] else []
  | a :: as, [], c =>
      sumBit a false c :: addCarry as [] (carryBit a false c)
  | [], b :: bs, c =>
      sumBit false b c :: addCarry [] bs (carryBit false b c)
  | a :: as, b :: bs, c =>
      sumBit a b c :: addCarry as bs (carryBit a b c)
termination_by xs ys _ => xs.length + ys.length
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem size_mul_le (a b : Nat) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

def shift (xs : List Bool) : List Bool :=
  if xs = [] then [] else false :: xs

def consBit : Bool → List Bool → List Bool
  | false, [] => []
  | b, bs => b :: bs

def trimHigh : List Bool → List Bool
  | [] => []
  | false :: bs => trimHigh bs
  | true :: bs => true :: bs

def diffBit (a b c : Bool) : Bool := (a != b) != c

def borrowBit (a b c : Bool) : Bool := ((!a) && (b || c)) || (b && c)

theorem size_monus_le (a b : Nat) : (a - b).size ≤ a.size :=
  Nat.size_le_size (Nat.sub_le a b)

end BinPackingGap.BinaryArithmetic

namespace BinPackingGap.UnaryToBinaryMachine

open Turing BinPackingGames.Foundations.Complexity
open BinaryArithmetic

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

variable {K Λ A : Type} [DecidableEq K]

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => (state.1, none))
    (match exit with | none => .halt | some label => .goto fun _ => label)

end BinPackingGap.UnaryToBinaryMachine

namespace BinPackingGap.BinaryAddMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinaryArithmetic

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := ((A × Bool) × Option Bool) × Option Bool

variable {A : Type}

def state (a : A) (carry : Bool) (left right : Option Bool) : State A :=
  (((a, carry), left), right)

def clean (a : A) : State A := state a false none none

variable {K Λ A : Type} [DecidableEq K]

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun s => clean s.1.1.1) (exitAt exit)

def addLoop (left right output : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop left (fun s head => ((s.1.1, head), s.2))
    (.pop right (fun s head => (s.1, head))
      (.branch (fun s => s.1.2.isNone && s.2.isNone)
        (.branch (fun s => s.1.1.2)
          (.push output (fun _ => true) (finish exit)) (finish exit))
        (.push output (fun s => sumBit (s.1.2.getD false) (s.2.getD false) s.1.1.2)
          (.load (fun s => state s.1.1.1
            (carryBit (s.1.2.getD false) (s.2.getD false) s.1.1.2) none none)
            (.goto fun _ => again)))))

def tapes (left right output : K) (base : K → List Bool)
    (xs ys out : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base left xs) right ys) output out

end BinPackingGap.BinaryAddMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryPowerMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryMulMachine

open Turing
open BinPackingGames.Foundations.Complexity

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end BinPackingGap.BinaryMulMachine

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

def fieldNext (start : Fin 4 → Λ) (exit : Option Λ) (j : Fin 4) : Option Λ :=
  match j.val with
  | 0 => some (start 1)
  | 1 => some (start 2)
  | 2 => some (start 3)
  | _ => exit

end BinPackingGames.Foundations.Hastad.SourceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Expanders_SpectralCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.SpectralReturn

open scoped BigOperators

def edgeProfile {V D : Type*} [Fintype D] (bad : V × D → Bool) (v : V) : ℝ :=
  Finset.univ.expect (fun d => if bad (v, d) then 1 else 0)

end BinPackingGames.Foundations.PCP.SpectralReturn

namespace BinPackingGames.Foundations.PCP.SpectralCut

open scoped BigOperators
open SpectralReturn

section Indicators
variable {V : Type*} [Fintype V] [DecidableEq V]

def indicator (S : Finset V) (v : V) : ℝ := if v ∈ S then 1 else 0

end Indicators

end BinPackingGames.Foundations.PCP.SpectralCut

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Expanders_ZigzagSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.ZigzagSpectral

open SpectralReturn

noncomputable section

variable {V D E : Type*}

def liftCloud (f : V → ℝ) (x : V × D) : ℝ := f x.1

end

end BinPackingGames.Foundations.PCP.ZigzagSpectral

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Queries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.CodeComposition

open scoped BigOperators
open BinPackingGames.Foundations.Hastad

def disagreement (a b : Bool) : ℝ := if a = b then 0 else 1

end BinPackingGames.Foundations.PCP.CodeComposition

namespace BinPackingGames.Foundations.PCP.AssignmentTester

open BinPackingGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def truth (b : Bool) : ℝ := if b then 1 else 0

def disagree (a b : Bool) : ℝ := if a = b then 0 else 1

def distance {K : Type*} [Fintype K] (f g : K → Bool) : ℝ :=
  𝔼 k, disagree (f k) (g k)

end BinPackingGames.Foundations.PCP.AssignmentTester

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Expanders_LazySmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.LazySmoothing

open scoped BigOperators

def bitCount {n : ℕ} (tape : Fin n → Bool) : ℕ :=
  ∑ i, if tape i then 1 else 0

noncomputable def binomialMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  Finset.univ.expect (fun tape : Fin n → Bool => g (bitCount tape))

def splitTape (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Bool × (Fin n → Bool)) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv _ := rfl

@[simp] theorem mean_const (n : ℕ) (c : ℝ) :
    binomialMean n (fun _ => c) = c := Fintype.expect_const c

@[simp] theorem mean_zero (g : ℕ → ℝ) : binomialMean 0 g = g 0 := by
  simp [binomialMean, bitCount]

def score (n k : ℕ) : ℝ := (n : ℝ) - 2 * (k : ℝ)

noncomputable def scoreMean (n : ℕ) (g : ℕ → ℝ) : ℝ :=
  binomialMean n (fun k => score n k * g k)

@[simp] theorem scoreMean_zero (g : ℕ → ℝ) : scoreMean 0 g = 0 := by
  simp [scoreMean, score]

end BinPackingGames.Foundations.PCP.LazySmoothing

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PoweringMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.PoweringMoment

open scoped BigOperators

def bit (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

def hits {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i, bit (E i ω)

def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ := Finset.univ.expect f

end BinPackingGames.Foundations.PCP.PoweringMoment

end

namespace BinPackingGames.Foundations.PCP.PoweringReturn

open SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

def portConsEquiv (D : Type*) (n : Nat) :
    (D × (Fin n → D)) ≃ (Fin (n + 1) → D) where
  toFun z := Fin.cases z.1 z.2
  invFun r := (r 0, fun j => r j.succ)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      rfl
  right_inv r := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

end BinPackingGames.Foundations.PCP.PoweringReturn

namespace BinPackingGames.Foundations.PCP.PoweringMomentBound

open scoped BigOperators
open SpectralReturn PoweringReturn
open PoweringMoment (bit hits)

def windowIndex (n start m : Nat) (h : start + m ≤ n + 1) (i : Fin m) : Fin (n + 1) :=
  ⟨start + i.val, (Nat.add_lt_add_left i.isLt start).trans_le h⟩

end BinPackingGames.Foundations.PCP.PoweringMomentBound

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Reductions_MachineReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Reduction.MachineReverse

open Turing

def loop : TM2.Stmt (fun _ : Bool => Bool) Unit (Option Bool) :=
  .pop false (fun _ head => head)
    (.branch Option.isSome
      (.push true (fun state => state.getD false) (.goto fun _ => ()))
      .halt)

def machine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ := loop

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

def running (input output : List Bool) (state : Option Bool) : machine.Cfg :=
  ⟨some (), state, tapeStacks input output⟩

def halted (output : List Bool) : machine.Cfg :=
  ⟨none, none, tapeStacks [] output⟩

theorem update_input (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

theorem update_output (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

theorem step_empty (output : List Bool) (state : Option Bool) :
    machine.step (running [] output state) = some (halted output) := by
  change some (TM2.stepAux loop state (tapeStacks [] output)) = some (halted output)
  simp [loop, TM2.stepAux, tapeStacks, halted, Function.update]
  rw [update_input]
  rfl

theorem step_cons (head : Bool) (input output : List Bool) (state : Option Bool) :
    machine.step (running (head :: input) output state) =
      some (running input (head :: output) (some head)) := by
  change some (TM2.stepAux loop state (tapeStacks (head :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, running, Function.update]
  rw [update_input, update_output]
  rfl

def next (configuration : Option machine.Cfg) : Option machine.Cfg :=
  configuration.bind machine.step

theorem reverse_steps (input output : List Bool) (state : Option Bool) :
    next^[input.length + 1] (some (running input output state)) =
      some (halted (input.reverse ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.reverse_nil, List.nil_append] using step_empty output state
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change next^[input.length + 1]
      (machine.step (running (head :: input) output state)) = _
    rw [step_cons, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem initList_eq (input : List Bool) :
    initList machine input = running input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (output : List Bool) : haltList machine output = halted output := by
  unfold haltList halted
  congr 1

theorem reverse_init_steps (input : List Bool) :
    next^[input.length + 1] (some (initList machine input)) =
      some (haltList machine input.reverse) := by
  rw [initList_eq, haltList_eq]
  simpa only [List.append_nil] using reverse_steps input [] none

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input (some input.reverse) (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := reverse_init_steps input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (input : List Bool) :
    (outputsInTime input).steps = input.length + 1 := rfl

end BinPackingGames.Reduction.MachineReverse

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Reductions_MachineTransducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Reduction.MachineTransducer

open Turing
open BinPackingGames.Foundations.Complexity

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

theorem update_input (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

theorem update_output (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

variable {Q : Type} [Fintype Q]

def loop (initial : Q) :
    TM2.Stmt (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool) :=
  .pop false (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun state => some (state.1, state.2.getD false))
      (.load (fun _ => (initial, none)) .halt))

end BinPackingGames.Reduction.MachineTransducer

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineHorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

inductive Label
  | copyDrain | copyFork | seed | guard | scan | emitFalse | emitTrue | restore | finish
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyDrain, .copyFork, .seed, .guard, .scan,
  .emitFalse, .emitTrue, .restore, .finish]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (_ : Unit) (bit : Bool) : List Bool := if bit then [true] else []

def emitterLabel (labels : Label → Λ) (_ : Unit) (bit : Bool) : Λ :=
  if bit then labels .emitTrue else labels .emitFalse

def bodySteps (a : ℕ) : ℕ := 3 * (a + 1) + 2
def steps (a b : ℕ) : ℕ := 3 * a * b + 8 * b + 7

end BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

namespace BinPackingGames.Foundations.Complexity.MachineRadixStep

open Turing

inductive Label
  | multiply (label : MachineUnaryMultiply.Label)
  | digitDrain | digitFork | add | finish
  deriving DecidableEq, Fintype

variable {K Λ σ : Type}

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := MachineUnaryMultiply.State σ

variable [DecidableEq K]

def steps (radix acc digit : ℕ) : ℕ := 3 * radix * acc + 8 * acc + 3 * digit + 13

end BinPackingGames.Foundations.Complexity.MachineRadixStep

namespace BinPackingGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

abbrev State (σ : Type) := MachineRadixStep.State σ

inductive Label (width : Nat)
  | start
  | radix (i : Fin width) (inner : MachineRadixStep.Label)
  | clear (i : Fin width)
  | finishDrain | finishRestore
  deriving DecidableEq, Fintype

def entryLabel (width n : Nat) : Label width :=
  if h : n < width then .radix ⟨n, h⟩ (.multiply .copyDrain) else .finishDrain

variable [DecidableEq K]

def stepCost (radix acc digit : Nat) : Nat :=
  MachineRadixStep.steps radix acc digit + acc + 1

open scoped BigOperators

end BinPackingGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_FractionWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace Packing

variable {I : Instance} {b : ℕ}

def binItems (p : Packing I b) (j : Fin b) : Finset I.Item :=
  Finset.univ.filter fun i => p.assignment i = j

@[simp] theorem mem_binItems (p : Packing I b) (j : Fin b) (i : I.Item) :
    i ∈ p.binItems j ↔ p.assignment i = j := by
  simp [binItems]

end Packing

namespace RawInstance

@[simp] theorem toInstance_n (r : RawInstance) (hr : r.Valid) :
    (r.toInstance hr).n = r.length := rfl

@[simp] theorem toInstance_size (r : RawInstance) (hr : r.Valid) (i : Fin r.length) :
    (r.toInstance hr).size i = ratValue (r.get i) := rfl

@[simp] theorem valid_nil : Valid [] := by simp [Valid]

end RawInstance

namespace RawPacking

theorem zip_ofFn_eq {α β : Type*} {n : ℕ} (f : Fin n → α) (g : Fin n → β) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.zip_cons_cons, ih]

theorem load_ofFn (r : RawInstance) (f : Fin r.length → ℕ) (j : ℕ) :
    load r (List.ofFn f) j =
      ∑ i : Fin r.length, if f i = j then RawInstance.ratValue (r.get i) else 0 := by
  have hz : r.zip (List.ofFn f) = List.ofFn (fun i => (r.get i, f i)) := by
    calc
      r.zip (List.ofFn f) = (List.ofFn r.get).zip (List.ofFn f) :=
        congrArg (fun xs => xs.zip (List.ofFn f)) (List.ofFn_get r).symm
      _ = _ := zip_ofFn_eq r.get f
  simp only [load, hz, List.map_ofFn, List.sum_ofFn, Function.comp_apply]

def assignmentFn (r : RawInstance) (p : RawPacking)
    (h : p.assignments.length = r.length) (i : Fin r.length) : ℕ :=
  p.assignments.get (Fin.cast h.symm i)

theorem assignments_eq_ofFn (r : RawInstance) (p : RawPacking)
    (h : p.assignments.length = r.length) :
    p.assignments = List.ofFn (assignmentFn r p h) := by
  exact (List.ofFn_get p.assignments).symm.trans
    (List.ofFn_congr h p.assignments.get)

def toPacking (r : RawInstance) (hr : r.Valid) (p : RawPacking) (hp : Feasible r p) :
    Packing (r.toInstance hr) p.bins where
  assignment i := ⟨assignmentFn r p hp.1 i,
    hp.2.1 _ (List.get_mem p.assignments (Fin.cast hp.1.symm i))⟩
  capacity j := by
    have hcap := hp.2.2 j.val j.isLt
    rw [assignments_eq_ofFn r p hp.1, load_ofFn] at hcap
    simpa only [RawInstance.toInstance, Fin.ext_iff] using! hcap

@[simp] theorem toPacking_assignment_val (r : RawInstance) (hr : r.Valid)
    (p : RawPacking) (hp : Feasible r p) (i : Fin r.length) :
    ((toPacking r hr p hp).assignment i).val = assignmentFn r p hp.1 i := rfl

@[simp] theorem feasible_nil_iff (p : RawPacking) :
    Feasible [] p ↔ p.assignments = [] := by
  constructor
  · intro hp
    exact List.length_eq_zero_iff.mp hp.1
  · intro h
    cases p with
    | mk b a =>
        dsimp at h
        subst a
        simp [Feasible, load]

end RawPacking

end BinPackingGap

namespace BinPackingGap.FractionWidth

def denominatorBits (r : RawInstance) : ℕ :=
  (r.map fun q => q.2.size).sum

@[simp] theorem denominatorBits_nil : denominatorBits [] = 0 := rfl

@[simp] theorem denominatorBits_cons (q : ℕ × ℕ) (r : RawInstance) :
    denominatorBits (q :: r) = q.2.size + denominatorBits r := rfl

end BinPackingGap.FractionWidth

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_GraphTallyMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryEncoding

def parseOption {α : Type} (parse : Parser α) : Parser (Option α)
  | [] => none
  | false :: rest => some (none, rest)
  | true :: rest => do
    let (a, suffix) ← parse rest
    return (some a, suffix)

def extensionBits (bins : Nat) (r : RawInstance) (fixed : List (Option Nat)) : List Bool :=
  natBits bins ++ rawInstanceBits r ++ listBits (optionBits natBits) fixed

def parseAssignments : Parser (List Nat) := parseList parseNat

def parseExtension : Parser (Nat × RawInstance × List (Option Nat)) :=
  parsePair parseNat (parsePair parseRawInstance (parseList (parseOption parseNat)))

def decodeAssignments := decode parseAssignments
def decodeExtension := decode parseExtension

@[simp] theorem listBits_length {α : Type} (encode : α → List Bool) (xs : List α) :
    (listBits encode xs).length = 1 + (xs.map fun x => 1 + (encode x).length).sum := by
  induction xs with
  | nil => simp [listBits]
  | cons x xs ih => simp [listBits, ih]; omega

theorem list_length_lt_bits_length {α : Type} (encode : α → List Bool) (xs : List α) :
    xs.length < (listBits encode xs).length := by
  induction xs with
  | nil => simp [listBits]
  | cons x xs ih => simp only [listBits, List.length_cons, List.length_append]; omega

theorem list_length_le_bits_length {α : Type} (encode : α → List Bool) (xs : List α) :
    xs.length ≤ (listBits encode xs).length :=
  Nat.le_of_lt (list_length_lt_bits_length encode xs)

@[simp] theorem pairBits_length {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (p : α × β) : (pairBits ea eb p).length = (ea p.1).length + (eb p.2).length := by
  simp [pairBits]

theorem parsePair_pairBits {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (pa : Parser α) (pb : Parser β)
    (ha : ∀ a suffix, pa (ea a ++ suffix) = some (a, suffix))
    (hb : ∀ b suffix, pb (eb b ++ suffix) = some (b, suffix))
    (p : α × β) (suffix : List Bool) :
    parsePair pa pb (pairBits ea eb p ++ suffix) = some (p, suffix) := by
  rcases p with ⟨a, b⟩
  simp [pairBits, parsePair, List.append_assoc, ha, hb]

theorem parseOption_optionBits {α : Type} (encode : α → List Bool) (parse : Parser α)
    (h : ∀ a suffix, parse (encode a ++ suffix) = some (a, suffix))
    (a : Option α) (suffix : List Bool) :
    parseOption parse (optionBits encode a ++ suffix) = some (a, suffix) := by
  cases a <;> simp [optionBits, parseOption, h]

theorem parseListAux_listBits {α : Type} (encode : α → List Bool) (parse : Parser α)
    (h : ∀ a suffix, parse (encode a ++ suffix) = some (a, suffix))
    (xs : List α) (suffix : List Bool) (fuel : Nat) (enough : xs.length < fuel) :
    parseListAux parse fuel (listBits encode xs ++ suffix) = some (xs, suffix) := by
  induction xs generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at enough
      | succ fuel => simp [listBits, parseListAux]
  | cons x xs ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have ht : xs.length < fuel := by simpa using enough
          simp [listBits, parseListAux, List.append_assoc, h, ih fuel ht]

theorem parseList_listBits {α : Type} (encode : α → List Bool) (parse : Parser α)
    (h : ∀ a suffix, parse (encode a ++ suffix) = some (a, suffix))
    (xs : List α) (suffix : List Bool) :
    parseList parse (listBits encode xs ++ suffix) = some (xs, suffix) := by
  apply parseListAux_listBits encode parse h xs suffix
  have hlen := list_length_lt_bits_length encode xs
  simp only [List.length_append]
  omega

theorem decode_encode {α : Type} (encode : α → List Bool) (parse : Parser α)
    (h : ∀ a suffix, parse (encode a ++ suffix) = some (a, suffix)) (a : α) :
    decode parse (encode a) = some a := by
  have ha := h a []
  simp only [List.append_nil] at ha
  simp [decode, ha]

def ParserSound {α : Type} (encode : α → List Bool) (parse : Parser α) : Prop :=
  ∀ {input a suffix}, parse input = some (a, suffix) → input = encode a ++ suffix

theorem decode_sound {α : Type} (encode : α → List Bool) (parse : Parser α)
    (hp : ParserSound encode parse) {input : List Bool} {a : α}
    (h : decode parse input = some a) : input = encode a := by
  cases hparse : parse input with
  | none => simp [decode, hparse] at h
  | some result =>
      rcases result with ⟨x, suffix⟩
      cases suffix with
      | nil =>
          simp [decode, hparse] at h
          subst x
          simpa using hp hparse
      | cons bit rest => simp [decode, hparse] at h

end BinPackingGap.BinaryEncoding

namespace BinPackingGap

structure GraphFields where
  k : Nat
  vertices : List Nat
  endpoints : List (Nat × Nat)
  deriving DecidableEq

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpressionBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryAddPreserving

open Turing
open BinPackingGames.Foundations.Complexity
open BinaryAddMachine (State clean)

variable {K Λ A : Type} [DecidableEq K]

inductive Label
  | leftOut | leftBack | rightOut | rightBack | add | transfer
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.leftOut, .leftBack, .rightOut, .rightBack, .add,
  .transfer]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def resultTapes (slots : Fin 7 ↪ K) (base : K → List Bool) (a b : Nat) : K → List Bool :=
  Function.update base (slots 5) (a + b).bits

@[simp] theorem resultTapes_output (slots : Fin 7 ↪ K) (base : K → List Bool) (a b : Nat) :
    resultTapes slots base a b (slots 5) = (a + b).bits := by simp [resultTapes]

def steps (a b : Nat) : Nat :=
  2 * (a.size + 1) + 2 * (b.size + 1) + (max a.size b.size + 1) + ((a + b).size + 1)

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGap.BinaryAddPreserving

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Lookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open BinPackingGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

noncomputable def headTimePolynomial : Polynomial Nat :=
  Polynomial.C 7 * Polynomial.X + Polynomial.C 5

end BinPackingGames.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_FinalCNFRowTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

section

open Turing
open PCP.AlphabetTable

noncomputable def headerTimePolynomial : Polynomial Nat :=
  Polynomial.C 25 * Polynomial.X + Polynomial.C 52

end

open Turing PCP PCP.AlphabetTable

end BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

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

variable {K Λ σ : Type} [DecidableEq K]

def popN (k : K) : Nat → TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, continuation => continuation
  | n + 1, continuation => .pop k (fun state _ => state) (popN k n continuation)

theorem stepAux_popN (k : K) (n : Nat)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (popN k n continuation) state tapes =
      TM2.stepAux continuation state (Function.update tapes k ((tapes k).drop n)) := by
  induction n generalizing tapes with
  | zero => simp [popN]
  | succ n ih =>
    simp only [popN, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.drop_tail]

end LiteralFields

noncomputable section

def prefixValuePolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => Polynomial.X * prefixValuePolynomial digits i + Polynomial.C (digits i)

def prefixCostPolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => prefixCostPolynomial digits i +
      Polynomial.C 3 * Polynomial.X * prefixValuePolynomial digits i +
      Polynomial.C 9 * prefixValuePolynomial digits i + Polynomial.C (3 * digits i + 14)

end

end BinPackingGames.Foundations.Complexity.CookLevin.PolynomialMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PoweringFinalConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.PoweringSoundness

open scoped BigOperators
open SpectralReturn PoweringMomentBound
open PoweringMoment (bit hits)

variable {V D A : Type*}

def center (q M : Nat) : Nat := (4 * q * M) ^ 2

def gain (q M : Nat) (lambda : ℝ) : ℝ :=
  (1 / (2 * (q : ℝ))) ^ 4 * ((2 * M + 1 : Nat) : ℝ) /
    ((1 + 2 / (1 - lambda)) + 1)

end BinPackingGames.Foundations.PCP.PoweringSoundness

namespace BinPackingGames.Foundations.PCP.PoweringPortReindex
open SpectralReturn PoweringSoundness

variable {V D E A : Type*}

def wordEquiv (ports : D ≃ E) (n : Nat) : (Fin n → D) ≃ (Fin n → E) where
  toFun p := fun i => ports (p i)
  invFun p := fun i => ports.symm (p i)
  left_inv p := by funext i; exact ports.symm_apply_apply (p i)
  right_inv p := by funext i; exact ports.apply_symm_apply (p i)

end BinPackingGames.Foundations.PCP.PoweringPortReindex

namespace BinPackingGames.Foundations.PCP.PoweringFinalConstants

abbrev Alphabet := Fin 6 → Bool

@[simp] theorem card_alphabet : Fintype.card Alphabet = 64 := by
  norm_num [Alphabet, Fintype.card_fun]

end BinPackingGames.Foundations.PCP.PoweringFinalConstants

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RoundTableGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Addresses

open BinPackingGames.Foundations.Hastad

def values (n m edge tail head : Nat) : Fin 5 → Nat := ![n, m, edge, tail, head]

end BinPackingGames.Foundations.PCP.AlphabetTable.Addresses

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_FinalCNFRowPlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.FinalCNFTemplate

open PCP

inductive Reference where
  | query : Fin 12 → Reference
  | auxiliary : Fin 9 → Reference
  deriving DecidableEq

structure LiteralTemplate where
  reference : Reference
  positive : Bool
  deriving DecidableEq

abbrev ClauseTemplate := Vector LiteralTemplate 3

def queryLiteral (bits : Fin 12 → Bool) (i : Fin 12) : LiteralTemplate :=
  ⟨.query i, !(bits i)⟩

def auxiliaryLiteral (j : Fin 9) (positive : Bool) : LiteralTemplate :=
  ⟨.auxiliary j, positive⟩

def tautologyTemplate : ClauseTemplate :=
  #v[⟨.query 0, true⟩, ⟨.query 0, false⟩, ⟨.query 0, true⟩]

def chainTemplates (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  #v[
    #v[queryLiteral bits 0, queryLiteral bits 1, auxiliaryLiteral 0 true],
    #v[auxiliaryLiteral 0 false, queryLiteral bits 2, auxiliaryLiteral 1 true],
    #v[auxiliaryLiteral 1 false, queryLiteral bits 3, auxiliaryLiteral 2 true],
    #v[auxiliaryLiteral 2 false, queryLiteral bits 4, auxiliaryLiteral 3 true],
    #v[auxiliaryLiteral 3 false, queryLiteral bits 5, auxiliaryLiteral 4 true],
    #v[auxiliaryLiteral 4 false, queryLiteral bits 6, auxiliaryLiteral 5 true],
    #v[auxiliaryLiteral 5 false, queryLiteral bits 7, auxiliaryLiteral 6 true],
    #v[auxiliaryLiteral 6 false, queryLiteral bits 8, auxiliaryLiteral 7 true],
    #v[auxiliaryLiteral 7 false, queryLiteral bits 9, auxiliaryLiteral 8 true],
    #v[auxiliaryLiteral 8 false, queryLiteral bits 10, queryLiteral bits 11]]

def blockTemplates (accepted : Bool) (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  if accepted then Vector.replicate 10 tautologyTemplate else chainTemplates bits

def templates (accepted : Bool) (bits : Fin 12 → Bool) : List ClauseTemplate :=
  (blockTemplates accepted bits).toList

def literalAt (accepted : Bool) (bits : Fin 12 → Bool)
    (clause : Fin 10) (slot : Fin 3) : LiteralTemplate :=
  (blockTemplates accepted bits)[clause][slot]

@[simp] theorem templates_length (accepted : Bool) (bits : Fin 12 → Bool) :
    (templates accepted bits).length = 10 := Vector.length_toList

theorem templates_true (bits : Fin 12 → Bool) :
    templates true bits = List.replicate 10 tautologyTemplate := by rfl

theorem templates_false (bits : Fin 12 → Bool) :
    templates false bits = (chainTemplates bits).toList := by rfl

def literalWords (index : Reference → Nat) (literal : LiteralTemplate) : List Nat :=
  [index literal.reference, if literal.positive then 1 else 0]

def clauseWords (index : Reference → Nat) (clause : ClauseTemplate) : List Nat :=
  literalWords index clause[0] ++ literalWords index clause[1] ++ literalWords index clause[2]

def words (accepted : Bool) (bits : Fin 12 → Bool) (index : Reference → Nat) : List Nat :=
  (templates accepted bits).flatMap (clauseWords index)

end BinPackingGames.Foundations.Complexity.FinalCNFTemplate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_GraphCounterStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineLogCounter

open Turing

def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

@[simp] theorem bitLength_zero : bitLength 0 = 0 := rfl

theorem bitLength_positive {n : Nat} (h : n ≠ 0) : bitLength n = n.log2 + 1 := by
  simp [bitLength, h]

def increments (n : Nat) (started : Bool) : Nat :=
  if n = 0 then (if started then 0 else 1) else bitLength n

@[simp] theorem increments_true (n : Nat) : increments n true = bitLength n := by
  by_cases hn : n = 0 <;> simp [increments, hn]

theorem increments_false (n : Nat) : increments n false = n.log2 + 1 := by
  by_cases hn : n = 0
  · subst n; rfl
  · simp [increments, bitLength, hn]

def coreTime (n : Nat) : Nat :=
  if h : n = 0 then 1 else n + n / 2 + 3 + coreTime (n / 2)
termination_by n
decreasing_by omega

@[simp] theorem coreTime_zero : coreTime 0 = 1 := by rw [coreTime]; rfl

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := (Bool × Bool) × Option Bool

def initialState : State := ((false, false), none)

def rawTapes (input scratch output : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => scratch
  | 2 => output

theorem update_input (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 0 replacement = rawTapes replacement scratch output := by
  funext k
  fin_cases k <;> rfl

theorem update_scratch (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 1 replacement = rawTapes input replacement output := by
  funext k
  fin_cases k <;> rfl

theorem update_output (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 2 replacement = rawTapes input scratch replacement := by
  funext k
  fin_cases k <;> rfl

def stripLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push 1 (fun _ => true) (.goto fun _ => (1 : Fin 5)))
      (.load (fun _ => initialState) (.goto fun _ => 4)))

def guardLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .peek 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 2 (fun _ => true)
        (.load (fun _ => ((false, true), none)) (.goto fun _ => 3)))
      (.branch (fun state => state.1.2)
        (.load (fun _ => initialState) .halt)
        (.push 2 (fun _ => true) (.load (fun _ => initialState) .halt))))

def halfLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.branch (fun state => state.1.1)
        (.push 1 (fun _ => true)
          (.load (fun state => ((false, state.1.2), state.2)) (.goto fun _ => 3)))
        (.load (fun state => ((true, state.1.2), state.2)) (.goto fun _ => 3)))
      (.load (fun state => ((false, state.1.2), none)) (.goto fun _ => 4)))

def totalTime (n : Nat) : Nat := 2 * n + 3 + coreTime n

end BinPackingGames.Foundations.Complexity.MachineLogCounter

namespace BinPackingGames.Foundations.Complexity.GraphCounterModel

open Turing

inductive ExtraTape where
  | input | archive | scratch | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.input, .archive, .scratch, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive ExtraLabel where
  | copyFirst | copySecond | seed | headerFirst | headerSecond
  | clearInput | clockCopy | archiveCopy | finalReverse
  deriving DecidableEq

protected abbrev ExtraLabel.enumList : List ExtraLabel := [.copyFirst, .copySecond, .seed,
  .headerFirst, .headerSecond, .clearInput, .clockCopy, .archiveCopy, .finalReverse]

protected theorem ExtraLabel.enumList_nodup : ExtraLabel.enumList.Nodup := by decide

instance instFintypeExtraLabel : Fintype ExtraLabel where
  elems := ⟨ExtraLabel.enumList, ExtraLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 3 ⊕ ExtraTape
abbrev Label := Fin 5 ⊕ ExtraLabel
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineLogCounter.State × Option Bool

def initialState : State := (MachineLogCounter.initialState, none)

def clockLabel : Option (Fin 5) → Option Label
  | none => some (.inr .clearInput)
  | some l => some (.inl l)

def clockStatement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State →
    TM2.Stmt Alphabet Label State
  | .push k f next => .push (.inl k) (fun state => f state.1) (clockStatement next)
  | .peek k f next => .peek (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .pop k f next => .pop (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (clockStatement next)
  | .branch f yes no => .branch (fun state => f state.1) (clockStatement yes) (clockStatement no)
  | .goto f => .goto (fun state => .inl (f state.1))
  | .halt => .goto (fun _ => .inr .clearInput)

def readHeader (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop (.inr .input) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push (.inl 0) (fun _ => true) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def clockTapes (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool) : Tape → List Bool
  | .inl k => tapes k
  | .inr k => extra k

def clockConfiguration (extra : ExtraTape → List Bool) (register : Option Bool)
    (c : TM2.Cfg MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State) :
    TM2.Cfg Alphabet Label State := ⟨clockLabel c.l, (c.var, register), clockTapes c.stk extra⟩

theorem clockTapes_update (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool)
    (k : Fin 3) (word : List Bool) :
    clockTapes (Function.update tapes k word) extra =
      Function.update (clockTapes tapes extra) (.inl k) word := by
  funext tape
  cases tape <;> simp [clockTapes, Function.comp_def]

theorem clockStatement_simulation (extra : ExtraTape → List Bool) (register : Option Bool)
    (statement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State)
    (state : MachineLogCounter.State) (tapes : Fin 3 → List Bool) :
    TM2.stepAux (clockStatement statement) (state, register) (clockTapes tapes extra) =
      clockConfiguration extra register (TM2.stepAux statement state tapes) := by
  induction statement generalizing state tapes with
  | push k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [clockStatement, TM2.stepAux, clockTapes] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [clockStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

end BinPackingGames.Foundations.Complexity.GraphCounterModel

namespace BinPackingGames.Foundations.Complexity.PCPIterationMachine

open Turing

def rounds (n : Nat) : Nat := n.log2 + 1

theorem rounds_le (n : Nat) : rounds n ≤ n + 1 :=
  Nat.add_le_add_right (Nat.log2_le_self n) 1

theorem two_pow_rounds_le (n : Nat) : 2 ^ rounds n ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n; decide
  · have h := Nat.log2_self_le hn
    simp only [rounds, pow_succ]
    omega

theorem growth_pow_rounds_le (growth n : Nat) :
    growth ^ rounds n ≤ (2 * (n + 1)) ^ growth := by
  calc
    growth ^ rounds n ≤ (2 ^ growth) ^ rounds n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := growth))) _
    _ = (2 ^ rounds n) ^ growth := by simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * (n + 1)) ^ growth := Nat.pow_le_pow_left (two_pow_rounds_le n) growth

def sizeEnvelope (growth n : Nat) : Nat := (n + 1) * (2 * (n + 1)) ^ growth

theorem semanticSize_geometric (sizes : Nat → Nat) (growth n : Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ (n + 1) * growth ^ i := by
  induction i with
  | zero => simpa only [pow_zero, Nat.mul_one] using initialBound
  | succ i ih =>
    have ilt : i < rounds n := by omega
    calc
      sizes (i + 1) ≤ growth * sizes i := growthBound i ilt
      _ ≤ growth * ((n + 1) * growth ^ i) :=
        Nat.mul_le_mul_left growth (ih (by omega))
      _ = (n + 1) * growth ^ (i + 1) := by rw [pow_succ]; ac_rfl

theorem semanticSize_bound (sizes : Nat → Nat) (growth n : Nat)
    (growthPositive : 0 < growth)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ sizeEnvelope growth n := by
  calc
    sizes i ≤ (n + 1) * growth ^ i :=
      semanticSize_geometric sizes growth n initialBound growthBound i hi
    _ ≤ (n + 1) * growth ^ rounds n :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right growthPositive hi)
    _ ≤ sizeEnvelope growth n :=
      Nat.mul_le_mul_left _ (growth_pow_rounds_le growth n)

noncomputable def sizePolynomial (growth : Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (2 * (Polynomial.X + 1)) ^ growth

@[simp] theorem sizePolynomial_eval (growth n : Nat) :
    (sizePolynomial growth).eval n = sizeEnvelope growth n := by
  simp [sizePolynomial, sizeEnvelope]

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool
abbrev Labels (Λ : Type) := Bool ⊕ Λ

end BinPackingGames.Foundations.Complexity.PCPIterationMachine

namespace BinPackingGames.Foundations.Complexity.GraphCounterModel

open Turing

def startExtra (input archive : List Bool) : ExtraTape → List Bool
  | .input => input
  | .archive => archive
  | _ => []

def startMemory (input archive sum : List Bool) : Tape → List Bool
  | .inl k => if k = 0 then sum else []
  | .inr k => startExtra input archive k

end BinPackingGames.Foundations.Complexity.GraphCounterModel

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PCPSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.FinalTableFormula

open Complexity

noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C 77824 * Polynomial.X + Polynomial.C 2 +
    (Polynomial.C 40960 * Polynomial.X) *
      (Polynomial.C 3 * (Polynomial.C 36864 * Polynomial.X + Polynomial.C 2))

theorem sizePolynomial_eval (N : Nat) :
    sizePolynomial.eval N = 77824 * N + 2 + (40960 * N) * (3 * (36864 * N + 2)) := by
  simp [sizePolynomial]

end BinPackingGames.Foundations.PCP.FinalTableFormula

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_GraphIterationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

def extraTapes (rest original : List Bool) : ExtraTape → List Bool
  | .input => rest
  | .archive => original
  | _ => []

def frame (input archive counter reversed output : List Bool) : Tape → List Bool
  | .inl i => if i = 2 then counter else []
  | .inr .input => input
  | .inr .archive => archive
  | .inr .scratch => reversed
  | .inr .output => output

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.Complexity.GraphCounterFinish

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineInitialHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineInitialHeaders

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

theorem replicate_append_cons (n : ℕ) (xs : List Bool) :
    List.replicate n true ++ true :: xs = List.replicate (n + 1) true ++ xs := by
  rw [List.replicate_add]
  simp

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.Complexity.MachineInitialHeaders

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineLoopData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialRows

def orderedList {α : Type*} {n : Nat} (e : α ≃ Fin n) : List α :=
  List.ofFn e.symm

theorem orderedList_cast {α : Type*} {m n : Nat} (e : α ≃ Fin m) (h : m = n) :
    orderedList (e.trans (finCongr h)) = orderedList e := by
  subst n
  rfl

theorem orderedList_prod {α β : Type*} {m n : Nat}
    (e : α ≃ Fin m) (f : β ≃ Fin n) :
    orderedList ((e.prodCongr f).trans finProdFinEquiv) =
      (orderedList e).flatMap (fun a => (orderedList f).map (fun b => (a, b))) := by
  change List.ofFn (fun q : Fin (m * n) =>
    (e.symm (finProdFinEquiv.symm q).1, f.symm (finProdFinEquiv.symm q).2)) = _
  rw [List.ofFn_mul]
  simp only [orderedList, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h : (⟨i.val * n + j.val, by
      calc
        i.val * n + j.val < (i.val + 1) * n :=
          (Nat.add_lt_add_left j.isLt _).trans_eq (by rw [Nat.add_mul, Nat.one_mul])
        _ ≤ m * n := Nat.mul_le_mul_right _ i.isLt⟩ : Fin (m * n)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [h, Equiv.symm_apply_apply]
  rfl

theorem orderedList_sum {α β : Type*} {m n : Nat}
    (e : α ≃ Fin m) (f : β ≃ Fin n) :
    orderedList ((e.sumCongr f).trans finSumFinEquiv) =
      (orderedList e).map Sum.inl ++ (orderedList f).map Sum.inr := by
  change List.ofFn (fun q : Fin (m + n) =>
    (e.sumCongr f).symm (finSumFinEquiv.symm q)) = _
  rw [List.ofFn_add]
  change (List.ofFn (fun i : Fin m =>
    (e.sumCongr f).symm (finSumFinEquiv.symm (i.castAdd n)))) ++
    (List.ofFn (fun i : Fin n =>
      (e.sumCongr f).symm (finSumFinEquiv.symm (i.natAdd m)))) = _
  simp [orderedList, List.map_ofFn]
  rfl

end BinPackingGames.Foundations.PCP.RawInitialRows

namespace BinPackingGames.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

abbrev Signs := Bool × Bool × Bool
abbrev State := Signs × Option Bool

inductive CopyPhase
  | tailVariables (slot : Fin 3)
  | tailIndex (slot : Fin 3)
  | variableName (slot : Fin 3)
  | reverseIndex (slot : Fin 3) (orientation : Bool)
  | dummyVariables | dummyIndex | dummyReverse
  deriving DecidableEq, Fintype

inductive Label
  | headerStart (slot : Fin 2) | headerLoop (slot : Fin 2)
  | scanN | restoreN | scanM1 | restoreM1 | closeFirst
  | scanM6 | restoreM6 | closeSecond | initializeIndex | guard
  | fieldStart (slot : Fin 6) | fieldLoop (slot : Fin 6) | loadSigns
  | scan (phase : CopyPhase) | restore (phase : CopyPhase)
  | closeTail (slot : Fin 3) (orientation : Bool)
  | closeReverse (slot : Fin 3) (orientation : Bool)
  | relation (slot : Fin 3) (orientation : Bool)
  | cleanupField (slot : Fin 6) | incrementIndex
  | closeDummyTail | closeDummyReverse | dummyRelation
  | cleanupFinal (slot : Fin 3) | reset | finalReverse
  deriving DecidableEq, Fintype

def initialState : State := ((false, false, false), none)

def stateKeys : List State :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c =>
      [none, some false, some true].map fun register => ((a, b, c), register)

theorem stateKeys_complete (state : State) : state ∈ stateKeys := by
  rcases state with ⟨⟨a, b, c⟩, register⟩
  cases a <;> cases b <;> cases c <;> cases register with
  | none => simp [stateKeys]
  | some bit => cases bit <;> simp [stateKeys]

def copyScale : CopyPhase → Nat
  | .reverseIndex _ _ | .dummyReverse => 6
  | _ => 1

def copyNext : CopyPhase → Label
  | .tailVariables slot => .scan (.tailIndex slot)
  | .tailIndex slot => .closeTail slot false
  | .variableName slot => .closeTail slot true
  | .reverseIndex slot orientation => .closeReverse slot orientation
  | .dummyVariables => .scan .dummyIndex
  | .dummyIndex => .closeDummyTail
  | .dummyReverse => .closeDummyReverse

def relationNext (slot : Fin 3) (orientation : Bool) : Label :=
  if orientation then
    if h : slot.val + 1 < 3 then .scan (.tailVariables ⟨slot.val + 1, h⟩)
    else .cleanupField 0
  else .scan (.variableName slot)

end BinPackingGames.Foundations.PCP.RawInitialMachineModel

namespace BinPackingGames.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.PCP.RawInitialMachineStart

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineReadClause
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineReadClause

open Turing Complexity Hastad RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.PCP.RawInitialMachineReadClause

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.PCP.RawInitialMachineCleanup

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.PCP.RawInitialMachineRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineBody

open Turing Complexity RawInitialMachineModel
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.PCP.RawInitialMachineBody

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.PCP.RawInitialMachineFinish

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineLoop

open Turing Complexity RawInitialMachineModel
open RawInitialMachineBudget RawInitialMachineBody RawInitialMachineFinish

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.PCP.RawInitialMachineLoop

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_MachineRawInitialTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.MachineRawInitialTable

open Turing Complexity RawInitialMachineModel
open RawInitialMachineBudget RawInitialMachineLoop

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.PCP.MachineRawInitialTable

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_TableIterationFiniteAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

section

open PCP

noncomputable def rowTimePolynomial : Polynomial Nat :=
  Polynomial.C 860160 * (Polynomial.C 3 * (Polynomial.X + Polynomial.C 1) + Polynomial.C 3) +
    Polynomial.C 12 * Polynomial.X + Polynomial.C 15

end

open Turing PCP

end BinPackingGames.Foundations.Complexity.FinalCNFMachine.Program

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_BoundedExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution

section Transition
variable {C : Type*}

def absorbingNext (step : C → Option C) (c : C) : C := (step c).getD c

@[simp] theorem absorbingNext_of_none (step : C → Option C) {c : C}
    (h : step c = none) : absorbingNext step c = c := by simp [absorbingNext, h]

@[simp] theorem absorbingNext_of_some (step : C → Option C) {c d : C}
    (h : step c = some d) : absorbingNext step c = d := by simp [absorbingNext, h]

def advance (step : C → Option C) (c : Option C) : Option C := c.bind step

theorem advance_iterate_none (step : C → Option C) (n : Nat) :
    (advance step)^[n] none = none := Function.iterate_fixed rfl n

theorem absorbing_of_successfulTrace (step : C → Option C) (n : Nat) (a b : C)
    (h : (fun c : Option C => c.bind step)^[n] (some a) = some b) :
    (absorbingNext step)^[n] a = b := by
  change (advance step)^[n] (some a) = some b at h
  induction n generalizing a with
  | zero => exact Option.some.inj h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    change (advance step)^[n] (step a) = some b at h
    cases hs : step a with
    | none =>
      rw [hs, advance_iterate_none] at h
      contradiction
    | some c =>
      rw [hs] at h
      rw [absorbingNext_of_some step hs]
      exact ih c h

def executionToAbsorbing (step : C → Option C) (a : C) (T : Nat) :
    StateTransition.EvalsToInTime step a (some ((absorbingNext step)^[T] a)) T := by
  induction T generalizing a with
  | zero => exact StateTransition.EvalsToInTime.refl step a
  | succ n ih =>
    cases hs : step a with
    | none =>
      have fixed : (absorbingNext step)^[n + 1] a = a :=
        Function.iterate_fixed (absorbingNext_of_none step hs) _
      exact {
        steps := 0
        evals_in_steps := by rw [fixed]; rfl
        steps_le_m := Nat.zero_le _ }
    | some b =>
      let first : StateTransition.EvalsToInTime step a (some b) 1 := {
        steps := 1
        evals_in_steps := by change step a = some b; exact hs
        steps_le_m := le_rfl }
      have full := StateTransition.EvalsToInTime.trans step 1 n a b
        (some ((absorbingNext step)^[n] b)) first (ih b)
      simpa only [Function.iterate_succ_apply, absorbingNext_of_some step hs] using full

theorem absorbing_eq_of_execution (step : C → Option C) {a b : C} {T : Nat}
    (execution : StateTransition.EvalsToInTime step a (some b) T)
    (halted : step b = none) : (absorbingNext step)^[T] a = b := by
  have hs : (absorbingNext step)^[execution.steps] a = b := by
    apply absorbing_of_successfulTrace
    exact execution.evals_in_steps
  have ht : T = (T - execution.steps) + execution.steps :=
    (Nat.sub_add_cancel execution.steps_le_m).symm
  rw [ht, Function.iterate_add_apply, hs]
  exact Function.iterate_fixed (absorbingNext_of_none step halted) _

end Transition

abbrev stickyNext (tm : Turing.FinTM2) : tm.Cfg → tm.Cfg := absorbingNext tm.step

def run (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (n : Nat) : tm.Cfg :=
  (stickyNext tm)^[n] (Turing.initList tm input)

@[simp] theorem run_zero (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) :
    run tm input 0 = Turing.initList tm input := rfl

theorem run_succ (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (n : Nat) :
    run tm input (n + 1) = stickyNext tm (run tm input n) := by
  simp only [run, Function.iterate_succ_apply']

theorem run_eq_halt_of_outputs (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (T : Nat)
    (h : Turing.TM2OutputsInTime tm input (some output) T) :
    run tm input T = Turing.haltList tm output :=
  absorbing_eq_of_execution tm.step h rfl

section Statement
variable {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]

def StackBound (S : Nat) (tapes : ∀ k, List (Γ k)) : Prop :=
  ∀ k, (tapes k).length ≤ S

def StatementSafe (S : Nat) : Turing.TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → Prop
  | .push k f q, v, tapes => StackBound S tapes ∧ (tapes k).length < S ∧
      StatementSafe S q v (Function.update tapes k (f v :: tapes k))
  | .peek k f q, v, tapes => StackBound S tapes ∧
      StatementSafe S q (f v (tapes k).head?) tapes
  | .pop k f q, v, tapes => StackBound S tapes ∧
      StatementSafe S q (f v (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | .load f q, v, tapes => StackBound S tapes ∧ StatementSafe S q (f v) tapes
  | .branch f yes no, v, tapes => StackBound S tapes ∧
      (if f v then StatementSafe S yes v tapes else StatementSafe S no v tapes)
  | .goto _, _, tapes => StackBound S tapes
  | .halt, _, tapes => StackBound S tapes

end Statement

end BinPackingGames.Foundations.Complexity.CookLevin.BoundedExecution

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ConfigIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

open Turing
open BoundedExecution

variable {K : Type} {Γ : K → Type} {Λ σ ι : Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [DecidableEq Λ]

noncomputable def unaryCost (σ : Type) [Fintype σ] (C : Nat) : Nat :=
  Fintype.card σ * (C + 3) + 1

noncomputable def headCost (σ A : Type) [Fintype σ] [Fintype A] (C : Nat) : Nat :=
  (Fintype.card σ * Fintype.card (Option A)) * (2 * C + 4) + 1

noncomputable def statementCost : TM2.Stmt Γ Λ σ → Nat → Nat
  | .push _ _ next, C => statementCost next (max C (unaryCost σ C))
  | .peek k _ next, C => statementCost next (max C (headCost σ (Γ k) C))
  | .pop k _ next, C => statementCost next (max C (headCost σ (Γ k) C))
  | .load _ next, C => statementCost next (max C (unaryCost σ C))
  | .branch _ yes no, C =>
      2 * unaryCost σ C + statementCost yes C + statementCost no C + 4
  | .goto _, C => max C (unaryCost σ C)
  | .halt, C => max C 1

end BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitEncodingBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel

open Turing
open BinPackingGames.Foundations.Hastad
open BinPackingGames.Reduction

def gateTemplate (tag : Fin 5) (position : Fin 9) : Fin 3 × Bool :=
  match tag.val with
  | 0 => (0, false)
  | 1 => (0, true)
  | 2 => [(0, true), (1, true), (1, true),
      (0, false), (1, false), (1, false),
      (0, true), (1, true), (1, true)].get position
  | 3 => [(0, false), (1, true), (1, true),
      (0, false), (2, true), (2, true),
      (0, true), (1, false), (2, false)].get position
  | _ => [(0, true), (1, false), (1, false),
      (0, true), (2, false), (2, false),
      (0, false), (1, true), (2, true)].get position

def templateWords (tag : Fin 5) (values : Fin 3 → Nat) : List Nat :=
  (List.finRange 9).flatMap fun j =>
    [values (gateTemplate tag j).1, if (gateTemplate tag j).2 then 1 else 0]

def outputWords (selected : Nat) : List Nat :=
  [selected, 1, selected, 1, selected, 1]

inductive Tape where
  | input | header | counter | selected | field (slot : Fin 4)
  | scratch | reversed | output
  deriving DecidableEq, Fintype

inductive Context where
  | header (slot : Fin 2)
  | gate (tag : Fin 5) (position : Fin 9)
  | output (position : Fin 3)
  deriving DecidableEq, Fintype

abbrev State := (Unit × Context) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive Label where
  | headerStart (slot : Fin 3)
  | headerLoop (slot : Fin 3)
  | setup (context : Context)
  | scan (context : Context)
  | emit (context control : Context) (symbol : Bool)
  | restore (context : Context)
  | clearHeader | guard
  | fieldStart (slot : Fin 4)
  | fieldLoop (slot : Fin 4)
  | decodeTag
  | cleanup (slot : Fin 4)
  | finalCounter | clearSelected | finalReverse
  deriving DecidableEq, Fintype

def defaultControl : Context := .header 0
def initialState : State := (((), defaultControl), none)

def headerNext (slot : Fin 3) : Option Label :=
  if h : slot.val + 1 < 3 then some (.headerStart ⟨slot.val + 1, h⟩)
  else some (.setup (.header 0))

def contextSource : Context → Tape
  | .header j => if j.val = 0 then .header else .counter
  | .gate tag j => .field ⟨(gateTemplate tag j).1.val + 1, by
      have := (gateTemplate tag j).1.isLt
      omega⟩
  | .output _ => .selected

def contextNext : Context → Option Label
  | .header j => if j.val = 0 then some (.setup (.header 1)) else some .clearHeader
  | .gate tag j => if h : j.val + 1 < 9 then
      some (.setup (.gate tag ⟨j.val + 1, h⟩)) else some (.cleanup 0)
  | .output j => if h : j.val + 1 < 3 then
      some (.setup (.output ⟨j.val + 1, h⟩)) else some .finalCounter

def cleanupNext (j : Fin 4) : Label :=
  if h : j.val + 1 < 4 then .cleanup ⟨j.val + 1, h⟩ else .guard

def drain (tape : Tape) (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop tape (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def resetGoto (next : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => initialState) (.goto fun _ => next)

def tagDecoder : Nat → Fin 5 → TM2.Stmt Alphabet Label State
  | 0, tag => .pop (.field 0) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false) .halt
        (resetGoto (.setup (.gate tag 0))))
  | fuel + 1, tag => .pop (.field 0) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (tagDecoder fuel ⟨min (tag.val + 1) 4, by omega⟩)
        (resetGoto (.setup (.gate tag 0))))

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission

open Turing
open BinPackingGames.Reduction
open CircuitProducerModel

def contextSteps (context : Context) (base : Tape → List Bool) : Nat :=
  3 * (base (contextSource context)).length + 3

theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_MachineCircuit
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

theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

def StepSafe (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ) (cfg : TM2.Cfg Γ Λ σ) : Prop :=
  ∀ label, cfg.l = some label → StatementSafe S (program label) cfg.var cfg.stk

omit [Fintype Λ] [DecidableEq Λ] [Fintype σ] [DecidableEq σ]
  [∀ stack, Fintype (Γ stack)] [∀ stack, DecidableEq (Γ stack)] in
theorem absorbing_live (program : Λ → TM2.Stmt Γ Λ σ) (cfg : TM2.Cfg Γ Λ σ)
    (label : Λ) (live : cfg.l = some label) :
    absorbingNext (TM2.step program) cfg = TM2.stepAux (program label) cfg.var cfg.stk := by
  cases cfg with
  | mk l v tapes =>
    change l = some label at live
    subst l
    rfl

omit [Fintype Λ] [DecidableEq Λ] [Fintype σ] [DecidableEq σ]
  [∀ stack, Fintype (Γ stack)] [∀ stack, DecidableEq (Γ stack)] in
theorem absorbing_halted (program : Λ → TM2.Stmt Γ Λ σ) (cfg : TM2.Cfg Γ Λ σ)
    (halted : cfg.l = none) : absorbingNext (TM2.step program) cfg = cfg := by
  apply absorbingNext_of_none
  cases cfg with
  | mk l v tapes =>
    change l = none at halted
    subst l
    rfl

noncomputable def programCost (program : Λ → TM2.Stmt Γ Λ σ) : Nat :=
  ∑ label, statementCost (program label) 1

omit [DecidableEq K] [DecidableEq Λ] [DecidableEq σ]
  [∀ stack, DecidableEq (Γ stack)] in
theorem statementCost_le_programCost (program : Λ → TM2.Stmt Γ Λ σ) (label : Λ) :
    statementCost (program label) 1 ≤ programCost program := by
  unfold programCost
  exact Finset.single_le_sum (f := fun i : Λ => statementCost (program i) 1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)

noncomputable def expressionCost (program : Λ → TM2.Stmt Γ Λ σ) : Nat :=
  5 + Fintype.card Λ * (programCost program + 3)

end BinPackingGames.Foundations.Complexity.CookLevin.MachineCircuit

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_OutputOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PositionMachine

open Turing

section Statements

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

def decrement (destination : K)
    (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek destination (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.pop destination (fun s _ => (s.1, none)) continuation)
      (.load (fun s => (s.1, none)) continuation))

inductive Label where
  | start
  | scan
  | restore
  | finish
  deriving DecidableEq

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 2 * Polynomial.X + Polynomial.C 4

end Statements

end BinPackingGames.Foundations.Complexity.CookLevin.PositionMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

open Turing StatementCircuit

variable {K : Type} (Γ : K → Type) (σ : Type)

variable {Γ σ} [∀ k, DecidableEq (Γ k)]

variable {Λ : Type} [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [DecidableEq Λ]

abbrev OutputKind (Γ : K → Type) (Λ σ : Type) :=
  Option Λ ⊕ (σ ⊕ (Σ k, Option (Γ k)))

variable [Fintype Λ]

def rootLookup (roots : List Nat) (address : Nat) : Nat := roots[address]?.getD 0

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ClashMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def clean (ambient : σ) : State σ := ((ambient, false), none)

theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

namespace Input

inductive Label where
  | tag | scan | emit (b : Bool) | restore
  deriving DecidableEq

instance instFintypeLabel : Fintype Label where
  elems := { .tag, .scan, .emit false, .emit true, .restore }
  complete l := by cases l with
    | emit b => cases b <;> simp
    | tag => simp
    | scan => simp
    | restore => simp

def steps (n : Nat) : Nat := 3 * (n + 1) + 3

end Input

namespace Pair

def leftMap : Fin 4 ↪ Fin 6 := ⟨![0, 1, 2, 3], by decide⟩
def rightMap : Fin 4 ↪ Fin 6 := ⟨![1, 0, 2, 3], by decide⟩
def inputLeftMap : Fin 4 ↪ Fin 6 := ⟨![0, 2, 4, 5], by decide⟩
def inputRightMap : Fin 4 ↪ Fin 6 := ⟨![1, 2, 4, 5], by decide⟩

def choose (yes no : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .branch (fun s => s.1.2)
    (.load (fun s => clean s.1.1) (.goto fun _ => yes))
    (.load (fun s => clean s.1.1) (.goto fun _ => no))

theorem stepAux_choose (yes no : Λ) (base : K → List Bool) (ambient : σ) (flag : Bool) :
    TM2.stepAux (choose yes no) ((ambient, flag), none) base =
      ⟨some (if flag then yes else no), clean ambient, base⟩ := by
  cases flag <;> rfl

def offSteps (i j : Nat) : Nat := Input.steps i + Input.steps j + 1

end Pair

namespace Row

def pairMap : Fin 6 ↪ Fin 7 := ⟨![1, 2, 3, 4, 5, 6], by decide⟩

end Row

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.OrClosure

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

theorem replicate_push (n : Nat) (count : List Bool) :
    List.replicate n true ++ true :: count =
      List.replicate (n + 1) true ++ count := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [List.replicate_succ, List.cons_append] using (congrArg (List.cons true) ih)

end BinPackingGames.Foundations.Complexity.CookLevin.OrClosure

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

open Turing
open ClashMachine (State clean )

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

namespace SelectorLoop

def inputMap : Fin 4 ↪ Fin 5 := ⟨![1, 2, 3, 4], by decide⟩

inductive Label where
  | guard | input (l : ClashMachine.Input.Label) | increment
  deriving DecidableEq, Fintype

def steps : Nat → Nat → Nat
  | 0, _ => 1
  | count + 1, start => 1 + ClashMachine.Input.steps start + 1 + steps count (start + 1)

end SelectorLoop

namespace Nonempty

def loopMap : Fin 5 ↪ Fin 7 := ⟨![1, 2, 3, 5, 6], by decide⟩

def steps (q : Nat) : Nat :=
  1 + (2 * (q + 1) + 1) + (2 * (q + 1) + 1) +
    SelectorLoop.steps (q + 1) 0 + (q + 3) + 1 + (q + 3)

end Nonempty

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

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

namespace BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine

open Turing

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev Alphabet (_ : K) := Bool

inductive Label (symbols : Nat)
  | scan
  | emit (bit : Bool) (index : Fin (symbols + 1))
  deriving DecidableEq, Fintype

end BinPackingGames.Foundations.Complexity.CookLevin.InputCellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl

open Turing

theorem flatten_singletons {α β : Type*} (xs : List α) (f : α → β) :
    (xs.map fun x => [f x]).flatten = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

variable {K Λ σ : Type} [DecidableEq K]

def exitStatement (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl

namespace BinPackingGames.Foundations.Complexity.CookLevin.CellsPrefixStage

open Turing InputCellsMachine

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev Ports (K : Type) := Fin 7 ↪ K

inductive Label (symbols : Nat)
  | capacityFirst | capacitySecond | prefixFirst | prefixSecond
  | stream (entry : InputCellsMachine.Label symbols)
  deriving DecidableEq, Fintype

def streamLabels (label : Label A ↪ Λ) : InputCellsMachine.Label A ↪ Λ where
  toFun entry := label (.stream entry)
  inj' := by
    intro i j h
    exact Label.stream.inj (label.injective h)

end BinPackingGames.Foundations.Complexity.CookLevin.CellsPrefixStage

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_InitializationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachine

open Turing

inductive Label where
  | guard | inputTag | scan | emit (symbol : Bool) | restore | test
  | result (value : Bool) | done
  deriving DecidableEq, Fintype

def bodySteps (i : Nat) : Nat := 3 * (i + 1) + 5

def selectorSteps : Nat → Nat → Nat
  | _, 0 => 1
  | i, m + 1 => 1 + bodySteps i + selectorSteps (i + 1) m

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_InitializationMachineAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt

open Turing
open InitializationMachine (Label bodySteps selectorSteps)

variable {K Λ σ : Type} [DecidableEq K]

abbrev Ports (K : Type) := Fin 6 ↪ K
abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def initialState (ambient : σ) : State σ := ((ambient, false), none)

def frame (p : Ports K) (base : K → List Bool) (contents : Fin 6 → List Bool)
    (k : K) : List Bool :=
  if k = p 0 then contents 0 else if k = p 1 then contents 1
  else if k = p 2 then contents 2 else if k = p 3 then contents 3
  else if k = p 4 then contents 4 else if k = p 5 then contents 5 else base k

@[simp] theorem frame_at (p : Ports K) (base : K → List Bool)
    (contents : Fin 6 → List Bool) (j : Fin 6) : frame p base contents (p j) = contents j := by
  fin_cases j <;> simp [frame, p.injective.eq_iff]

theorem frame_other (p : Ports K) (base : K → List Bool) (contents : Fin 6 → List Bool)
    (k : K) (hk : ∀ j, k ≠ p j) : frame p base contents k = base k := by
  simp [frame, hk]

theorem update_frame (p : Ports K) (base : K → List Bool) (contents : Fin 6 → List Bool)
    (j : Fin 6) (replacement : List Bool) :
    Function.update (frame p base contents) (p j) replacement =
      frame p base (Function.update contents j replacement) := by
  funext k
  by_cases hk : ∃ r, p r = k
  · obtain ⟨r, rfl⟩ := hk
    by_cases hr : r = j
    · subst r; simp
    · simp [p.injective.ne hr, hr]
  · have hn : ∀ r, k ≠ p r := fun r h => hk ⟨r, h.symm⟩
    simp [Function.update_of_ne (hn j), frame_other p base _ k hn]

theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[m + n] x = z := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem prepend_three (n : Nat) (count : List Bool) :
    List.replicate n true ++ (true :: true :: true :: count) =
      List.replicate (n + 3) true ++ count := by
  change List.replicate n true ++ (List.replicate 3 true ++ count) = _
  rw [← List.append_assoc, List.replicate_append_replicate]

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationMachineAt

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

open Turing

variable {K Λ σ : Type} [DecidableEq K]

namespace Full

def rowMap : Fin 7 ↪ Fin 10 := ⟨![2, 3, 4, 5, 6, 7, 8], by decide⟩

theorem ext_slots {n : Nat} (slots : Fin n ↪ K) (f g : K → List Bool)
    (atSlot : ∀ i, f (slots i) = g (slots i))
    (outside : ∀ k, (∀ i, k ≠ slots i) → f k = g k) : f = g := by
  classical
  funext k
  by_cases h : ∃ i, slots i = k
  · rcases h with ⟨i, rfl⟩
    exact atSlot i
  · exact outside k (fun i hi => h ⟨i, hi.symm⟩)

inductive CopyContext where
  | outer | inner | rowClose | allClose
  deriving DecidableEq

instance instFintypeCopyContext : Fintype CopyContext where
  elems := { .outer, .inner, .rowClose, .allClose }
  complete c := by cases c <;> simp

inductive CopyLabel where
  | seed | scan | restore
  deriving DecidableEq

instance instFintypeCopyLabel : Fintype CopyLabel where
  elems := { .seed, .scan, .restore }
  complete l := by cases l <;> simp

def copyTarget (slots : Fin 10 ↪ K) : CopyContext → K
  | .outer => slots 1
  | .inner => slots 2
  | .rowClose | .allClose => slots 9

def copySteps (q : Nat) : Nat := 2 * (q + 1) + 1

def bodyBudget (q : Nat) : Nat := (q + 1) * (12 * (2 * q + 3) + 2) + 1 + 6 * q + 14

noncomputable def bodyPolynomial : Polynomial Nat :=
  (Polynomial.X + Polynomial.C 1) *
    (Polynomial.C 12 * (Polynomial.C 2 * Polynomial.X + Polynomial.C 3) + Polynomial.C 2) +
    Polynomial.C 1 + Polynomial.C 6 * Polynomial.X + Polynomial.C 14

noncomputable def timePolynomial : Polynomial Nat :=
  (Polynomial.X + Polynomial.C 1) * (bodyPolynomial + Polynomial.C 1) +
    Polynomial.C 1 + Polynomial.C 6 * Polynomial.X + Polynomial.C 13

theorem timePolynomial_eval (q : Nat) :
    timePolynomial.eval q = (q + 1) * (bodyBudget q + 1) + 1 + 6 * q + 13 := by
  simp [timePolynomial, bodyPolynomial, bodyBudget]

end Full

end BinPackingGames.Foundations.Complexity.CookLevin.ClashMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full

open Turing
open ClashMachine (State clean )

variable {K Λ σ : Type} [DecidableEq K]

def nonemptyMap : Fin 7 ↪ Fin 10 := ⟨![0, 1, 3, 5, 9, 7, 8], by decide⟩

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X + Polynomial.C 2) ^ 2 +
    ClashMachine.Full.timePolynomial + Polynomial.C 1

theorem timePolynomial_eval (q : Nat) :
    timePolynomial.eval q = 20 * (q + 2) ^ 2 + ClashMachine.Full.timePolynomial.eval q + 1 := by
  simp [timePolynomial]

theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PayloadPresenceMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadPresenceMachine

open Turing
open ClashMachine (State clean )

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev Ports (K : Type) := Fin 9 ↪ K

def presenceMap : Fin 6 ↪ Fin 9 := ⟨![2, 3, 4, 5, 7, 8], by decide⟩

omit [DecidableEq K] in
theorem closing_distinct (slots : Ports K) (j : Fin 6) : slots 6 ≠ (presenceMap.trans slots) j := by
  apply slots.injective.ne
  fin_cases j <;> decide

inductive CopyContext where
  | remaining | threshold | closing
  deriving DecidableEq

protected abbrev CopyContext.enumList : List CopyContext := [.remaining, .threshold, .closing]

protected theorem CopyContext.enumList_nodup : CopyContext.enumList.Nodup := by decide

instance instFintypeCopyContext : Fintype CopyContext where
  elems := ⟨CopyContext.enumList, CopyContext.enumList_nodup⟩
  complete x := by cases x <;> decide

def copySource (slots : Ports K) : CopyContext → K
  | .remaining | .closing => slots 0
  | .threshold => slots 1

def copyTarget (slots : Ports K) : CopyContext → K
  | .remaining => slots 2
  | .threshold => slots 4
  | .closing => slots 6

def steps (q i : Nat) : Nat :=
  1 + (2 * (q + 1) + 1) + (2 * (i + 1) + 1) + (2 * (q + 1) + 1) +
    (InitializationMachine.selectorSteps 0 (q + 1) + (q + 1 + 2)) + 1 + (q + 3)

theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadPresenceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CellsTokensAlignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

open Turing
open ClashMachine (State clean )
open PayloadPresenceMachine (Ports )

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

structure SymbolSpec where
  isInput : Bool
  trueValue : Bool
  falseValue : Bool
  absentValue : Bool
  deriving DecidableEq, Fintype

namespace Payload

def inputMap : Fin 4 ↪ Fin 9 := ⟨![3, 5, 7, 8], by decide⟩

inductive Label where
  | seed | scanQ | restoreQ | scanI | restoreI
  | inputTrue (l : ClashMachine.Input.Label)
  | middle
  | inputFalse (l : ClashMachine.Input.Label)
  | suffix | drain
  deriving DecidableEq, Fintype

def addressSteps (q i : Nat) := (2 * (q + 1) + 1) + 2 * (i + 1)

def steps (q i : Nat) : Nat := addressSteps q i + ClashMachine.Input.steps (q + 1 + i) + 1 +
  ClashMachine.Input.steps (q + 1 + i) + 1 + (q + 1 + i + 2)

theorem steps_le (q i : Nat) (hi : i < q) : steps q i ≤ 40 * (q + 2) := by
  unfold steps addressSteps ClashMachine.Input.steps
  omega

end Payload

namespace Symbol

def steps (spec : SymbolSpec) (q i : Nat) : Nat :=
  if spec.isInput then
    1 + PayloadPresenceMachine.steps q i + Payload.steps q i + 1 + PayloadPresenceMachine.steps q i + 1
  else 1

end Symbol

namespace Row

variable {A : Nat}

def tableAt (table : Fin A → SymbolSpec) (j : Nat) : SymbolSpec :=
  if hj : j < A then table ⟨j, hj⟩ else ⟨false, false, false, false⟩

def stepsFrom (table : Fin A → SymbolSpec) (q i : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | start, count + 1 => 1 + Symbol.steps (tableAt table start) q i + stepsFrom table q i (start + 1) count

def steps (table : Fin A → SymbolSpec) (q i : Nat) : Nat := stepsFrom table q i 0 A

end Row

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadCellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.PayloadRowsLoop

open Turing
open ClashMachine (State clean )
open PayloadCellsMachine (SymbolSpec)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev Alphabet (_ : K) := Bool

def rowMap : Fin 9 ↪ Fin 11 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)

def steps (table : Fin A → SymbolSpec) (q : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | i, m + 1 => 1 + PayloadCellsMachine.Row.steps table q i + 1 + steps table q (i + 1) m

end BinPackingGames.Foundations.Complexity.CookLevin.PayloadRowsLoop

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

open Turing

inductive Tape
  | current | freeInputs | root | reversedRecords | output | gateCount | scratch
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.current, .freeInputs, .root, .reversedRecords,
  .output, .gateCount, .scratch]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | copyOut | copyBack | cancel | records
  | rootOut | rootBack | countOut | countBack | currentOut | currentBack
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyOut, .copyBack, .cancel, .records, .rootOut,
  .rootBack, .countOut, .countBack, .currentOut, .currentBack]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := σ × Option Bool

def memory (current freeInputs root reversedRecords output gateCount scratch : List Bool) :
    Tape → List Bool
  | .current => current
  | .freeInputs => freeInputs
  | .root => root
  | .reversedRecords => reversedRecords
  | .output => output
  | .gateCount => gateCount
  | .scratch => scratch

@[simp] theorem update_current (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .current x = memory x b c d e f g := by
  funext t; cases t <;> rfl
@[simp] theorem update_freeInputs (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .freeInputs x = memory a x c d e f g := by
  funext t; cases t <;> rfl
@[simp] theorem update_root (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .root x = memory a b x d e f g := by
  funext t; cases t <;> rfl
@[simp] theorem update_reversedRecords (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .reversedRecords x = memory a b c x e f g := by
  funext t; cases t <;> rfl
@[simp] theorem update_output (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .output x = memory a b c d x f g := by
  funext t; cases t <;> rfl
@[simp] theorem update_gateCount (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .gateCount x = memory a b c d e x g := by
  funext t; cases t <;> rfl
@[simp] theorem update_scratch (a b c d e f g x : List Bool) :
    Function.update (memory a b c d e f g) .scratch x = memory a b c d e f x := by
  funext t; cases t <;> rfl

variable {σ : Type}

def cancelLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .freeInputs (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop .gateCount (fun state _ => (state.1, none)) (.goto fun _ => .cancel))
      (.load (fun state => (state.1, none)) (.goto fun _ => .records)))

theorem appendTrace {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, first, second]

def totalTime (n f root recordLength : Nat) : Nat :=
  2 * (n + 2) + (f + 1) + (recordLength + 1) +
    2 * (root + 2) + 2 * (n - f + 2) + 2 * (n + 2)

theorem totalTime_eq (n f root recordLength : Nat) :
    totalTime n f root recordLength = 4 * n + f + 2 * root + 2 * (n - f) + recordLength + 18 := by
  unfold totalTime
  ring

theorem totalTime_le (n f root recordLength : Nat) (hf : f ≤ n) (hr : root < n) :
    totalTime n f root recordLength ≤ 9 * n + recordLength + 18 := by
  rw [totalTime_eq]
  have hg := Nat.sub_le n f
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PostfixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixMachine

open Turing Hastad

abbrev State := Unit × Option Bool

inductive Label
  | headerStart (slot : Fin 2) | headerLoop (slot : Fin 2)
  | guard | decode
  | readStart (tag : Fin 6) (pass : Fin 2) | readLoop (tag : Fin 6) (pass : Fin 2)
  | emitTag (tag : Fin 6)
  | field (tag : Fin 6) (slot : Fin 3)
  | restore (tag : Fin 6) (slot : Fin 3)
  | closeField (tag : Fin 6) (slot : Fin 3)
  | rootDrain | rootFork | increment | clearLeft | clearRight | finish | finalReverse
  deriving DecidableEq, Fintype

def initialState : State := ((), none)

def binary (tag : Fin 6) : Bool := decide (tag.val = 3 ∨ tag.val = 4)

def readNext (tag : Fin 6) (pass : Fin 2) : Label :=
  if binary tag && decide (pass.val = 0) then .readStart tag 1 else .emitTag tag

def prepare (tag : Fin 6) : Label :=
  if tag.val < 2 then .emitTag tag else .readStart tag 0

def gateTag (tag : Fin 6) : Nat := if tag.val = 5 then 4 else tag.val

def fieldUnused (tag : Fin 6) (slot : Fin 3) : Bool :=
  decide (slot.val ≠ 0 ∧ (tag.val < 2 ∨ (tag.val = 2 ∧ slot.val = 2)))

def fieldNext (tag : Fin 6) (slot : Fin 3) : Label :=
  if h : slot.val + 1 < 3 then .field tag ⟨slot.val + 1, h⟩ else .rootDrain

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def fieldSteps (tag : Fin 6) (slot : Fin 3) (value : Nat) : Nat :=
  if fieldUnused tag slot then 1 else 2 * value + 3

def recordSteps (tag : Fin 6) (values : Fin 3 → Nat) : Nat :=
  1 + fieldSteps tag 0 (values 0) + fieldSteps tag 1 (values 1) + fieldSteps tag 2 (values 2)

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixBounds

open StatementCircuit PostfixMachine
open CircuitProducerModel

def RootsBounded (R : Nat) (roots : List Nat) : Prop := ∀ r ∈ roots, r ≤ R

theorem fieldSteps_le (tag : Fin 6) (slot : Fin 3) (value R : Nat) (h : value ≤ R) :
    fieldSteps tag slot value ≤ 2 * R + 3 := by
  unfold fieldSteps
  split <;> omega

theorem recordSteps_le (tag : Fin 6) (values : Fin 3 → Nat) (R : Nat)
    (h : ∀ slot, values slot ≤ R) : recordSteps tag values ≤ 6 * R + 10 := by
  have h0 := fieldSteps_le tag 0 (values 0) R (h 0)
  have h1 := fieldSteps_le tag 1 (values 1) R (h 1)
  have h2 := fieldSteps_le tag 2 (values 2) R (h 2)
  unfold recordSteps
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ForestStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ForestPlacement

open Turing

variable {I J K L Λ σ : Type}

abbrev Tapes (I : Type) := I → List Bool

noncomputable def fill (ports : I ↪ K) (base : Tapes K) (contents : Tapes I) : Tapes K :=
  Function.extend ports contents base

@[simp] theorem fill_at (ports : I ↪ K) (base : Tapes K) (contents : Tapes I) (i : I) :
    fill ports base contents (ports i) = contents i :=
  ports.injective.extend_apply contents base i

theorem fill_other (ports : I ↪ K) (base : Tapes K) (contents : Tapes I) (k : K)
    (outside : ∀ i, ports i ≠ k) : fill ports base contents k = base k :=
  Function.extend_apply' contents base k (not_exists.mpr outside)

theorem fill_self (ports : I ↪ K) (base : Tapes K) :
    fill ports base (fun i => base (ports i)) = base := by
  classical
  funext k
  by_cases h : ∃ i, ports i = k
  · rcases h with ⟨i, rfl⟩
    exact fill_at ports base _ i
  · exact fill_other ports base _ k (not_exists.mp h)

theorem fill_update [DecidableEq I] [DecidableEq K] (ports : I ↪ K)
    (base : Tapes K) (contents : Tapes I) (i : I) (word : List Bool) :
    fill ports base (Function.update contents i word) =
      Function.update (fill ports base contents) (ports i) word := by
  classical
  funext k
  by_cases hk : k = ports i
  · subst k
    simp only [fill_at, Function.update_self]
  · by_cases hr : ∃ j, ports j = k
    · rcases hr with ⟨j, rfl⟩
      have hj : j ≠ i := fun h => hk (congrArg ports h)
      rw [fill_at, Function.update_of_ne hj, Function.update_of_ne hk, fill_at]
    · rw [fill_other ports base _ k (not_exists.mp hr), Function.update_of_ne hk,
        fill_other ports base _ k (not_exists.mp hr)]

def placedLabel (labels : L → Λ) (haltTarget : Option Λ) : Option L → Option Λ
  | none => haltTarget
  | some label => some (labels label)

noncomputable def configuration (ports : I ↪ K) (labels : L → Λ)
    (haltTarget : Option Λ) (base : Tapes K)
    (cfg : TM2.Cfg (fun _ : I => Bool) L σ) : TM2.Cfg (fun _ : K => Bool) Λ σ where
  l := placedLabel labels haltTarget cfg.l
  var := cfg.var
  stk := fill ports base cfg.stk

def statement (ports : I ↪ K) (labels : L → Λ) (haltTarget : Option Λ) :
    TM2.Stmt (fun _ : I => Bool) L σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | .push i value next => .push (ports i) value (statement ports labels haltTarget next)
  | .peek i observe next => .peek (ports i) observe (statement ports labels haltTarget next)
  | .pop i observe next => .pop (ports i) observe (statement ports labels haltTarget next)
  | .load update next => .load update (statement ports labels haltTarget next)
  | .branch predicate yes no => .branch predicate
      (statement ports labels haltTarget yes) (statement ports labels haltTarget no)
  | .goto next => .goto (fun state => labels (next state))
  | .halt => match haltTarget with
      | none => .halt
      | some label => .goto (fun _ => label)

variable [DecidableEq I] [DecidableEq K]

theorem stepAux_simulation (ports : I ↪ K) (labels : L → Λ) (haltTarget : Option Λ)
    (base : Tapes K) (q : TM2.Stmt (fun _ : I => Bool) L σ)
    (state : σ) (contents : Tapes I) :
    TM2.stepAux (statement ports labels haltTarget q) state (fill ports base contents) =
      configuration ports labels haltTarget base (TM2.stepAux q state contents) := by
  induction q generalizing state contents with
  | push i value next ih =>
      simp only [statement, TM2.stepAux, fill_at]
      rw [← fill_update]
      exact ih state (Function.update contents i (value state :: contents i))
  | peek i observe next ih =>
      simpa only [statement, TM2.stepAux, fill_at] using
        ih (observe state (contents i).head?) contents
  | pop i observe next ih =>
      simp only [statement, TM2.stepAux, fill_at]
      rw [← fill_update]
      exact ih (observe state (contents i).head?) (Function.update contents i (contents i).tail)
  | load update next ih =>
      simpa only [statement, TM2.stepAux] using ih (update state) contents
  | branch predicate yes no ihYes ihNo =>
      cases h : predicate state
      · simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihNo state contents
      · simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihYes state contents
  | goto next => rfl
  | halt => cases haltTarget <;> rfl

theorem step_simulation (ports : I ↪ K) (labels : L → Λ) (haltTarget : Option Λ)
    (base : Tapes K) (source : L → TM2.Stmt (fun _ : I => Bool) L σ)
    (ambientProgram : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (atLabels : ∀ l, ambientProgram (labels l) = statement ports labels haltTarget (source l))
    (a b : TM2.Cfg (fun _ : I => Bool) L σ)
    (transition : TM2.step source a = some b) :
    TM2.step ambientProgram (configuration ports labels haltTarget base a) =
      some (configuration ports labels haltTarget base b) := by
  cases a with
  | mk label state contents =>
      cases label with
      | none => simp [TM2.step] at transition
      | some label =>
          have result : TM2.stepAux (source label) state contents = b := Option.some.inj transition
          rw [← result]
          change some (TM2.stepAux (ambientProgram (labels label)) state
            (fill ports base contents)) = _
          rw [atLabels, stepAux_simulation]

end BinPackingGames.Foundations.Complexity.CookLevin.ForestPlacement

namespace BinPackingGames.Foundations.Complexity.CookLevin.RootRefresh

open Turing
open BinPackingGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end BinPackingGames.Foundations.Complexity.CookLevin.RootRefresh

namespace BinPackingGames.Foundations.Complexity.CookLevin.ForestStage

open Turing StatementCircuit CircuitProducerModel
abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

inductive Label
  | reverseTokens
  | lower (label : PostfixMachine.Label)
  | reverseRecords | drainRoots | rootGuard | rootStart | rootLoop | finish
  deriving DecidableEq, Fintype

theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

def stateEquiv (σ : Type) : PostfixMachine.State × (σ × Bool) ≃ State σ where
  toFun state := (state.2, state.1.2)
  invFun state := (((), state.2), state.1)
  left_inv state := by rcases state with ⟨⟨u, register⟩, ambient⟩; cases u; rfl
  right_inv _ := rfl

theorem forest_cost_quadratic (start c T R S G H : Nat)
    (hS : S ≤ c * (12 * (start + c) + 25))
    (hG : G ≤ 4 * c * (start + c + 5))
    (hH : H ≤ 3 * (c * (start + c + 1)) + 1) :
    let m := start + c + T + R + 1
    T + S + 2 * G + R + H + 7 ≤ 25 * m ^ 2 + 80 * m + 20 := by
  dsimp only
  let m := start + c + T + R + 1
  change T + S + 2 * G + R + H + 7 ≤ 25 * m ^ 2 + 80 * m + 20
  have hc : c ≤ m := by dsimp only [m]; omega
  have hsc : start + c ≤ m := by dsimp only [m]; omega
  have hsc1 : start + c + 1 ≤ m := by dsimp only [m]; omega
  have hTR : T + R ≤ m := by dsimp only [m]; omega
  have hS' : S ≤ m * (12 * m + 25) := hS.trans (Nat.mul_le_mul hc (by omega))
  have hG' : G ≤ 4 * m * (m + 5) :=
    hG.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hc) (by omega))
  have hr : c * (start + c + 1) ≤ m * m := Nat.mul_le_mul hc hsc1
  have hH' : H ≤ 3 * (m * m) + 1 :=
    hH.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hr) 1)
  calc
    _ ≤ (T + R) + m * (12 * m + 25) +
        2 * (4 * m * (m + 5)) + (3 * (m * m) + 1) + 7 := by omega
    _ ≤ m + m * (12 * m + 25) +
        2 * (4 * m * (m + 5)) + (3 * (m * m) + 1) + 7 := by omega
    _ = 23 * m ^ 2 + 66 * m + 8 := by ring
    _ ≤ 25 * m ^ 2 + 80 * m + 20 := by omega

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 25 * Polynomial.X ^ 2 + Polynomial.C 80 * Polynomial.X + Polynomial.C 20

end BinPackingGames.Foundations.Complexity.CookLevin.ForestStage

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TermMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.TermMachine

open Turing TransitionTemplate

inductive Tape
  | cursor | capacity | roots | count | reversed
  | position | address | value | scratch | copy | saveLeft | saveRight
  deriving DecidableEq

abbrev Alphabet (_ : Tape) := Bool
abbrev State := (Unit × Bool) × Option Bool

def initialState : State := (((), false), none)

structure Input where
  cursor : Nat
  capacity : Nat
  roots : List Nat

def work : Tape → Bool
  | .cursor | .capacity | .roots | .count | .reversed => false
  | _ => true

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

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

open StatementCircuit

structure Snapshot where
  current : Nat
  roots : List Nat
  reversedRecords : List Bool
  deriving DecidableEq

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

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

namespace BinPackingGames.Foundations.Complexity.CookLevin.InputFrame

open Turing
abbrev Label := Fin 5
abbrev State := Unit × Option Bool

end BinPackingGames.Foundations.Complexity.CookLevin.InputFrame

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation

open Turing
open PolynomialMachine

variable {K Λ σ : Type}

variable [DecidableEq K]

theorem trace_trans {A : Type*} (f : A → A) {a b : Nat} {x y z : A}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierFront
open Turing
open BinPackingGames.Foundations.Hastad

abbrev State (A : Type) := A × Option Bool

def frameStates (A : Type) : (InputFrame.State × A) ≃ State A where
  toFun s := (s.2, s.1.2)
  invFun s := (((), s.2), s.1)
  left_inv := by rintro ⟨⟨⟨⟩, r⟩, a⟩; rfl
  right_inv _ := rfl

def clockStates (A : Type) : MachineHorner.State A ≃ State A where
  toFun s := (s.1.1, s.2)
  invFun s := ((s.1, ()), s.2)
  left_inv := by rintro ⟨⟨a, ⟨⟩⟩, r⟩; rfl
  right_inv _ := rfl

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierFront

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

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Ports (K : Type) := Fin 5 ↪ K

inductive Label
  | copy | restore | seed
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copy, .restore, .seed]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev State (σ : Type) := σ × Option Bool

def copied (p : Ports K) (base : K → List Bool) : K → List Bool :=
  Function.update base (p 1) (base (p 0) ++ base (p 1))

def prepared (p : Ports K) (base : K → List Bool) : K → List Bool :=
  Function.update (Function.update (copied p base) (p 3) (false :: copied p base (p 3)))
    (p 4) (false :: copied p base (p 4))

theorem prepared_other (p : Ports K) (base : K → List Bool) (k : K)
    (hc : k ≠ p 1) (ht : k ≠ p 3) (hz : k ≠ p 4) : prepared p base k = base k := by
  simp [prepared, copied, hc, ht, hz]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

namespace BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine

open Turing
open ClashMachine (State clean chain)
open PayloadCellsMachine (SymbolSpec)

variable {K Λ σ : Type} [DecidableEq K] {A : Nat}

abbrev Ports (K : Type) := Fin 14 ↪ K
abbrev Alphabet (_ : K) := Bool

def prefixMap : Fin 7 ↪ Fin 14 := ⟨![0, 2, 3, 4, 5, 6, 7], by decide⟩
def loopMap : Fin 11 ↪ Fin 14 := ⟨![1, 8, 9, 10, 11, 7, 12, 3, 4, 13, 6], by decide⟩
def paddingMap : Fin 4 ↪ Fin 14 := ⟨![5, 3, 4, 6], by decide⟩

abbrev prefixPorts (p : Ports K) := prefixMap.trans p
abbrev loopPorts (p : Ports K) := loopMap.trans p
abbrev paddingPorts (p : Ports K) := paddingMap.trans p

def WorkEmpty (p : Ports K) (base : K → List Bool) : Prop :=
  ∀ j : Fin 14, 5 ≤ j.val → base (p j) = []

theorem ext_ports (p : Ports K) {f g : K → List Bool}
    (atPorts : ∀ j, f (p j) = g (p j))
    (outside : ∀ k, (∀ j, k ≠ p j) → f k = g k) : f = g := by
  funext k
  by_cases hk : ∃ j, p j = k
  · obtain ⟨j, rfl⟩ := hk
    exact atPorts j
  · exact outside k (fun j h => hk ⟨j, h.symm⟩)

variable (p : Ports K)
  (exit : Option Λ)
  (payload : Fin A → SymbolSpec)
  (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))

def steps (payload : Fin A → SymbolSpec) (inputLength q S : Nat) : Nat :=
  (2 * (S + 2) + ((A + 4) * inputLength + 3)) + (2 * (q + 2) + 1) +
    PayloadRowsLoop.steps payload q 0 q + (S - inputLength - q + 1) + (1 + (q + 2))

end BinPackingGames.Foundations.Complexity.CookLevin.CellsMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly

open Turing

inductive Tape (cellWork : Nat) where
  | rawInput | framedInput | witnessBound | capacity | reversed | count
  | validityWork (index : Fin 7)
  | cellWork (index : Fin cellWork)
  deriving DecidableEq, Fintype

def validitySlots (n : Nat) : Fin 10 ↪ Tape n :=
  ⟨![.witnessBound, .validityWork 0, .validityWork 1, .validityWork 2,
      .validityWork 3, .validityWork 4, .validityWork 5, .reversed, .count,
      .validityWork 6], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

@[simp] theorem validitySlots_apply (n : Nat) (i : Fin 10) :
    validitySlots n i =
      ![.witnessBound, .validityWork 0, .validityWork 1, .validityWork 2,
        .validityWork 3, .validityWork 4, .validityWork 5, .reversed, .count,
        .validityWork 6] i := by
  simp only [validitySlots]
  rfl

open ClashMachine (State clean )

def cellsSlots : Fin 14 ↪ Tape 9 :=
  ⟨![.framedInput, .witnessBound, .capacity, .reversed, .count,
      .cellWork 0, .cellWork 1, .cellWork 2, .cellWork 3, .cellWork 4,
      .cellWork 5, .cellWork 6, .cellWork 7, .cellWork 8], by decide⟩

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionMachine

open Turing TransitionTemplate TermMachine

variable {K Λ σ : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration

open Turing StatementCircuit TransitionTemplate

variable {K Λ σ : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

variable {inputs : Nat}

theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionIterationTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

open Turing TermMachine TransitionTemplate

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

inductive ClosureLabel
  | seed | scan | restore | orSeed | orLoop | finish
  deriving DecidableEq

protected abbrev ClosureLabel.enumList : List ClosureLabel := [.seed, .scan, .restore, .orSeed,
  .orLoop, .finish]

protected theorem ClosureLabel.enumList_nodup : ClosureLabel.enumList.Nodup := by decide

instance instFintypeClosureLabel : Fintype ClosureLabel where
  elems := ⟨ClosureLabel.enumList, ClosureLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

section Indexed

end Indexed

theorem rootLookup_ofFn {n : Nat} (wire : Fin n → Nat) (i : Fin n) :
    rootLookup (List.ofFn wire) i.val = wire i := by
  simp [rootLookup, i.isLt]

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

open Turing StatementCircuit
open ProducerInvariant

local instance iterationTimeVerifierLabelFintype_r7b0691_1 (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype_r7b0691_1 (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype_r7b0691_1 (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq_r7b0691_1 (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq_r7b0691_1 (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq_r7b0691_1 (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _
theorem chain {α : Type*} (f : α → α) {n m : Nat} {a b c : α}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

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

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage

open Turing StatementCircuit

abbrev State (σ : Type) := ForestStage.State σ

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_CompareLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open BinPackingGames.Foundations.Complexity

variable {q : Nat} {Λ : Type}

def comparisonTime (tailName headName : Nat) : Nat :=
  2 * (tailName + 2) + 2 * (headName + 2) + max (tailName + 1) (headName + 1) + 2

theorem comparisonTime_le_of_lt (tailName headName N : Nat)
    (hTail : tailName < N) (hHead : headName < N) :
    comparisonTime tailName headName ≤ 5 * N + 6 := by
  have hm : max (tailName + 1) (headName + 1) ≤ N := max_le (by omega) (by omega)
  unfold comparisonTime
  omega

end BinPackingGames.Foundations.PCP.AlphabetTable.CompareLoop

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Initialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open BinPackingGames.Foundations.Complexity

theorem vector_list_ofFn {α : Type} {n : Nat} (vector : Vector α n) :
    List.ofFn (fun index : Fin n => vector[index]) = vector.toList := by
  have equality := congrArg Vector.toList (Vector.ofFn_getElem (xs := vector))
  simpa only [Vector.toList_ofFn, Fin.getElem_fin] using equality

theorem flatMap_length_le {α β : Type} (items : List α) (f : α → List β)
    (bound : Nat) (bounded : ∀ item ∈ items, (f item).length ≤ bound) :
    (items.flatMap f).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item items ih =>
    have hh := bounded item (by simp)
    have ht := ih (fun x hx => bounded x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

end BinPackingGames.Foundations.PCP.AlphabetTable.EmitRows

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ApproximationImpliesP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

def approximationAccepts (c : Nat) : Option RawPacking → Bool
  | none => false
  | some p => decide (5 * p.bins ≤ p.assignments.length + 5 * c)

@[simp] theorem approximationAccepts_none (c : Nat) :
    approximationAccepts c none = false := rfl

@[simp] theorem approximationAccepts_some (c : Nat) (p : RawPacking) :
    approximationAccepts c (some p) = true ↔
      5 * p.bins ≤ p.assignments.length + 5 * c := by
  simp [approximationAccepts]

end BinPackingGap

namespace BinPackingGap.ApproximationDecisionMachine

open Turing BinPackingGames.Foundations.Complexity
open BinaryEncoding
open BinPackingCompleteness.BinaryEncoding (bitsValue frame)

def borrowPred : List Bool → Option (List Bool)
  | [] => none
  | true :: tail => some (false :: tail)
  | false :: tail => (borrowPred tail).map (true :: ·)

def predWord (bits : List Bool) : List Bool := (borrowPred bits).getD []

theorem borrowPred_length (bits out : List Bool) (h : borrowPred bits = some out) :
    out.length = bits.length := by
  induction bits generalizing out with
  | nil => simp [borrowPred] at h
  | cons bit bits ih =>
    cases bit with
    | true => cases h; rfl
    | false =>
      cases ht : borrowPred bits with
      | none => simp [borrowPred, ht] at h
      | some tail =>
        simp only [borrowPred, ht, Option.map_some, Option.some.injEq] at h
        subst out
        simpa using ih tail ht

theorem predWord_length_le (bits : List Bool) : (predWord bits).length ≤ bits.length := by
  cases h : borrowPred bits with
  | none => simp [predWord, h]
  | some out => simp only [predWord, h, Option.getD_some]; exact (borrowPred_length _ _ h).le

def nextCount (count : Fin 5) : Fin 5 :=
  if h : count.val = 4 then 0 else ⟨count.val + 1, by omega⟩

def process (count : Fin 5) (bits : List Bool) : List Nat → List Bool
  | [] => bits
  | _ :: tail => process (nextCount count)
      (if count.val = 4 then predWord bits else bits) tail

inductive Tape
  | input | binary | scratch | constant | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .binary, .scratch, .constant, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | start | binRead | binRestore
  | items (count : Fin 5) | name (count : Fin 5)
  | decrement | predRestore | predDrain | compare | answer (bit : Bool)
  deriving DecidableEq, Fintype

abbrev Register := BinaryOrderMachine.State Unit
abbrev Alphabet (_ : Tape) := Bool

def clean : Register := BinaryOrderMachine.clean ()
def read (head : Option Bool) : Register := ((((), .eq), head), none)
def head (state : Register) : Option Bool := state.1.2

def tapes (input binary scratch constant output : List Bool) : Tape → List Bool
  | .input => input
  | .binary => binary
  | .scratch => scratch
  | .constant => constant
  | .output => output

@[simp] theorem tapes_input (a b d e f : List Bool) : tapes a b d e f .input = a := rfl
@[simp] theorem tapes_binary (a b d e f : List Bool) : tapes a b d e f .binary = b := rfl
@[simp] theorem tapes_scratch (a b d e f : List Bool) : tapes a b d e f .scratch = d := rfl
@[simp] theorem tapes_constant (a b d e f : List Bool) : tapes a b d e f .constant = e := rfl
@[simp] theorem tapes_output (a b d e f : List Bool) : tapes a b d e f .output = f := rfl

@[simp] theorem update_input (a b d e f x : List Bool) :
    Function.update (tapes a b d e f) .input x = tapes x b d e f := by
  funext k; cases k <;> rfl
@[simp] theorem update_binary (a b d e f x : List Bool) :
    Function.update (tapes a b d e f) .binary x = tapes a x d e f := by
  funext k; cases k <;> rfl
@[simp] theorem update_scratch (a b d e f x : List Bool) :
    Function.update (tapes a b d e f) .scratch x = tapes a b x e f := by
  funext k; cases k <;> rfl
@[simp] theorem update_constant (a b d e f x : List Bool) :
    Function.update (tapes a b d e f) .constant x = tapes a b d x f := by
  funext k; cases k <;> rfl
@[simp] theorem update_output (a b d e f x : List Bool) :
    Function.update (tapes a b d e f) .output x = tapes a b d e x := by
  funext k; cases k <;> rfl

def go (label : Label) : TM2.Stmt Alphabet Label Register :=
  .load (fun _ => clean) (.goto fun _ => label)

def finish (bit : Bool) : TM2.Stmt Alphabet Label Register :=
  .push .output (fun _ => bit) (.load (fun _ => clean) .halt)

def pushConstant (bits : List Bool) (next : TM2.Stmt Alphabet Label Register) :
    TM2.Stmt Alphabet Label Register :=
  bits.foldr (fun bit rest => .push .constant (fun _ => bit) rest) next

theorem stepAux_pushConstant (bits : List Bool) (next : TM2.Stmt Alphabet Label Register)
    (state : Register) (base : Tape → List Bool) :
    TM2.stepAux (pushConstant bits next) state base =
      TM2.stepAux next state (Function.update base .constant (bits.reverse ++ base .constant)) := by
  induction bits generalizing base with
  | nil => simp [pushConstant]
  | cons bit bits ih =>
    simp only [pushConstant, List.foldr_cons, TM2.stepAux]
    change TM2.stepAux (pushConstant bits next) state
      (Function.update base .constant (bit :: base .constant)) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

def orderExit : Ordering → Option Label
  | .lt => some (.answer true)
  | .eq => some (.answer true)
  | .gt => some (.answer false)

theorem joinTrace {X : Type*} {f : X → X} {a b d : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = d) : f^[n + m] a = d := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def borrowCost : List Bool → Nat → Nat
  | [], n => n + 2
  | true :: _, n => n + 2
  | false :: bits, n => 1 + borrowCost bits (n + 1)

def itemsCost (count : Fin 5) (bits : List Bool) : List Nat → Nat
  | [] => 1
  | a :: tail => 1 + (a.size + 1) +
      (if count.val = 4 then borrowCost bits 0 else 0) +
      itemsCost (nextCount count) (if count.val = 4 then predWord bits else bits) tail

def someSteps (c : Nat) (p : RawPacking) : Nat :=
  1 + (p.bins.size + 1) + (p.bins.size + 1) +
    itemsCost 0 p.bins.bits p.assignments +
    (max (process 0 p.bins.bits p.assignments).length c.bits.length + 2)

noncomputable def rawTime (c : Nat) : Polynomial Nat :=
  Polynomial.C (c.size + 20) * (Polynomial.X + 1) ^ 2

def cleanupTapes : List Tape := [.input, .binary, .scratch, .constant]

end BinPackingGap.ApproximationDecisionMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionCapacityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionCapacityMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

abbrev Tape := Fin 22

end BinPackingGap.ExtensionCapacityMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_IntegerTreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

structure UniformTree where
  height : ℕ
  leaves : Finset (List ℕ)
  leaves_nonempty : leaves.Nonempty
  length_leaf : ∀ l ∈ leaves, l.length = height
  positive_labels : ∀ l ∈ leaves, ∀ a ∈ l, 0 < a

namespace UniformTree

def prefixes (l : List ℕ) : Finset (List ℕ) :=
  (Finset.range (l.length + 1)).image (fun k => l.take k)

@[simp] theorem mem_prefixes_iff {w l : List ℕ} :
    w ∈ prefixes l ↔ w.IsPrefix l := by
  constructor
  · intro hw
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
    exact List.take_prefix k l
  · intro h
    exact Finset.mem_image.mpr
      ⟨w.length, Finset.mem_range.mpr (Nat.lt_succ_of_le h.length_le),
        (List.prefix_iff_eq_take.mp h).symm⟩

def vertices (T : UniformTree) : Finset (List ℕ) :=
  T.leaves.biUnion prefixes

theorem mem_vertices_iff (T : UniformTree) {w : List ℕ} :
    w ∈ T.vertices ↔ ∃ l ∈ T.leaves, w.IsPrefix l := by
  simp only [vertices, Finset.mem_biUnion, mem_prefixes_iff]

theorem leaf_mem_vertices (T : UniformTree) {l : List ℕ} (hl : l ∈ T.leaves) :
    l ∈ T.vertices :=
  (T.mem_vertices_iff).mpr ⟨l, hl, List.prefix_refl l⟩

theorem nil_mem_vertices (T : UniformTree) : [] ∈ T.vertices := by
  obtain ⟨l, hl⟩ := T.leaves_nonempty
  exact (T.mem_vertices_iff).mpr ⟨l, hl, List.nil_prefix⟩

theorem prefix_mem_vertices (T : UniformTree) {u v : List ℕ}
    (hv : v ∈ T.vertices) (h : u.IsPrefix v) : u ∈ T.vertices := by
  obtain ⟨l, hl, hvl⟩ := T.mem_vertices_iff.mp hv
  exact T.mem_vertices_iff.mpr ⟨l, hl, h.trans hvl⟩

theorem take_mem_vertices (T : UniformTree) {w : List ℕ}
    (hw : w ∈ T.vertices) (k : ℕ) : w.take k ∈ T.vertices :=
  T.prefix_mem_vertices hw (List.take_prefix k w)

theorem length_le_height (T : UniformTree) {w : List ℕ}
    (hw : w ∈ T.vertices) : w.length ≤ T.height := by
  obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp hw
  exact (T.length_leaf l hl) ▸ h.length_le

abbrev Node (T : UniformTree) := {w : List ℕ // w ∈ T.vertices}

instance nodeFintype (T : UniformTree) : Fintype T.Node :=
  Finset.fintypeCoeSort T.vertices

def root (T : UniformTree) : T.Node := ⟨[], T.nil_mem_vertices⟩

@[simp] theorem root_val (T : UniformTree) : T.root.val = [] := rfl

@[simp] theorem node_card (T : UniformTree) :
    Fintype.card T.Node = T.vertices.card := Fintype.card_coe T.vertices

def depth {T : UniformTree} (v : T.Node) : ℕ := v.val.length

def ancestor {T : UniformTree} (u v : T.Node) : Prop := u.val.IsPrefix v.val

@[simp] theorem depth_root (T : UniformTree) : depth T.root = 0 := rfl

@[simp] theorem ancestor_refl {T : UniformTree} (v : T.Node) : ancestor v v :=
  List.prefix_refl v.val

@[simp] theorem root_ancestor {T : UniformTree} (v : T.Node) : ancestor T.root v :=
  List.nil_prefix

def ancestorAt {T : UniformTree} (v : T.Node) (k : ℕ) : T.Node :=
  ⟨v.val.take k, T.take_mem_vertices v.property k⟩

@[simp] theorem ancestorAt_val {T : UniformTree} (v : T.Node) (k : ℕ) :
    (ancestorAt v k).val = v.val.take k := rfl

end UniformTree

def levelCount (marks : Finset (List ℕ)) (depth : ℕ) : ℕ :=
  (marks.filter (fun w => w.length = depth)).card

def colorCount (marks : Finset (List ℕ)) (leaf : List ℕ) : ℕ :=
  (marks.filter (fun w => w.IsPrefix leaf)).card

def RespectsTreeQuota (T : UniformTree) (quota : ℕ → ℕ)
    (marks : Finset (List ℕ)) : Prop :=
  [] ∉ marks ∧ ∀ depth, 1 ≤ depth → depth ≤ T.height →
    levelCount marks depth ≤ quota depth

structure AuxiliaryTree (phases : ℕ) where
  tree : UniformTree
  quota : ℕ → ℕ
  quota_pos : ∀ depth, 1 ≤ depth → depth ≤ tree.height → 0 < quota depth
  red : Finset (List ℕ)
  blue : Finset (List ℕ)
  red_subset : red ⊆ tree.vertices
  blue_subset : blue ⊆ tree.vertices
  root_not_red : [] ∉ red
  root_not_blue : [] ∉ blue
  red_blue_disjoint : Disjoint red blue
  red_level : ∀ depth, 1 ≤ depth → depth ≤ tree.height →
    levelCount red depth ≤ quota depth
  blue_level : ∀ depth, 1 ≤ depth → depth ≤ tree.height →
    levelCount blue depth ≤ quota depth
  total_count : ∀ leaf ∈ tree.leaves,
    colorCount red leaf + colorCount blue leaf = phases
  red_witness : ∃ leaf ∈ tree.leaves, colorCount red leaf = phases
  blue_witness : ∃ leaf ∈ tree.leaves, colorCount blue leaf = phases

  avoids : ∀ marks : Finset (List ℕ),
    RespectsTreeQuota tree quota marks →
    ∃ leaf ∈ tree.leaves, Disjoint marks (UniformTree.prefixes leaf)

theorem card_hit_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A : Finset α) (P : ι → Finset α)
    (hP : (I : Set ι).PairwiseDisjoint P) :
    (I.filter (fun i => ¬ Disjoint A (P i))).card ≤ A.card := by
  classical
  let hit := I.filter (fun i => ¬ Disjoint A (P i))
  have hx (i : {i // i ∈ hit}) : ∃ x : {x // x ∈ A}, x.val ∈ P i.val := by
    obtain ⟨x, hxA, hxP⟩ :=
      Finset.not_disjoint_iff.mp (Finset.mem_filter.mp i.property).2
    exact ⟨⟨x, hxA⟩, hxP⟩
  let f (i : {i // i ∈ hit}) : {x // x ∈ A} := (hx i).choose
  have hf (i : {i // i ∈ hit}) : (f i).val ∈ P i.val := (hx i).choose_spec
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    apply Finset.disjoint_left.mp
      (hP (Finset.mem_filter.mp i.property).1
        (Finset.mem_filter.mp j.property).1 hne) (hf i)
    rw [hij]
    exact hf j
  simpa only [Fintype.card_coe, hit] using Fintype.card_le_of_injective f hinj

theorem exists_disjoint_of_card_lt {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A : Finset α) (P : ι → Finset α)
    (hP : (I : Set ι).PairwiseDisjoint P) (hcard : A.card < I.card) :
    ∃ i ∈ I, Disjoint A (P i) := by
  classical
  by_contra h
  have hhit : ∀ i ∈ I, ¬ Disjoint A (P i) := fun i hi hd => h ⟨i, hi, hd⟩
  have hfilter : I.filter (fun i => ¬ Disjoint A (P i)) = I :=
    Finset.filter_eq_self.mpr hhit
  have hle := card_hit_le I A P hP
  rw [hfilter] at hle
  exact (Nat.not_le_of_lt hcard) hle

def prefixesAfter (stem word : List ℕ) : Finset (List ℕ) :=
  ((UniformTree.prefixes word).erase []).image (fun v => stem ++ v)

@[simp]
theorem mem_prefixesAfter_iff {stem word w : List ℕ} :
    w ∈ prefixesAfter stem word ↔
      ∃ v, v ≠ [] ∧ v.IsPrefix word ∧ stem ++ v = w := by
  simp [prefixesAfter, Finset.mem_image, and_assoc]

theorem prefixes_append_eq (stem word : List ℕ) :
    UniformTree.prefixes (stem ++ word) =
      UniformTree.prefixes stem ∪ prefixesAfter stem word := by
  ext w
  simp only [Finset.mem_union, UniformTree.mem_prefixes_iff]
  constructor
  · intro hw
    rcases List.prefix_or_prefix_of_prefix hw (List.prefix_append stem word) with h | h
    · exact Or.inl h
    · obtain ⟨v, rfl⟩ := h
      by_cases hv : v = []
      · subst v
        exact Or.inl (by simpa only [List.append_nil] using List.prefix_refl stem)
      · exact Or.inr (mem_prefixesAfter_iff.mpr
          ⟨v, hv, (List.prefix_append_right_inj stem).mp hw, rfl⟩)
  · rintro (hw | hw)
    · exact hw.trans (List.prefix_append stem word)
    · obtain ⟨v, _, hv, rfl⟩ := mem_prefixesAfter_iff.mp hw
      exact (List.prefix_append_right_inj stem).mpr hv

theorem disjoint_positive_prefixes_cons {a b : ℕ} (u v : List ℕ) (hab : a ≠ b) :
    Disjoint ((UniformTree.prefixes (a :: u)).erase [])
      ((UniformTree.prefixes (b :: v)).erase []) := by
  apply Finset.disjoint_left.mpr
  intro w hwa hwb
  have hpa := UniformTree.mem_prefixes_iff.mp (Finset.mem_erase.mp hwa).2
  have hpb := UniformTree.mem_prefixes_iff.mp (Finset.mem_erase.mp hwb).2
  cases w with
  | nil => exact (Finset.mem_erase.mp hwa).1 rfl
  | cons x xs =>
      exact hab ((List.cons_prefix_cons.mp hpa).1.symm.trans
        (List.cons_prefix_cons.mp hpb).1)

theorem disjoint_prefixesAfter_cons (stem : List ℕ) {a b : ℕ}
    (u v : List ℕ) (hab : a ≠ b) :
    Disjoint (prefixesAfter stem (a :: u)) (prefixesAfter stem (b :: v)) := by
  apply Finset.disjoint_left.mpr
  intro w hwa hwb
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hwa
  obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hwb
  have hxy : x = y := List.append_cancel_left (hxeq.trans hyeq.symm)
  exact Finset.disjoint_left.mp (disjoint_positive_prefixes_cons u v hab)
    hx (hxy.symm ▸ hy)

theorem disjoint_positive_spine_prefixes {a b n m : ℕ} (hab : a ≠ b) :
    Disjoint ((UniformTree.prefixes ((a + 1) :: List.replicate n 1)).erase [])
      ((UniformTree.prefixes ((b + 1) :: List.replicate m 1)).erase []) := by
  apply disjoint_positive_prefixes_cons
  exact fun h => hab (Nat.add_right_cancel h)

theorem disjoint_spine_prefixesAfter (stem : List ℕ) {a b n m : ℕ} (hab : a ≠ b) :
    Disjoint (prefixesAfter stem ((a + 1) :: List.replicate n 1))
      (prefixesAfter stem ((b + 1) :: List.replicate m 1)) := by
  apply disjoint_prefixesAfter_cons
  exact fun h => hab (Nat.add_right_cancel h)

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TreeAttachment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap
namespace UniformTree

def graftLeaves (T : UniformTree) (G : T.leaves → UniformTree) : Finset (List ℕ) :=
  Finset.univ.biUnion (fun l : T.leaves =>
    (G l).leaves.image (fun w => l.val ++ w))

theorem mem_graftLeaves (T : UniformTree) (G : T.leaves → UniformTree)
    {x : List ℕ} :
    x ∈ graftLeaves T G ↔ ∃ l : T.leaves, ∃ w ∈ (G l).leaves, x = l.val ++ w := by
  constructor
  · intro hx
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨w, hw, hx⟩ := Finset.mem_image.mp hl
    exact ⟨l, w, hw, hx.symm⟩
  · rintro ⟨l, w, hw, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨l, Finset.mem_univ l, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩

def graft (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) : UniformTree where
  height := T.height + N
  leaves := graftLeaves T G
  leaves_nonempty := by
    obtain ⟨l, hl⟩ := T.leaves_nonempty
    obtain ⟨w, hw⟩ := (G ⟨l, hl⟩).leaves_nonempty
    exact ⟨l ++ w, (mem_graftLeaves T G).mpr ⟨⟨l, hl⟩, w, hw, rfl⟩⟩
  length_leaf := by
    intro x hx
    obtain ⟨l, w, hw, rfl⟩ := (mem_graftLeaves T G).mp hx
    rw [List.length_append, T.length_leaf l.val l.property,
      (G l).length_leaf w hw, hG l]
  positive_labels := by
    intro x hx a ha
    obtain ⟨l, w, hw, rfl⟩ := (mem_graftLeaves T G).mp hx
    rcases List.mem_append.mp ha with ha | ha
    · exact T.positive_labels l.val l.property a ha
    · exact (G l).positive_labels w hw a ha

@[simp] theorem graft_height (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) :
    (graft T G N hG).height = T.height + N := rfl

theorem mem_graft_leaves (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) {x : List ℕ} :
    x ∈ (graft T G N hG).leaves ↔
      ∃ l : T.leaves, ∃ w ∈ (G l).leaves, x = l.val ++ w :=
  mem_graftLeaves T G

theorem append_eq_append_iff (T : UniformTree) (l₁ l₂ : T.leaves)
    (u v : List ℕ) :
    l₁.val ++ u = l₂.val ++ v ↔ l₁ = l₂ ∧ u = v := by
  constructor
  · intro h
    have hlen : l₁.val.length = l₂.val.length :=
      (T.length_leaf l₁.val l₁.property).trans (T.length_leaf l₂.val l₂.property).symm
    exact ⟨Subtype.ext (List.append_inj_left h hlen), List.append_inj_right h hlen⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem old_prefix_iff (T : UniformTree) {u : List ℕ} (hu : u ∈ T.vertices)
    (l : T.leaves) (w : List ℕ) :
    u.IsPrefix (l.val ++ w) ↔ u.IsPrefix l.val := by
  apply List.isPrefix_append_of_length
  rw [T.length_leaf l.val l.property]
  exact T.length_le_height hu

theorem leaf_prefix_append_iff (T : UniformTree) (l₁ l₂ : T.leaves)
    (w : List ℕ) : l₁.val.IsPrefix (l₂.val ++ w) ↔ l₁ = l₂ := by
  rw [T.old_prefix_iff (T.leaf_mem_vertices l₁.property) l₂ w]
  constructor
  · intro h
    exact Subtype.ext (h.eq_of_length
      ((T.length_leaf l₁.val l₁.property).trans
        (T.length_leaf l₂.val l₂.property).symm))
  · rintro rfl
    exact List.prefix_refl l₁.val

theorem vertices_subset_graft (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) :
    T.vertices ⊆ (graft T G N hG).vertices := by
  intro u hu
  obtain ⟨l, hl, hul⟩ := T.mem_vertices_iff.mp hu
  let oldLeaf : T.leaves := ⟨l, hl⟩
  obtain ⟨w, hw⟩ := (G oldLeaf).leaves_nonempty
  apply (graft T G N hG).mem_vertices_iff.mpr
  refine ⟨l ++ w, ?_, hul.trans (List.prefix_append l w)⟩
  exact (mem_graft_leaves T G N hG).mpr ⟨oldLeaf, w, hw, rfl⟩

theorem append_mem_graft_vertices (T : UniformTree) (G : T.leaves → UniformTree)
    (N : ℕ) (hG : ∀ l, (G l).height = N) (l : T.leaves)
    {v : List ℕ} (hv : v ∈ (G l).vertices) :
    l.val ++ v ∈ (graft T G N hG).vertices := by
  obtain ⟨w, hw, hvw⟩ := (G l).mem_vertices_iff.mp hv
  exact (graft T G N hG).mem_vertices_iff.mpr
    ⟨l.val ++ w, (mem_graft_leaves T G N hG).mpr ⟨l, w, hw, rfl⟩,
      (List.prefix_append_right_inj l.val).mpr hvw⟩

theorem filter_old_prefix_append (T : UniformTree) (marks : Finset (List ℕ))
    (hmarks : marks ⊆ T.vertices) (l : T.leaves) (w : List ℕ) :
    marks.filter (fun u => u.IsPrefix (l.val ++ w)) =
      marks.filter (fun u => u.IsPrefix l.val) := by
  apply Finset.filter_congr
  intro u hu
  exact T.old_prefix_iff (hmarks hu) l w

theorem append_prefix_append_iff (T : UniformTree) (l₁ l₂ : T.leaves)
    (u v : List ℕ) :
    (l₁.val ++ u).IsPrefix (l₂.val ++ v) ↔ l₁ = l₂ ∧ u.IsPrefix v := by
  constructor
  · intro h
    have heq : l₁ = l₂ := (T.leaf_prefix_append_iff l₁ l₂ v).mp
      ((List.prefix_append l₁.val u).trans h)
    subst l₂
    exact ⟨rfl, (List.prefix_append_right_inj l₁.val).mp h⟩
  · rintro ⟨rfl, h⟩
    exact (List.prefix_append_right_inj l₁.val).mpr h

end UniformTree
end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TreePruning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace UniformTree

def prune (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty) : UniformTree where
  height := T.height
  leaves := keep
  leaves_nonempty := hne
  length_leaf := fun l hl => T.length_leaf l (hsub hl)
  positive_labels := fun l hl => T.positive_labels l (hsub hl)

@[simp] theorem prune_height (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty) :
    (T.prune keep hsub hne).height = T.height := rfl

@[simp] theorem prune_leaves (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty) :
    (T.prune keep hsub hne).leaves = keep := rfl

theorem prune_vertices_subset (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty) :
    (T.prune keep hsub hne).vertices ⊆ T.vertices := by
  intro w hw
  obtain ⟨l, hl, hwl⟩ := (T.prune keep hsub hne).mem_vertices_iff.mp hw
  exact T.mem_vertices_iff.mpr ⟨l, hsub hl, hwl⟩

def pruneEmbedding (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty) :
    (T.prune keep hsub hne).Node ↪ T.Node where
  toFun v := ⟨v.val, T.prune_vertices_subset keep hsub hne v.property⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun v : T.Node => v.val) h)

@[simp] theorem pruneEmbedding_val (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty)
    (v : (T.prune keep hsub hne).Node) :
    (T.pruneEmbedding keep hsub hne v).val = v.val := rfl

@[simp] theorem pruneEmbedding_depth (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty)
    (v : (T.prune keep hsub hne).Node) :
    depth (T.pruneEmbedding keep hsub hne v) = depth v := rfl

@[simp] theorem pruneEmbedding_ancestor (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty)
    (u v : (T.prune keep hsub hne).Node) :
    ancestor (T.pruneEmbedding keep hsub hne u)
      (T.pruneEmbedding keep hsub hne v) ↔ ancestor u v := Iff.rfl

def projectMarks {T : UniformTree} (A : Finset T.Node) : Finset (List ℕ) :=
  A.image Subtype.val

@[simp] theorem mem_projectMarks {T : UniformTree} (A : Finset T.Node)
    (w : List ℕ) : w ∈ projectMarks A ↔ ∃ v ∈ A, v.val = w := by
  simp only [projectMarks, Finset.mem_image]

def retainMarks (T : UniformTree) (marks : Finset (List ℕ)) : Finset T.Node :=
  Finset.univ.filter (fun v => v.val ∈ marks)

@[simp] theorem mem_retainMarks (T : UniformTree) (marks : Finset (List ℕ))
    (v : T.Node) : v ∈ T.retainMarks marks ↔ v.val ∈ marks := by
  simp only [retainMarks, Finset.mem_filter, Finset.mem_univ, true_and]

end UniformTree

open UniformTree

namespace AuxiliaryTree

def richLeaves {n : ℕ} (aux : AuxiliaryTree n)
    (marks : Finset (List ℕ)) (d : ℕ) : Finset (List ℕ) :=
  aux.tree.leaves.filter (fun l => d ≤ colorCount marks l)

theorem richLeaves_subset {n : ℕ} (aux : AuxiliaryTree n)
    (marks : Finset (List ℕ)) (d : ℕ) :
    aux.richLeaves marks d ⊆ aux.tree.leaves := Finset.filter_subset _ _

theorem richLeaves_nonempty {n d : ℕ} (aux : AuxiliaryTree n)
    (marks : Finset (List ℕ)) (h : d ≤ n)
    (hw : ∃ l ∈ aux.tree.leaves, colorCount marks l = n) :
    (aux.richLeaves marks d).Nonempty := by
  obtain ⟨l, hl, heq⟩ := hw
  exact ⟨l, Finset.mem_filter.mpr ⟨hl, heq.symm ▸ h⟩⟩

theorem richLeaves_cover {d : ℕ} (aux : AuxiliaryTree (2 * d - 1))
    (l : List ℕ) (hl : l ∈ aux.tree.leaves) :
    l ∈ aux.richLeaves aux.red d ∨ l ∈ aux.richLeaves aux.blue d := by
  have htotal := aux.total_count l hl
  have hrich : d ≤ colorCount aux.red l ∨ d ≤ colorCount aux.blue l := by omega
  exact hrich.imp (fun h => Finset.mem_filter.mpr ⟨hl, h⟩)
    (fun h => Finset.mem_filter.mpr ⟨hl, h⟩)

theorem height_pos {n : ℕ} (aux : AuxiliaryTree n) (hn : 0 < n) :
    0 < aux.tree.height := by
  obtain ⟨l, hl, hcount⟩ := aux.red_witness
  by_contra hpos
  have hheight : aux.tree.height = 0 := by omega
  have hl_nil : l = [] := List.length_eq_zero_iff.mp ((aux.tree.length_leaf l hl).trans hheight)
  have hempty : aux.red.filter (fun w => w.IsPrefix l) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hred, hp⟩ := Finset.mem_filter.mp hw
    have hw_nil : w = [] := by
      apply List.length_eq_zero_iff.mp
      have hle := hp.length_le
      rw [hl_nil] at hle
      exact Nat.eq_zero_of_le_zero hle
    exact aux.root_not_red (hw_nil ▸ hred)
  have hz : colorCount aux.red l = 0 := by rw [colorCount, hempty, Finset.card_empty]
  omega

def richTree {n d : ℕ} (aux : AuxiliaryTree n) (marks : Finset (List ℕ))
    (hne : (aux.richLeaves marks d).Nonempty) : UniformTree :=
  aux.tree.prune (aux.richLeaves marks d) (aux.richLeaves_subset marks d) hne

end AuxiliaryTree

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TreeColorCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

section

open scoped BigOperators

def phaseQuota (j : ℕ) : ℕ := 2 ^ (j - 1)

@[simp] theorem phaseQuota_succ (j : ℕ) : phaseQuota (j + 1) = 2 ^ j := by
  simp [phaseQuota]

theorem phaseQuota_pos (j : ℕ) : 0 < phaseQuota j := by
  exact Nat.pow_pos (by decide)

theorem sum_phaseQuota_add_one (i : ℕ) :
    (∑ j ∈ Finset.Icc 1 i, phaseQuota j) + 1 = 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hset : Finset.Icc 1 (i + 1) = insert (i + 1) (Finset.Icc 1 i) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : i + 1 ∉ Finset.Icc 1 i := by simp
      rw [hset, Finset.sum_insert hnot, phaseQuota_succ, pow_succ]
      omega

theorem sum_phaseQuota_lt (i : ℕ) :
    (∑ j ∈ Finset.Icc 1 i, phaseQuota j) < 2 ^ i := by
  have h := sum_phaseQuota_add_one i
  omega

def continuationCount (i N : ℕ) : ℕ :=
  1 + ∑ j ∈ Finset.Icc (i + 1) N, phaseQuota j

theorem continuationCount_pos (i N : ℕ) : 0 < continuationCount i N := by
  unfold continuationCount
  omega

@[simp] theorem continuationCount_self (N : ℕ) : continuationCount N N = 1 := by
  simp [continuationCount]

section FiniteMarkings

variable {α : Type*}

theorem card_rank_window_eq (A : Finset α) (rank : α → ℕ) (h lo hi : ℕ) :
    (A.filter (fun x => h + lo < rank x ∧ rank x ≤ h + hi)).card =
      ∑ j ∈ Finset.Icc (lo + 1) hi,
        (A.filter (fun x => rank x = h + j)).card := by
  classical
  calc
    (A.filter (fun x => h + lo < rank x ∧ rank x ≤ h + hi)).card =
        (A.filter (fun x => rank x - h ∈ Finset.Icc (lo + 1) hi)).card := by
      apply congrArg Finset.card
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hx, hlo, hhi⟩
        exact ⟨hx, by omega, by omega⟩
      · rintro ⟨hx, hlo, hhi⟩
        exact ⟨hx, by omega, by omega⟩
    _ = ∑ j ∈ Finset.Icc (lo + 1) hi,
        (A.filter (fun x => rank x - h = j)).card :=
      (Finset.sum_card_fiberwise_eq_card_filter A
        (Finset.Icc (lo + 1) hi) (fun x => rank x - h)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjpos : 1 ≤ j := by
        have := (Finset.mem_Icc.mp hj).1
        omega
      apply congrArg Finset.card
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, hxrank⟩
        exact ⟨hx, by omega⟩
      · rintro ⟨hx, hxrank⟩
        exact ⟨hx, by omega⟩

theorem card_rank_window_le (A : Finset α) (rank : α → ℕ) (q : ℕ → ℕ)
    (h lo hi : ℕ)
    (hquota : ∀ j ∈ Finset.Icc (lo + 1) hi,
      (A.filter (fun x => rank x = h + j)).card ≤ q j) :
    (A.filter (fun x => h + lo < rank x ∧ rank x ≤ h + hi)).card ≤
      ∑ j ∈ Finset.Icc (lo + 1) hi, q j := by
  rw [card_rank_window_eq]
  exact Finset.sum_le_sum hquota

theorem card_rank_initial_lt_pow (A : Finset α) (rank : α → ℕ) (h i : ℕ)
    (hquota : ∀ j ∈ Finset.Icc 1 i,
      (A.filter (fun x => rank x = h + j)).card ≤ phaseQuota j) :
    (A.filter (fun x => h < rank x ∧ rank x ≤ h + i)).card < 2 ^ i := by
  have hle := card_rank_window_le A rank phaseQuota h 0 i hquota
  simp only [Nat.add_zero, Nat.zero_add] at hle
  exact lt_of_le_of_lt hle (sum_phaseQuota_lt i)

theorem card_rank_tail_lt_continuations (A : Finset α) (rank : α → ℕ)
    (h i N : ℕ)
    (hquota : ∀ j ∈ Finset.Icc (i + 1) N,
      (A.filter (fun x => rank x = h + j)).card ≤ phaseQuota j) :
    (A.filter (fun x => h + i < rank x ∧ rank x ≤ h + N)).card <
      continuationCount i N := by
  have hle := card_rank_window_le A rank phaseQuota h i N hquota
  unfold continuationCount
  omega

end FiniteMarkings

end

section
namespace ForkGadget

open scoped BigOperators

def spine (i a : ℕ) : List ℕ := (a + 1) :: List.replicate (i - 1) 1

def continuation (N i b : ℕ) : List ℕ :=
  if i < N then (b + 1) :: List.replicate (N - i - 1) 1 else []

def leafWord (N i a b : ℕ) : List ℕ := spine i a ++ continuation N i b

def leaves (N i : ℕ) : Finset (List ℕ) :=
  ((Finset.range (2 ^ i)).product (Finset.range (continuationCount i N))).image
    (fun ab => leafWord N i ab.1 ab.2)

@[simp] theorem spine_length {i : ℕ} (hi : 1 ≤ i) (a : ℕ) :
    (spine i a).length = i := by
  simp only [spine, List.length_cons, List.length_replicate]
  omega

@[simp] theorem continuation_length {N i : ℕ} (hiN : i ≤ N) (b : ℕ) :
    (continuation N i b).length = N - i := by
  unfold continuation
  split_ifs with h
  · simp only [List.length_cons, List.length_replicate]
    omega
  · simp only [List.length_nil]
    omega

@[simp] theorem leafWord_length {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N)
    (a b : ℕ) : (leafWord N i a b).length = N := by
  simp only [leafWord, List.length_append, spine_length hi, continuation_length hiN]
  omega

theorem spine_injective (i : ℕ) : Function.Injective (spine i) := by
  intro a b h
  have heq : a + 1 = b + 1 := (List.cons.inj h).1
  omega

theorem leafWord_positive (N i a b : ℕ) :
    ∀ x ∈ leafWord N i a b, 0 < x := by
  intro x hx
  simp only [leafWord, List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [spine, List.mem_cons, List.mem_replicate] at hx
    rcases hx with rfl | ⟨_, rfl⟩ <;> omega
  · unfold continuation at hx
    split_ifs at hx with h
    · simp only [List.mem_cons, List.mem_replicate] at hx
      rcases hx with rfl | ⟨_, rfl⟩ <;> omega
    · simp only [List.not_mem_nil] at hx

theorem leafWord_mem {N i a b : ℕ} (ha : a < 2 ^ i)
    (hb : b < continuationCount i N) : leafWord N i a b ∈ leaves N i := by
  exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr hb⟩, rfl⟩

theorem mem_leaves_iff {N i : ℕ} {l : List ℕ} :
    l ∈ leaves N i ↔ ∃ a < 2 ^ i, ∃ b < continuationCount i N,
      leafWord N i a b = l := by
  constructor
  · intro hl
    obtain ⟨ab, hab, heq⟩ := Finset.mem_image.mp hl
    have hab' := Finset.mem_product.mp hab
    exact ⟨ab.1, Finset.mem_range.mp hab'.1, ab.2,
      Finset.mem_range.mp hab'.2, heq⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact leafWord_mem ha hb

def tree (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) : UniformTree where
  height := N
  leaves := leaves N i
  leaves_nonempty := ⟨leafWord N i 0 0,
    leafWord_mem (Nat.two_pow_pos i) (continuationCount_pos i N)⟩
  length_leaf := by
    intro l hl
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_leaves_iff.mp hl
    exact leafWord_length hi hiN a b
  positive_labels := by
    intro l hl
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_leaves_iff.mp hl
    exact leafWord_positive N i a b

@[simp] theorem tree_height (N i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    (tree N i hi hiN).height = N := rfl

def red (i : ℕ) : Finset (List ℕ) :=
  (Finset.range (phaseQuota i)).image (spine i)

def blue (i : ℕ) : Finset (List ℕ) :=
  (Finset.Ico (phaseQuota i) (2 ^ i)).image (spine i)

theorem two_mul_phaseQuota {i : ℕ} (hi : 1 ≤ i) : 2 * phaseQuota i = 2 ^ i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp [phaseQuota, pow_succ, Nat.mul_comm]

theorem card_red (i : ℕ) : (red i).card = phaseQuota i := by
  rw [red, Finset.card_image_of_injective _ (spine_injective i), Finset.card_range]

theorem card_blue {i : ℕ} (hi : 1 ≤ i) : (blue i).card = phaseQuota i := by
  rw [blue, Finset.card_image_of_injective _ (spine_injective i), Nat.card_Ico]
  have h := two_mul_phaseQuota hi
  omega

theorem red_depth {i : ℕ} (hi : 1 ≤ i) {w : List ℕ} (hw : w ∈ red i) :
    w.length = i := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
  exact spine_length hi a

theorem blue_depth {i : ℕ} (hi : 1 ≤ i) {w : List ℕ} (hw : w ∈ blue i) :
    w.length = i := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
  exact spine_length hi a

theorem root_not_red {i : ℕ} (hi : 1 ≤ i) : [] ∉ red i := by
  intro h
  have := red_depth hi h
  simp only [List.length_nil] at this
  omega

theorem root_not_blue {i : ℕ} (hi : 1 ≤ i) : [] ∉ blue i := by
  intro h
  have := blue_depth hi h
  simp only [List.length_nil] at this
  omega

theorem red_blue_disjoint (i : ℕ) : Disjoint (red i) (blue i) := by
  apply Finset.disjoint_left.mpr
  intro w hr hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hb
  have hab := spine_injective i heq
  have hlt := Finset.mem_range.mp ha
  have hle := (Finset.mem_Ico.mp hb).1
  omega

theorem spine_mem_vertices {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N)
    {a : ℕ} (ha : a < 2 ^ i) : spine i a ∈ (tree N i hi hiN).vertices := by
  apply (tree N i hi hiN).mem_vertices_iff.mpr
  exact ⟨leafWord N i a 0, leafWord_mem ha (continuationCount_pos i N),
    List.prefix_append _ _⟩

theorem red_subset {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N) :
    red i ⊆ (tree N i hi hiN).vertices := by
  intro w hw
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
  apply spine_mem_vertices hi hiN
  have hlt := Finset.mem_range.mp ha
  have hp := phaseQuota_pos i
  have heq := two_mul_phaseQuota hi
  omega

theorem blue_subset {N i : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N) :
    blue i ⊆ (tree N i hi hiN).vertices := by
  intro w hw
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
  exact spine_mem_vertices hi hiN (Finset.mem_Ico.mp ha).2

theorem level_le_of_single_depth (marks : Finset (List ℕ)) (i : ℕ)
    (hdepth : ∀ w ∈ marks, w.length = i) (hcard : marks.card = phaseQuota i)
    (depth : ℕ) : levelCount marks depth ≤ phaseQuota depth := by
  by_cases h : depth = i
  · subst depth
    exact (Finset.card_filter_le marks _).trans_eq hcard
  · have hf : marks.filter (fun w => w.length = depth) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw hd
      exact h (hd.symm.trans (hdepth w hw))
    simp only [levelCount, hf, Finset.card_empty, Nat.zero_le]

theorem red_level {i : ℕ} (hi : 1 ≤ i) (depth : ℕ) :
    levelCount (red i) depth ≤ phaseQuota depth :=
  level_le_of_single_depth (red i) i (fun _ hw => red_depth hi hw) (card_red i) depth

theorem blue_level {i : ℕ} (hi : 1 ≤ i) (depth : ℕ) :
    levelCount (blue i) depth ≤ phaseQuota depth :=
  level_le_of_single_depth (blue i) i (fun _ hw => blue_depth hi hw) (card_blue hi) depth

theorem spine_prefix_leafWord_iff {N i a b c : ℕ} (hi : 1 ≤ i) :
    (spine i c).IsPrefix (leafWord N i a b) ↔ c = a := by
  constructor
  · intro h
    have hs : (spine i a).IsPrefix (leafWord N i a b) := List.prefix_append _ _
    rcases List.prefix_or_prefix_of_prefix h hs with hca | hac
    · exact spine_injective i (hca.eq_of_length (by rw [spine_length hi, spine_length hi]))
    · exact (spine_injective i (hac.eq_of_length
        (by rw [spine_length hi, spine_length hi]))).symm
  · rintro rfl
    exact List.prefix_append _ _

theorem colorCount_spines (I : Finset ℕ) {N i : ℕ} (hi : 1 ≤ i)
    (a b : ℕ) : colorCount (I.image (spine i)) (leafWord N i a b) =
      if a ∈ I then 1 else 0 := by
  have hf : (I.image (spine i)).filter (fun w => w.IsPrefix (leafWord N i a b)) =
      if a ∈ I then {spine i a} else ∅ := by
    ext w
    by_cases ha : a ∈ I
    · simp only [ha, ite_true, if_true, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hw, hp⟩
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
        rw [(spine_prefix_leafWord_iff hi).mp hp]
      · rintro rfl
        exact ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, List.prefix_append _ _⟩
    · simp only [ha, ite_false, Finset.mem_filter]
      constructor
      · rintro ⟨hw, hp⟩
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hw
        exact (ha ((spine_prefix_leafWord_iff hi).mp hp ▸ hc)).elim
      · simp
  unfold colorCount
  rw [hf]
  split_ifs <;> simp

theorem red_count {N i : ℕ} (hi : 1 ≤ i) (a b : ℕ) :
    colorCount (red i) (leafWord N i a b) = if a < phaseQuota i then 1 else 0 := by
  simpa only [red, Finset.mem_range] using
    colorCount_spines (Finset.range (phaseQuota i)) (N := N) hi a b

theorem blue_count {N i : ℕ} (hi : 1 ≤ i) (a b : ℕ) :
    colorCount (blue i) (leafWord N i a b) =
      if phaseQuota i ≤ a ∧ a < 2 ^ i then 1 else 0 := by
  simpa only [blue, Finset.mem_Ico] using
    colorCount_spines (Finset.Ico (phaseQuota i) (2 ^ i)) (N := N) hi a b

theorem total_count {N i : ℕ} (hi : 1 ≤ i) {l : List ℕ} (hl : l ∈ leaves N i) :
    colorCount (red i) l + colorCount (blue i) l = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_leaves_iff.mp hl
  rw [red_count hi, blue_count hi]
  split_ifs <;> omega

end ForkGadget

open scoped BigOperators

end

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TreeAvoidance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

def pullMarks (stem : List ℕ) (marks : Finset (List ℕ)) : Finset (List ℕ) :=
  (marks.filter (fun w => stem.IsPrefix w)).image (fun w => w.drop stem.length)

@[simp] theorem mem_pullMarks (stem word : List ℕ) (marks : Finset (List ℕ)) :
    word ∈ pullMarks stem marks ↔ stem ++ word ∈ marks := by
  constructor
  · intro hw
    obtain ⟨v, hv, hdrop⟩ := Finset.mem_image.mp hw
    obtain ⟨hvA, hpref⟩ := Finset.mem_filter.mp hv
    have heq : stem ++ word = v := by
      calc
        stem ++ word = stem ++ v.drop stem.length :=
          congrArg (fun t => stem ++ t) hdrop.symm
        _ = v.take stem.length ++ v.drop stem.length :=
          congrArg (fun t => t ++ v.drop stem.length) (List.prefix_iff_eq_take.mp hpref)
        _ = v := List.take_append_drop stem.length v
    exact heq.symm ▸ hvA
  · intro hw
    exact Finset.mem_image.mpr
      ⟨stem ++ word, Finset.mem_filter.mpr ⟨hw, List.prefix_append stem word⟩,
        by simp⟩

@[simp] theorem nil_mem_pullMarks (stem : List ℕ) (marks : Finset (List ℕ)) :
    [] ∈ pullMarks stem marks ↔ stem ∈ marks := by
  simpa only [List.append_nil] using mem_pullMarks stem [] marks

theorem levelCount_pullMarks_le (stem : List ℕ) (marks : Finset (List ℕ)) (j : ℕ) :
    levelCount (pullMarks stem marks) j ≤ levelCount marks (stem.length + j) := by
  have hsub : (pullMarks stem marks).filter (fun w => w.length = j) ⊆
      (marks.filter (fun w => w.length = stem.length + j)).image
        (fun w => w.drop stem.length) := by
    intro w hw
    obtain ⟨hw, hlen⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_image.mpr ⟨stem ++ w, ?_, by simp⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_pullMarks stem w marks).mp hw, by simp only [List.length_append, hlen]⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

theorem disjoint_prefixes_append_of_pull (stem word : List ℕ)
    (marks : Finset (List ℕ))
    (hold : Disjoint marks (UniformTree.prefixes stem))
    (hnew : Disjoint (pullMarks stem marks) (UniformTree.prefixes word)) :
    Disjoint marks (UniformTree.prefixes (stem ++ word)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hprefix
  rw [prefixes_append_eq] at hprefix
  rcases Finset.mem_union.mp hprefix with hprefix | hprefix
  · exact Finset.disjoint_left.mp hold hv hprefix
  · obtain ⟨w, _, hw, heq⟩ := mem_prefixesAfter_iff.mp hprefix
    apply Finset.disjoint_left.mp hnew
    · exact (mem_pullMarks stem w marks).mpr (heq.symm ▸ hv)
    · exact UniformTree.mem_prefixes_iff.mpr hw

end BinPackingGap

end OAI
end


