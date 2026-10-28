-- Prove2me | Definitions.Def_OAIQ082C003
-- name    : OAIQ082C003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:23:53.927039+00:00
-- url     : https://prove2.me/theorems/c2fb8a7a-f260-47b2-b20e-10f120c451c7
-- title:
--   Definitions bundle OAIQ082C003 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 647 declarations of OpenAI's Lean: 280 definitions, 62 inductive types or structures, 33 instances and 272 theorems. The definitions and types are `OAI.BinPackingGap.BinaryMonusMachine.trimSteps`, `OAI.BinPackingGap.BinaryMonusPreserving.Label`, `OAI.BinPackingGap.BinaryMonusPreserving.Label.enumList`, `OAI.BinPackingGap.BinaryMonusPreserving.budget`, `OAI.BinPackingGap.BinaryMonusPreserving.enlarge`, `OAI.BinPackingGap.BinaryMonusPreserving.resultTapes`, `OAI.BinPackingGap.BinaryMulMachine.Label`, `OAI.BinPackingGap.BinaryMulMachine.Label.enumList`, `OAI.BinPackingGap.BinaryMulMachine.framedTapes`, `OAI.BinPackingGap.BinaryMulMachine.timePolynomial`, `OAI.BinPackingGap.BinaryOrderMachine.PreserveLabel`, `OAI.BinPackingGap.BinaryOrderMachine.PreserveLabel.enumList`, `OAI.BinPackingGap.BinaryOrderMachine.preservingSteps`, `OAI.BinPackingGap.BinaryPowerMachine.Label`, `OAI.BinPackingGap.BinaryPowerMachine.Workspace`, `OAI.BinPackingGap.BinaryPowerMachine.bodyBudget`, `OAI.BinPackingGap.BinaryPowerMachine.loopBudget`, `OAI.BinPackingGap.BinaryPowerMachine.mulSlots`, `OAI.BinPackingGap.BinaryPowerMachine.perIteration`, `OAI.BinPackingGap.BinaryPowerMachine.timePolynomial`, `OAI.BinPackingGap.BinaryRegisterProgram.Command`, `OAI.BinPackingGap.BinaryRegisterProgram.Operands`, `OAI.BinPackingGap.BinaryRegisterProgram.Ready`, `OAI.BinPackingGap.BinaryRegisterProgram.addSlots`, `OAI.BinPackingGap.BinaryRegisterProgram.appendRuns`, `OAI.BinPackingGap.BinaryRegisterProgram.commandBound`, `OAI.BinPackingGap.BinaryRegisterProgram.commandReady`, `OAI.BinPackingGap.BinaryRegisterProgram.destination`, `OAI.BinPackingGap.BinaryRegisterProgram.mulSlots`, `OAI.BinPackingGap.BinaryRegisterProgram.registerTapes`, `OAI.BinPackingGap.BinaryRegisterProgram.registerWords`, `OAI.BinPackingGap.BinaryRegisterProgram.result`, `OAI.BinPackingGap.BinaryRegisterProgram.value`, `OAI.BinPackingGap.BinaryTallyMachine.Alphabet`, `OAI.BinPackingGap.BinaryTallyMachine.Label`, `OAI.BinPackingGap.BinaryToTallyMachine.Reg`, `OAI.BinPackingGap.BinaryToTallyMachine.initial`, `OAI.BinPackingGap.BinaryToTallyMachine.running`, `OAI.BinPackingGap.BinaryToTallyMachine.runtimeBound`, `OAI.BinPackingGap.BooleanTapeCode.FrameLabel` and 302 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_BinaryOrderMachine`, `BinPacking_Arithmetic_BinaryPowerMachine`, `BinPacking_Arithmetic_BinaryTallyMachine`, `BinPacking_Arithmetic_BinaryToTallyMachine`, `BinPacking_Arithmetic_GraphPackingRegisters`, `BinPacking_Arithmetic_GraphTallyMachine`, `BinPacking_Arithmetic_NatExpression`, `BinPacking_Arithmetic_NatExpressionBounds`, `BinPacking_Arithmetic_NatExpressionBranch`, `BinPacking_Arithmetic_PackingRegisterFrame`, `BinPacking_Configurations_ConfigurationLP`, `BinPacking_Inventory_CurrentMatches`, `BinPacking_Inventory_InventoryScores`, `BinPacking_Inventory_LabelConservation`, `BinPacking_Machines_DropPackingBoundMachine`, `BinPacking_Machines_FrameEmitMachine`, `BinPacking_Machines_GraphPackingBounds`, `BinPacking_Machines_GraphPackingJobList`, `BinPacking_Machines_GraphPackingPreparationFinish`, `BinPacking_Machines_IntegerPackingArithmetic`, `BinPacking_Machines_MachineBoundedIteration`, `BinPacking_Machines_PackingCountedProgram`, `BinPacking_Machines_PackingJobLoop`, `BinPacking_Machines_PackingPowerProgram`, `BinPacking_Machines_PackingSetupGraph`, `BinPacking_Machines_PackingVertexUpdate`, `BinPacking_Packing_CapacityScan`, `BinPacking_Packing_CoordinateOrder`, `BinPacking_Packing_FiniteHall`, `BinPacking_Packing_FractionWidth`, `BinPacking_Packing_ItemEnumeration`, `BinPacking_Packing_K4Graph`, `BinPacking_Packing_PackingScalar`, `BinPacking_Packing_PackingScalarExpression`, `BinPacking_Search_ExtensionAgreementMachine`, `BinPacking_Search_ExtensionCapacityBounds`, `BinPacking_Search_ExtensionMachineSpace`, `BinPacking_Search_ExtensionShapeMachine`, `BinPacking_Search_ExtensionValidationMachine`, `BinPacking_Search_ExtensionVerifier`, `BinPacking_Search_ExtensionVerifierMachine`, `BinPacking_Search_ExtensionVerifierPipeline`, `BinPacking_Search_SearchInitialItemsMachine`, `BinPacking_Search_SearchInitializeEncoding`, `BinPacking_Trees_CompletionGeometry`, `BinPacking_Trees_IntegerTreeGeometry`, `BinPacking_Trees_KeyGeometry`, `BinPacking_Trees_TestGeometry`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C007`, `OAIQ082C008` and `OAIQ082C009`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap

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

section Preserving

variable {K Λ σ : Type} [DecidableEq K]

inductive PreserveLabel
  | leftOut | leftBack | rightOut | rightBack | compare
  deriving DecidableEq

protected abbrev PreserveLabel.enumList : List PreserveLabel := [.leftOut, .leftBack, .rightOut,
  .rightBack, .compare]

protected theorem PreserveLabel.enumList_nodup : PreserveLabel.enumList.Nodup := by decide

instance instFintypePreserveLabel : Fintype PreserveLabel where
  elems := ⟨PreserveLabel.enumList, PreserveLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

def preservingSteps (leftLength rightLength : Nat) : Nat :=
  2 * (leftLength + 1) + 2 * (rightLength + 1) + max leftLength rightLength + 1

theorem preservingSteps_le (leftLength rightLength : Nat) :
    preservingSteps leftLength rightLength ≤ 3 * (leftLength + rightLength) + 5 := by
  unfold preservingSteps
  omega

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Preserving

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

namespace BinPackingGap.UnaryToBinaryMachine

open Turing BinPackingGames.Foundations.Complexity

theorem size_le_self (n : Nat) : n.size ≤ n := by
  apply Nat.size_le.mpr
  exact n.lt_two_pow_self

inductive Label
  | scan | carry | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .carry, .restore]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ A : Type} [DecidableEq K]

def tapes (source output scratch : K) (base : K → List Bool)
    (input binary work : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base source input) output binary) scratch work

variable (source output scratch : K)
variable (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)

variable (labels : Label → Λ) (exit : Option Λ)
variable (base : K → List Bool) (ambient : A)

include hSO hSC hOC

omit [DecidableEq K] hSO hSC hOC in
theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGap.UnaryToBinaryMachine

namespace BinPackingGap.BinaryTallyMachine

open Turing
open BinPackingGames.Foundations.Complexity

abbrev Label := UnaryToBinaryMachine.Label
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {K Λ A : Type} [DecidableEq K]

theorem joinPlainTrace {X : Type} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGap.BinaryTallyMachine

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

inductive Label
  | copyLeft | forkLeft | copyRight | forkRight | guard
  | copyAddend | forkAddend | add | restoreSum | shift
  | clearShift | reverseOutput | output
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyLeft, .forkLeft, .copyRight, .forkRight,
  .guard, .copyAddend, .forkAddend, .add, .restoreSum, .shift, .clearShift, .reverseOutput,
  .output]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

noncomputable def framedTapes (slots : Fin 9 ↪ K) (base : K → List Bool)
    (words : Fin 9 → List Bool) : K → List Bool := fun k =>
  if h : ∃ i, slots i = k then words (Classical.choose h) else base k

theorem composeTrace {S : Type} {f : S → S} {n m : Nat} {a b c : S}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[m + n] a = c := by
  rw [Function.iterate_add_apply, first, second]

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 4 * Polynomial.X ^ 2 + Polynomial.C 14 * Polynomial.X + Polynomial.C 12

end BinPackingGap.BinaryMulMachine

namespace BinPackingGap.BinaryPowerMachine

open Turing
open BinPackingGames.Foundations.Complexity

variable {K Λ A : Type} [DecidableEq K]

inductive Label
  | initialize_ | guard | multiply (phase : BinaryMulMachine.Label)
  | clearAccumulator | reverseProduct | restoreAccumulator
  deriving DecidableEq, Fintype

def mulSlots (slots : Fin 11 ↪ K) : Fin 9 ↪ K where
  toFun i := slots ⟨i.val, by omega⟩
  inj' := by
    intro i j h
    have h' := congrArg Fin.val (slots.injective h)
    exact Fin.ext h'

def Workspace (slots : Fin 11 ↪ K) (base : K → List Bool) : Prop :=
  ∀ i : Fin 11, 2 ≤ i.val → i.val ≠ 9 → base (slots i) = []

noncomputable def bodyBudget (a r : Nat) : Nat :=
  1 + BinaryMulMachine.timePolynomial.eval (a.size + r.size) +
    (r.size + 1) + ((a * r).size + 1) + ((a * r).size + 1)

noncomputable def loopBudget (a : Nat) : Nat → List Bool → Nat
  | _, [] => 1
  | r, _ :: tally => bodyBudget a r + loopBudget a (a * r) tally

noncomputable def perIteration (width : Nat) : Nat :=
  BinaryMulMachine.timePolynomial.eval (2 * width) + 3 * width + 5

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 100 * (Polynomial.X + Polynomial.C 2) ^ 5

end BinPackingGap.BinaryPowerMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.NatExpressionCompiler

universe u

inductive Expr (α : Type u) : Type u
  | constant (value : Nat)
  | input (index : α)
  | add (left right : Expr α)
  | mul (left right : Expr α)
  | monus (left right : Expr α)

variable {α : Type u}

def eval (values : α → Nat) : Expr α → Nat
  | .constant value => value
  | .input index => values index
  | .add left right => eval values left + eval values right
  | .mul left right => eval values left * eval values right
  | .monus left right => eval values left - eval values right

@[simp] theorem eval_constant (values : α → Nat) (value : Nat) :
    eval values (.constant value) = value := rfl

@[simp] theorem eval_input (values : α → Nat) (index : α) :
    eval values (.input index) = values index := rfl

@[simp] theorem eval_add (values : α → Nat) (left right : Expr α) :
    eval values (.add left right) = eval values left + eval values right := rfl

@[simp] theorem eval_mul (values : α → Nat) (left right : Expr α) :
    eval values (.mul left right) = eval values left * eval values right := rfl

@[simp] theorem eval_monus (values : α → Nat) (left right : Expr α) :
    eval values (.monus left right) = eval values left - eval values right := rfl

def Node : Expr α → Type
  | .constant _ => Unit
  | .input _ => Unit
  | .add left right => Unit ⊕ (Node left ⊕ Node right)
  | .mul left right => Unit ⊕ (Node left ⊕ Node right)
  | .monus left right => Unit ⊕ (Node left ⊕ Node right)

instance nodeDecidableEq : (expression : Expr α) → DecidableEq (Node expression)
  | .constant _ => inferInstanceAs (DecidableEq Unit)
  | .input _ => inferInstanceAs (DecidableEq Unit)
  | .add left right =>
      letI : DecidableEq (Node left) := nodeDecidableEq left
      letI : DecidableEq (Node right) := nodeDecidableEq right
      inferInstanceAs (DecidableEq (Unit ⊕ (Node left ⊕ Node right)))
  | .mul left right =>
      letI : DecidableEq (Node left) := nodeDecidableEq left
      letI : DecidableEq (Node right) := nodeDecidableEq right
      inferInstanceAs (DecidableEq (Unit ⊕ (Node left ⊕ Node right)))
  | .monus left right =>
      letI : DecidableEq (Node left) := nodeDecidableEq left
      letI : DecidableEq (Node right) := nodeDecidableEq right
      inferInstanceAs (DecidableEq (Unit ⊕ (Node left ⊕ Node right)))

def rootBranch (left right : Expr α) : Unit ⊕ (Node left ⊕ Node right) :=
  .inl ()

def root : (expression : Expr α) → Node expression
  | .constant _ => ()
  | .input _ => ()
  | .add left right => rootBranch left right
  | .mul left right => rootBranch left right
  | .monus left right => rootBranch left right

@[simp] theorem rootBranch_eq (left right : Expr α) :
    rootBranch left right = Sum.inl () := rfl

@[simp] theorem root_constant (value : Nat) :
    root (.constant (α := α) value) = () := rfl

@[simp] theorem root_input (index : α) : root (.input index) = () := rfl

@[simp] theorem root_add (left right : Expr α) :
    root (.add left right) = rootBranch left right := rfl

@[simp] theorem root_mul (left right : Expr α) :
    root (.mul left right) = rootBranch left right := rfl

@[simp] theorem root_monus (left right : Expr α) :
    root (.monus left right) = rootBranch left right := rfl

end BinPackingGap.NatExpressionCompiler

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_PackingRegisterFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryRegisterProgram

structure Operands (Reg : Type*) where
  destination : Reg
  left : Reg
  right : Reg
  left_ne_right : left ≠ right
  left_ne_destination : left ≠ destination
  right_ne_destination : right ≠ destination

variable {Reg K : Type*}

def addSlots (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) : Fin 7 ↪ K where
  toFun i := slot (![Sum.inl op.left, Sum.inl op.right, Sum.inr 0, Sum.inr 1,
    Sum.inr 2, Sum.inl op.destination, Sum.inr 3] i)
  inj' := by
    intro i j hij
    have heq := slot.injective hij
    fin_cases i <;> fin_cases j <;>
      simp_all [op.left_ne_right, op.left_ne_destination, op.right_ne_destination,
        Ne.symm op.left_ne_right, Ne.symm op.left_ne_destination,
        Ne.symm op.right_ne_destination]

@[simp] theorem addSlots_zero (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 0 = slot (Sum.inl op.left) := rfl

@[simp] theorem addSlots_one (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 1 = slot (Sum.inl op.right) := rfl

@[simp] theorem addSlots_two (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 2 = slot (Sum.inr 0) := rfl

@[simp] theorem addSlots_three (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 3 = slot (Sum.inr 1) := rfl

@[simp] theorem addSlots_four (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 4 = slot (Sum.inr 2) := rfl

@[simp] theorem addSlots_five (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 5 = slot (Sum.inl op.destination) := rfl

@[simp] theorem addSlots_six (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    addSlots slot op 6 = slot (Sum.inr 3) := rfl

def mulSlots (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) : Fin 9 ↪ K where
  toFun i := slot (![Sum.inl op.left, Sum.inl op.right, Sum.inl op.destination,
    Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5] i)
  inj' := by
    intro i j hij
    have heq := slot.injective hij
    fin_cases i <;> fin_cases j <;>
      simp_all [op.left_ne_right, op.left_ne_destination, op.right_ne_destination,
        Ne.symm op.left_ne_right, Ne.symm op.left_ne_destination,
        Ne.symm op.right_ne_destination]

@[simp] theorem mulSlots_zero (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 0 = slot (Sum.inl op.left) := rfl

@[simp] theorem mulSlots_one (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 1 = slot (Sum.inl op.right) := rfl

@[simp] theorem mulSlots_two (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 2 = slot (Sum.inl op.destination) := rfl

@[simp] theorem mulSlots_three (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 3 = slot (Sum.inr 0) := rfl

@[simp] theorem mulSlots_four (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 4 = slot (Sum.inr 1) := rfl

@[simp] theorem mulSlots_five (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 5 = slot (Sum.inr 2) := rfl

@[simp] theorem mulSlots_six (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 6 = slot (Sum.inr 3) := rfl

@[simp] theorem mulSlots_seven (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 7 = slot (Sum.inr 4) := rfl

@[simp] theorem mulSlots_eight (slot : (Reg ⊕ Fin 6) ↪ K) (op : Operands Reg) :
    mulSlots slot op 8 = slot (Sum.inr 5) := rfl

def registerWords (values : Reg → ℕ) : Reg ⊕ Fin 6 → List Bool
  | Sum.inl r => (values r).bits
  | Sum.inr _ => []

@[simp] theorem registerWords_reg (values : Reg → ℕ) (r : Reg) :
    registerWords values (Sum.inl r) = (values r).bits := rfl

@[simp] theorem registerWords_scratch (values : Reg → ℕ) (i : Fin 6) :
    registerWords values (Sum.inr i) = [] := rfl

noncomputable def registerTapes (slot : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Reg → ℕ) : K → List Bool := by
  classical
  exact fun k =>
    if h : ∃ i, slot i = k then registerWords values (Classical.choose h) else base k

end BinPackingGap.BinaryRegisterProgram

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpressionBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.BinaryMonusMachine

open Turing
open BinPackingGames.Foundations.Complexity

variable {K Λ A : Type} [DecidableEq K]

variable {σ : Type}

def trimSteps : List Bool → Nat
  | false :: xs => trimSteps xs + 1
  | _ => 1

theorem trimSteps_le (xs : List Bool) : trimSteps xs ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [trimSteps]
  | cons bit xs ih =>
      cases bit <;> simp [trimSteps]
      omega

end BinPackingGap.BinaryMonusMachine

namespace BinPackingGap.BinaryMonusPreserving

open Turing
open BinPackingGames.Foundations.Complexity

variable {K Λ A : Type} [DecidableEq K]

inductive Label
  | leftOut | leftBack | rightOut | rightBack | subtract | trim | transfer | drain
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.leftOut, .leftBack, .rightOut, .rightBack,
  .subtract, .trim, .transfer, .drain]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def resultTapes (slots : Fin 7 ↪ K) (base : K → List Bool) (a b : Nat) : K → List Bool :=
  Function.update base (slots 5) (a - b).bits

def budget (a b : Nat) : Nat :=
  2 * (a.size + 1) + 2 * (b.size + 1) + 3 * (max a.size b.size + 1)

theorem budget_le (a b : Nat) : budget a b ≤ 5 * (a.size + b.size) + 7 := by
  unfold budget
  omega

def enlarge {X : Type} {step : X → Option X} {a : X} {b : Option X} {m n : Nat}
    (run : StateTransition.EvalsToInTime step a b m) (h : m ≤ n) :
    StateTransition.EvalsToInTime step a b n where
  steps := run.steps
  evals_in_steps := run.evals_in_steps
  steps_le_m := run.steps_le_m.trans h

end BinPackingGap.BinaryMonusPreserving

namespace BinPackingGap.BinaryRegisterProgram

open Turing
open BinPackingGames.Foundations.Complexity

inductive Command (Reg : Type)
  | add (op : Operands Reg)
  | mul (op : Operands Reg)
  | monus (op : Operands Reg)
  | constant (dst : Reg) (value : Nat)
  | clear (dst : Reg)
  | copy (dst src : Reg) (different : dst ≠ src)

variable {Reg K Λ A : Type}

def destination : Command Reg → Reg
  | .add op | .mul op | .monus op => op.destination
  | .constant dst _ | .clear dst | .copy dst _ _ => dst

def value (command : Command Reg) (values : Reg → Nat) : Nat :=
  match command with
  | .add op => values op.left + values op.right
  | .mul op => values op.left * values op.right
  | .monus op => values op.left - values op.right
  | .constant _ n => n
  | .clear _ => 0
  | .copy _ src _ => values src

def result [DecidableEq Reg] (command : Command Reg) (values : Reg → Nat) : Reg → Nat :=
  Function.update values (destination command) (value command values)

def commandReady (command : Command Reg) (values : Reg → Nat) : Prop :=
  match command with
  | .clear _ => True
  | _ => values (destination command) = 0

def Ready [DecidableEq Reg] : List (Command Reg) → (Reg → Nat) → Prop
  | [], _ => True
  | command :: commands, values =>
      commandReady command values ∧ Ready commands (result command values)

@[simp] theorem result_destination [DecidableEq Reg] (command : Command Reg)
    (values : Reg → Nat) : result command values (destination command) = value command values := by
  simp [result]

theorem result_other [DecidableEq Reg] (command : Command Reg) (values : Reg → Nat)
    (r : Reg) (h : r ≠ destination command) : result command values r = values r := by
  simp [result, h]

end BinPackingGap.BinaryRegisterProgram

namespace BinPackingGap.NatExpressionCompiler

open BinaryRegisterProgram

inductive BinaryOp
  | add
  | mul
  | monus
  deriving DecidableEq

def applyOp : BinaryOp → Nat → Nat → Nat
  | .add, left, right => left + right
  | .mul, left, right => left * right
  | .monus, left, right => left - right

variable {α Reg L R N : Type}

def leftReg (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) : L ↪ Reg where
  toFun node := loc (.inr (.inl node))
  inj' := by
    intro a b h
    exact Sum.inl.inj (Sum.inr.inj (loc.injective h))

def rightReg (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg) : R ↪ Reg where
  toFun node := loc (.inr (.inr node))
  inj' := by
    intro a b h
    exact Sum.inr.inj (Sum.inr.inj (loc.injective h))

end BinPackingGap.NatExpressionCompiler

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

theorem nat_size_mono {a b : ℕ} (h : a ≤ b) : Nat.size a ≤ Nat.size b :=
  Nat.size_le_size h

theorem nat_size_mul_le (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  simpa only [Nat.pow_add] using
    Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem nat_size_pow_succ_le (a m : ℕ) :
    Nat.size (a ^ (m + 1)) ≤ (m + 1) * Nat.size a := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      Nat.size (a ^ (m + 1 + 1)) = Nat.size (a ^ (m + 1) * a) := by rw [Nat.pow_succ]
      _ ≤ Nat.size (a ^ (m + 1)) + Nat.size a := nat_size_mul_le _ _
      _ ≤ (m + 1) * Nat.size a + Nat.size a := Nat.add_le_add_right ih _
      _ = (m + 1 + 1) * Nat.size a := by simp only [Nat.add_mul, Nat.one_mul]

theorem nat_size_pow_le (a m : ℕ) :
    Nat.size (a ^ m) ≤ m * Nat.size a + 1 := by
  cases m with
  | zero => simp [Nat.size_one]
  | succ m => exact Nat.le_trans (nat_size_pow_succ_le a m) (Nat.le_succ _)

theorem nat_size_add_le_max (a b : ℕ) :
    Nat.size (a + b) ≤ max (Nat.size a) (Nat.size b) + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ max (Nat.size a) (Nat.size b) :=
    Nat.size_le.mp (Nat.le_max_left _ _)
  have hb : b < 2 ^ max (Nat.size a) (Nat.size b) :=
    Nat.size_le.mp (Nat.le_max_right _ _)
  calc
    a + b < 2 ^ max (Nat.size a) (Nat.size b) +
        2 ^ max (Nat.size a) (Nat.size b) := Nat.add_lt_add ha hb
    _ = 2 ^ (max (Nat.size a) (Nat.size b) + 1) := by
      rw [Nat.pow_succ]
      omega

theorem nat_size_le_self (n : ℕ) : Nat.size n ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

theorem nat_size_sub_le (a b : ℕ) : Nat.size (a - b) ≤ Nat.size a :=
  nat_size_mono (Nat.sub_le a b)

end BinPackingGap

namespace BinPackingGap.GraphPackingBounds

def repetitionCoefficient (P K : ℕ) : ℕ := 100 * (P + K + 1)

def binCoefficient (P K t d : ℕ) : ℕ := t + 4 * d * repetitionCoefficient P K

theorem one_le_input_square (s : ℕ) : 1 ≤ (s + 1) ^ 2 :=
  Nat.pow_pos (Nat.succ_pos s)

theorem input_le_input_square (s : ℕ) : s + 1 ≤ (s + 1) ^ 2 := by nlinarith

theorem constant_le_quadratic (c s : ℕ) : c ≤ c * (s + 1) ^ 2 := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left c (one_le_input_square s)

theorem linear_le_quadratic (c s : ℕ) :
    c * (s + 1) ≤ c * (s + 1) ^ 2 :=
  Nat.mul_le_mul_left c (input_le_input_square s)

theorem repetitions_le_linear (P K n s : ℕ) (hn : n ≤ s) :
    100 * (P + n * K + 1) ≤ repetitionCoefficient P K * (s + 1) := by
  have hnk := Nat.mul_le_mul_right K hn
  unfold repetitionCoefficient
  nlinarith [Nat.zero_le (P * s)]

theorem bins_le_quadratic (P K n m t d s : ℕ) (hn : n ≤ s) (hm : m ≤ s) :
    n * t + 4 * d * m * (100 * (P + n * K + 1)) ≤
      binCoefficient P K t d * (s + 1) ^ 2 := by
  let c := repetitionCoefficient P K
  have hR := repetitions_le_linear P K n s hn
  have hmul := Nat.mul_le_mul (show m ≤ s + 1 by omega) hR
  have hmul' : m * (100 * (P + n * K + 1)) ≤ c * (s + 1) ^ 2 := by
    dsimp [c]
    nlinarith [hmul]
  have hnt : n * t ≤ t * (s + 1) ^ 2 := by
    have hn' : n ≤ (s + 1) ^ 2 := by
      exact hn.trans ((Nat.le_succ s).trans (input_le_input_square s))
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right t hn'
  have hrest := Nat.mul_le_mul_left (4 * d) hmul'
  unfold binCoefficient
  dsimp [c] at hrest
  nlinarith

theorem size_radix_le_linear (P K n s : ℕ) (hn : n ≤ s) :
    Nat.size (100 * (P + n * K + 1) + 1) ≤
      (repetitionCoefficient P K + 1) * (s + 1) := by
  have h := (nat_size_le_self _).trans
    (Nat.add_le_add_right (repetitions_le_linear P K n s hn) 1)
  nlinarith

theorem size_edge_power_le_quadratic (P K n m s : ℕ) (hn : n ≤ s) (hm : m ≤ s) :
    Nat.size ((100 * (P + n * K + 1) + 1) ^ m) ≤
      (repetitionCoefficient P K + 2) * (s + 1) ^ 2 := by
  have hpow := nat_size_pow_le (100 * (P + n * K + 1) + 1) m
  have hradix := size_radix_le_linear P K n s hn
  have hm' : m ≤ s + 1 := by omega
  have hprod := Nat.mul_le_mul hm' hradix
  have hsq := one_le_input_square s
  nlinarith

theorem size_vertex_power_le_linear (n s : ℕ) (hn : n ≤ s) :
    Nat.size (3 ^ n) ≤ 3 * (s + 1) := by
  have h := nat_size_pow_le 3 n
  have hthree : Nat.size 3 ≤ 2 := by decide
  have hp := Nat.mul_le_mul_left n hthree
  omega

theorem size_geometry_denominator_le_quadratic (P K T n m s : ℕ)
    (hn : n ≤ s) (hm : m ≤ s) :
    Nat.size (160 * (100 * (P + n * K + 1) + 1) ^ m * T) ≤
      (repetitionCoefficient P K + 2 + Nat.size 160 + Nat.size T) *
        (s + 1) ^ 2 := by
  have hmul₁ := nat_size_mul_le 160 ((100 * (P + n * K + 1) + 1) ^ m)
  have hmul₂ := nat_size_mul_le (160 * (100 * (P + n * K + 1) + 1) ^ m) T
  have hp := size_edge_power_le_quadratic P K n m s hn hm
  have hc₁ := constant_le_quadratic (Nat.size 160) s
  have hc₂ := constant_le_quadratic (Nat.size T) s
  nlinarith

end BinPackingGap.GraphPackingBounds

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

open Turing
open BinPackingGames.Foundations.Complexity

variable {Reg K Λ A : Type} [DecidableEq Reg] [DecidableEq K]

def appendRuns {X : Type} {step : X → Option X} {a b c : X} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) where
  steps := first.steps + second.steps
  evals_in_steps := by
    rw [Nat.add_comm, Function.iterate_add_apply, first.evals_in_steps]
    exact second.evals_in_steps
  steps_le_m := Nat.add_le_add first.steps_le_m second.steps_le_m

def commandBound (width : Nat) : Nat := 16 * width ^ 2 + 28 * width + 12

end BinPackingGap.BinaryRegisterProgram

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_FrameEmitMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.FrameEmitMachine

open Turing BinPackingGames.Foundations.Complexity

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => (state.1, none))
    (match exit with | none => .halt | some label => .goto fun _ => label)

def instruction (source output : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push output (fun _ => true)
        (.push output (fun state => state.2.getD false) (finish (some again))))
      (.push output (fun _ => false) (finish exit)))

end BinPackingGap.FrameEmitMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_K4Graph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

def primaryScoreBound : ℕ := 100 ^ 11

def lossAllowance (c : ℕ) : ℕ := 25 * (c + 1) * (1 + 5 * primaryScoreBound)

def depthDemand (c : ℕ) (ρ : ℝ) : ℕ :=
  Nat.ceil (max (72 * (lossAllowance c : ℝ)) (120 * (lossAllowance c : ℝ) / ρ))

def repetitions (P n K : ℕ) : ℕ := 100 * (P + n * K + 1)

theorem lossAllowance_pos (c : ℕ) : 0 < lossAllowance c := by
  unfold lossAllowance
  positivity

theorem depthDemand_ge_72_real (c : ℕ) (ρ : ℝ) :
    72 * (lossAllowance c : ℝ) ≤ (depthDemand c ρ : ℝ) := by
  exact (le_max_left _ _).trans (Nat.le_ceil _)

theorem depthDemand_ge_72 (c : ℕ) (ρ : ℝ) :
    72 * lossAllowance c ≤ depthDemand c ρ := by
  exact_mod_cast depthDemand_ge_72_real c ρ

theorem depthDemand_pos (c : ℕ) (ρ : ℝ) : 0 < depthDemand c ρ :=
  lt_of_lt_of_le (Nat.mul_pos (by norm_num) (lossAllowance_pos c))
    (depthDemand_ge_72 c ρ)

structure GraphInput where
  n : ℕ
  edges : List (Fin n × Fin n)
  ordered : ∀ e ∈ edges, e.1 < e.2
  distinct : edges.Nodup

namespace GraphInput

abbrev Vertex (G : GraphInput) := Fin G.n

abbrev Edge (G : GraphInput) := Fin G.edges.length

def left (G : GraphInput) (e : G.Edge) : G.Vertex := (G.edges[e]).1

def right (G : GraphInput) (e : G.Edge) : G.Vertex := (G.edges[e]).2

def IsCover (G : GraphInput) (C : Finset G.Vertex) : Prop :=
  ∀ e ∈ G.edges, e.1 ∈ C ∨ e.2 ∈ C

def CoverAtMost (G : GraphInput) (k : ℕ) : Prop :=
  ∃ C : Finset G.Vertex, G.IsCover C ∧ C.card ≤ k

end GraphInput

open scoped BigOperators

namespace GraphInput

def endpoint (G : GraphInput) (e : G.Edge) (s : Fin 2) : G.Vertex :=
  if s = 0 then G.left e else G.right e

@[simp] theorem endpoint_zero (G : GraphInput) (e : G.Edge) :
    G.endpoint e 0 = G.left e := by simp [endpoint]

@[simp] theorem endpoint_one (G : GraphInput) (e : G.Edge) :
    G.endpoint e 1 = G.right e := by simp [endpoint]

theorem left_lt_right (G : GraphInput) (e : G.Edge) : G.left e < G.right e :=
  G.ordered _ (List.getElem_mem e.isLt)

theorem left_ne_right (G : GraphInput) (e : G.Edge) : G.left e ≠ G.right e :=
  (G.left_lt_right e).ne

theorem endpoint_injective (G : GraphInput) (e : G.Edge) :
    Function.Injective (G.endpoint e) := by
  intro s t h
  have hs : s = 0 ∨ s = 1 := by omega
  have ht : t = 0 ∨ t = 1 := by omega
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · rfl
  · exact False.elim (G.left_ne_right e (by simpa using h))
  · exact False.elim (G.left_ne_right e (by simpa using h.symm))
  · rfl

abbrev Incidence (G : GraphInput) (v : G.Vertex) :=
  {es : G.Edge × Fin 2 // G.endpoint es.1 es.2 = v}

def incidenceEquiv (G : GraphInput) :
    (Σ v : G.Vertex, G.Incidence v) ≃ G.Edge × Fin 2 :=
  Equiv.sigmaFiberEquiv (fun es : G.Edge × Fin 2 => G.endpoint es.1 es.2)

def degree (G : GraphInput) (v : G.Vertex) : ℕ :=
  Fintype.card (G.Incidence v)

theorem sum_degree (G : GraphInput) :
    (∑ v : G.Vertex, G.degree v) = 2 * G.edges.length := by
  have h := Fintype.card_congr (G.incidenceEquiv)
  simpa [degree, Fintype.card_sigma, Fintype.card_prod, Nat.mul_comm] using h

abbrev IncidencePosition (G : GraphInput) (R : ℕ) (v : G.Vertex) :=
  G.Incidence v × Fin R

abbrev JobCopy (G : GraphInput) (R d : ℕ) (v : G.Vertex) :=
  G.IncidencePosition R v × Fin d

theorem card_jobCopy (G : GraphInput) (R d : ℕ) (v : G.Vertex) :
    Fintype.card (G.JobCopy R d v) = d * R * G.degree v := by
  simp [JobCopy, IncidencePosition, degree, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]

theorem sum_card_jobCopy (G : GraphInput) (R d : ℕ) :
    (∑ v : G.Vertex, Fintype.card (G.JobCopy R d v)) =
      2 * d * G.edges.length * R := by
  simp_rw [card_jobCopy]
  rw [← Finset.mul_sum, sum_degree]
  ac_rfl

end GraphInput

end BinPackingGap

end

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

def iterate {α : Type} (step : α → α) (p : Nat × α) : α := step^[p.1] p.2

end BinPackingGap.MachineBoundedIteration

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

namespace Instance

noncomputable def ofFintype {ι : Type*} [Fintype ι]
    (s : ι → ℚ) (hpos : ∀ i, 0 < s i) (hle : ∀ i, s i ≤ 1) : Instance where
  n := Fintype.card ι
  size i := s ((Fintype.equivFin ι).symm i)
  size_pos _ := hpos _
  size_le_one _ := hle _

end Instance

namespace RawPacking

def addFraction (x y : ℕ × ℕ) : ℕ × ℕ :=
  (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

theorem addFraction_den_pos (x y : ℕ × ℕ) (hx : 0 < x.2) (hy : 0 < y.2) :
    0 < (addFraction x y).2 := Nat.mul_pos hx hy

end RawPacking

end BinPackingGap

namespace BinPackingGap.FractionWidth

theorem size_mono {a b : ℕ} (h : a ≤ b) : a.size ≤ b.size := by
  apply Nat.size_le.mpr
  exact lt_of_le_of_lt h (Nat.size_le.mp (le_refl b.size))

theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ a.size := Nat.size_le.mp (le_refl a.size)
  have hb : b < 2 ^ b.size := Nat.size_le.mp (le_refl b.size)
  calc
    a * b ≤ a * 2 ^ b.size := Nat.mul_le_mul_left a (Nat.le_of_lt hb)
    _ < 2 ^ a.size * 2 ^ b.size :=
      mul_lt_mul_of_pos_right ha (pow_pos (by decide) _)
    _ = 2 ^ (a.size + b.size) := (pow_add 2 a.size b.size).symm

theorem size_add_le {a b H : ℕ} (ha : a.size ≤ H) (hb : b.size ≤ H) :
    (a + b).size ≤ H + 1 := by
  apply Nat.size_le.mpr
  have h := Nat.add_lt_add (Nat.size_le.mp ha) (Nat.size_le.mp hb)
  simpa only [pow_succ, Nat.mul_two] using h

theorem addFraction_left_product_size_le {x q : ℕ × ℕ} (hx : x.1 ≤ x.2) :
    (x.1 * q.2).size ≤ x.2.size + q.2.size := by
  exact (size_mono (Nat.mul_le_mul_right q.2 hx)).trans (size_mul_le x.2 q.2)

theorem addFraction_right_product_size_le {x q : ℕ × ℕ} (hq : q.1 ≤ q.2) :
    (q.1 * x.2).size ≤ x.2.size + q.2.size := by
  have h := (size_mono (Nat.mul_le_mul_right x.2 hq)).trans
    (size_mul_le q.2 x.2)
  simpa only [Nat.add_comm] using h

theorem addFraction_num_size_le {x q : ℕ × ℕ}
    (hx : x.1 ≤ x.2) (hq : q.1 ≤ q.2) :
    (RawPacking.addFraction x q).1.size ≤ x.2.size + q.2.size + 1 := by
  exact size_add_le (addFraction_left_product_size_le hx)
    (addFraction_right_product_size_le hq)

theorem addFraction_den_size_le (x q : ℕ × ℕ) :
    (RawPacking.addFraction x q).2.size ≤ x.2.size + q.2.size :=
  size_mul_le x.2 q.2

theorem addFraction_overflow {x q : ℕ × ℕ}
    (hx : x.2 < x.1) (hq : 0 < q.2) :
    (RawPacking.addFraction x q).2 < (RawPacking.addFraction x q).1 := by
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hx hq)
    (Nat.le_add_right (x.1 * q.2) (q.1 * x.2))

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

namespace BinPackingGap

namespace GraphInput

def endpointPairs (G : GraphInput) : List (Nat × Nat) :=
  G.edges.map (fun edge => (edge.1.val, edge.2.val))

@[simp] theorem endpointPairs_length (G : GraphInput) :
    G.endpointPairs.length = G.edges.length := by
  simp [endpointPairs]

end GraphInput

structure GraphReductionInput where
  graph : GraphInput
  k : Nat
  k_le : k ≤ graph.n
  nonempty : graph.edges ≠ []

end BinPackingGap

namespace BinPackingGap.GraphTallyMachine

open Turing
open BinPackingGap.BinaryEncoding
open BinPackingGames.Foundations.Complexity

inductive Slot
  | header
  | vertex
  | edgeFirst
  | edgeSecond
  deriving DecidableEq

end BinPackingGap.GraphTallyMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitializeEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionQuery

def Agrees (fixed : List (Option Nat)) (assignments : List Nat) : Prop :=
  fixed.length = assignments.length ∧
    ∀ (i j : Nat), fixed[i]? = some (some j) → assignments[i]? = some j

@[simp] theorem agrees_nil_left (assignments : List Nat) :
    Agrees [] assignments ↔ assignments = [] := by
  cases assignments with
  | nil => simp [Agrees]
  | cons head tail => simp [Agrees]

@[simp] theorem agrees_nil_right (fixed : List (Option Nat)) :
    Agrees fixed [] ↔ fixed = [] := by
  cases fixed with
  | nil => simp [Agrees]
  | cons head tail => simp [Agrees]

theorem agrees_cons (entry : Option Nat) (fixed : List (Option Nat))
    (label : Nat) (assignments : List Nat) :
    Agrees (entry :: fixed) (label :: assignments) ↔
      (entry = none ∨ entry = some label) ∧ Agrees fixed assignments := by
  constructor
  · rintro ⟨lengths, agrees⟩
    refine ⟨?_, Nat.succ.inj lengths, ?_⟩
    · cases entry with
      | none => exact Or.inl rfl
      | some value =>
          right
          have equal : label = value := by simpa using agrees 0 value rfl
          exact congrArg some equal.symm
    · intro i j fixedAt
      simpa using agrees (i + 1) j (by simpa using fixedAt)
  · rintro ⟨head, lengths, tail⟩
    refine ⟨congrArg Nat.succ lengths, ?_⟩
    intro i j fixedAt
    cases i with
    | zero =>
        have entryAt : entry = some j := by simpa using fixedAt
        rcases head with head | head
        · rw [head] at entryAt
          cases entryAt
        · have equal : label = j := Option.some.inj (head.symm.trans entryAt)
          simpa using congrArg some equal
    | succ i =>
        simpa using tail i j (by simpa using fixedAt)

@[simp] theorem agrees_replicate_none (n : Nat) (assignments : List Nat) :
    Agrees (List.replicate n none) assignments ↔ n = assignments.length := by
  induction n generalizing assignments with
  | zero => simp [eq_comm]
  | succ n ih =>
      cases assignments with
      | nil => simp
      | cons label assignments =>
          simp [List.replicate_succ, agrees_cons, ih]

@[simp] theorem agrees_map_some (fixed assignments : List Nat) :
    Agrees (fixed.map some) assignments ↔ fixed = assignments := by
  induction fixed generalizing assignments with
  | nil => simp [eq_comm]
  | cons label fixed ih =>
      cases assignments with
      | nil => simp
      | cons other assignments =>
          simp [agrees_cons, ih]

end BinPackingGap.ExtensionQuery

namespace BinPackingGap.SearchSemantics

open ExtensionQuery

def labels (fixed : List (Option Nat)) : List Nat :=
  fixed.map (fun x => x.getD 0)

inductive Phase where
  | find | fill | done | invalid
  deriving DecidableEq, Repr

end BinPackingGap.SearchSemantics

namespace BinPackingGap.ExtensionCertificate

open ExtensionQuery

def agreesBool : List (Option Nat) → List Nat → Bool
  | [], [] => true
  | none :: fixed, _ :: assignments => agreesBool fixed assignments
  | some label :: fixed, value :: assignments =>
      decide (label = value) && agreesBool fixed assignments
  | _, _ => false

@[simp] theorem agreesBool_eq_true_iff (fixed : List (Option Nat))
    (assignments : List Nat) : agreesBool fixed assignments = true ↔ Agrees fixed assignments := by
  induction fixed generalizing assignments with
  | nil => cases assignments <;> simp [agreesBool]
  | cons entry fixed ih =>
      cases assignments with
      | nil => simp [agreesBool]
      | cons value assignments =>
          cases entry <;> simp [agreesBool, agrees_cons, ih]

end BinPackingGap.ExtensionCertificate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialItemsMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionMachineRegisters

open Turing.TM2
open BinPackingGames.Foundations.Complexity

structure Lens (Big Small : Type) where
  get : Big → Small
  set : Big → Small → Big
  get_set : ∀ s v, get (set s v) = v
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s v w, set (set s v) w = set s w

namespace Lens

variable {Big Small Middle : Type}

def identity (State : Type) : Lens State State where
  get := id
  set := fun _ v => v
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def ofEquiv (e : Small ≃ Big) : Lens Big Small where
  get := e.symm
  set := fun _ v => e v
  get_set _ v := e.symm_apply_apply v
  set_get s := e.apply_symm_apply s
  set_set _ _ _ := rfl

end Lens

variable {K Label Big Small : Type} {Γ : K → Type}

def statement (lens : Lens Big Small) : Stmt Γ Label Small → Stmt Γ Label Big
  | .push k f next => .push k (fun s => f (lens.get s)) (statement lens next)
  | .peek k f next => .peek k (fun s symbol => lens.set s (f (lens.get s) symbol))
      (statement lens next)
  | .pop k f next => .pop k (fun s symbol => lens.set s (f (lens.get s) symbol))
      (statement lens next)
  | .load f next => .load (fun s => lens.set s (f (lens.get s))) (statement lens next)
  | .branch f yes no => .branch (fun s => f (lens.get s))
      (statement lens yes) (statement lens no)
  | .goto f => .goto (fun s => f (lens.get s))
  | .halt => .halt

@[simp] theorem statement_identity (q : Stmt Γ Label Small) :
    statement (Lens.identity Small) q = q := by
  induction q <;> simp_all [statement, Lens.identity]

@[simp] theorem statement_ofEquiv_symm (e : Small ≃ Big) (q : Stmt Γ Label Big) :
    statement (Lens.ofEquiv e) (statement (Lens.ofEquiv e.symm) q) = q := by
  induction q <;> simp_all [statement, Lens.ofEquiv]

def equivConfiguration (e : Small ≃ Big) (c : Cfg Γ Label Small) : Cfg Γ Label Big :=
  ⟨c.l, e c.var, c.stk⟩

def configuration (lens : Lens Big Small) (base : Big) (c : Cfg Γ Label Small) :
    Cfg Γ Label Big := ⟨c.l, lens.set base c.var, c.stk⟩

@[simp] theorem configuration_ofEquiv (e : Small ≃ Big) (base : Big)
    (c : Cfg Γ Label Small) :
    configuration (Lens.ofEquiv e) base c = equivConfiguration e c := rfl

@[simp] theorem equivConfiguration_symm (e : Small ≃ Big) (c : Cfg Γ Label Big) :
    equivConfiguration e (equivConfiguration e.symm c) = c := by
  cases c
  simp [equivConfiguration]

variable [DecidableEq K]

theorem stepAux_transport (lens : Lens Big Small) (base : Big)
    (q : Stmt Γ Label Small) (state : Small) (tapes : ∀ k, List (Γ k)) :
    stepAux (statement lens q) (lens.set base state) tapes =
      configuration lens base (stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
      simp only [statement, stepAux, lens.get_set]
      exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [statement, stepAux, lens.get_set, lens.set_set] using
        ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simpa only [statement, stepAux, lens.get_set, lens.set_set] using
        ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [statement, stepAux, lens.get_set, lens.set_set] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases test : f state with
      | false =>
          simpa only [statement, stepAux, lens.get_set, test, Bool.cond_false] using
            ihNo state tapes
      | true =>
          simpa only [statement, stepAux, lens.get_set, test, Bool.cond_true] using
            ihYes state tapes
  | goto f => simp [statement, stepAux, lens.get_set, configuration]
  | halt => rfl

def program (lens : Lens Big Small) (source : Label → Stmt Γ Label Small) :
    Label → Stmt Γ Label Big := fun label => statement lens (source label)

omit [DecidableEq K] in
@[simp] theorem program_identity (source : Label → Stmt Γ Label Small) :
    program (Lens.identity Small) source = source := by
  funext label
  exact statement_identity (source label)

omit [DecidableEq K] in
@[simp] theorem program_ofEquiv_symm (e : Small ≃ Big)
    (target : Label → Stmt Γ Label Big) :
    program (Lens.ofEquiv e) (program (Lens.ofEquiv e.symm) target) = target := by
  funext label
  exact statement_ofEquiv_symm e (target label)

theorem step_transport (lens : Lens Big Small) (base : Big)
    (source : Label → Stmt Γ Label Small) (c : Cfg Γ Label Small) :
    step (program lens source) (configuration lens base c) =
      (step source c).map (configuration lens base) := by
  cases c with
  | mk label state tapes =>
      cases label with
      | none => rfl
      | some label =>
          change some (stepAux (statement lens (source label)) (lens.set base state) tapes) = _
          rw [stepAux_transport]
          rfl

end BinPackingGap.ExtensionMachineRegisters

namespace BinPackingGap.ExtensionMachinePlacement

open Turing BinPackingGames.Foundations.Complexity
open ExtensionMachineRegisters (Lens)

variable {K K' Label Label' Small Big : Type}

def tapes (view : K' → Option K) (source : K → List Bool)
    (extra : K' → List Bool) : K' → List Bool :=
  fun j => match view j with
    | some k => source k
    | none => extra j

def label (labels : Label → Label') (exit : Option Label') : Option Label → Option Label'
  | some l => some (labels l)
  | none => exit

def configuration (view : K' → Option K) (labels : Label → Label')
    (exit : Option Label') (lens : Lens Big Small) (base : Big)
    (extra : K' → List Bool) (c : TM2.Cfg (fun _ : K => Bool) Label Small) :
    TM2.Cfg (fun _ : K' => Bool) Label' Big :=
  ⟨label labels exit c.l, lens.set base c.var, tapes view c.stk extra⟩

def statement (tape : K → K') (labels : Label → Label') (exit : Option Label')
    (lens : Lens Big Small) :
    TM2.Stmt (fun _ : K => Bool) Label Small → TM2.Stmt (fun _ : K' => Bool) Label' Big
  | .push k f next => .push (tape k) (fun s => f (lens.get s))
      (statement tape labels exit lens next)
  | .peek k f next => .peek (tape k) (fun s bit => lens.set s (f (lens.get s) bit))
      (statement tape labels exit lens next)
  | .pop k f next => .pop (tape k) (fun s bit => lens.set s (f (lens.get s) bit))
      (statement tape labels exit lens next)
  | .load f next => .load (fun s => lens.set s (f (lens.get s)))
      (statement tape labels exit lens next)
  | .branch f yes no => .branch (fun s => f (lens.get s))
      (statement tape labels exit lens yes) (statement tape labels exit lens no)
  | .goto f => .goto (fun s => labels (f (lens.get s)))
  | .halt => match exit with
    | some l => .goto (fun _ => l)
    | none => .halt

@[simp] theorem tapes_apply (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (source : K → List Bool) (extra : K' → List Bool) (k : K) :
    tapes view source extra (tape k) = source k := by
  simp only [tapes, left]

@[simp] theorem tapes_unmapped (view : K' → Option K)
    (source : K → List Bool) (extra : K' → List Bool) (j : K')
    (unmapped : view j = none) : tapes view source extra j = extra j := by
  simp only [tapes, unmapped]

theorem tapes_restrict (tape : K → K') (view : K' → Option K)
    (right : ∀ j k, view j = some k → tape k = j) (base : K' → List Bool) :
    tapes view (fun k => base (tape k)) base = base := by
  funext j
  cases found : view j with
  | none => simp [tapes, found]
  | some k => simp [tapes, found, right j k found]

variable [DecidableEq K] [DecidableEq K']

theorem tapes_update (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (source : K → List Bool) (extra : K' → List Bool) (k : K) (word : List Bool) :
    tapes view (Function.update source k word) extra =
      Function.update (tapes view source extra) (tape k) word := by
  funext j
  by_cases same : j = tape k
  · subst j
    simp [tapes, left]
  · cases found : view j with
    | none => simp [tapes, found, same]
    | some i =>
      have distinct : i ≠ k := by
        intro equal
        subst i
        exact same (right j k found).symm
      simp [tapes, found, same, distinct]

theorem stepAux_simulation (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label → Label') (exit : Option Label') (lens : Lens Big Small)
    (base : Big) (extra : K' → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Label Small)
    (state : Small) (source : K → List Bool) :
    TM2.stepAux (statement tape labels exit lens q) (lens.set base state)
        (tapes view source extra) =
      configuration view labels exit lens base extra (TM2.stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
      simp only [statement, TM2.stepAux, lens.get_set, tapes_apply tape view left]
      rw [← tapes_update tape view left right]
      exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
      simpa only [statement, TM2.stepAux, lens.get_set, lens.set_set,
        tapes_apply tape view left] using ih (f state (source k).head?) source
  | pop k f next ih =>
      simp only [statement, TM2.stepAux, lens.get_set, lens.set_set,
        tapes_apply tape view left]
      rw [← tapes_update tape view left right]
      exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih =>
      simpa only [statement, TM2.stepAux, lens.get_set, lens.set_set] using ih (f state) source
  | branch f yes no ihYes ihNo =>
      cases test : f state with
      | false =>
          simpa only [statement, TM2.stepAux, lens.get_set, test, Bool.cond_false] using
            ihNo state source
      | true =>
          simpa only [statement, TM2.stepAux, lens.get_set, test, Bool.cond_true] using
            ihYes state source
  | goto f => simp [statement, TM2.stepAux, lens.get_set, configuration, label]
  | halt => cases exit <;> rfl

theorem step_simulation (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label → Label') (exit : Option Label') (lens : Lens Big Small)
    (base : Big) (extra : K' → List Bool)
    (source : Label → TM2.Stmt (fun _ : K => Bool) Label Small)
    (target : Label' → TM2.Stmt (fun _ : K' => Bool) Label' Big)
    (atLabels : ∀ l, target (labels l) = statement tape labels exit lens (source l))
    (a b : TM2.Cfg (fun _ : K => Bool) Label Small)
    (run : TM2.step source a = some b) :
    TM2.step target (configuration view labels exit lens base extra a) =
      some (configuration view labels exit lens base extra b) := by
  cases a with
  | mk current state sourceTapes =>
      cases current with
      | none => simp [TM2.step] at run
      | some current =>
          have finish : TM2.stepAux (source current) state sourceTapes = b :=
            Option.some.inj run
          rw [← finish]
          change some (TM2.stepAux (target (labels current)) (lens.set base state)
            (tapes view sourceTapes extra)) = _
          rw [atLabels, stepAux_simulation tape view left right]

end BinPackingGap.ExtensionMachinePlacement

namespace BinPackingGap.ExtensionNatMachine

open Turing
open BinPackingGames.Foundations.Complexity
abbrev Alphabet {K : Type} (_ : K) := Bool

inductive Label
  | scan | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .restore]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ A : Type} [DecidableEq K]

def resultTapes (slots : Fin 3 ↪ K) (base : K → List Bool) (n : Nat)
    (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (slots 0) suffix) (slots 1) (n.bits ++ base (slots 1))

end BinPackingGap.ExtensionNatMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPowerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.FiniteTapeProgram

section

open Turing BinPackingGames.Foundations.Complexity

variable (K S : Type)

structure Data where
  state : S
  tapes : K → List Bool

inductive Action where
  | done
  | push (tape : K) (symbol : S → Bool) (next : Action)
  | pop (tape : K) (save : S → Option Bool → S) (next : Action)
  | peek (tape : K) (save : S → Option Bool → S) (next : Action)
  | load (update : S → S) (next : Action)
  | branch (test : S → Bool) (yes no : Action)

variable {K S}

def Action.statement {Λ : Type} (exit : TM2.Stmt (fun _ : K => Bool) Λ S) :
    Action K S → TM2.Stmt (fun _ : K => Bool) Λ S
  | .done => exit
  | .push k f a => .push k f (a.statement exit)
  | .pop k f a => .pop k f (a.statement exit)
  | .peek k f a => .peek k f (a.statement exit)
  | .load f a => .load f (a.statement exit)
  | .branch f a b => .branch f (a.statement exit) (b.statement exit)

variable [DecidableEq K]

def Action.eval : Action K S → Data K S → Data K S
  | .done, d => d
  | .push k f a, d => a.eval ⟨d.state, Function.update d.tapes k (f d.state :: d.tapes k)⟩
  | .pop k f a, d => a.eval ⟨f d.state (d.tapes k).head?,
      Function.update d.tapes k (d.tapes k).tail⟩
  | .peek k f a, d => a.eval ⟨f d.state (d.tapes k).head?, d.tapes⟩
  | .load f a, d => a.eval ⟨f d.state, d.tapes⟩
  | .branch f a b, d => if f d.state then a.eval d else b.eval d

theorem Action.stepAux_statement {Λ : Type} (a : Action K S)
    (exit : TM2.Stmt (fun _ : K => Bool) Λ S) (d : Data K S) :
    TM2.stepAux (a.statement exit) d.state d.tapes =
      TM2.stepAux exit (a.eval d).state (a.eval d).tapes := by
  induction a generalizing d with
  | done => rfl
  | push k f a ih =>
      simpa only [Action.statement, Action.eval, TM2.stepAux] using
        ih ⟨d.state, Function.update d.tapes k (f d.state :: d.tapes k)⟩
  | pop k f a ih =>
      simpa only [Action.statement, Action.eval, TM2.stepAux] using
        ih ⟨f d.state (d.tapes k).head?, Function.update d.tapes k (d.tapes k).tail⟩
  | peek k f a ih =>
      simpa only [Action.statement, Action.eval, TM2.stepAux] using
        ih ⟨f d.state (d.tapes k).head?, d.tapes⟩
  | load f a ih =>
      simpa only [Action.statement, Action.eval, TM2.stepAux] using ih ⟨f d.state, d.tapes⟩
  | branch f a b iha ihb =>
      cases h : f d.state <;> simp [Action.statement, Action.eval, TM2.stepAux, h, iha, ihb]

inductive Code : Type 1 where
  | atom (action : Action K S)
  | routine (labels : Type) (finite : Fintype labels) (main : labels)
      (program : labels → TM2.Stmt (fun _ : K => Bool) labels S)
  | seq (first second : Code)
  | branch (test : S → Bool) (yes no : Code)
  | loop (guard : Action K S) (test : S → Bool) (body : Code)

@[reducible] def Code.Label : Code (K := K) (S := S) → Type
  | .atom _ => Unit
  | .routine labels _ _ _ => labels
  | .seq a b => a.Label ⊕ b.Label
  | .branch _ a b => Unit ⊕ (a.Label ⊕ b.Label)
  | .loop _ _ a => Unit ⊕ a.Label

instance Code.labelFintype : (c : Code (K := K) (S := S)) → Fintype c.Label
  | .atom _ => inferInstanceAs (Fintype Unit)
  | .routine _ finite _ _ => finite
  | .seq a b =>
      letI := labelFintype a
      letI := labelFintype b
      inferInstanceAs (Fintype (a.Label ⊕ b.Label))
  | .branch _ a b =>
      letI := labelFintype a
      letI := labelFintype b
      inferInstanceAs (Fintype (Unit ⊕ (a.Label ⊕ b.Label)))
  | .loop _ _ a =>
      letI := labelFintype a
      inferInstanceAs (Fintype (Unit ⊕ a.Label))

def Code.entry : (c : Code (K := K) (S := S)) → c.Label
  | .atom _ => ()
  | .routine _ _ main _ => main
  | .seq a _ => .inl a.entry
  | .branch _ _ _ => .inl ()
  | .loop _ _ _ => .inl ()

def jump {Λ : Type} (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ S :=
  match exit with
  | none => .halt
  | some label => .goto (fun _ => label)

@[simp] theorem stepAux_jump {Λ : Type} (exit : Option Λ) (d : Data K S) :
    TM2.stepAux (jump exit) d.state d.tapes = ⟨exit, d.state, d.tapes⟩ := by
  cases exit <;> rfl

end

open Turing BinPackingGames.Foundations.Complexity

end BinPackingGap.FiniteTapeProgram

namespace BinPackingGap.BooleanTapeCode

open Turing FiniteTapeProgram BinPackingGames.Foundations.Complexity

variable {K A : Type} [DecidableEq K]

abbrev State (A : Type) := (A × Unit) × Option Bool
abbrev Program (K A : Type) := Code (K := K) (S := State A)

def clean (a : A) : State A := ((a, ()), none)

inductive FrameLabel
  | scan | restore | emit (bit : Bool)
  deriving DecidableEq, Fintype

end BinPackingGap.BooleanTapeCode

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryToTallyMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.BinaryToTallyMachine

open BinPackingGames.Foundations.Complexity BinaryRegisterProgram FiniteTapeProgram

inductive Reg
  | source | counter | one | temporary
  deriving DecidableEq

instance instFintypeReg : Fintype Reg where
  elems := {.source, .counter, .one, .temporary}
  complete r := by cases r <;> simp

def initial (n : Nat) : Reg → Nat
  | .source => n
  | _ => 0

def running (n remaining : Nat) : Reg → Nat
  | .source => n
  | .counter => remaining
  | .one => 1
  | .temporary => 0

variable {K A : Type} [DecidableEq K]

theorem replicate_append_true (r : Nat) (suffix : List Bool) :
    List.replicate r true ++ true :: suffix = List.replicate (r + 1) true ++ suffix := by
  induction r with
  | zero => rfl
  | succ r ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (true :: ·) ih

def runtimeBound (n : Nat) : Nat := 40 * (n + 1) * (n.size + 1) ^ 2

end BinPackingGap.BinaryToTallyMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_FiniteHall
attribute [-instance] _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Finset

namespace BinPackingGap.FiniteHall

universe u v

namespace HallMarriageTheorem

variable {ι : Type u} {α : Type v} [DecidableEq α] {t : ι → Finset α}

section Fintype

variable [Fintype ι]

theorem hall_cond_of_erase {x : ι} (a : α)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t))
    (s' : Finset { x' : ι | x' ≠ x }) : #s' ≤ #(s'.biUnion fun x' => (t x').erase a) := by
  have := Classical.decEq ι
  specialize ha (s'.image fun z => z.1)
  rw [image_nonempty, Finset.card_image_of_injective s' Subtype.coe_injective] at ha
  by_cases! he : s'.Nonempty
  · have ha' : #s' < #(s'.biUnion fun x => t x) := by
      convert! ha he fun h => by simpa [← h] using mem_univ x using 2
      all_goals try with_reducible_and_instances rfl
      ext x
      simp only [mem_image, mem_biUnion, SetCoe.exists, exists_and_right,
        exists_eq_right]
    rw [← erase_biUnion]
    by_cases hb : a ∈ s'.biUnion fun x => t x
    · rw [card_erase_of_mem hb]
      exact Nat.le_sub_one_of_lt ha'
    · rw [erase_eq_of_notMem hb]
      exact Nat.le_of_lt ha'
  · subst s'
    simp

theorem hall_hard_inductive_step_A {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (hn.symm ▸ Nat.succ_pos _)
  have := Classical.decEq ι

  let x := Classical.arbitrary ι
  have tx_ne : (t x).Nonempty := by
    rw [← Finset.card_pos]
    calc
      0 < 1 := Nat.one_pos
      _ ≤ #(.biUnion {x} t) := ht {x}
      _ = (t x).card := by rw [Finset.singleton_biUnion]
  choose y hy using tx_ne

  let ι' := { x' : ι | x' ≠ x }
  let t' : ι' → Finset α := fun x' => (t x').erase y
  have card_ι' : Fintype.card ι' = n :=
    calc
      Fintype.card ι' = Fintype.card ι - 1 := Set.card_ne_eq _
      _ = n := by rw [hn, Nat.add_succ_sub_one, add_zero]
  rcases ih t' card_ι'.le (hall_cond_of_erase y ha) with ⟨f', hfinj, hfr⟩

  refine ⟨fun z => if h : z = x then y else f' ⟨z, h⟩, ?_, ?_⟩
  · rintro z₁ z₂
    have key : ∀ {x}, y ≠ f' x := by
      intro x h
      simpa [t', ← h] using hfr x
    by_cases h₁ : z₁ = x <;> by_cases h₂ : z₂ = x <;>
      simp [h₁, h₂, hfinj.eq_iff, key, key.symm]
  · intro z
    simp only
    split_ifs with hz
    · rwa [hz]
    · specialize hfr ⟨z, hz⟩
      rw [mem_erase] at hfr
      exact hfr.2

theorem hall_cond_of_restrict {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) (s' : Finset (s : Set ι)) :
    #s' ≤ #(s'.biUnion fun a' => t a') := by
  classical
    rw [← card_image_of_injective s' Subtype.coe_injective]
    convert! ht (s'.image fun z => z.1) using 1
    all_goals try with_reducible_and_instances rfl
    apply congr_arg
    ext y
    simp

theorem hall_cond_of_compl {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (hus : #s = #(s.biUnion t)) (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (s' : Finset (sᶜ : Set ι)) : #s' ≤ #(s'.biUnion fun x' => t x' \ s.biUnion t) := by
  have := Classical.decEq ι
  have disj : Disjoint s (s'.image fun z => z.1) := by
    simp only [disjoint_left, not_exists, mem_image, SetCoe.exists, exists_and_right,
      exists_eq_right]
    intro x hx hc _
    exact absurd hx hc
  have : #s' = #(s ∪ s'.image fun z => z.1) - #s := by
    simp [disj, card_image_of_injective _ Subtype.coe_injective, Nat.add_sub_cancel_left]
  rw [this, hus]
  refine (Nat.sub_le_sub_right (ht _) _).trans ?_
  rw [← card_sdiff_of_subset]
  · gcongr
    intro t
    simp only [mem_biUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union,
      exists_imp]
    rintro x (hx | ⟨x', hx', rfl⟩) rat hs
    · exact False.elim <| (hs x) <| And.intro hx rat
    · use x', hx', rat, hs
  · apply biUnion_subset_biUnion_of_subset_left
    apply subset_union_left

theorem hall_hard_inductive_step_B {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (s : Finset ι) (hs : s.Nonempty) (hns : s ≠ univ) (hus : #s = #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  have := Classical.decEq ι

  rw [Nat.add_one] at hn
  have card_ι'_le : Fintype.card s ≤ n := by
    apply Nat.le_of_lt_succ
    calc
      Fintype.card s = #s := Fintype.card_coe _
      _ < Fintype.card ι := (card_lt_iff_ne_univ _).mpr hns
      _ = n.succ := hn
  let t' : s → Finset α := fun x' => t x'
  rcases ih t' card_ι'_le (hall_cond_of_restrict ht) with ⟨f', hf', hsf'⟩

  set ι'' := (s : Set ι)ᶜ
  let t'' : ι'' → Finset α := fun a'' => t a'' \ s.biUnion t
  have card_ι''_le : Fintype.card ι'' ≤ n := by
    simp_rw [ι'', ← Nat.lt_succ_iff, ← hn, ← Finset.coe_compl, coe_sort_coe]
    rwa [Fintype.card_coe, card_compl_lt_iff_nonempty]
  rcases ih t'' card_ι''_le (hall_cond_of_compl hus ht) with ⟨f'', hf'', hsf''⟩

  have f''_notMem_biUnion : ∀ (x'') (hx'' : x'' ∉ s), f'' ⟨x'', hx''⟩ ∉ s.biUnion t := by
    intro x'' hx''
    have h := hsf'' ⟨x'', hx''⟩
    rw [mem_sdiff] at h
    exact h.2
  have im_disj :
      ∀ (x' x'' : ι) (hx' : x' ∈ s) (hx'' : x'' ∉ s), f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩ := by
    grind
  refine ⟨fun x => if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, h⟩, ?_, ?_⟩
  · refine hf'.dite _ hf'' (@fun x x' => im_disj x x' _ _)
  · intro x
    simp only
    split_ifs with h
    · exact hsf' ⟨x, h⟩
    · exact sdiff_subset (hsf'' ⟨x, h⟩)

end Fintype

variable [Finite ι]

theorem hall_hard_inductive (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  cases nonempty_fintype ι
  generalize hn : Fintype.card ι = m
  induction m using Nat.strongRecOn generalizing ι with | ind n ih => _
  rcases n with (_ | n)
  · rw [Fintype.card_eq_zero_iff] at hn
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  · have ih' : ∀ (ι' : Type u) [Fintype ι'] (t' : ι' → Finset α), Fintype.card ι' ≤ n →
        (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
        ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x := by
      intro ι' _ _ hι' ht'
      exact ih _ (Nat.lt_succ_of_le hι') ht' _ rfl
    by_cases! h : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)
    · refine hall_hard_inductive_step_A hn ht (@fun ι' => ih' ι') h
    · rcases h with ⟨s, sne, snu, sle⟩
      exact hall_hard_inductive_step_B hn ht (@fun ι' => ih' ι')
        s sne snu (Nat.le_antisymm (ht _) sle)

end HallMarriageTheorem

theorem all_card_le_biUnion_card_iff_existsInjective {ι α : Type*} [Finite ι]
    [DecidableEq α] (t : ι → Finset α) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  constructor
  · exact HallMarriageTheorem.hall_hard_inductive
  · rintro ⟨f, hf₁, hf₂⟩ s
    rw [← card_image_of_injective s hf₁]
    apply card_le_card
    intro
    rw [mem_image, mem_biUnion]
    rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hf₂ x⟩

end BinPackingGap.FiniteHall

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalar
attribute [-instance] _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

inductive Role
  | x
  | anchor
  | «global»
  | «local»
  | flag
  deriving DecidableEq

instance instFintypeRole : Fintype Role where
  elems := {.x, .anchor, .«global», .«local», .flag}
  complete := by intro r; cases r <;> simp

inductive Subclass
  | tp
  | tm
  | s
  | z
  | y
  | up
  | um
  | w
  | dm
  | dg
  | ft
  | fm
  | fg
  deriving DecidableEq

instance instFintypeSubclass : Fintype Subclass where
  elems := {.tp, .tm, .s, .z, .y, .up, .um, .w, .dm, .dg, .ft, .fm, .fg}
  complete := by intro subclass; cases subclass <;> simp

inductive Pattern
  | plusTree
  | minusTree
  | mainJob
  | edgeJob
  deriving DecidableEq

instance instFintypePattern : Fintype Pattern where
  elems := {.plusTree, .minusTree, .mainJob, .edgeJob}
  complete := by intro p; cases p <;> simp

namespace Role

def index : Role → Fin 5
  | .x => 0
  | .anchor => 1
  | .«global» => 2
  | .«local» => 3
  | .flag => 4

theorem sum_univ {A : Type*} [AddCommMonoid A] (f : Role → A) :
    (∑ r, f r) = f .x + f .anchor + f .«global» + f .«local» + f .flag := by
  have h : (Finset.univ : Finset Role) =
      {.x, .anchor, .«global», .«local», .flag} := by decide
  rw [h]
  simp [add_assoc]

end Role

def Subclass.role : Subclass → Role
  | .tp | .tm | .s => .x
  | .z | .y => .anchor
  | .up | .um | .w => .«global»
  | .dm | .dg => .«local»
  | .ft | .fm | .fg => .flag

@[simp] theorem role_eq_x_iff (c : Subclass) :
    c.role = Role.x ↔ c = .tp ∨ c = .tm ∨ c = .s := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_anchor_iff (c : Subclass) :
    c.role = Role.anchor ↔ c = .z ∨ c = .y := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_global_iff (c : Subclass) :
    c.role = Role.«global» ↔ c = .up ∨ c = .um ∨ c = .w := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_local_iff (c : Subclass) :
    c.role = Role.«local» ↔ c = .dm ∨ c = .dg := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_flag_iff (c : Subclass) :
    c.role = Role.flag ↔ c = .ft ∨ c = .fm ∨ c = .fg := by
  cases c <;> simp [Subclass.role]

def patternSubclass : Pattern → Role → Subclass
  | .plusTree, .x => .tp
  | .plusTree, .anchor => .z
  | .plusTree, .«global» => .up
  | .plusTree, .«local» => .dm
  | .plusTree, .flag => .ft
  | .minusTree, .x => .tm
  | .minusTree, .anchor => .z
  | .minusTree, .«global» => .um
  | .minusTree, .«local» => .dm
  | .minusTree, .flag => .ft
  | .mainJob, .x => .s
  | .mainJob, .anchor => .z
  | .mainJob, .«global» => .up
  | .mainJob, .«local» => .dm
  | .mainJob, .flag => .fm
  | .edgeJob, .x => .s
  | .edgeJob, .anchor => .y
  | .edgeJob, .«global» => .w
  | .edgeJob, .«local» => .dg
  | .edgeJob, .flag => .fg

@[simp] theorem patternSubclass_role (p : Pattern) (r : Role) :
    (patternSubclass p r).role = r := by
  cases p <;> cases r <;> rfl

@[simp] theorem card_role : Fintype.card Role = 5 := by decide

@[simp] theorem card_subclass : Fintype.card Subclass = 13 := by decide

@[simp] theorem card_pattern : Fintype.card Pattern = 4 := by decide

def IsPatternTuple (t : Fin 5 → Subclass) : Prop :=
  ∃ p : Pattern, ∃ e : Fin 5 ≃ Role, ∀ i, t i = patternSubclass p (e i)

end

section

def labelWeight {n : ℕ} (v : Fin n) : ℤ := 3 ^ (v.val + 1)

theorem labelWeight_pos {n : ℕ} (v : Fin n) : 0 < labelWeight v := by
  exact pow_pos (by norm_num : (0 : ℤ) < 3) _

theorem labelWeight_le {n : ℕ} (v : Fin n) : labelWeight v ≤ (3 : ℤ) ^ n := by
  unfold labelWeight
  exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3)
    (Nat.succ_le_of_lt v.isLt)

open scoped BigOperators

def subclassIndicator (a b : Subclass) : ℤ := if a = b then 1 else 0

def primaryCoeff (j : Fin 10) (subclass : Subclass) : ℤ :=
  match j.val with
  | 0 => 5 * (if subclass.role = .x then 1 else 0) - 1
  | 1 => 5 * (if subclass.role = .anchor then 1 else 0) - 1
  | 2 => 5 * (if subclass.role = .«global» then 1 else 0) - 1
  | 3 => 5 * (if subclass.role = .«local» then 1 else 0) - 1
  | 4 => 5 * (if subclass.role = .flag then 1 else 0) - 1
  | 5 => subclassIndicator subclass .tp + subclassIndicator subclass .tm - subclassIndicator subclass .ft
  | 6 => subclassIndicator subclass .z - subclassIndicator subclass .ft - subclassIndicator subclass .fm
  | 7 => subclassIndicator subclass .up + subclassIndicator subclass .um -
      subclassIndicator subclass .ft - subclassIndicator subclass .fm
  | 8 => subclassIndicator subclass .dm - subclassIndicator subclass .ft - subclassIndicator subclass .fm
  | 9 => subclassIndicator subclass .tm - subclassIndicator subclass .um
  | _ => 0

def primaryScore (subclass : Subclass) : ℤ :=
  ∑ j : Fin 10, (100 : ℤ) ^ j.val * primaryCoeff j subclass

def primaryBound : ℕ := 100 ^ 11

def roleCoeffIndex (r : Role) : Fin 10 :=
  ⟨r.index.val, lt_trans r.index.isLt (by decide)⟩

theorem primaryCoeff_role (r : Role) (subclass : Subclass) :
    primaryCoeff (roleCoeffIndex r) subclass = 5 * (if subclass.role = r then 1 else 0) - 1 := by
  cases r <;> cases subclass <;> decide

theorem primaryCoeff_abs_le (j : Fin 10) (subclass : Subclass) :
    |primaryCoeff j subclass| ≤ 4 := by
  fin_cases j <;> cases subclass <;> decide

theorem primaryScore_abs_lt (subclass : Subclass) :
    |primaryScore subclass| < (primaryBound : ℤ) := by
  cases subclass <;>
    norm_num [primaryScore, primaryCoeff, subclassIndicator, Subclass.role,
      primaryBound, Fin.sum_univ_succ] <;> decide

theorem sum_primaryScore_eq {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryScore (t i)) =
      ∑ j : Fin 10, (100 : ℤ) ^ j.val * (∑ i, primaryCoeff j (t i)) := by
  simp only [primaryScore, Finset.mul_sum]
  exact Finset.sum_comm

def roleCount {I : Type*} [Fintype I] (t : I → Subclass) (r : Role) : ℤ :=
  ∑ i, if (t i).role = r then 1 else 0

def subclassCount {I : Type*} [Fintype I] (t : I → Subclass) (subclass : Subclass) : ℤ :=
  ∑ i, subclassIndicator (t i) subclass

theorem sum_primaryCoeff_role {I : Type*} [Fintype I]
    (t : I → Subclass) (r : Role) :
    (∑ i, primaryCoeff (roleCoeffIndex r) (t i)) =
      5 * roleCount t r - (Fintype.card I : ℤ) := by
  simp only [primaryCoeff_role, Finset.sum_sub_distrib, ← Finset.mul_sum,
    roleCount, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem sum_primaryCoeff_five {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 5 (t i)) =
      subclassCount t .tp + subclassCount t .tm - subclassCount t .ft := by
  simp [primaryCoeff, subclassCount, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_six {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 6 (t i)) =
      subclassCount t .z - subclassCount t .ft - subclassCount t .fm := by
  simp [primaryCoeff, subclassCount, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_seven {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 7 (t i)) =
      subclassCount t .up + subclassCount t .um -
        subclassCount t .ft - subclassCount t .fm := by
  simp [primaryCoeff, subclassCount, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_eight {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 8 (t i)) =
      subclassCount t .dm - subclassCount t .ft - subclassCount t .fm := by
  simp [primaryCoeff, subclassCount, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_nine {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 9 (t i)) = subclassCount t .tm - subclassCount t .um := by
  simp [primaryCoeff, subclassCount, Finset.sum_sub_distrib]

theorem radix100_eq_zero_iff {n : ℕ} (a : Fin n → ℤ)
    (ha : ∀ i, |a i| < 100) :
    (∑ i, (100 : ℤ) ^ i.val * a i) = 0 ↔ ∀ i, a i = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      constructor
      · intro hs
        have hsplit : a 0 + 100 * (∑ i : Fin n, (100 : ℤ) ^ i.val * a i.succ) = 0 := by
          calc
            a 0 + 100 * (∑ i : Fin n, (100 : ℤ) ^ i.val * a i.succ) =
                ∑ i : Fin (n + 1), (100 : ℤ) ^ i.val * a i := by
              rw [Fin.sum_univ_succ]
              simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [pow_succ]
              ring
            _ = 0 := hs
        have hfirst := abs_lt.mp (ha 0)
        have hz : a 0 = 0 := by omega
        have htail : (∑ i : Fin n, (100 : ℤ) ^ i.val * a i.succ) = 0 := by omega
        have hrest := (ih (fun i => a i.succ) (fun i => ha i.succ)).mp htail
        intro i
        exact Fin.cases hz (fun k => hrest k) i
      · intro hz
        simp [hz]

theorem primaryCoeff_total_abs_lt (t : Fin 5 → Subclass) (j : Fin 10) :
    |∑ i, primaryCoeff j (t i)| < 100 := by
  calc
    |∑ i, primaryCoeff j (t i)| ≤ ∑ i, |primaryCoeff j (t i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, (4 : ℤ) :=
      Finset.sum_le_sum (fun i _ => primaryCoeff_abs_le j (t i))
    _ < 100 := by norm_num

theorem sum_primaryScore_eq_zero_iff_coefficients (t : Fin 5 → Subclass) :
    (∑ i, primaryScore (t i)) = 0 ↔ ∀ j : Fin 10, (∑ i, primaryCoeff j (t i)) = 0 := by
  rw [sum_primaryScore_eq]
  exact radix100_eq_zero_iff _ (primaryCoeff_total_abs_lt t)

theorem pattern_primaryCoeff_sum (p : Pattern) (j : Fin 10) :
    (∑ r : Role, primaryCoeff j (patternSubclass p r)) = 0 := by
  cases p <;> fin_cases j <;>
    norm_num [Role.sum_univ, patternSubclass, primaryCoeff, subclassIndicator,
      Subclass.role] <;> decide

theorem sum_role_subclassIndicator (v : Role → Subclass)
    (hrole : ∀ r, (v r).role = r) (c : Subclass) :
    (∑ r : Role, subclassIndicator (v r) c) = subclassIndicator (v c.role) c := by
  classical
  apply Finset.sum_eq_single c.role
  · intro r _ hr
    have hne : v r ≠ c := by
      intro he
      exact hr ((hrole r).symm.trans (congrArg Subclass.role he))
    simp [subclassIndicator, hne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem roleTuple_eq_pattern (v : Role → Subclass)
    (hrole : ∀ r, (v r).role = r)
    (hcoeff : ∀ j : Fin 10, (∑ r, primaryCoeff j (v r)) = 0) :
    ∃ p : Pattern, ∀ r, v r = patternSubclass p r := by
  have hx := (role_eq_x_iff _).mp (hrole .x)
  have ha := (role_eq_anchor_iff _).mp (hrole .anchor)
  have hu := (role_eq_global_iff _).mp (hrole .«global»)
  have hd := (role_eq_local_iff _).mp (hrole .«local»)
  have hf := (role_eq_flag_iff _).mp (hrole .flag)
  have h5 := hcoeff 5
  have h6 := hcoeff 6
  have h7 := hcoeff 7
  have h8 := hcoeff 8
  have h9 := hcoeff 9
  rw [sum_primaryCoeff_five] at h5
  rw [sum_primaryCoeff_six] at h6
  rw [sum_primaryCoeff_seven] at h7
  rw [sum_primaryCoeff_eight] at h8
  rw [sum_primaryCoeff_nine] at h9
  simp only [subclassCount, sum_role_subclassIndicator v hrole, Subclass.role]
    at h5 h6 h7 h8 h9
  rcases hf with hf | hf | hf
  all_goals
    rcases ha with ha | ha <;> rcases hd with hd | hd
  all_goals
    simp +decide [subclassIndicator, ha, hd, hf] at h6 h8
  all_goals
    rcases hx with hx | hx | hx <;> rcases hu with hu | hu | hu
  all_goals
    simp +decide [subclassIndicator, hx, hu, hf] at h5 h7 h9
  · refine ⟨.plusTree, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]
  · refine ⟨.minusTree, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]
  · refine ⟨.mainJob, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]
  · refine ⟨.edgeJob, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]

theorem sum_primaryScore_eq_zero_iff_pattern (t : Fin 5 → Subclass) :
    (∑ i, primaryScore (t i)) = 0 ↔ IsPatternTuple t := by
  classical
  rw [sum_primaryScore_eq_zero_iff_coefficients]
  constructor
  · intro hc
    have hcount (r : Role) : roleCount t r = 1 := by
      have h := hc (roleCoeffIndex r)
      rw [sum_primaryCoeff_role] at h
      norm_num at h
      omega
    have hsurj : Function.Surjective (fun i : Fin 5 => (t i).role) := by
      intro r
      by_contra hno
      have hne : ∀ i : Fin 5, (t i).role ≠ r := fun i hi => hno ⟨i, hi⟩
      have hh := hcount r
      simp [roleCount, hne] at hh
    let e₀ : Fin 5 ≃ Role := Fintype.equivOfCardEq (by simp)
    have hinj : Function.Injective (fun i : Fin 5 => (t i).role) :=
      (Finite.injective_iff_surjective_of_equiv e₀).mpr hsurj
    let e : Fin 5 ≃ Role := Equiv.ofBijective _ ⟨hinj, hsurj⟩
    let v : Role → Subclass := fun r => t (e.symm r)
    have hvrole (r : Role) : (v r).role = r := by
      change e (e.symm r) = r
      exact e.apply_symm_apply r
    have hvcoeff (j : Fin 10) : (∑ r : Role, primaryCoeff j (v r)) = 0 := by
      calc
        (∑ r : Role, primaryCoeff j (v r)) =
            ∑ i : Fin 5, primaryCoeff j (v (e i)) := (e.sum_comp _).symm
        _ = 0 := by simpa [v] using hc j
    obtain ⟨p, hp⟩ := roleTuple_eq_pattern v hvrole hvcoeff
    refine ⟨p, e, ?_⟩
    intro i
    simpa [v] using hp (e i)
  · rintro ⟨p, e, he⟩ j
    calc
      (∑ i, primaryCoeff j (t i)) =
          ∑ i : Fin 5, primaryCoeff j (patternSubclass p (e i)) := by simp only [he]
      _ = ∑ r : Role, primaryCoeff j (patternSubclass p r) :=
        e.sum_comp (fun r : Role => primaryCoeff j (patternSubclass p r))
      _ = 0 := pattern_primaryCoeff_sum p j

end

section

def secondaryScore {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) : ℤ :=
  let q := label.elim 0 labelWeight
  match subclass.role with
  | .x => q
  | .anchor => -2 * q
  | .«global» => 0
  | .«local» => q
  | .flag => 0

@[simp] theorem secondaryScore_none {n : ℕ} (subclass : Subclass) :
    secondaryScore subclass (none : Option (Fin n)) = 0 := by
  cases hs : subclass.role <;> simp [secondaryScore, hs]

def gamma : ℚ := 1 / (1000 * (primaryBound : ℚ))

def mu (n : ℕ) : ℚ := gamma / (1000 * (3 : ℚ) ^ n)

def nu (n : ℕ) : ℚ := mu n / 1000

def encodedSize {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) (w : ℚ) : ℚ :=
  1 / 5 + gamma * (primaryScore subclass : ℚ) +
    mu n * (secondaryScore subclass label : ℚ) + nu n * w

theorem gamma_pos : 0 < gamma := by
  norm_num [gamma, primaryBound]

theorem gamma_le_one : gamma ≤ 1 := by
  norm_num [gamma, primaryBound]

theorem gamma_mul_primaryBound : gamma * (primaryBound : ℚ) = 1 / 1000 := by
  norm_num [gamma, primaryBound]

theorem mu_pos (n : ℕ) : 0 < mu n := by
  exact div_pos gamma_pos (mul_pos (by norm_num) (pow_pos (by norm_num) n))

theorem nu_pos (n : ℕ) : 0 < nu n := div_pos (mu_pos n) (by norm_num)

theorem mu_mul_labelBound (n : ℕ) : mu n * (3 : ℚ) ^ n = gamma / 1000 := by
  unfold mu
  have hn : (3 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp [hn]

theorem mu_le_gamma_div (n : ℕ) : mu n ≤ gamma / 1000 := by
  have hn : (1 : ℚ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have h := mul_le_mul_of_nonneg_left hn (mu_pos n).le
  rw [mul_one, mu_mul_labelBound] at h
  exact h

theorem nu_le_gamma_div (n : ℕ) : nu n ≤ gamma / 1000000 := by
  have h := div_le_div_of_nonneg_right (mu_le_gamma_div n) (by norm_num : (0 : ℚ) ≤ 1000)
  simpa only [nu, div_div, show (1000 : ℚ) * 1000 = 1000000 by norm_num] using h

theorem secondaryScore_abs_le {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) :
    |secondaryScore subclass label| ≤ 2 * (3 : ℤ) ^ n := by
  cases label with
  | none =>
      cases hs : subclass.role <;> simp [secondaryScore, hs]
  | some v =>
      have hv0 := labelWeight_pos v
      have hv := labelWeight_le v
      cases hs : subclass.role <;>
        norm_num [secondaryScore, hs, abs_mul, abs_of_pos hv0] <;> linarith

theorem secondaryScore_rat_abs_le {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) :
    |(secondaryScore subclass label : ℚ)| ≤ 2 * (3 : ℚ) ^ n := by
  exact_mod_cast secondaryScore_abs_le subclass label

theorem primaryScore_rat_abs_le (subclass : Subclass) :
    |(primaryScore subclass : ℚ)| ≤ (primaryBound : ℚ) := by
  exact_mod_cast (primaryScore_abs_lt subclass).le

theorem perturbation_triangle (g m v p q w : ℚ)
    (hg : 0 ≤ g) (hm : 0 ≤ m) (hv : 0 ≤ v) :
    |(1 / 5 + g * p + m * q + v * w) - 1 / 5| ≤
      g * |p| + m * |q| + v * |w| := by
  have heq : (1 / 5 + g * p + m * q + v * w) - 1 / 5 =
      g * p + m * q + v * w := by ring
  rw [heq]
  have hp : |g * p| = g * |p| := by rw [abs_mul, abs_of_nonneg hg]
  have hq : |m * q| = m * |q| := by rw [abs_mul, abs_of_nonneg hm]
  have hw : |v * w| = v * |w| := by rw [abs_mul, abs_of_nonneg hv]
  have hfirst : |g * p + m * q| ≤ |g * p| + |m * q| :=
    abs_add_le (g * p) (m * q)
  have hsecond : |g * p + m * q + v * w| ≤ |g * p + m * q| + |v * w| :=
    abs_add_le (g * p + m * q) (v * w)
  rw [hp, hq] at hfirst
  rw [hw] at hsecond
  linarith only [hfirst, hsecond]

theorem perturbation_small (g m v p q w : ℚ)
    (hg : 0 ≤ g) (hm : 0 ≤ m) (hv : 0 ≤ v) (hg1 : g ≤ 1)
    (hp : g * |p| ≤ 1 / 1000) (hq : m * |q| ≤ 2 * g / 1000)
    (hw : v * |w| ≤ v * 6) (hnu : v ≤ g / 1000000) :
    |(1 / 5 + g * p + m * q + v * w) - 1 / 5| ≤ 1 / 100 := by
  have hsum := perturbation_triangle g m v p q w hg hm hv
  nlinarith only [hsum, hg1, hp, hq, hw, hnu]

theorem encodedSize_perturbation_bound {n : ℕ} (subclass : Subclass)
    (label : Option (Fin n)) (w : ℚ) (hw : |w| ≤ 6) :
    |encodedSize subclass label w - 1 / 5| ≤ 1 / 100 := by
  have hp := mul_le_mul_of_nonneg_left (primaryScore_rat_abs_le subclass) gamma_pos.le
  rw [gamma_mul_primaryBound] at hp
  have hq := mul_le_mul_of_nonneg_left (secondaryScore_rat_abs_le subclass label) (mu_pos n).le
  have hq' : mu n * |(secondaryScore subclass label : ℚ)| ≤ 2 * gamma / 1000 := by
    calc
      _ ≤ mu n * (2 * (3 : ℚ) ^ n) := hq
      _ = 2 * gamma / 1000 := by
        rw [← mul_assoc, mul_comm (mu n) 2, mul_assoc, mu_mul_labelBound]
        ring
  have hw' := mul_le_mul_of_nonneg_left hw (nu_pos n).le
  exact perturbation_small gamma (mu n) (nu n) (primaryScore subclass)
    (secondaryScore subclass label) w gamma_pos.le (mu_pos n).le (nu_pos n).le
    gamma_le_one hp hq' hw' (nu_le_gamma_div n)

theorem encodedSize_mem_interval {n : ℕ} (subclass : Subclass)
    (label : Option (Fin n)) (w : ℚ) (hw : |w| ≤ 6) :
    1 / 6 < encodedSize subclass label w ∧ encodedSize subclass label w < 1 := by
  have hb := abs_le.mp (encodedSize_perturbation_bound subclass label w hw)
  constructor <;> linarith

open scoped BigOperators

end

open scoped BigOperators

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_CompletionGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.Geometry

abbrev Position (m R : ℕ) := Fin m × Fin R

def theta (R : ℕ) {m : ℕ} (e : Fin m) : ℚ :=
  ((R : ℚ) + 1) ^ e.val - 1

def heightCode (R : ℕ) {m : ℕ} (r : Position m R) : ℚ :=
  ((r.2.val : ℚ) + 1) * ((R : ℚ) + 1) ^ r.1.val - 1

def gap (m R : ℕ) : ℚ := 1 / (16 * ((R : ℚ) + 1) ^ m)

def baseline (m R : ℕ) (r : Position m R) : ℚ :=
  1 / 2 + gap m R * heightCode R r

def beta (m R : ℕ) (e : Fin m) : ℚ := gap m R * theta R e

def lambda (m R D ell : ℕ) : ℚ :=
  gap m R / (100 * ((D : ℚ) + 1)) ^ ell

def delta (m R D L : ℕ) : ℚ := lambda m R D L / 10

theorem base_pos (R : ℕ) : 0 < (R : ℚ) + 1 := by positivity

theorem base_one_le (R : ℕ) : 1 ≤ (R : ℚ) + 1 := by
  have hR : (0 : ℚ) ≤ R := Nat.cast_nonneg R
  linarith

theorem widthScale_pos (D : ℕ) : 0 < 100 * ((D : ℚ) + 1) := by positivity

theorem widthScale_one_le (D : ℕ) : 1 ≤ 100 * ((D : ℚ) + 1) := by
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg D
  linarith

theorem gap_pos (m R : ℕ) : 0 < gap m R := by
  unfold gap
  positivity

theorem gap_nonneg (m R : ℕ) : 0 ≤ gap m R := (gap_pos m R).le

theorem gap_le_one_sixteen (m R : ℕ) : gap m R ≤ 1 / 16 := by
  unfold gap
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have hp : (1 : ℚ) ≤ ((R : ℚ) + 1) ^ m := one_le_pow₀ (base_one_le R)
  linarith

theorem gap_mul_power (m R : ℕ) : gap m R * ((R : ℚ) + 1) ^ m = 1 / 16 := by
  unfold gap
  have hp : ((R : ℚ) + 1) ^ m ≠ 0 := (pow_pos (base_pos R) m).ne'
  field_simp [hp]

theorem theta_nonneg (R : ℕ) {m : ℕ} (e : Fin m) : 0 ≤ theta R e := by
  exact sub_nonneg.mpr (one_le_pow₀ (base_one_le R))

theorem theta_lt_power (R : ℕ) {m : ℕ} (e : Fin m) :
    theta R e < ((R : ℚ) + 1) ^ m := by
  have hp := pow_le_pow_right₀ (base_one_le R) (Nat.le_of_lt e.isLt)
  unfold theta
  linarith

theorem heightCode_nonneg (R : ℕ) {m : ℕ} (r : Position m R) :
    0 ≤ heightCode R r := by
  have hj : (1 : ℚ) ≤ (r.2.val : ℚ) + 1 := by
    have h := (Nat.cast_nonneg r.2.val : (0 : ℚ) ≤ r.2.val)
    linarith
  have hp : (1 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := one_le_pow₀ (base_one_le R)
  have hprod : (1 : ℚ) * 1 ≤ ((r.2.val : ℚ) + 1) * ((R : ℚ) + 1) ^ r.1.val :=
    mul_le_mul hj hp (by norm_num) (by positivity)
  unfold heightCode
  linarith

theorem heightCode_lt_power (R : ℕ) {m : ℕ} (r : Position m R) :
    heightCode R r < ((R : ℚ) + 1) ^ m := by
  have hj : (r.2.val : ℚ) + 1 < (R : ℚ) + 1 := by
    exact_mod_cast Nat.add_lt_add_right r.2.isLt 1
  have hp : 0 < ((R : ℚ) + 1) ^ r.1.val := pow_pos (base_pos R) _
  have he : r.1.val + 1 ≤ m := r.1.isLt
  have hpow := pow_le_pow_right₀ (base_one_le R) he
  have hmul := mul_lt_mul_of_pos_right hj hp
  rw [pow_succ] at hpow
  unfold heightCode
  nlinarith

theorem baseline_lower (m R : ℕ) (r : Position m R) : 1 / 2 ≤ baseline m R r := by
  unfold baseline
  exact le_add_of_nonneg_right (mul_nonneg (gap_nonneg _ _) (heightCode_nonneg _ _))

theorem baseline_upper (m R : ℕ) (r : Position m R) : baseline m R r < 9 / 16 := by
  have h := mul_lt_mul_of_pos_left (heightCode_lt_power R r) (gap_pos m R)
  rw [gap_mul_power] at h
  unfold baseline
  linarith

theorem baseline_range (m R : ℕ) (r : Position m R) :
    1 / 2 ≤ baseline m R r ∧ baseline m R r < 9 / 16 :=
  ⟨baseline_lower _ _ _, baseline_upper _ _ _⟩

theorem beta_nonneg (m R : ℕ) (e : Fin m) : 0 ≤ beta m R e :=
  mul_nonneg (gap_nonneg _ _) (theta_nonneg _ _)

theorem beta_lt_one_sixteen (m R : ℕ) (e : Fin m) : beta m R e < 1 / 16 := by
  have h := mul_lt_mul_of_pos_left (theta_lt_power R e) (gap_pos m R)
  rwa [gap_mul_power] at h

theorem lambda_pos (m R D ell : ℕ) : 0 < lambda m R D ell :=
  div_pos (gap_pos _ _) (pow_pos (widthScale_pos D) ell)

theorem lambda_nonneg (m R D ell : ℕ) : 0 ≤ lambda m R D ell :=
  (lambda_pos _ _ _ _).le

@[simp] theorem lambda_zero (m R D : ℕ) : lambda m R D 0 = gap m R := by
  simp [lambda]

theorem lambda_succ (m R D ell : ℕ) :
    lambda m R D (ell + 1) = lambda m R D ell / (100 * ((D : ℚ) + 1)) := by
  simp only [lambda, pow_succ, div_div]

theorem lambda_antitone (m R D : ℕ) : Antitone (lambda m R D) := by
  intro a b hab
  exact div_le_div_of_nonneg_left (gap_nonneg m R) (pow_pos (widthScale_pos D) a)
    (pow_le_pow_right₀ (widthScale_one_le D) hab)

theorem lambda_le_gap (m R D ell : ℕ) : lambda m R D ell ≤ gap m R := by
  simpa only [lambda_zero] using lambda_antitone m R D (Nat.zero_le ell)

theorem lambda_le_one (m R D ell : ℕ) : lambda m R D ell ≤ 1 := by
  have h := (lambda_le_gap m R D ell).trans (gap_le_one_sixteen m R)
  linarith

theorem delta_pos (m R D L : ℕ) : 0 < delta m R D L :=
  div_pos (lambda_pos _ _ _ _) (by norm_num)

theorem delta_nonneg (m R D L : ℕ) : 0 ≤ delta m R D L := (delta_pos _ _ _ _).le

theorem delta_le_tenth (m R D : ℕ) {ell L : ℕ} (h : ell ≤ L) :
    delta m R D L ≤ lambda m R D ell / 10 :=
  div_le_div_of_nonneg_right (lambda_antitone m R D h) (by norm_num)

theorem delta_lt_gap (m R D L : ℕ) : delta m R D L < gap m R := by
  have hd := delta_le_tenth m R D (Nat.zero_le L)
  rw [lambda_zero] at hd
  have hg := gap_pos m R
  linarith

theorem children_succ_lt_parent (m R D ell : ℕ) :
    (4 * (D : ℚ) + 1) * lambda m R D (ell + 1) < lambda m R D ell := by
  rw [lambda_succ, ← mul_div_assoc]
  apply (div_lt_iff₀ (widthScale_pos D)).2
  have hcoeff : 4 * (D : ℚ) + 1 < 100 * ((D : ℚ) + 1) := by
    have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg D
    linarith
  simpa only [mul_comm] using mul_lt_mul_of_pos_right hcoeff (lambda_pos m R D ell)

theorem first_children_lt_gap_twentyfifth (m R D : ℕ) :
    (4 * (D : ℚ) + 1) * lambda m R D 1 < gap m R / 25 := by
  simp only [lambda, pow_one]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (widthScale_pos D)).2
  have hcoeff : 25 * (4 * (D : ℚ) + 1) < 100 * ((D : ℚ) + 1) := by
    linarith
  have h := mul_lt_mul_of_pos_right hcoeff (gap_pos m R)
  nlinarith

theorem first_children_lt_tenth (m R D : ℕ) :
    (4 * (D : ℚ) + 1) * lambda m R D 1 < 1 / 10 := by
  have h := first_children_lt_gap_twentyfifth m R D
  have hg := gap_le_one_sixteen m R
  linarith

end BinPackingGap.Geometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_CurrentMatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace CoverageCounts

section FiniteCounts

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β]

theorem interval_prefix_card [LinearOrder γ] (s : Finset α) (h b : α → γ)
    (hle : ∀ i ∈ s, h i ≤ b i) (a : γ) :
    (s.filter fun i => h i ≤ a).card =
      (s.filter fun i => b i ≤ a).card +
        (s.filter fun i => h i ≤ a ∧ a < b i).card := by
  classical
  have hunion : (s.filter fun i => h i ≤ a) =
      (s.filter fun i => b i ≤ a) ∪
        (s.filter fun i => h i ≤ a ∧ a < b i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨his, hia⟩
      by_cases hba : b i ≤ a
      · exact Or.inl ⟨his, hba⟩
      · exact Or.inr ⟨his, hia, lt_of_not_ge hba⟩
    · rintro (⟨his, hba⟩ | ⟨his, hia, _⟩)
      · exact ⟨his, (hle i his).trans hba⟩
      · exact ⟨his, hia⟩
  have hdis : Disjoint (s.filter fun i => b i ≤ a)
      (s.filter fun i => h i ≤ a ∧ a < b i) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (Finset.mem_filter.mp hi).2)
      (Finset.mem_filter.mp hj).2.2
  rw [hunion, Finset.card_union_of_disjoint hdis]

end FiniteCounts

end CoverageCounts
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_IntegerPackingArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.IntegerPackingArithmetic

def widthRadix (D : ℕ) : ℕ := 100 * (D + 1)

def geomDenominator (m R D L : ℕ) : ℕ :=
  160 * (R + 1) ^ m * widthRadix D ^ L

def sizeDenominator (n geom : ℕ) : ℕ :=
  10 ^ 9 * primaryBound * 3 ^ n * geom

def signedNumerator (n geom : ℕ) (p q W : ℤ) : ℤ :=
  200000000 * (primaryBound : ℤ) * 3 ^ n * geom +
    1000000 * 3 ^ n * geom * p + 1000 * geom * q + W

def localNumerator (D L ell : ℕ) : ℕ := 10 * widthRadix D ^ (L - ell)

def baselineNumerator (m R D L : ℕ) (r : Geometry.Position m R) : ℤ :=
  80 * (R + 1 : ℤ) ^ m * (widthRadix D : ℤ) ^ L +
    10 * (widthRadix D : ℤ) ^ L *
      (((r.2.val : ℤ) + 1) * (R + 1 : ℤ) ^ r.1.val - 1)

def betaNumerator (m R D L : ℕ) (e : Fin m) : ℤ :=
  10 * (widthRadix D : ℤ) ^ L * ((R + 1 : ℤ) ^ e.val - 1)

end BinPackingGap.IntegerPackingArithmetic

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_IntegerTreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.TreeGeometry

open _root_.OAI.BinPackingGap.Geometry

inductive Side where
  | plus
  | minus
  deriving DecidableEq

def rootOffset : Side → ℚ
  | .plus => 0
  | .minus => 4

def pathSum (m R D : ℕ) : ℕ → List ℕ → ℚ
  | _, [] => 0
  | k, a :: w => 4 * (a : ℚ) * lambda m R D (k + 1) + pathSum m R D (k + 1) w

def left (m R D : ℕ) (s : Side) (w : List ℕ) : ℚ :=
  rootOffset s + pathSum m R D 0 w

def width (m R D : ℕ) (w : List ℕ) : ℚ :=
  if w = [] then 1 else lambda m R D w.length

def right (m R D : ℕ) (s : Side) (w : List ℕ) : ℚ :=
  left m R D s w + width m R D w

def BoundedAddress (D : ℕ) (w : List ℕ) : Prop := ∀ a ∈ w, a ≤ D

end BinPackingGap.TreeGeometry

namespace BinPackingGap.IntegerPackingArithmetic

def pathNumerator (D L : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | k, a :: w => 40 * a * widthRadix D ^ (L - (k + 1)) +
      pathNumerator D L (k + 1) w

end BinPackingGap.IntegerPackingArithmetic

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryScores
attribute [-instance] _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

inductive GlobalSpecies (G : GraphInput) where
  | up (unitLength : Bool)
  | um (unitLength : Bool)
  | edge (e : G.Edge) (permit : Bool)
  deriving DecidableEq

instance instFintypeGlobalSpecies (G : GraphInput) : Fintype (GlobalSpecies G) where
  elems := (Finset.univ.image GlobalSpecies.up) ∪
    (Finset.univ.image GlobalSpecies.um) ∪
    ((Finset.univ : Finset (G.Edge × Bool)).image
      (fun p => GlobalSpecies.edge p.1 p.2))
  complete := by
    intro s
    cases s <;> simp

inductive FlagSpecies where
  | tree
  | main
  | edge
  deriving DecidableEq

instance instFintypeFlagSpecies : Fintype FlagSpecies where
  elems := {.tree, .main, .edge}
  complete := by intro s; cases s <;> simp

namespace GlobalSpecies

def equivSum (G : GraphInput) :
    GlobalSpecies G ≃ (Bool ⊕ Bool) ⊕ (G.Edge × Bool) where
  toFun
    | .up b => .inl (.inl b)
    | .um b => .inl (.inr b)
    | .edge e b => .inr (e, b)
  invFun
    | .inl (.inl b) => .up b
    | .inl (.inr b) => .um b
    | .inr (e, b) => .edge e b
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with ((b | b) | ⟨e, b⟩) <;> rfl

theorem sum_univ {A : Type*} [AddCommMonoid A] (G : GraphInput)
    (f : GlobalSpecies G → A) :
    (∑ s, f s) = f (.up true) + f (.up false) + f (.um true) + f (.um false) +
      ∑ e : G.Edge, (f (.edge e true) + f (.edge e false)) := by
  calc
    _ = ∑ x : (Bool ⊕ Bool) ⊕ (G.Edge × Bool), f ((equivSum G).symm x) :=
      Fintype.sum_equiv (equivSum G) _ _ (fun _ => by simp)
    _ = _ := by
      simp [equivSum, Fintype.sum_sum_type, Fintype.sum_prod_type,
        add_assoc, add_comm]

end GlobalSpecies

namespace FlagSpecies

theorem sum_univ {A : Type*} [AddCommMonoid A] (f : FlagSpecies → A) :
    (∑ s, f s) = f .tree + f .main + f .edge := by
  have h : (Finset.univ : Finset FlagSpecies) = {.tree, .main, .edge} := by decide
  rw [h]
  simp [add_assoc]

end FlagSpecies

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_LabelConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

namespace LabelConservation

open scoped BigOperators

variable {n : ℕ}
variable {T A R D : Type*}
variable [Fintype T] [Fintype A] [Fintype R] [Fintype D]
variable [DecidableEq A] [DecidableEq R] [DecidableEq D]

def outsideItems (f : T → A) : Finset A := Finset.univ \ Finset.univ.image f

def labelDefects (labelA : A → Fin n) (labelR : R → Fin n)
    (anchor : T → A) (role : T → R) (v : Fin n) : Finset T :=
  Finset.univ.filter fun t => labelA (anchor t) = v ∧ labelR (role t) ≠ v

def badAnchors (labelA : A → Fin n) (labelR : R → Fin n) (labelD : D → Fin n)
    (anchor : T → A) (role : T → R) (localRole : T → D) (v : Fin n) : Finset A :=
  ((outsideItems anchor).filter fun a => labelA a = v) ∪
    (labelDefects labelA labelR anchor role v).image anchor ∪
    (labelDefects labelA labelD anchor localRole v).image anchor

end LabelConservation
end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_CoordinateOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.Geometry

variable {m R : ℕ}

def posLT (r s : Position m R) : Prop :=
  r.1.val < s.1.val ∨ r.1 = s.1 ∧ r.2.val < s.2.val

def posLE (r s : Position m R) : Prop := r = s ∨ posLT r s

theorem posLT_trichotomy (r s : Position m R) :
    posLT r s ∨ r = s ∨ posLT s r := by
  simp only [posLT, Prod.ext_iff, Fin.ext_iff]
  omega

theorem posLT_or_posLT_of_ne {r s : Position m R} (hne : r ≠ s) :
    posLT r s ∨ posLT s r := by
  rcases posLT_trichotomy r s with hrs | hrs | hsr
  · exact Or.inl hrs
  · exact (hne hrs).elim
  · exact Or.inr hsr

theorem heightCode_ge_theta (R : ℕ) (r : Position m R) :
    theta R r.1 ≤ heightCode R r := by
  have hj : (0 : ℚ) ≤ r.2.val := Nat.cast_nonneg _
  have hp : (0 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := pow_nonneg (by positivity) _
  unfold theta heightCode
  nlinarith

theorem heightCode_le_edgeMax (R : ℕ) (r : Position m R) :
    heightCode R r ≤ (R : ℚ) * ((R : ℚ) + 1) ^ r.1.val - 1 := by
  have hj : (r.2.val : ℚ) + 1 ≤ R := by
    exact_mod_cast Nat.succ_le_of_lt r.2.isLt
  have hp : (0 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := pow_nonneg (by positivity) _
  have hmul := mul_le_mul_of_nonneg_right hj hp
  unfold heightCode
  linarith

theorem heightCode_jump {r s : Position m R} (h : posLT r s) :
    theta R r.1 + 1 ≤ heightCode R s - heightCode R r := by
  rcases h with he | ⟨he, hj⟩
  · have hp : ((R : ℚ) + 1) ^ (r.1.val + 1) ≤
        ((R : ℚ) + 1) ^ s.1.val :=
      pow_le_pow_right₀ (base_one_le R) (Nat.succ_le_of_lt he)
    rw [pow_succ] at hp
    have hlo := heightCode_ge_theta R s
    have hhi := heightCode_le_edgeMax R r
    unfold theta at hlo ⊢
    nlinarith
  · have hj' : (r.2.val : ℚ) + 1 ≤ s.2.val := by
      exact_mod_cast Nat.succ_le_of_lt hj
    have hp : (0 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := pow_nonneg (by positivity) _
    have hmul := mul_le_mul_of_nonneg_right hj' hp
    simp only [heightCode, theta, ← he]
    nlinarith

theorem baseline_gap_of_posLT {r s : Position m R} (h : posLT r s) :
    gap m R ≤ baseline m R s - baseline m R r := by
  have hjump := heightCode_jump h
  have ht := theta_nonneg R r.1
  have hheight : (1 : ℚ) ≤ heightCode R s - heightCode R r := by linarith
  have hmul := mul_le_mul_of_nonneg_left hheight (gap_pos m R).le
  unfold baseline
  nlinarith

end BinPackingGap.Geometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TestGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.Geometry

variable {m R D L : ℕ}

def jobLeft (m R D L : ℕ) (r : Position m R) : ℚ :=
  baseline m R r - delta m R D L

def closedJobCell (m R D L : ℕ) (r : Position m R) : Set ℚ :=
  Set.Icc (jobLeft m R D L r) (baseline m R r)

def jobTestInterval (m R D L : ℕ) (r : Position m R) : Set ℚ :=
  Set.Ico (jobLeft m R D L r) (baseline m R r)

def jobInterior (m R D L : ℕ) (r : Position m R) : ℚ :=
  baseline m R r - delta m R D L / 2

theorem jobLeft_lt_baseline (m R D L : ℕ) (r : Position m R) :
    jobLeft m R D L r < baseline m R r := by
  have h := delta_pos m R D L
  unfold jobLeft
  linarith

theorem one_tenth_lt_jobLeft (m R D L : ℕ) (r : Position m R) :
    1 / 10 < jobLeft m R D L r := by
  have hb := baseline_lower m R r
  have hd := delta_lt_gap m R D L
  have hg := gap_le_one_sixteen m R
  unfold jobLeft
  linarith

theorem job_baseline_lt_one (m R : ℕ) (r : Position m R) :
    baseline m R r < 1 := by
  have h := baseline_upper m R r
  linarith

theorem closedJobCell_bounds {r : Position m R} {x : ℚ}
    (hx : x ∈ closedJobCell m R D L r) : 1 / 10 < x ∧ x < 1 := by
  exact ⟨lt_of_lt_of_le (one_tenth_lt_jobLeft m R D L r) hx.1,
    lt_of_le_of_lt hx.2 (job_baseline_lt_one m R r)⟩

theorem jobTestInterval_subset_closedJobCell (m R D L : ℕ) (r : Position m R) :
    jobTestInterval m R D L r ⊆ closedJobCell m R D L r := by
  intro x hx
  exact ⟨hx.1, hx.2.le⟩

theorem job_gap_of_posLT (D L : ℕ) {r s : Position m R} (hrs : posLT r s) :
    gap m R - delta m R D L ≤ jobLeft m R D L s - baseline m R r := by
  have h := baseline_gap_of_posLT hrs
  unfold jobLeft
  linarith

theorem baseline_lt_jobLeft_of_posLT (D L : ℕ) {r s : Position m R}
    (hrs : posLT r s) : baseline m R r < jobLeft m R D L s := by
  have hgap := job_gap_of_posLT D L hrs
  have hd := delta_lt_gap m R D L
  linarith

theorem closedJobCell_disjoint {r s : Position m R} (hrs : r ≠ s) :
    Disjoint (closedJobCell m R D L r) (closedJobCell m R D L s) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases posLT_or_posLT_of_ne hrs with hlt | hlt
  · have h := baseline_lt_jobLeft_of_posLT D L hlt
    exact (not_le_of_gt h) (hy.1.trans hx.2)
  · have h := baseline_lt_jobLeft_of_posLT D L hlt
    exact (not_le_of_gt h) (hx.1.trans hy.2)

end BinPackingGap.Geometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_KeyGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.Geometry

def keyExpression (m R D L : ℕ) (row key : Position m R) (edge : Fin m)
    (nonpermit short : Bool) : ℚ :=
  baseline m R row - baseline m R key + beta m R edge - beta m R key.1 +
    delta m R D L * ((if nonpermit then 1 else 0) - (if short then 1 else 0))

end BinPackingGap.Geometry

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_ItemEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

theorem length_flatMap_constant {α β : Type*} (l : List α)
    (f : α → List β) (n : ℕ) (hf : ∀ a, (f a).length = n) :
    (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih => simp [hf, ih, Nat.add_mul, Nat.add_comm]

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalarExpression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.NaturalPackingNumerator

open IntegerPackingArithmetic

structure NatDifference where
  pos : Nat
  neg : Nat
  deriving DecidableEq

namespace NatDifference

def eval (a : NatDifference) : Int := (a.pos : Int) - a.neg

def ofNat (n : Nat) : NatDifference := ⟨n, 0⟩

def ofInt (z : Int) : NatDifference := ⟨z.toNat, (-z).toNat⟩

def negate (a : NatDifference) : NatDifference := ⟨a.neg, a.pos⟩

def add (a b : NatDifference) : NatDifference := ⟨a.pos + b.pos, a.neg + b.neg⟩

def sub (a b : NatDifference) : NatDifference := ⟨a.pos + b.neg, a.neg + b.pos⟩

def scale (n : Nat) (a : NatDifference) : NatDifference := ⟨n * a.pos, n * a.neg⟩

def toNat (a : NatDifference) : Nat := a.pos - a.neg

@[simp] theorem eval_ofNat (n : Nat) : (ofNat n).eval = (n : Int) := by
  simp [ofNat, eval]

@[simp] theorem eval_ofInt (z : Int) : (ofInt z).eval = z :=
  Int.toNat_sub_toNat_neg z

@[simp] theorem eval_negate (a : NatDifference) : a.negate.eval = -a.eval := by
  simp only [negate, eval]
  ring

@[simp] theorem eval_add (a b : NatDifference) : (a.add b).eval = a.eval + b.eval := by
  simp only [add, eval, Nat.cast_add]
  ring

@[simp] theorem eval_sub (a b : NatDifference) : (a.sub b).eval = a.eval - b.eval := by
  simp only [sub, eval, Nat.cast_add]
  ring

@[simp] theorem eval_scale (n : Nat) (a : NatDifference) :
    (scale n a).eval = (n : Int) * a.eval := by
  simp only [scale, eval, Nat.cast_mul]
  ring

end NatDifference

def baselineParts (m R D L : Nat) (r : Geometry.Position m R) : NatDifference :=
  ⟨80 * (R + 1) ^ m * widthRadix D ^ L +
      10 * widthRadix D ^ L * (r.2.val + 1) * (R + 1) ^ r.1.val,
    10 * widthRadix D ^ L⟩

def betaParts (m R D L : Nat) (edge : Fin m) : NatDifference :=
  ⟨10 * widthRadix D ^ L * (R + 1) ^ edge.val, 10 * widthRadix D ^ L⟩

@[simp] theorem eval_baselineParts (m R D L : Nat) (r : Geometry.Position m R) :
    (baselineParts m R D L r).eval = baselineNumerator m R D L r := by
  simp only [baselineParts, NatDifference.eval, baselineNumerator, Nat.cast_add,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  ring

@[simp] theorem eval_betaParts (m R D L : Nat) (edge : Fin m) :
    (betaParts m R D L edge).eval = betaNumerator m R D L edge := by
  simp only [betaParts, NatDifference.eval, betaNumerator, Nat.cast_add,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  ring

def labelPower {n : Nat} (label : Option (Fin n)) : Nat :=
  label.elim 0 (fun v => 3 ^ (v.val + 1))

def signedParts (n geom : Nat) (p q W : NatDifference) : NatDifference :=
  (((NatDifference.ofNat (200000000 * primaryBound * 3 ^ n * geom)).add
    (NatDifference.scale (1000000 * 3 ^ n * geom) p)).add
      (NatDifference.scale (1000 * geom) q)).add W

@[simp] theorem signedParts_pos (n geom : Nat) (p q W : NatDifference) :
    (signedParts n geom p q W).pos =
      200000000 * primaryBound * 3 ^ n * geom +
        (1000000 * 3 ^ n * geom) * p.pos + (1000 * geom) * q.pos + W.pos := rfl

@[simp] theorem signedParts_neg (n geom : Nat) (p q W : NatDifference) :
    (signedParts n geom p q W).neg =
      (1000000 * 3 ^ n * geom) * p.neg + (1000 * geom) * q.neg + W.neg := by
  simp [signedParts, NatDifference.ofNat, NatDifference.add, NatDifference.scale]

end BinPackingGap.NaturalPackingNumerator

namespace BinPackingGap.PackingCoordinateExpression

open IntegerPackingArithmetic
open NaturalPackingNumerator
open NatExpressionCompiler

inductive Input
  | geometryDg
  | totalPowerA
  | edgePower
  | repetitionOne
  deriving DecidableEq

structure Parts where
  pos : Expr Input
  neg : Expr Input

namespace Parts

def ofExpr (e : Expr Input) : Parts := ⟨e, .constant 0⟩
def negate (p : Parts) : Parts := ⟨p.neg, p.pos⟩
def add (p q : Parts) : Parts := ⟨.add p.pos q.pos, .add p.neg q.neg⟩
def sub (p q : Parts) : Parts := ⟨.add p.pos q.neg, .add p.neg q.pos⟩

end Parts

end BinPackingGap.PackingCoordinateExpression

namespace BinPackingGap.PackingScalarExpression

open NatExpressionCompiler NaturalPackingNumerator IntegerPackingArithmetic

inductive Variable
  | vertexPower | geometry | labelPower | coordinatePositive | coordinateNegative
  deriving DecidableEq

end BinPackingGap.PackingScalarExpression

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingCountedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.GraphFieldMachine

open Turing
open BinaryEncoding
open BinPackingGames.Foundations.Complexity
open GraphTallyMachine (Slot )

inductive Field
  | threshold
  | endpoints
  deriving DecidableEq

instance instFintypeField : Fintype Field where
  elems := {.threshold, .endpoints}
  complete field := by cases field <;> simp

def keepsName : Field → Slot → Bool
  | .threshold, .header => true
  | .endpoints, .edgeFirst => true
  | .endpoints, .edgeSecond => true
  | _, _ => false

end BinPackingGap.GraphFieldMachine

namespace BinPackingGap.GraphTokenMachine

open Turing
open BinaryEncoding
open BinPackingGames.Foundations.Complexity
open GraphTallyMachine (Slot )

inductive Field
  | vertex
  | edge
  deriving DecidableEq

end BinPackingGap.GraphTokenMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingVertexUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingMachineLayout

open NatExpressionCompiler BinaryRegisterProgram

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input]

abbrev Reg (num : Descriptor → Expr Input) (den : Expr Input) (Other : Type) :=
  (Input ⊕ Other) ⊕ (Σ d : Descriptor, Node (num d) ⊕ Node den)

abbrev Tape (num : Descriptor → Expr Input) (den : Expr Input)
    (Other Extra : Type) := (Reg num den Other ⊕ Fin 6) ⊕ Extra

def registers (num : Descriptor → Expr Input) (den : Expr Input) :
    (Reg num den Other ⊕ Fin 6) ↪ Tape num den Other Extra := Function.Embedding.inl

def inputs (num : Descriptor → Expr Input) (den : Expr Input) : Input ↪ Reg num den Other where
  toFun a := .inl (.inl a)
  inj' := by intro a b h; exact Sum.inl.inj (Sum.inl.inj h)

def others (num : Descriptor → Expr Input) (den : Expr Input) : Other ↪ Reg num den Other where
  toFun a := .inl (.inr a)
  inj' := by intro a b h; exact Sum.inr.inj (Sum.inl.inj h)

def values (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) : Reg num den Other → Nat
  | .inl (.inl a) => input a
  | .inl (.inr b) => other b
  | .inr _ => 0

omit [DecidableEq Descriptor] [DecidableEq Input] in
@[simp] theorem values_inputs (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (a : Input) :
    values num den input other (inputs num den a) = input a := rfl

omit [DecidableEq Descriptor] [DecidableEq Input] in
@[simp] theorem values_others (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (a : Other) :
    values num den input other (others num den a) = other a := rfl

end BinPackingGap.PackingMachineLayout

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingJobLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

namespace BinPackingGap.PackingItemExpression

open NatExpressionCompiler

inductive Variable
  | vertexPower | geometry | labelPower | totalPower | edgePower | repetitionOne
  deriving DecidableEq

end BinPackingGap.PackingItemExpression

end

namespace BinPackingGap.PackingVertexLoop

open NatExpressionCompiler

variable {α δ : Type} [DecidableEq α]

def vertexInput (input : α → Nat) (power : α) (v : Nat) : α → Nat :=
  Function.update input power (3 ^ (v + 1))

end BinPackingGap.PackingVertexLoop

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

namespace BinPackingGap.PackingSetupExpression

section

open NatExpressionCompiler

structure Parameters where
  P : Nat
  K : Nat
  d : Nat
  tPlus : Nat
  tMinus : Nat

inductive Input
  | n | m | k
  deriving DecidableEq

inductive Output
  | repetitions | base | edgeRepetitions | bins
  | upOne | upZero | umOne | umZero | edgeStock
  | treeFlags | jobFlags | one | three
  deriving DecidableEq

def inputs (n m k : Nat) : Input → Nat
  | .n => n
  | .m => m
  | .k => k

def repetitions (p : Parameters) : Expr Input :=
  .mul (.constant 100) (.add (.add (.constant p.P)
    (.mul (.input .n) (.constant p.K))) (.constant 1))

def edgeRepetitions (p : Parameters) : Expr Input :=
  .mul (.input .m) (repetitions p)

def jobFlags (p : Parameters) : Expr Input :=
  .mul (.constant (2 * p.d)) (edgeRepetitions p)

def expression (p : Parameters) : Output → Expr Input
  | .repetitions => repetitions p
  | .base => .add (repetitions p) (.constant 1)
  | .edgeRepetitions => edgeRepetitions p
  | .bins => .add (.mul (.input .n) (.constant (p.tPlus + p.tMinus)))
      (.mul (.constant (4 * p.d)) (edgeRepetitions p))
  | .upOne => .mul (.constant p.d) (.input .k)
  | .upZero => .monus (.add (.mul (.input .n) (.constant p.tPlus)) (jobFlags p))
      (.mul (.constant p.d) (.input .k))
  | .umOne => .mul (.constant p.d) (.monus (.input .n) (.input .k))
  | .umZero => .monus (.mul (.input .n) (.constant p.tMinus))
      (.mul (.constant p.d) (.monus (.input .n) (.input .k)))
  | .edgeStock => .mul (.constant p.d) (repetitions p)
  | .treeFlags => .mul (.input .n) (.constant (p.tPlus + p.tMinus))
  | .jobFlags => jobFlags p
  | .one => .constant 1
  | .three => .constant 3

end

end BinPackingGap.PackingSetupExpression

namespace BinPackingGap.PackingSetupMachine

section

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram
open PackingSetupExpression

abbrev Reg (p : Parameters) := Input ⊕ (Output ⊕ (Σ o : Output, Node (expression p o)))

def input (p : Parameters) : Input → Reg p := Sum.inl
def output (p : Parameters) (o : Output) : Reg p := .inr (.inl o)

def nodes (p : Parameters) (o : Output) : Node (expression p o) ↪ Reg p where
  toFun n := .inr (.inr ⟨o, n⟩)
  inj' := by
    intro a b h
    have hs := Sum.inr.inj (Sum.inr.inj h)
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hs

def frame (p : Parameters) (ins : Input → Nat) (outs : Output → Nat) : Reg p → Nat
  | .inl a => ins a
  | .inr (.inl o) => outs o
  | .inr (.inr _) => 0

def outputOrder : List Output :=
  [.repetitions, .base, .edgeRepetitions, .bins, .upOne, .upZero,
    .umOne, .umZero, .edgeStock, .treeFlags, .jobFlags, .one, .three]

end

open BinaryRegisterProgram FiniteTapeProgram PackingSetupExpression

end BinPackingGap.PackingSetupMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_GraphPackingRegisters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingRegisters

open PackingItemExpression
open PackingMachineLayout

inductive Work
  | leftEndpoint | rightEndpoint | leftPower | rightPower
  | counter | one | temporary | reverse | geometryFactor | header
  deriving DecidableEq

end BinPackingGap.GraphPackingRegisters

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Configurations_ConfigurationLP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators
open Set

namespace BinPackingGap.FractionalCover

variable {I C : Type*} [Fintype C]

variable {J : Type*} [Fintype J]

def pushforward (f : J → C) (mass : J → ℝ) : C → ℝ := by
  classical
  exact fun c => ∑ j, if f j = c then mass j else 0

end BinPackingGap.FractionalCover

end

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_DropPackingBoundMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.DropPackingBoundMachine

open Turing BinPackingGames.Foundations.Complexity
open BinaryEncoding

inductive Mode
  | name | digit | copy
  deriving DecidableEq

protected abbrev Mode.enumList : List Mode := [.name, .digit, .copy]

protected theorem Mode.enumList_nodup : Mode.enumList.Nodup := by decide

instance instFintypeMode : Fintype Mode where
  elems := ⟨Mode.enumList, Mode.enumList_nodup⟩
  complete x := by cases x <;> decide

def transition : Mode → Bool → Mode
  | .name, true => .digit
  | .name, false => .copy
  | .digit, _ => .name
  | .copy, _ => .copy

def emit : Mode → Bool → List Bool
  | .copy, bit => [bit]
  | _, _ => []

end BinPackingGap.DropPackingBoundMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

open GraphPackingRegisters PackingItemExpression

variable (K : Nat)

def endpointWork (right : Bool) : Work := if right then .rightEndpoint else .leftEndpoint
def powerWork (right : Bool) : Work := if right then .rightPower else .leftPower

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingPreparationFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingEndpointPower

open BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram FiniteTapeProgram

variable {K : Type} [DecidableEq K]

theorem size_three : (3 : Nat).size = 2 := by decide

end BinPackingGap.PackingEndpointPower

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

def step (label : Nat) (accumulator : Nat × Nat) (row : (Nat × Nat) × Nat) : Nat × Nat :=
  if row.2 = label then RawPacking.addFraction accumulator row.1 else accumulator

end BinPackingGap.CapacityScan

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionAgreementMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionAgreementMachine

open Turing BinPackingGames.Foundations.Complexity

inductive Label
  | entry | option | skipFlag | skipDigit | compareFlag | compareDigit | checkEnd
  | drainFixed | drainAssignments | accept | reject
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.entry, .option, .skipFlag, .skipDigit,
  .compareFlag, .compareDigit, .checkEnd, .drainFixed, .drainAssignments, .accept, .reject]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Fin 2) := Bool
abbrev State := Option Bool × Option Bool

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => (none, none)) (.goto fun _ => label)

def readBoth (zero one : Label) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (head, state.2))
    (.pop 1 (fun state head => (state.1, head))
      (.branch (fun state => state.1.isSome && state.2.isSome)
        (.branch (fun state => decide (state.1 = state.2))
          (.branch (fun state => state.1.getD false) (jump one) (jump zero))
          (jump .drainFixed))
        (jump .drainFixed)))

def program : Label → TM2.Stmt Alphabet Label State
  | .entry => readBoth .checkEnd .option
  | .option => .pop 0 (fun state head => (head, state.2))
      (.branch (fun state => state.1.isSome)
        (.branch (fun state => state.1.getD false)
          (jump .compareFlag) (jump .skipFlag))
        (jump .drainFixed))
  | .skipFlag => .pop 1 (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.branch (fun state => state.2.getD false)
          (jump .skipDigit) (jump .entry))
        (jump .drainFixed))
  | .skipDigit => .pop 1 (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome) (jump .skipFlag) (jump .drainFixed))
  | .compareFlag => readBoth .entry .compareDigit
  | .compareDigit => readBoth .compareFlag .compareFlag
  | .checkEnd => .pop 0 (fun state head => (head, state.2))
      (.pop 1 (fun state head => (state.1, head))
        (.branch (fun state => state.1.isNone && state.2.isNone)
          (jump .accept) (jump .drainFixed)))
  | .drainFixed => .pop 0 (fun state head => (head, state.2))
      (.branch (fun state => state.1.isSome)
        (jump .drainFixed) (jump .drainAssignments))
  | .drainAssignments => .pop 1 (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (jump .drainAssignments) (jump .reject))
  | .accept => .push 0 (fun _ => true) .halt
  | .reject => .push 0 (fun _ => false) .halt

abbrev machine : FinTM2 where
  K := Fin 2
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := .entry
  σ := State
  initialState := (none, none)
  m := program

def tapes (fixed assignments : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then fixed else assignments

def cfg (label : Label) (fixed assignments : List Bool) : machine.Cfg :=
  ⟨some label, (none, none), tapes fixed assignments⟩

theorem update_fixed (fixed assignments replacement : List Bool) :
    Function.update (tapes fixed assignments) 0 replacement = tapes replacement assignments := by
  funext k; fin_cases k <;> simp [tapes]

theorem update_assignments (fixed assignments replacement : List Bool) :
    Function.update (tapes fixed assignments) 1 replacement = tapes fixed replacement := by
  funext k; fin_cases k <;> simp [tapes]

structure View where
  label : Label
  fixed : List Bool
  assignments : List Bool

def View.cfg (view : View) : machine.Cfg :=
  BinPackingGap.ExtensionAgreementMachine.cfg view.label view.fixed view.assignments

def bothView (zero one : Label) (fixed assignments : List Bool) : View :=
  if fixed.head?.isSome && assignments.head?.isSome then
    if fixed.head? = assignments.head? then
      ⟨if fixed.head?.getD false then one else zero, fixed.tail, assignments.tail⟩
    else ⟨.drainFixed, fixed.tail, assignments.tail⟩
  else ⟨.drainFixed, fixed.tail, assignments.tail⟩

def next (view : View) : View :=
  match view.label with
  | .entry => bothView .checkEnd .option view.fixed view.assignments
  | .option =>
      if view.fixed.head?.isSome then
        ⟨if view.fixed.head?.getD false then .compareFlag else .skipFlag,
          view.fixed.tail, view.assignments⟩
      else ⟨.drainFixed, view.fixed.tail, view.assignments⟩
  | .skipFlag =>
      if view.assignments.head?.isSome then
        ⟨if view.assignments.head?.getD false then .skipDigit else .entry,
          view.fixed, view.assignments.tail⟩
      else ⟨.drainFixed, view.fixed, view.assignments.tail⟩
  | .skipDigit =>
      ⟨if view.assignments.head?.isSome then .skipFlag else .drainFixed,
        view.fixed, view.assignments.tail⟩
  | .compareFlag => bothView .entry .compareDigit view.fixed view.assignments
  | .compareDigit => bothView .compareFlag .compareFlag view.fixed view.assignments
  | .checkEnd =>
      ⟨if view.fixed.head?.isNone && view.assignments.head?.isNone then
          .accept else .drainFixed, view.fixed.tail, view.assignments.tail⟩
  | .drainFixed =>
      ⟨if view.fixed.head?.isSome then .drainFixed else .drainAssignments,
        view.fixed.tail, view.assignments⟩
  | .drainAssignments =>
      ⟨if view.assignments.head?.isSome then .drainAssignments else .reject,
        view.fixed, view.assignments.tail⟩
  | .accept | .reject => view

def Terminal (label : Label) : Prop := label = .accept ∨ label = .reject

instance instDecidableTerminal (label : Label) : Decidable (Terminal label) := inferInstanceAs
  (Decidable (label = .accept ∨ label = .reject))

def rank : Label → Nat
  | .accept | .reject => 0
  | .drainAssignments => 1
  | .drainFixed => 2
  | _ => 3

def potential (view : View) : Nat :=
  view.fixed.length + view.assignments.length + rank view.label

theorem next_decreases (view : View) (active : ¬ Terminal view.label) :
    potential (next view) < potential view := by
  rcases view with ⟨label, fixed, assignments⟩
  cases label <;> cases fixed <;> cases assignments <;>
    simp_all [Terminal, next, bothView, potential, rank] <;>
    (try split_ifs) <;> (try simp_all) <;> omega

theorem step_view (view : View) (active : ¬ Terminal view.label) :
    machine.step view.cfg = some (next view).cfg := by
  rcases view with ⟨label, fixed, assignments⟩
  change (some (TM2.stepAux (program label) (none, none) (tapes fixed assignments)) :
    Option (TM2.Cfg Alphabet Label State)) =
    some ⟨some (next ⟨label, fixed, assignments⟩).label, (none, none),
      tapes (next ⟨label, fixed, assignments⟩).fixed
        (next ⟨label, fixed, assignments⟩).assignments⟩
  cases label <;> cases fixed <;> cases assignments <;>
    simp_all [Terminal, program, readBoth, jump,
      TM2.stepAux, next, bothView, update_fixed, update_assignments,
      tapes, Bool.cond_eq_ite] <;>
    (try split_ifs) <;> simp_all

def run (view : View) : View :=
  if _stopped : Terminal view.label then view else run (next view)
termination_by potential view
decreasing_by exact next_decreases view _stopped

def resultView (accepted : Bool) : View :=
  ⟨if accepted then .accept else .reject, [], []⟩

noncomputable def agreementTime : Polynomial Nat := Polynomial.X + 3

structure RawRun (fixed assignments : List Bool) where
  finish : View
  terminal : Terminal finish.label
  execution : StateTransition.EvalsToInTime machine.step (cfg .entry fixed assignments)
    (some finish.cfg) (agreementTime.eval (fixed.length + assignments.length))

theorem flagStep (accepted : Bool) :
    machine.step (cfg (if accepted then .accept else .reject) [] []) =
      some ⟨none, (none, none), tapes [accepted] []⟩ := by
  cases accepted <;>
    simp [FinTM2.step, TM2.step, machine, program, cfg, TM2.stepAux, update_fixed, tapes] <;> rfl

end BinPackingGap.ExtensionAgreementMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionCapacityBounds
attribute [-instance] _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionWitness

open BinaryEncoding

def bound (inputLength : Nat) : Nat := 4 * (inputLength + 1) ^ 2

noncomputable def witnessPolynomial : Polynomial Nat :=
  Polynomial.C 4 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp] theorem witnessPolynomial_eval (inputLength : Nat) :
    witnessPolynomial.eval inputLength = bound inputLength := by
  simp [witnessPolynomial, bound]

end BinPackingGap.ExtensionWitness

namespace BinPackingGap.ExtensionFractionMachine

open Turing
open BinPackingGames.Foundations.Complexity

inductive Product
  | leftNumerator | rightNumerator | denominator
  deriving DecidableEq

protected abbrev Product.enumList : List Product := [.leftNumerator, .rightNumerator,
  .denominator]

protected theorem Product.enumList_nodup : Product.enumList.Nodup := by decide

instance instFintypeProduct : Fintype Product where
  elems := ⟨Product.enumList, Product.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | multiply (product : Product) (localLabel : BinaryMulMachine.Label)
  | add
  | restore
  deriving DecidableEq, Fintype

abbrev Alphabet {K : Type} (_ : K) := Bool

abbrev Tape := Fin 15

def productTapes : Product → (Fin 9 ↪ Tape)
  | .leftNumerator =>
      ⟨![0, 3, 6, 9, 10, 11, 12, 13, 14], by decide⟩
  | .rightNumerator =>
      ⟨![2, 1, 7, 9, 10, 11, 12, 13, 14], by decide⟩
  | .denominator =>
      ⟨![1, 3, 5, 9, 10, 11, 12, 13, 14], by decide⟩

def productExit {Λ : Type} (labels : Label → Λ) : Product → Option Λ
  | .leftNumerator => some (labels (.multiply .rightNumerator .copyLeft))
  | .rightNumerator => some (labels (.multiply .denominator .copyLeft))
  | .denominator => some (labels .add)

variable {K Λ A : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem workspace_multiply (slots : Tape ↪ K) (base : K → List Bool)
    (workspace : ∀ i : Tape, 9 ≤ i.val → base (slots i) = [])
    (product : Product) :
    ∀ i : Fin 9, 3 ≤ i.val → base (((productTapes product).trans slots) i) = [] := by
  intro i hi
  have h9 := workspace 9 (by decide)
  have h10 := workspace 10 (by decide)
  have h11 := workspace 11 (by decide)
  have h12 := workspace 12 (by decide)
  have h13 := workspace 13 (by decide)
  have h14 := workspace 14 (by decide)
  cases product <;> fin_cases i <;> simp_all [productTapes]

theorem workspace_update (slots : Tape ↪ K) (base : K → List Bool)
    (workspace : ∀ i : Tape, 9 ≤ i.val → base (slots i) = [])
    (j : Tape) (hj : j.val < 9) (word : List Bool) :
    ∀ i : Tape, 9 ≤ i.val → Function.update base (slots j) word (slots i) = [] := by
  intro i hi
  have distinct : i ≠ j := by intro h; subst i; omega
  simpa only [Function.update_of_ne (slots.injective.ne distinct)] using workspace i hi

def resultTapes (slots : Tape ↪ K) (base : K → List Bool) (A D a d : Nat) :
    K → List Bool :=
  Function.update (Function.update base (slots 5) (D * d).bits)
    (slots 4) (A * d + a * D).bits

noncomputable def arithmeticBudget (A D a d : Nat) : Nat :=
  BinaryMulMachine.timePolynomial.eval (A.size + d.size) +
    BinaryMulMachine.timePolynomial.eval (a.size + D.size) +
    BinaryMulMachine.timePolynomial.eval (D.size + d.size) +
    (max (A * d).size (a * D).size + 1) +
    ((A * d + a * D).size + 1)

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 12 * Polynomial.X ^ 2 + Polynomial.C 44 * Polynomial.X + Polynomial.C 39

end BinPackingGap.ExtensionFractionMachine

namespace BinPackingGap.ExtensionCapacityMachine

open Turing
open BinPackingGames.Foundations.Complexity

inductive Field
  | numerator | denominator | label
  deriving DecidableEq

protected abbrev Field.enumList : List Field := [.numerator, .denominator, .label]

protected theorem Field.enumList_nodup : Field.enumList.Nodup := by decide

instance instFintypeField : Fintype Field where
  elems := ⟨Field.enumList, Field.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Compare
  | label | capacity
  deriving DecidableEq

protected abbrev Compare.enumList : List Compare := [.label, .capacity]

protected theorem Compare.enumList_nodup : Compare.enumList.Nodup := by decide

instance instFintypeCompare : Fintype Compare where
  elems := ⟨Compare.enumList, Compare.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | guard
  | number (field : Field) (phase : ExtensionNatMachine.Label)
  | compare (which : Compare) (phase : BinaryOrderMachine.PreserveLabel)
  | fraction (phase : ExtensionFractionMachine.Label)
  | clearOldNumerator | clearOldDenominator
  | numeratorOut | numeratorBack | denominatorOut | denominatorBack
  | clearItemNumerator | clearItemDenominator | clearItemLabel
  deriving DecidableEq, Fintype

abbrev Alphabet {K : Type} (_ : K) := Bool

def comparisonExits {Λ : Type} (labels : Label → Λ) (rejected : Option Λ) :
    Compare → Ordering → Option Λ
  | .label, .eq => some (labels (.fraction (.multiply .leftNumerator .copyLeft)))
  | .label, _ => some (labels .clearItemNumerator)
  | .capacity, .gt => rejected
  | .capacity, _ => some (labels .clearOldNumerator)

variable {K Λ A : Type} [DecidableEq K]

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 4096 * (Polynomial.X + 1) ^ 3

end BinPackingGap.ExtensionCapacityMachine

namespace BinPackingGap.ExtensionArithmeticBounds

open BinPackingGames.Foundations.Complexity

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 512 * (Polynomial.X + Polynomial.C 1) ^ 2

@[simp] theorem timePolynomial_eval (inputLength : Nat) :
    timePolynomial.eval inputLength = 512 * (inputLength + 1) ^ 2 := by
  simp [timePolynomial]

end BinPackingGap.ExtensionArithmeticBounds

namespace BinPackingGap.ExtensionCapacityMachine

section

open Turing
open BinPackingGames.Foundations.Complexity

noncomputable def rowCost (num den a d assigned selected : Nat) : Nat :=
  1 + ((2 * a.size + 2) + (2 * d.size + 2) + (2 * assigned.size + 2)) +
    BinaryOrderMachine.preservingSteps assigned.size selected.size +
    ExtensionFractionMachine.arithmeticBudget num den a d +
    BinaryOrderMachine.preservingSteps (num * d + a * den).size (den * d).size +
    (num.size + den.size + 2 * (num * d + a * den).size + 2 * (den * d).size + 6) +
    (a.size + d.size + assigned.size + 3)

end

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

def lengthSum {K : Type} {Γ : K → Type} (chosen : List K)
    (tapes : ∀ k, List (Γ k)) : Nat :=
  (chosen.map fun k => (tapes k).length).sum

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

inductive Kind
  | extension
  | assignments
  deriving DecidableEq

inductive Continuation
  | bins
  | numerator
  | denominator
  | fixed
  | assignment
  deriving DecidableEq

protected abbrev Continuation.enumList : List Continuation := [.bins, .numerator, .denominator,
  .fixed, .assignment]

protected theorem Continuation.enumList_nodup : Continuation.enumList.Nodup := by decide

instance instFintypeContinuation : Fintype Continuation where
  elems := ⟨Continuation.enumList, Continuation.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Mode
  | name (next : Continuation) (last : Bool)
  | digit (next : Continuation)
  | items
  | fixedList
  | fixedOption
  | assignments
  | done
  | reject
  deriving DecidableEq, Fintype

def start : Kind → Mode
  | .extension => .name .bins true
  | .assignments => .assignments

def afterName : Continuation → Mode
  | .bins => .items
  | .numerator => .name .denominator true
  | .denominator => .items
  | .fixed => .fixedList
  | .assignment => .assignments

def nextMode : Mode → Bool → Mode
  | .name next _, true => .digit next
  | .name next last, false => if last then afterName next else .reject
  | .digit next, bit => .name next bit
  | .items, true => .name .numerator true
  | .items, false => .fixedList
  | .fixedList, true => .fixedOption
  | .fixedList, false => .done
  | .fixedOption, true => .name .fixed true
  | .fixedOption, false => .fixedList
  | .assignments, true => .name .assignment true
  | .assignments, false => .done
  | .done, _ => .reject
  | .reject, _ => .reject

def run : Mode → List Bool → Mode
  | mode, [] => mode
  | mode, bit :: rest => run (nextMode mode bit) rest

@[simp] theorem run_reject (input : List Bool) : run .reject input = .reject := by
  induction input with
  | nil => rfl
  | cons bit input ih => simpa only [run, nextMode] using ih

theorem run_done_iff (input : List Bool) : run .done input = .done ↔ input = [] := by
  cases input with
  | nil => simp [run]
  | cons bit rest => simp [run, nextMode]

def accepts (kind : Kind) (input : List Bool) : Bool :=
  decide (run (start kind) input = .done)

open Turing
open BinPackingGames.Foundations.Complexity

inductive Label
  | scan
  | restore
  | finish
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .restore, .finish]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := Mode × Option Bool

def tapes (input output saved : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => output
  | _ => saved

@[simp] theorem tapes_input (input output saved : List Bool) :
    tapes input output saved 0 = input := rfl

@[simp] theorem tapes_output (input output saved : List Bool) :
    tapes input output saved 1 = output := rfl

@[simp] theorem tapes_saved (input output saved : List Bool) :
    tapes input output saved 2 = saved := rfl

theorem update_input (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 0 replacement =
      tapes replacement output saved := by
  funext k
  fin_cases k <;> rfl

theorem update_output (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 1 replacement =
      tapes input replacement saved := by
  funext k
  fin_cases k <;> rfl

theorem update_saved (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 2 replacement =
      tapes input output replacement := by
  funext k
  fin_cases k <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end BinPackingGap.ExtensionShapeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionValidationMachine
attribute [-instance] _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionValidationMachine

open Turing BinPackingGames.Foundations.Complexity

inductive ScanCall
  | bins | numerator | denominator | assigned
  deriving DecidableEq

protected abbrev ScanCall.enumList : List ScanCall := [.bins, .numerator, .denominator, .assigned]

protected theorem ScanCall.enumList_nodup : ScanCall.enumList.Nodup := by decide

instance instFintypeScanCall : Fintype ScanCall where
  elems := ⟨ScanCall.enumList, ScanCall.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev ScanPhase := ExtensionNatMachine.Label

inductive OrderCall
  | fraction | bound
  deriving DecidableEq

protected abbrev OrderCall.enumList : List OrderCall := [.fraction, .bound]

protected theorem OrderCall.enumList_nodup : OrderCall.enumList.Nodup := by decide

instance instFintypeOrderCall : Fintype OrderCall where
  elems := ⟨OrderCall.enumList, OrderCall.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Control
  | boundEnd | marker | positive | clearNumerator | clearDenominator | clearAssigned
  | endCheck | accept | reject
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.boundEnd, .marker, .positive,
  .clearNumerator, .clearDenominator, .clearAssigned, .endCheck, .accept, .reject]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | control (phase : Control)
  | number (call : ScanCall) (phase : ScanPhase)
  | order (call : OrderCall) (phase : BinaryOrderMachine.PreserveLabel)
  deriving DecidableEq, Fintype

abbrev Tape := Fin 10
abbrev Alphabet (_ : Tape) := Bool

def scanSource : ScanCall → Tape
  | .bins => 0
  | .numerator | .denominator => 1
  | .assigned => 2

def scanOutput : ScanCall → Tape
  | .bins => 3
  | .numerator => 4
  | .denominator => 5
  | .assigned => 6

def scanTape (call : ScanCall) : Fin 3 → Tape
  | 0 => scanSource call
  | 1 => scanOutput call
  | _ => 7

def scanPorts (call : ScanCall) : Fin 3 ↪ Tape :=
  ⟨scanTape call, by
    intro i j h
    cases call <;> fin_cases i <;> fin_cases j <;>
      simp_all [scanTape, scanSource, scanOutput]⟩

@[simp] theorem scanPorts_apply (call : ScanCall) (i : Fin 3) :
    scanPorts call i = scanTape call i := by
  simp only [scanPorts]
  rfl

def orderTape (call : OrderCall) : Fin 5 → Tape
  | 0 => match call with | .fraction => 4 | .bound => 6
  | 1 => match call with | .fraction => 5 | .bound => 3
  | 2 => 8
  | 3 => 9
  | _ => 7

def orderPorts (call : OrderCall) : Fin 5 ↪ Tape :=
  ⟨orderTape call, by
    intro i j h
    cases call <;> fin_cases i <;> fin_cases j <;> simp_all [orderTape]⟩

def scanSuccess : ScanCall → Label
  | .bins => .control .boundEnd
  | .numerator => .control .positive
  | .denominator => .order .fraction .leftOut
  | .assigned => .order .bound .leftOut

def orderExit : OrderCall → Ordering → Option Label
  | .fraction, .lt | .fraction, .eq => some (.number .assigned .scan)
  | .fraction, .gt => some (.control .reject)
  | .bound, .lt => some (.control .clearNumerator)
  | .bound, .eq | .bound, .gt => some (.control .reject)

def work (bound items assignments numerator denominator assigned : List Bool) : Tape → List Bool
  | 0 => []
  | 1 => items
  | 2 => assignments
  | 3 => bound
  | 4 => numerator
  | 5 => denominator
  | 6 => assigned
  | _ => []

theorem update_items (b i a n d j replacement : List Bool) :
    Function.update (work b i a n d j) 1 replacement = work b replacement a n d j := by
  funext k; fin_cases k <;> rfl

theorem update_assignments (b i a n d j replacement : List Bool) :
    Function.update (work b i a n d j) 2 replacement = work b i replacement n d j := by
  funext k; fin_cases k <;> rfl

theorem update_numerator (b i a n d j replacement : List Bool) :
    Function.update (work b i a n d j) 4 replacement = work b i a replacement d j := by
  funext k; fin_cases k <;> rfl

theorem update_denominator (b i a n d j replacement : List Bool) :
    Function.update (work b i a n d j) 5 replacement = work b i a n replacement j := by
  funext k; fin_cases k <;> rfl

theorem update_assigned (b i a n d j replacement : List Bool) :
    Function.update (work b i a n d j) 6 replacement = work b i a n d replacement := by
  funext k; fin_cases k <;> rfl

def rowBudget (bins a d j : Nat) : Nat :=
  6 * (a.size + d.size + j.size) + 3 * bins.size + 23

theorem base_budget (b t : Nat) : 2 ≤ 10 * (b + 1) * (t + 1) := by
  have h : 1 ≤ (b + 1) * (t + 1) :=
    Nat.mul_le_mul (by omega : 1 ≤ b + 1) (by omega : 1 ≤ t + 1)
  calc
    2 ≤ 10 := by decide
    _ ≤ 10 * (b + 1) * (t + 1) := by
      simpa only [Nat.mul_one, Nat.mul_assoc] using Nat.mul_le_mul_left 10 h

theorem row_budget (b s : Nat) :
    6 * s + 3 * b + 23 ≤ 10 * (b + 1) * (2 * s + 5) := by
  nlinarith [Nat.zero_le (b * s)]

noncomputable def validationTime : Polynomial Nat := 16 * (Polynomial.X + 1) ^ 2

theorem total_budget (b F A steps : Nat)
    (bounded : steps ≤ 10 * (b + 1) * (F + A + 1)) :
    2 * b + 3 + steps + 1 ≤ 16 * ((2 * b + 1 + F + A) + 1) ^ 2 := by
  let M := 2 * b + 1 + F + A
  have hb : b + 1 ≤ M + 1 := by dsimp [M]; omega
  have hs : F + A + 1 ≤ M + 1 := by dsimp [M]; omega
  have hp := Nat.mul_le_mul hb hs
  have hloop : steps ≤ 10 * (M + 1) ^ 2 := by
    calc
      steps ≤ 10 * (b + 1) * (F + A + 1) := bounded
      _ ≤ 10 * ((M + 1) * (M + 1)) := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 10 hp
      _ = 10 * (M + 1) ^ 2 := by rw [pow_two]
  have hsq : M + 1 ≤ (M + 1) ^ 2 := by nlinarith [Nat.zero_le (M * M)]
  change 2 * b + 3 + steps + 1 ≤ 16 * (M + 1) ^ 2
  omega

end BinPackingGap.ExtensionValidationMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionVerifierMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionVerifierMachine.Fields

open Turing
open BinPackingGames.Foundations.Complexity

inductive Block
  | bins | items | fixed
  deriving DecidableEq

inductive Field
  | bins | numerator | denominator
  deriving DecidableEq

protected abbrev Field.enumList : List Field := [.bins, .numerator, .denominator]

protected theorem Field.enumList_nodup : Field.enumList.Nodup := by decide

instance instFintypeField : Fintype Field where
  elems := ⟨Field.enumList, Field.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Mode
  | flag (field : Field)
  | digit (field : Field)
  | items
  | fixed
  deriving DecidableEq, Fintype

def Field.block : Field → Block
  | .bins => .bins
  | .numerator | .denominator => .items

def afterField : Field → Mode
  | .bins => .items
  | .numerator => .flag .denominator
  | .denominator => .items

def Mode.block : Mode → Block
  | .flag f | .digit f => f.block
  | .items => .items
  | .fixed => .fixed

def nextMode : Mode → Bool → Mode
  | .flag f, true => .digit f
  | .flag f, false => afterField f
  | .digit f, _ => .flag f
  | .items, true => .flag .numerator
  | .items, false => .fixed
  | .fixed, _ => .fixed

abbrev Words := Block → List Bool

def prepend (words : Words) (block : Block) (chunk : List Bool) : Words :=
  Function.update words block (chunk ++ words block)

@[simp] theorem prepend_nil (words : Words) (block : Block) :
    prepend words block [] = words := by
  simp [prepend]

theorem prepend_prepend (words : Words) (block : Block) (first second : List Bool) :
    prepend (prepend words block first) block second =
      prepend words block (second ++ first) := by
  funext k
  by_cases h : k = block
  · subst k; simp [prepend, List.append_assoc]
  · simp [prepend, h]

def run : Mode → Words → List Bool → Mode × Words
  | mode, words, [] => (mode, words)
  | mode, words, bit :: rest =>
      run (nextMode mode bit) (prepend words mode.block [bit]) rest

theorem run_fixed (input : List Bool) (words : Words) :
    run .fixed words input = (.fixed, prepend words .fixed input.reverse) := by
  induction input generalizing words with
  | nil => simp [run]
  | cons bit input ih =>
      simpa only [run, nextMode, Mode.block, prepend_prepend,
        List.reverse_cons] using ih (prepend words .fixed [bit])

def empty : Words := fun _ => []

def reversed (words : Words) : Words := fun block => (words block).reverse

@[simp] theorem reversed_reversed (words : Words) : reversed (reversed words) = words := by
  funext block
  simp [reversed]

def wordLength (words : Words) : Nat :=
  (words .bins).length + (words .items).length + (words .fixed).length

@[simp] theorem wordLength_empty : wordLength empty = 0 := rfl

@[simp] theorem wordLength_reversed (words : Words) :
    wordLength (reversed words) = wordLength words := by simp [wordLength, reversed]

inductive Label
  | scan | restoreBins | restoreItems | restoreFixed
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .restoreBins, .restoreItems,
  .restoreFixed]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Fin 7) := Bool
abbrev State := Mode × Option Bool

def scanFinish : TM2.Stmt Alphabet Label State :=
  .load (fun state => (nextMode state.1 (state.2.getD false), none))
    (.goto fun _ => .scan)

def tapes (input : List Bool) (saved output : Words) : Fin 7 → List Bool
  | 0 => input
  | 1 => saved .bins
  | 2 => saved .items
  | 3 => saved .fixed
  | 4 => output .bins
  | 5 => output .items
  | _ => output .fixed

theorem update_input (input replacement : List Bool) (saved output : Words) :
    Function.update (tapes input saved output) 0 replacement =
      tapes replacement saved output := by
  funext k; fin_cases k <;> rfl

theorem appendTrace {X : Type*} (f : X → X) {a b : Nat} {x y z : X}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, first, second]

end BinPackingGap.ExtensionVerifierMachine.Fields

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionVerifierPipeline
attribute [-instance] _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionCapacityOuterMachine

open Turing BinPackingGames.Foundations.Complexity

abbrev Tape := Fin 26
abbrev Alphabet (_ : Tape) := Bool

def allTapes : List Tape := List.ofFn id

inductive CopyKind
  | outerLabels | items | assignments
  deriving DecidableEq

protected abbrev CopyKind.enumList : List CopyKind := [.outerLabels, .items, .assignments]

protected theorem CopyKind.enumList_nodup : CopyKind.enumList.Nodup := by decide

instance instFintypeCopyKind : Fintype CopyKind where
  elems := ⟨CopyKind.enumList, CopyKind.enumList_nodup⟩
  complete x := by cases x <;> decide

def numberTapes : Fin 3 ↪ Tape := ⟨![24, 4, 25], by decide⟩

def copySource : CopyKind → Tape
  | .outerLabels => 23
  | .items => 22
  | .assignments => 23

def copyDestination : CopyKind → Tape
  | .outerLabels => 24
  | .items => 2
  | .assignments => 3

def resultTapes (result : Bool) : Tape → List Bool :=
  Function.update (fun _ => []) 0 [result]

noncomputable def roundBudget (inputLength : Nat) : Nat :=
  ExtensionCapacityMachine.timePolynomial.eval (2 * inputLength) + 6 * inputLength + 8

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 65536 * (Polynomial.X + Polynomial.C 1) ^ 4

theorem totalBudget_le (itemLength assignmentLength visits : Nat)
    (bounded : visits ≤ itemLength + assignmentLength) :
    visits * roundBudget (itemLength + assignmentLength) +
        itemLength + 4 * assignmentLength + 30 ≤
      timePolynomial.eval (itemLength + assignmentLength) := by
  have product := Nat.mul_le_mul_right
    (roundBudget (itemLength + assignmentLength)) bounded
  have linear : itemLength + 4 * assignmentLength ≤
      4 * (itemLength + assignmentLength) := by omega
  apply (Nat.add_le_add_right
    (show visits * roundBudget (itemLength + assignmentLength) +
        itemLength + 4 * assignmentLength ≤
      (itemLength + assignmentLength) * roundBudget (itemLength + assignmentLength) +
        4 * (itemLength + assignmentLength) by omega) 30).trans
  simp only [roundBudget, timePolynomial, ExtensionCapacityMachine.timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith [Nat.zero_le ((itemLength + assignmentLength) ^ 2),
    Nat.zero_le ((itemLength + assignmentLength) ^ 3),
    Nat.zero_le ((itemLength + assignmentLength) ^ 4)]

end BinPackingGap.ExtensionCapacityOuterMachine

namespace BinPackingGap.ExtensionVerifierMachine

open Turing BinPackingGames.Foundations.Complexity
open ExtensionMachineRegisters (Lens)

inductive Helper
  | pair | query | witness | fields | validation | agreement | capacity
  deriving DecidableEq

protected abbrev Helper.enumList : List Helper := [.pair, .query, .witness, .fields, .validation,
  .agreement, .capacity]

protected theorem Helper.enumList_nodup : Helper.enumList.Nodup := by decide

instance instFintypeHelper : Fintype Helper where
  elems := ⟨Helper.enumList, Helper.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev LocalTape : Helper → Type
  | .pair | .query | .witness => Fin 3
  | .fields => Fin 7
  | .validation => Fin 10
  | .agreement => Fin 2
  | .capacity => Fin 26

instance instFintypeLocalTape (h : Helper) : Fintype (LocalTape h) := by cases h <;> infer_instance
instance instDecidableEqLocalTape (h : Helper) : DecidableEq (LocalTape h) := by cases h <;> infer_instance

abbrev Tape := Fin 40
abbrev Alphabet (_ : Tape) := Bool

inductive Gate
  | query | witness | validation | agreement | capacity
  deriving DecidableEq

protected abbrev Gate.enumList : List Gate := [.query, .witness, .validation, .agreement,
  .capacity]

protected theorem Gate.enumList_nodup : Gate.enumList.Nodup := by decide

instance instFintypeGate : Fintype Gate where
  elems := ⟨Gate.enumList, Gate.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Copy
  | items | validationAssignments | agreementAssignments
  deriving DecidableEq

protected abbrev Copy.enumList : List Copy := [.items, .validationAssignments,
  .agreementAssignments]

protected theorem Copy.enumList_nodup : Copy.enumList.Nodup := by decide

instance instFintypeCopy : Fintype Copy where
  elems := ⟨Copy.enumList, Copy.enumList_nodup⟩
  complete x := by cases x <;> decide

end BinPackingGap.ExtensionVerifierMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionVerifierMachine

open Turing BinPackingGames.Foundations.Complexity

noncomputable def canonicalTime : Polynomial Nat :=
  ExtensionCapacityOuterMachine.timePolynomial + ExtensionValidationMachine.validationTime +
    Polynomial.C 10 * Polynomial.X + Polynomial.C 20

noncomputable def decisionTime : Polynomial Nat :=
  Polynomial.C 16 * (Polynomial.X + Polynomial.C 1) + canonicalTime

end BinPackingGap.ExtensionVerifierMachine

end OAI
end


