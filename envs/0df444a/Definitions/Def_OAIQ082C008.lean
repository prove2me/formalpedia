-- Prove2me | Definitions.Def_OAIQ082C008
-- name    : OAIQ082C008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:28:05.228158+00:00
-- url     : https://prove2.me/theorems/2061fcb9-9d06-4334-a87e-9cd6a6182b9a
-- title:
--   Definitions bundle OAIQ082C008 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 493 declarations of OpenAI's Lean: 245 definitions, 7 inductive types or structures, 7 instances and 234 theorems. The definitions and types are `OAI.BinPackingGap.BinaryPowerMachine.appendRuns`, `OAI.BinPackingGap.BinaryTallyMachine.instruction`, `OAI.BinPackingGap.BinaryToTallyMachine.State`, `OAI.BinPackingGap.BinaryToTallyMachine.guard`, `OAI.BinPackingGap.BinaryToTallyMachine.more`, `OAI.BinPackingGap.BinaryToTallyMachine.reset`, `OAI.BinPackingGap.BooleanTapeCode.convert`, `OAI.BinPackingGap.BooleanTapeCode.frame`, `OAI.BinPackingGap.BooleanTapeCode.framePayload`, `OAI.BinPackingGap.BooleanTapeCode.frameProgram`, `OAI.BinPackingGap.BooleanTapeCode.increment`, `OAI.BinPackingGap.BooleanTapeCode.transfer`, `OAI.BinPackingGap.CompetingTrees`, `OAI.BinPackingGap.CompetingTrees.ofAuxiliary`, `OAI.BinPackingGap.CompetingTrees.quotaTotal`, `OAI.BinPackingGap.Coverage.anchorItemsAt`, `OAI.BinPackingGap.Coverage.badAnchorsAt`, `OAI.BinPackingGap.Coverage.badRoleAnchors`, `OAI.BinPackingGap.Coverage.baselinePrefixAt`, `OAI.BinPackingGap.Coverage.completionPrefixAt`, `OAI.BinPackingGap.Coverage.coveringTuplesAt`, `OAI.BinPackingGap.Coverage.currentEdgeTuplesAt`, `OAI.BinPackingGap.Coverage.currentKeyItemsAt`, `OAI.BinPackingGap.Coverage.currentLongEdgeAt`, `OAI.BinPackingGap.Coverage.currentShortEdgeAt`, `OAI.BinPackingGap.Coverage.currentShortItemsAt`, `OAI.BinPackingGap.Coverage.currentShortMainAt`, `OAI.BinPackingGap.Coverage.deadlinePrefixAt`, `OAI.BinPackingGap.Coverage.displacedTuplesAt`, `OAI.BinPackingGap.Coverage.edgePrefixAt`, `OAI.BinPackingGap.Coverage.edgeTuplesAt`, `OAI.BinPackingGap.Coverage.goodTuplesAt`, `OAI.BinPackingGap.Coverage.jobRowPrefixAt`, `OAI.BinPackingGap.Coverage.keyPrefixAt`, `OAI.BinPackingGap.Coverage.mainJobPrefixAt`, `OAI.BinPackingGap.Coverage.mainTreePrefixAt`, `OAI.BinPackingGap.Coverage.mainTuplesAt`, `OAI.BinPackingGap.Coverage.roleItems`, `OAI.BinPackingGap.Coverage.treeRowPrefixAt`, `OAI.BinPackingGap.DropPackingBoundMachine.output` and 212 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_BinaryPowerMachine`, `BinPacking_Arithmetic_BinaryTallyMachine`, `BinPacking_Arithmetic_BinaryToTallyMachine`, `BinPacking_Arithmetic_PackingRegisterFrame`, `BinPacking_Hardness_LiteralSlotGraph`, `BinPacking_Inventory_CurrentMatches`, `BinPacking_Inventory_InventoryPrefixConservation`, `BinPacking_Inventory_InventoryScores`, `BinPacking_Machines_DropPackingBoundMachine`, `BinPacking_Machines_FrameEmitMachine`, `BinPacking_Machines_IntegerPackingArithmetic`, `BinPacking_Machines_PackingJobLoop`, `BinPacking_Machines_PackingPowerProgram`, `BinPacking_Machines_PackingVertexUpdate`, `BinPacking_Packing_FractionWidth`, `BinPacking_Packing_GoodAnchorBound`, `BinPacking_Packing_ItemEnumeration`, `BinPacking_Packing_PackingCoordinates`, `BinPacking_Packing_PackingScalar`, `BinPacking_Packing_PackingScalarExpression`, `BinPacking_Packing_PackingSelections`, `BinPacking_Search_ExtensionAgreementMachine`, `BinPacking_Search_ExtensionCapacityBounds`, `BinPacking_Search_ExtensionPairMachine`, `BinPacking_Search_ExtensionShapeMachine`, `BinPacking_Search_ExtensionValidationMachine`, `BinPacking_Search_ExtensionVerifierMachine`, `BinPacking_Search_ExtensionVerifierPipeline`, `BinPacking_Search_SearchInitialItemsMachine`, `BinPacking_Trees_IntegerTreeGeometry`, `BinPacking_Trees_InventoryFromTrees`, `BinPacking_Trees_TestGeometry`, `BinPacking_Trees_TreePruning`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C000`, `OAIQ082C001`, `OAIQ082C002` and `OAIQ082C003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C013`, `OAIQ082C014` and `OAIQ082C015`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C000
import Definitions.Def_OAIQ082C001
import Definitions.Def_OAIQ082C002
import Definitions.Def_OAIQ082C003

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryTallyMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.UnaryToBinaryMachine

open Turing BinPackingGames.Foundations.Complexity
open MachineComposition BinaryArithmetic
open BinPackingGames.Reduction.MachineTransfer

def increment : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: increment bits

def incrementCost : List Bool → Nat
  | [] => 2
  | false :: _ => 2
  | true :: bits => incrementCost bits + 2

def steps : Nat → Nat → Nat
  | 0, _ => 1
  | n + 1, initial => 1 + incrementCost initial.bits + steps n (initial + 1)

variable {K Λ A : Type} [DecidableEq K]

def instruction (source output scratch : K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .scan => .pop source (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (finish (some (labels .carry))) (finish exit))
  | .carry => .pop output (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.push scratch (fun _ => false) (finish (some (labels .carry))))
        (.push output (fun _ => true) (finish (some (labels .restore)))))
  | .restore => loopAt scratch output id false (labels .restore)
      (some (labels .scan))

variable (source output scratch : K)
variable (hSO : source ≠ output) (hSC : source ≠ scratch) (hOC : output ≠ scratch)

variable (labels : Label → Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction source output scratch labels exit l)
variable (base : K → List Bool) (ambient : A)

include hSO hSC hOC atLabels

omit [DecidableEq K] hSO hSC hOC atLabels in
theorem oneStepTrace {X : Type} {f : X → Option X} {a b : X}
    (h : f a = some b) : (advance f)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

end BinPackingGap.UnaryToBinaryMachine

namespace BinPackingGap.BinaryTallyMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinaryAddMachine (State clean)

variable {K Λ A : Type} [DecidableEq K]

def instruction (source output scratch : K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  UnaryToBinaryMachine.instruction (A := (A × Bool) × Option Bool)
    source output scratch labels exit

theorem stepAsPlainTrace {X : Type} {step : X → Option X} {a b : X}
    (h : step a = some b) : (advance step)^[1] (some a) = some b := h

end BinPackingGap.BinaryTallyMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryPowerMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
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

def appendRuns {X : Type} (step : X → Option X) {a b c : X} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) where
  steps := first.steps + second.steps
  evals_in_steps := by
    change (MachineComposition.advance step)^[first.steps + second.steps] (some a) = some c
    rw [Nat.add_comm, Function.iterate_add_apply]
    have hfirst := first.evals_in_steps
    have hsecond := second.evals_in_steps
    change (MachineComposition.advance step)^[first.steps] (some a) = some b at hfirst
    change (MachineComposition.advance step)^[second.steps] (some b) = some c at hsecond
    rw [hfirst]
    exact hsecond
  steps_le_m := Nat.add_le_add first.steps_le_m second.steps_le_m

theorem loopBudget_le (a r : Nat) (tally : List Bool) (width : Nat)
    (ha : a.size ≤ width) (hr : r.size + tally.length * a.size ≤ width) :
    loopBudget a r tally ≤ (tally.length + 1) * perIteration width := by
  induction tally generalizing r with
  | nil => simp [loopBudget, perIteration]
  | cons token tally ih =>
      have hp := BinaryArithmetic.size_mul_le a r
      have hnext : (a * r).size + tally.length * a.size ≤ width := by
        simp only [List.length_cons, Nat.add_mul] at hr
        omega
      have hbound := ih (a * r) hnext
      have hrs : r.size ≤ width := by omega
      have hps : (a * r).size ≤ width := by omega
      have hm := MachineComposition.natPolynomial_eval_mono BinaryMulMachine.timePolynomial
        (show a.size + r.size ≤ 2 * width by omega)
      have hb : bodyBudget a r ≤ perIteration width := by
        unfold bodyBudget perIteration
        omega
      simp only [loopBudget, List.length_cons]
      nlinarith

theorem budget_le_timePolynomial (a : Nat) (tally : List Bool) :
    1 + loopBudget a 1 tally ≤ timePolynomial.eval (a.size + tally.length) := by
  let width := (a.size + tally.length + 2) ^ 2
  have hs : 1 ≤ a.size + tally.length + 2 := by omega
  have hsq : a.size + tally.length + 2 ≤ width := le_self_pow hs (by decide)
  have hw1 : 1 ≤ width := hs.trans hsq
  have ha : a.size ≤ width := (show a.size ≤ a.size + tally.length + 2 by omega).trans hsq
  have hr : (1 : Nat).size + tally.length * a.size ≤ width := by
    simp only [Nat.size_one]
    dsimp [width]
    nlinarith
  have hloop := loopBudget_le a 1 tally width ha hr
  have hper : perIteration width ≤ 64 * width ^ 2 := by
    simp only [perIteration, BinaryMulMachine.timePolynomial, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    nlinarith
  have hcount : tally.length + 1 ≤ a.size + tally.length + 2 := by omega
  have hmul := Nat.mul_le_mul hcount hper
  have hfull := hloop.trans hmul
  simp only [timePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
  dsimp [width] at hfull
  have hs5 : 1 ≤ (a.size + tally.length + 2) ^ 5 := hs.trans (le_self_pow hs (by decide))
  nlinarith [hs5]

end BinPackingGap.BinaryPowerMachine

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

variable {Reg K : Type*}

@[simp] theorem registerTapes_slot (slot : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Reg → ℕ) (i : Reg ⊕ Fin 6) :
    registerTapes slot base values (slot i) = registerWords values i := by
  unfold registerTapes
  rw [dite_eq_left ⟨i, rfl⟩]
  congr 1
  exact slot.injective (Classical.choose_spec (show ∃ j, slot j = slot i from ⟨i, rfl⟩))

@[simp] theorem registerTapes_reg (slot : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Reg → ℕ) (r : Reg) :
    registerTapes slot base values (slot (Sum.inl r)) = (values r).bits :=
  registerTapes_slot slot base values (Sum.inl r)

@[simp] theorem registerTapes_scratch (slot : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Reg → ℕ) (i : Fin 6) :
    registerTapes slot base values (slot (Sum.inr i)) = [] :=
  registerTapes_slot slot base values (Sum.inr i)

theorem registerTapes_other (slot : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Reg → ℕ) (k : K)
    (hk : ¬ ∃ i, slot i = k) : registerTapes slot base values k = base k := by
  simp [registerTapes, hk]

theorem registerTapes_update [DecidableEq Reg] [DecidableEq K]
    (slot : (Reg ⊕ Fin 6) ↪ K) (base : K → List Bool) (values : Reg → ℕ)
    (d : Reg) (v : ℕ) :
    Function.update (registerTapes slot base values) (slot (Sum.inl d)) v.bits =
      registerTapes slot base (Function.update values d v) := by
  funext k
  by_cases hk : ∃ j, slot j = k
  · obtain ⟨j, rfl⟩ := hk
    cases j with
    | inl r =>
      by_cases hrd : r = d
      · subst r; simp
      · have hslot : slot (Sum.inl r) ≠ slot (Sum.inl d) :=
          slot.injective.ne (by simpa only [ne_eq, Sum.inl.injEq] using hrd)
        simp [Function.update_of_ne, hrd, hslot]
    | inr i =>
      have hslot : slot (Sum.inr i) ≠ slot (Sum.inl d) := slot.injective.ne (by simp)
      simp [Function.update_of_ne, hslot]
  · have hslot : k ≠ slot (Sum.inl d) := fun h => hk ⟨Sum.inl d, h.symm⟩
    simp [Function.update_of_ne hslot, registerTapes_other slot base _ k hk]

theorem registerTapes_mul_workspace (slot : (Reg ⊕ Fin 6) ↪ K)
    (op : Operands Reg) (base : K → List Bool) (values : Reg → ℕ)
    (i : Fin 9) (hi : 3 ≤ i.val) :
    registerTapes slot base values (mulSlots slot op i) = [] := by
  fin_cases i <;> simp_all

theorem registerTapes_add_workspace (slot : (Reg ⊕ Fin 6) ↪ K)
    (op : Operands Reg) (base : K → List Bool) (values : Reg → ℕ)
    (i : Fin 7) (hi : 2 ≤ i.val) (hout : i ≠ 5) :
    registerTapes slot base values (addSlots slot op i) = [] := by
  fin_cases i <;> simp_all

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

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

variable (source output : K) (distinct : source ≠ output)
variable (again : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabel : program again = instruction source output again exit)
variable (base : K → List Bool) (ambient : A)

include distinct in
theorem update_source (input acc next : List Bool) :
    Function.update (tapesAt source output base input acc) source next =
      tapesAt source output base next acc := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases ho : k = output
    · subst k; simp [tapesAt, hs]
    · simp [tapesAt, hs, ho]

theorem update_output (input acc next : List Bool) :
    Function.update (tapesAt source output base input acc) output next =
      tapesAt source output base input next := by
  simp [tapesAt]

include distinct atLabel

theorem step_nil (acc : List Bool) :
    TM2.step program
      ⟨some again, (ambient, none), tapesAt source output base [] acc⟩ =
      some ⟨exit, (ambient, none), tapesAt source output base [] (false :: acc)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLabel]
  cases exit <;>
    simp [instruction, finish, TM2.stepAux, tapesAt_src, tapesAt_dst,
      distinct, update_source, update_output]

theorem step_cons (bit : Bool) (input acc : List Bool) :
    TM2.step program
      ⟨some again, (ambient, none), tapesAt source output base (bit :: input) acc⟩ =
      some ⟨some again, (ambient, none),
        tapesAt source output base input (bit :: true :: acc)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atLabel]
  simp [instruction, finish, TM2.stepAux, tapesAt_src, tapesAt_dst,
    distinct, update_source, update_output]

theorem trace (input acc : List Bool) :
    (advance (TM2.step program))^[input.length + 1]
      (some ⟨some again, (ambient, none), tapesAt source output base input acc⟩) =
      some ⟨exit, (ambient, none), tapesAt source output base []
        ((BinPackingCompleteness.BinaryEncoding.frame input).reverse ++ acc)⟩ := by
  induction input generalizing acc with
  | nil =>
      simpa [advance, BinPackingCompleteness.BinaryEncoding.frame] using
        step_nil source output distinct again exit program atLabel base ambient acc
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_cons source output distinct again exit program atLabel base ambient]
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using ih (bit :: true :: acc)

end BinPackingGap.FrameEmitMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_LiteralSlotGraph
attribute [-instance] _root_.OAI.BinPackingGap.instFintypeGlobalSpecies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraph

open BinPackingGames.Foundations.Target

def vertexCount (F : Formula) : ℕ := 3 * F.clauses.length

abbrev Vertex (F : Formula) := Fin (vertexCount F)

def occurrence (F : Formula) (u : Vertex F) : Fin F.clauses.length :=
  ⟨u.val / 3, by have := u.isLt; unfold vertexCount at this; omega⟩

def slot (F : Formula) (u : Vertex F) : Fin 3 :=
  ⟨u.val % 3, Nat.mod_lt _ (by decide)⟩

def index (F : Formula) (c : Fin F.clauses.length) (j : Fin 3) : Vertex F :=
  ⟨3 * c.val + j.val, by
    have := c.isLt
    have := j.isLt
    unfold vertexCount
    omega⟩

@[simp] theorem occurrence_index (F : Formula) (c : Fin F.clauses.length) (j : Fin 3) :
    occurrence F (index F c j) = c := by
  apply Fin.ext
  dsimp [occurrence, index]
  have := j.isLt
  omega

@[simp] theorem slot_index (F : Formula) (c : Fin F.clauses.length) (j : Fin 3) :
    slot F (index F c j) = j := by
  apply Fin.ext
  dsimp [slot, index]
  have := j.isLt
  omega

@[simp] theorem index_occurrence_slot (F : Formula) (u : Vertex F) :
    index F (occurrence F u) (slot F u) = u := by
  apply Fin.ext
  dsimp [index, occurrence, slot]
  omega

def literal (F : Formula) (u : Vertex F) : Literal F.variables :=
  (F.clauses[occurrence F u])[slot F u]

@[simp] theorem literal_index (F : Formula) (c : Fin F.clauses.length) (j : Fin 3) :
    literal F (index F c j) = (F.clauses[c])[j] := by
  simp [literal]

def Conflict (F : Formula) (u v : Vertex F) : Prop :=
  occurrence F u = occurrence F v ∨
    ((literal F u).variableIndex = (literal F v).variableIndex ∧
      (literal F u).positive ≠ (literal F v).positive)

instance instDecidableConflict (F : Formula) (u v : Vertex F) : Decidable (Conflict F u v) := by
  unfold Conflict
  infer_instance

def edgeList (F : Formula) : List (Vertex F × Vertex F) :=
  ((List.finRange (vertexCount F)).product (List.finRange (vertexCount F))).filter
    (fun e => decide (e.1 < e.2 ∧ Conflict F e.1 e.2))

@[simp] theorem mem_edgeList (F : Formula) (u v : Vertex F) :
    (u, v) ∈ edgeList F ↔ u < v ∧ Conflict F u v := by
  simp [edgeList]

def graph (F : Formula) : GraphInput where
  n := vertexCount F
  edges := edgeList F
  ordered := by
    intro e he
    exact ((mem_edgeList F e.1 e.2).mp he).1
  distinct :=
    ((List.nodup_finRange (vertexCount F)).product
      (List.nodup_finRange (vertexCount F))).filter _

@[simp] theorem graph_n (F : Formula) : (graph F).n = 3 * F.clauses.length := rfl

end BinPackingGap.LiteralSlotGraph

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_FractionWidth
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace RawPacking

def loadFraction (r : RawInstance) (a : List ℕ) (j : ℕ) : ℕ × ℕ :=
  (r.zip a).foldl
    (fun acc qa => if qa.2 = j then addFraction acc qa.1 else acc) (0, 1)

theorem ratValue_addFraction (x y : ℕ × ℕ) (hx : 0 < x.2) (hy : 0 < y.2) :
    RawInstance.ratValue (addFraction x y) =
      RawInstance.ratValue x + RawInstance.ratValue y := by
  unfold RawInstance.ratValue addFraction
  simp only [Nat.cast_add, Nat.cast_mul]
  have hx' : (x.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hx)
  have hy' : (y.2 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hy)
  field_simp [hx', hy']

theorem foldFraction_spec (rows : List ((ℕ × ℕ) × ℕ)) (j : ℕ)
    (acc : ℕ × ℕ) (hacc : 0 < acc.2)
    (hrows : ∀ row ∈ rows, 0 < row.1.2) :
    0 < (rows.foldl
      (fun acc qa => if qa.2 = j then addFraction acc qa.1 else acc) acc).2 ∧
    RawInstance.ratValue (rows.foldl
      (fun acc qa => if qa.2 = j then addFraction acc qa.1 else acc) acc) =
      RawInstance.ratValue acc +
        (rows.map fun qa => if qa.2 = j then RawInstance.ratValue qa.1 else 0).sum := by
  induction rows generalizing acc with
  | nil => simpa using And.intro hacc (rfl : RawInstance.ratValue acc = _)
  | cons row rows ih =>
      have hhead : 0 < row.1.2 := hrows row (List.mem_cons_self ..)
      have htail : ∀ q ∈ rows, 0 < q.1.2 :=
        fun q hq => hrows q (List.mem_cons_of_mem _ hq)
      by_cases h : row.2 = j
      · have hrec := ih (addFraction acc row.1) (addFraction_den_pos _ _ hacc hhead) htail
        refine ⟨?_, ?_⟩
        · simpa only [List.foldl_cons, ite_eq_left h] using hrec.1
        · simpa only [List.foldl_cons, ite_eq_left h, List.map_cons, List.sum_cons,
            ratValue_addFraction _ _ hacc hhead, add_assoc] using hrec.2
      · have hrec := ih acc hacc htail
        simpa only [List.foldl_cons, ite_eq_right h, List.map_cons, List.sum_cons, zero_add]
          using hrec

theorem zip_den_pos {r : RawInstance} (hr : r.Valid) (a : List ℕ) :
    ∀ row ∈ r.zip a, 0 < row.1.2 := by
  intro row hrow
  exact RawInstance.den_pos hr (List.of_mem_zip hrow).1

theorem loadFraction_den_pos (r : RawInstance) (hr : r.Valid) (a : List ℕ) (j : ℕ) :
    0 < (loadFraction r a j).2 :=
  (foldFraction_spec (r.zip a) j (0, 1) (by decide) (zip_den_pos hr a)).1

theorem load_eq_loadFraction (r : RawInstance) (hr : r.Valid) (a : List ℕ) (j : ℕ) :
    load r a j = RawInstance.ratValue (loadFraction r a j) := by
  have h := (foldFraction_spec (r.zip a) j (0, 1) (by decide) (zip_den_pos hr a)).2
  simpa [load, loadFraction, RawInstance.ratValue] using h.symm

theorem load_le_one_iff (r : RawInstance) (hr : r.Valid) (a : List ℕ) (j : ℕ) :
    load r a j ≤ 1 ↔ (loadFraction r a j).1 ≤ (loadFraction r a j).2 := by
  rw [load_eq_loadFraction r hr a j]
  unfold RawInstance.ratValue
  rw [div_le_one₀ (Nat.cast_pos.mpr (loadFraction_den_pos r hr a j))]
  exact Nat.cast_le

theorem load_eq_zero_of_not_mem (r : RawInstance) (a : List ℕ) (j : ℕ)
    (hj : j ∉ a) : load r a j = 0 := by
  unfold load
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
  have hmem : row.2 ∈ a := (List.of_mem_zip hrow).2
  have hne : row.2 ≠ j := fun h => hj (h ▸ hmem)
  simp [hne]

theorem feasible_iff_mem_capacity (r : RawInstance) (p : RawPacking) :
    Feasible r p ↔
      p.assignments.length = r.length ∧
      (∀ j ∈ p.assignments, j < p.bins) ∧
      ∀ j ∈ p.assignments, load r p.assignments j ≤ 1 := by
  constructor
  · rintro ⟨hl, hr, hc⟩
    exact ⟨hl, hr, fun j hj => hc j (hr j hj)⟩
  · rintro ⟨hl, hr, hc⟩
    refine ⟨hl, hr, fun j _ => ?_⟩
    by_cases hj : j ∈ p.assignments
    · exact hc j hj
    · rw [load_eq_zero_of_not_mem _ _ _ hj]
      decide

end RawPacking

end BinPackingGap

namespace BinPackingGap.FractionWidth

theorem fold_overflow (r : RawInstance) (a : List ℕ) (j : ℕ) (x : ℕ × ℕ)
    (hr : r.Valid) (hx : x.2 < x.1) :
    let y := (r.zip a).foldl
      (fun acc qa => if qa.2 = j then RawPacking.addFraction acc qa.1 else acc) x
    y.2 < y.1 := by
  induction r generalizing a x with
  | nil => simpa using hx
  | cons q r ih =>
      have hr' : RawInstance.Valid r := fun z hz => hr z (List.mem_cons_of_mem q hz)
      have hq : 0 < q.2 := RawInstance.den_pos hr (List.mem_cons_self ..)
      cases a with
      | nil => simpa using hx
      | cons b a =>
          simp only [List.zip_cons_cons, List.foldl_cons]
          by_cases hb : b = j
          · simp only [ite_eq_left hb]
            exact ih a (RawPacking.addFraction x q) hr' (addFraction_overflow hx hq)
          · simp only [ite_eq_right hb]
            exact ih a x hr' hx

end BinPackingGap.FractionWidth

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

variable {K Label Big Small : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem advance_transport (lens : Lens Big Small) (base : Big)
    (source : Label → Stmt Γ Label Small) (c : Option (Cfg Γ Label Small)) :
    MachineComposition.advance (step (program lens source)) (c.map (configuration lens base)) =
      (MachineComposition.advance (step source) c).map (configuration lens base) := by
  cases c with
  | none => rfl
  | some c => exact step_transport lens base source c

theorem iterate_transport (lens : Lens Big Small) (base : Big)
    (source : Label → Stmt Γ Label Small) (steps : Nat) (c : Option (Cfg Γ Label Small)) :
    (MachineComposition.advance (step (program lens source)))^[steps]
        (c.map (configuration lens base)) =
      ((MachineComposition.advance (step source))^[steps] c).map (configuration lens base) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply', ih, advance_transport,
        Function.iterate_succ_apply']

theorem trace (lens : Lens Big Small) (base : Big)
    (source : Label → Stmt Γ Label Small) (steps : Nat)
    (start finish : Cfg Γ Label Small)
    (run : (MachineComposition.advance (step source))^[steps] (some start) = some finish) :
    (MachineComposition.advance (step (program lens source)))^[steps]
      (some (configuration lens base start)) = some (configuration lens base finish) := by
  change (MachineComposition.advance (step (program lens source)))^[steps]
      ((some start).map (configuration lens base)) = (some finish).map (configuration lens base)
  rw [iterate_transport, run]

def execution (lens : Lens Big Small) (base : Big)
    (source : Label → Stmt Γ Label Small)
    {start : Cfg Γ Label Small} {finish : Option (Cfg Γ Label Small)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program lens source))
      (configuration lens base start) (finish.map (configuration lens base)) budget where
  steps := run.steps
  evals_in_steps := by
    have executed := run.evals_in_steps
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish at executed
    change (MachineComposition.advance (step (program lens source)))^[run.steps]
      ((some start).map (configuration lens base)) = finish.map (configuration lens base)
    rw [iterate_transport, executed]
  steps_le_m := run.steps_le_m

def equivExecution (e : Small ≃ Big) (target : Label → Stmt Γ Label Big)
    {start : Cfg Γ Label Small} {finish : Option (Cfg Γ Label Small)} {budget : Nat}
    (run : StateTransition.EvalsToInTime
      (step (program (Lens.ofEquiv e.symm) target)) start finish budget) :
    StateTransition.EvalsToInTime (step target) (equivConfiguration e start)
      (finish.map (equivConfiguration e)) budget := by
  have mapped : configuration (Γ := Γ) (Label := Label) (Lens.ofEquiv e) (e start.var) =
      equivConfiguration e := by
    funext c
    exact configuration_ofEquiv e _ c
  simpa only [program_ofEquiv_symm, mapped] using
    execution (Lens.ofEquiv e) (e start.var)
      (program (Lens.ofEquiv e.symm) target) run

theorem equivTrace (e : Small ≃ Big) (target : Label → Stmt Γ Label Big)
    (steps : Nat) (start finish : Cfg Γ Label Small)
    (run : (MachineComposition.advance
      (step (program (Lens.ofEquiv e.symm) target)))^[steps] (some start) = some finish) :
    (MachineComposition.advance (step target))^[steps]
      (some (equivConfiguration e start)) = some (equivConfiguration e finish) := by
  simpa only [program_ofEquiv_symm, configuration_ofEquiv] using
    trace (Lens.ofEquiv e) (e start.var) (program (Lens.ofEquiv e.symm) target)
      steps start finish run

end BinPackingGap.ExtensionMachineRegisters

namespace BinPackingGap.ExtensionMachinePlacement

open Turing BinPackingGames.Foundations.Complexity
open ExtensionMachineRegisters (Lens)

variable {K K' Label Label' Small Big : Type}

variable [DecidableEq K] [DecidableEq K']

def execution (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label → Label') (exit : Option Label') (lens : Lens Big Small)
    (base : Big) (extra : K' → List Bool)
    (source : Label → TM2.Stmt (fun _ : K => Bool) Label Small)
    (target : Label' → TM2.Stmt (fun _ : K' => Bool) Label' Big)
    (atLabels : ∀ l, target (labels l) = statement tape labels exit lens (source l))
    {start finish : TM2.Cfg (fun _ : K => Bool) Label Small} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) start (some finish) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration view labels exit lens base extra start)
      (some (configuration view labels exit lens base extra finish)) budget :=
  MachineComposition.liftExecutionInTime _ _ _
    (step_simulation tape view left right labels exit lens base extra source target atLabels) run

end BinPackingGap.ExtensionMachinePlacement

namespace BinPackingGap.ExtensionNatMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction.MachineTransfer

abbrev State (A : Type) := BinaryAddMachine.State A

def scannerEquiv (A : Type) : BinPackingCompleteness.BinaryNameMachine.State (A × Bool) ≃ State A where
  toFun s := ((s.1, s.2.1), s.2.2)
  invFun s := (s.1.1, s.1.2, s.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable {K Λ A : Type} [DecidableEq K]

def statement (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (accepted rejected : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .scan =>
      ExtensionMachineRegisters.statement
        (ExtensionMachineRegisters.Lens.ofEquiv (scannerEquiv A))
        (BinPackingCompleteness.BinaryNameMachine.scan (slots 0) (slots 2)
          (labels .scan) (some (labels .restore)) rejected)
  | .restore => loopAt (slots 2) (slots 1) id false (labels .restore) accepted

def orderEquiv (A : Type) : BinaryOrderMachine.State (A × Bool) ≃ State (A × Ordering) where
  toFun
    | ((((ambient, carry), order), left), right) => ((((ambient, order), carry), left), right)
  invFun
    | ((((ambient, order), carry), left), right) => ((((ambient, carry), order), left), right)
  left_inv _ := rfl
  right_inv _ := rfl

end BinPackingGap.ExtensionNatMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPowerProgram
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.FiniteTapeProgram

section

open Turing BinPackingGames.Foundations.Complexity MachineComposition

variable (K S : Type)

variable {K S}

variable [DecidableEq K]

def Code.instruction {Λ : Type} : (c : Code (K := K) (S := S)) →
    (c.Label → Λ) → Option Λ → c.Label → TM2.Stmt (fun _ : K => Bool) Λ S
  | .atom a, _, exit, () => a.statement (jump exit)
  | .routine _ _ _ program, labels, exit, l =>
      MachineSubroutine.statement labels exit (program l)
  | .seq a b, labels, _, .inl l =>
      a.instruction (fun l => labels (.inl l)) (some (labels (.inr b.entry))) l
  | .seq _ b, labels, exit, .inr l =>
      b.instruction (fun l => labels (.inr l)) exit l
  | .branch p a b, labels, _, .inl () =>
      .branch p (jump (some (labels (.inr (.inl a.entry)))))
        (jump (some (labels (.inr (.inr b.entry)))))
  | .branch _ a _, labels, exit, .inr (.inl l) =>
      a.instruction (fun l => labels (.inr (.inl l))) exit l
  | .branch _ _ b, labels, exit, .inr (.inr l) =>
      b.instruction (fun l => labels (.inr (.inr l))) exit l
  | .loop g p a, labels, exit, .inl () =>
      g.statement (.branch p (jump (some (labels (.inr a.entry)))) (jump exit))
  | .loop _ _ a, labels, _, .inr l =>
      a.instruction (fun l => labels (.inr l)) (some (labels (.inl ()))) l

inductive Exec : Code (K := K) (S := S) → Data K S → Nat → Data K S → Prop
  | atom (a : Action K S) (d : Data K S) : Exec (.atom a) d 1 (a.eval d)
  | routine {L : Type} (finite : Fintype L) (main : L)
      (program : L → TM2.Stmt (fun _ : K => Bool) L S) (d e : Data K S) (n : Nat) :
      (advance (TM2.step program))^[n]
        (some ⟨some main, d.state, d.tapes⟩) = some ⟨none, e.state, e.tapes⟩ →
      Exec (.routine L finite main program) d n e
  | seq {a b d e f n m} : Exec a d n e → Exec b e m f → Exec (.seq a b) d (n + m) f
  | branch_true {p a b d e n} : p d.state = true → Exec a d n e →
      Exec (.branch p a b) d (n + 1) e
  | branch_false {p a b d e n} : p d.state = false → Exec b d n e →
      Exec (.branch p a b) d (n + 1) e
  | loop_false {g p a d} : p (g.eval d).state = false → Exec (.loop g p a) d 1 (g.eval d)
  | loop_true {g p a d e f n m} : p (g.eval d).state = true →
      Exec a (g.eval d) n e → Exec (.loop g p a) e m f →
      Exec (.loop g p a) d (n + m + 1) f

variable [Fintype K] [Fintype S]

def Code.machine (c : Code (K := K) (S := S)) (input output : K) (initial : S) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := c.Label
  main := c.entry
  σ := S
  initialState := initial
  m := c.instruction id none

end

open Turing BinPackingGames.Foundations.Complexity MachineComposition

end BinPackingGap.FiniteTapeProgram

namespace BinPackingGap.BooleanTapeCode

open Turing FiniteTapeProgram BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

variable {K A : Type} [DecidableEq K]

def transfer (source destination : K) : Program K A :=
  .routine Unit inferInstance () (fun _ =>
    MachineTransfer.loopAt source destination id false () none)

theorem transfer_exec (source destination : K) (different : source ≠ destination)
    (base : K → List Bool) (s : State A) :
    Exec (transfer source destination) ⟨s, base⟩ ((base source).length + 1)
      ⟨(s.1, none), MachineTransfer.tapesAt source destination base []
        ((base source).reverse ++ base destination)⟩ := by
  rcases s with ⟨ambient, register⟩
  apply Exec.routine
  have run := MachineTransfer.transferAt_fromTapes source destination different id false () none
    (fun _ : Unit => MachineTransfer.loopAt source destination id false () none)
    rfl base ambient register
  have next_eq : MachineTransfer.nextAt (σ := A × Unit) (Γ := fun _ : K => Bool) destination
      (fun _ : Unit => MachineTransfer.loopAt source destination id false () none) =
      MachineComposition.advance (TM2.step
        (fun _ : Unit => MachineTransfer.loopAt source destination id false () none)) := rfl
  rw [next_eq] at run
  simpa only [List.map_id_fun, id_eq] using run

def convert (source destination scratch : K) : Program K A :=
  .routine UnaryToBinaryMachine.Label inferInstance .scan
    (UnaryToBinaryMachine.instruction source destination scratch id none)

def frameProgram (source scratch destination : K) :
    FrameLabel → TM2.Stmt (fun _ : K => Bool) FrameLabel (State A)
  | .scan => MachineTransducerCopy.scanLoop source scratch ()
      (fun _ b => .emit b) .restore
  | .emit b => MachineTransducerCopy.emitter destination (fun _ _ => ())
      (fun _ b => [true, b]) .scan () b
  | .restore => MachineTransfer.loopAt scratch source id false .restore none

def framePayload (source scratch destination : K) : Program K A :=
  .routine FrameLabel inferInstance .scan (frameProgram source scratch destination)

theorem framePayload_output (word : List Bool) :
    MachineTransducer.output (fun (_ : Unit) _ => ()) (fun _ b => [true, b]) () word =
      word.flatMap (fun b => [true, b]) := by
  induction word with
  | nil => rfl
  | cons b word ih => simp [MachineTransducer.output, ih]

def frame (source scratch destination : K) : Program K A :=
  .seq (framePayload source scratch destination)
    (.atom (.push destination (fun _ => false) .done))

theorem frame_eq (word : List Bool) :
    BinPackingCompleteness.BinaryEncoding.frame word = word.flatMap (fun b => [true, b]) ++ [false] := by
  induction word with
  | nil => rfl
  | cons b word ih => simp [BinPackingCompleteness.BinaryEncoding.frame, ih]

def increment (binary unary scratch : K) : Program K A :=
  .seq (.atom (.push unary (fun _ => false)
    (.push unary (fun _ => true) (.load (fun s => (s.1, none)) .done))))
    (convert unary binary scratch)

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

abbrev State (A : Type) := BinaryAddMachine.State A

variable {K A : Type} [DecidableEq K]

def guard (slot : (Reg ⊕ Fin 6) ↪ K) : Action K (State A) :=
  .peek (slot (.inl .counter)) (fun s head => (s.1, head)) .done

def more (s : State A) : Bool := s.2.isSome

def reset : Action K (State A) :=
  .load (fun s => BinaryAddMachine.clean s.1.1.1) .done

theorem guard_zero (slot : (Reg ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (n : Nat) (ambient : A) :
    (guard slot).eval
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n 0)⟩ =
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base (running n 0)⟩ := by
  simp [guard, Action.eval, running, BinaryAddMachine.clean, BinaryAddMachine.state]

theorem registerTapes_update_external (slot : (Reg ⊕ Fin 6) ↪ K) (output : K)
    (outside : ∀ q, slot q ≠ output) (base : K → List Bool)
    (values : Reg → Nat) (word : List Bool) :
    Function.update (registerTapes slot base values) output word =
      registerTapes slot (Function.update base output word) values := by
  funext k
  by_cases hk : ∃ q, slot q = k
  · obtain ⟨q, rfl⟩ := hk
    simp [outside q]
  · by_cases hko : k = output
    · subst k
      simp [registerTapes_other slot _ _ _ hk]
    · simp [hko, registerTapes_other slot _ _ _ hk]

end BinPackingGap.BinaryToTallyMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalar
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
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

def primaryTotal (p : Packing I b) (subclass : I.Item → Subclass) (j : Fin b) : ℤ :=
  ∑ i ∈ p.binItems j, primaryScore (subclass i)

def IsTableBin (p : Packing I b) (subclass : I.Item → Subclass) (j : Fin b) : Prop :=
  (p.binItems j).card = 5 ∧ p.primaryTotal subclass j = 0

abbrev TableBin (p : Packing I b) (subclass : I.Item → Subclass) :=
  {j : Fin b // p.IsTableBin subclass j}

instance instFintypeTableBin (p : Packing I b) (subclass : I.Item → Subclass) :
    Fintype (p.TableBin subclass) := Fintype.ofFinite _

theorem table_pattern (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) :
    ∃ pat : Pattern, ∃ e : Role ≃ p.binItems t.val,
      ∀ r, subclass (e r).val = patternSubclass pat r := by
  classical
  let e : Fin 5 ≃ p.binItems t.val :=
    (Finset.equivFinOfCardEq t.property.1).symm
  have hz : (∑ i : Fin 5, primaryScore (subclass (e i).val)) = 0 := by
    rw [e.sum_comp (fun i : p.binItems t.val => primaryScore (subclass i.val))]
    change (∑ i ∈ (p.binItems t.val).attach, primaryScore (subclass i.val)) = 0
    rw [Finset.sum_attach (p.binItems t.val) (fun i => primaryScore (subclass i))]
    exact t.property.2
  obtain ⟨pat, perm, hp⟩ :=
    (sum_primaryScore_eq_zero_iff_pattern (fun i => subclass (e i).val)).mp hz
  refine ⟨pat, perm.symm.trans e, ?_⟩
  intro r
  simpa using hp (perm.symm r)

def tablePattern (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) : Pattern :=
  Classical.choose (p.table_pattern subclass t)

def tableEquiv (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) : Role ≃ p.binItems t.val :=
  Classical.choose (Classical.choose_spec (p.table_pattern subclass t))

theorem tableEquiv_subclass (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    subclass (p.tableEquiv subclass t r).val =
      patternSubclass (p.tablePattern subclass t) r :=
  Classical.choose_spec (Classical.choose_spec (p.table_pattern subclass t)) r

def itemAtRole (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) : I.Item :=
  (p.tableEquiv subclass t r).val

theorem itemAtRole_subclass (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    subclass (p.itemAtRole subclass t r) =
      patternSubclass (p.tablePattern subclass t) r :=
  p.tableEquiv_subclass subclass t r

@[simp] theorem itemAtRole_role (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    (subclass (p.itemAtRole subclass t r)).role = r := by
  rw [p.itemAtRole_subclass subclass t r, patternSubclass_role]

def IsGoodTableBin (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) (t : p.TableBin subclass) : Prop :=
  label (p.itemAtRole subclass t .x) = label (p.itemAtRole subclass t .anchor) ∧
    label (p.itemAtRole subclass t .«local») =
      label (p.itemAtRole subclass t .anchor)

end Packing

end

open scoped BigOperators

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_CurrentMatches
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap
namespace Coverage

variable {I : Instance} {b n : ℕ}

def goodTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset (p.TableBin cls) := by
  classical
  exact Finset.univ.filter fun t => p.IsGoodTableBin cls label t ∧
    label (p.itemAtRole cls t .anchor) = some v

def mainTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset (p.TableBin cls) := by
  classical
  exact (goodTuplesAt p cls label v).filter fun t => p.tablePattern cls t ≠ .edgeJob

def edgeTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset (p.TableBin cls) := by
  classical
  exact (goodTuplesAt p cls label v).filter fun t => p.tablePattern cls t = .edgeJob

@[simp] theorem mem_goodTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (t : p.TableBin cls) :
    t ∈ goodTuplesAt p cls label v ↔ p.IsGoodTableBin cls label t ∧
      label (p.itemAtRole cls t .anchor) = some v := by
  classical
  simp [goodTuplesAt]

@[simp] theorem mem_mainTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (t : p.TableBin cls) :
    t ∈ mainTuplesAt p cls label v ↔ p.IsGoodTableBin cls label t ∧
      label (p.itemAtRole cls t .anchor) = some v ∧
        p.tablePattern cls t ≠ .edgeJob := by
  classical
  simp [mainTuplesAt, and_assoc]

@[simp] theorem mem_edgeTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (t : p.TableBin cls) :
    t ∈ edgeTuplesAt p cls label v ↔ p.IsGoodTableBin cls label t ∧
      label (p.itemAtRole cls t .anchor) = some v ∧
        p.tablePattern cls t = .edgeJob := by
  classical
  simp [edgeTuplesAt, and_assoc]

def roleItems (p : Packing I b) (cls : I.Item → Subclass)
    (s : Finset (p.TableBin cls)) (role : Role) : Finset I.Item :=
  s.image fun t => p.itemAtRole cls t role

def anchorItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => (cls i).role = .anchor ∧ label i = some v

@[simp] theorem mem_anchorItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (i : I.Item) :
    i ∈ anchorItemsAt (I := I) cls label v ↔
      (cls i).role = .anchor ∧ label i = some v := by
  classical
  simp [anchorItemsAt]

def badAnchorsAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) : Finset I.Item :=
  anchorItemsAt (I := I) cls label v \
    roleItems p cls (goodTuplesAt p cls label v) .anchor

@[simp] theorem mem_badAnchorsAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n) (i : I.Item) :
    i ∈ badAnchorsAt p cls label v ↔
      i ∈ anchorItemsAt (I := I) cls label v ∧
        i ∉ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
  simp only [badAnchorsAt, Finset.mem_sdiff]

def baselinePrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t => baseline (p.itemAtRole cls t .x) ≤ a

def completionPrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (finish : p.TableBin cls → ℚ) (a : ℚ) : Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t => finish t ≤ a

def coveringTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (finish : p.TableBin cls → ℚ) (a : ℚ) :
    Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t =>
    finish t ≤ a ∧ a < baseline (p.itemAtRole cls t .x)

def deadlinePrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .z ∧ label i = some v ∧ deadline i ≤ a

@[simp] theorem mem_deadlinePrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (deadline : I.Item → ℚ) (a : ℚ) (i : I.Item) :
    i ∈ deadlinePrefixAt (I := I) cls label v deadline a ↔
      cls i = .z ∧ label i = some v ∧ deadline i ≤ a := by
  classical
  simp [deadlinePrefixAt]

def jobRowPrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .s ∧ label i = some v ∧ baseline i ≤ a

def treeRowPrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i =>
    (cls i = .tp ∨ cls i = .tm) ∧ label i = some v ∧ baseline i ≤ a

def keyPrefixAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .y ∧ label i = some v ∧ keyBaseline i ≤ a

def edgePrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) :=
  (edgeTuplesAt p cls label v).filter fun t => keyBaseline (p.itemAtRole cls t .anchor) ≤ a

def mainJobPrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) := by
  classical
  exact (baselinePrefixAt p cls label v baseline a).filter fun t =>
    cls (p.itemAtRole cls t .x) = .s

def mainTreePrefixAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (a : ℚ) : Finset (p.TableBin cls) := by
  classical
  exact (baselinePrefixAt p cls label v baseline a).filter fun t =>
    cls (p.itemAtRole cls t .x) ≠ .s

def currentKeyItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (current : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i =>
    cls i = .y ∧ label i = some v ∧ keyBaseline i = current

def currentEdgeTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (current : ℚ) : Finset (p.TableBin cls) :=
  (edgeTuplesAt p cls label v).filter fun t =>
    keyBaseline (p.itemAtRole cls t .anchor) = current

def displacedTuplesAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (current : ℚ) : Finset (p.TableBin cls) :=
  (currentEdgeTuplesAt p cls label v keyBaseline current).filter fun t =>
    baseline (p.itemAtRole cls t .x) < current

def currentShortMainAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) :
    Finset (p.TableBin cls) :=
  (mainTuplesAt p cls label v).filter fun t =>
    baseline (p.itemAtRole cls t .x) = current ∧ short (p.itemAtRole cls t .x) = true

def currentShortEdgeAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) :
    Finset (p.TableBin cls) :=
  (currentEdgeTuplesAt p cls label v keyBaseline current).filter fun t =>
    baseline (p.itemAtRole cls t .x) = current ∧ short (p.itemAtRole cls t .x) = true

def currentLongEdgeAt (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline keyBaseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) :
    Finset (p.TableBin cls) :=
  (currentEdgeTuplesAt p cls label v keyBaseline current).filter fun t =>
    baseline (p.itemAtRole cls t .x) = current ∧ short (p.itemAtRole cls t .x) ≠ true

def currentShortItemsAt (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (baseline : I.Item → ℚ) (short : I.Item → Bool) (current : ℚ) : Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => cls i = .s ∧ label i = some v ∧
    baseline i = current ∧ short i = true

end Coverage
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

def itemNumerator {n : ℕ} (geom : ℕ) (subclass : Subclass)
    (label : Option (Fin n)) (W : ℤ) : ℤ :=
  signedNumerator n geom (primaryScore subclass) (secondaryScore subclass label) W

def rawItem {n : ℕ} (geom : ℕ) (subclass : Subclass)
    (label : Option (Fin n)) (W : ℤ) : ℕ × ℕ :=
  ((itemNumerator geom subclass label W).toNat, sizeDenominator n geom)

end BinPackingGap.IntegerPackingArithmetic

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_IntegerTreeGeometry
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

namespace UniformTree

instance nodeNonempty (T : UniformTree) : Nonempty T.Node := ⟨T.root⟩

theorem node_card_pos (T : UniformTree) : 0 < Fintype.card T.Node :=
  Fintype.card_pos

def leaf {T : UniformTree} (v : T.Node) : Prop := v.val ∈ T.leaves

theorem depth_le_height {T : UniformTree} (v : T.Node) : depth v ≤ T.height :=
  T.length_le_height v.property

theorem eq_root_iff_depth_eq_zero {T : UniformTree} (v : T.Node) :
    v = T.root ↔ depth v = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    exact List.length_eq_zero_iff.mp h

def branchBound (T : UniformTree) : ℕ :=
  max 1 (T.leaves.sup (fun l => l.toFinset.sup id))

theorem label_le_branchBound {T : UniformTree} (v : T.Node) {a : ℕ}
    (ha : a ∈ v.val) : a ≤ T.branchBound := by
  obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp v.property
  calc
    a ≤ l.toFinset.sup id :=
      Finset.le_sup (f := id) (List.mem_toFinset.mpr (h.subset ha))
    _ ≤ T.leaves.sup (fun l => l.toFinset.sup id) :=
      Finset.le_sup (f := fun l : List ℕ => l.toFinset.sup id) hl
    _ ≤ T.branchBound := le_max_right _ _

end UniformTree

end BinPackingGap

namespace BinPackingGap.TreeGeometry

open _root_.OAI.BinPackingGap.Geometry UniformTree

theorem boundedAddress_node {T : UniformTree} (v : T.Node) {D : ℕ}
    (hD : T.branchBound ≤ D) : BoundedAddress D v.val :=
  fun _ ha => (label_le_branchBound v ha).trans hD

@[simp] theorem left_nil (m R D : ℕ) (s : Side) :
    left m R D s [] = rootOffset s := by simp [left, pathSum]

@[simp] theorem width_nil (m R D : ℕ) : width m R D [] = 1 := by simp [width]

@[simp] theorem right_nil (m R D : ℕ) (s : Side) :
    right m R D s [] = rootOffset s + 1 := by simp [right]

theorem width_of_ne_nil (m R D : ℕ) {w : List ℕ} (hw : w ≠ []) :
    width m R D w = lambda m R D w.length := by simp [width, hw]

theorem width_pos (m R D : ℕ) (w : List ℕ) : 0 < width m R D w := by
  by_cases hw : w = []
  · simp [width, hw]
  · simpa [width, hw] using lambda_pos m R D w.length

theorem left_lt_right (m R D : ℕ) (s : Side) (w : List ℕ) :
    left m R D s w < right m R D s w := by
  exact lt_add_of_pos_right _ (width_pos m R D w)

theorem pathSum_append (m R D k : ℕ) (u v : List ℕ) :
    pathSum m R D k (u ++ v) =
      pathSum m R D k u + pathSum m R D (k + u.length) v := by
  induction u generalizing k with
  | nil => simp [pathSum]
  | cons a u ih =>
    simp only [List.cons_append, pathSum, ih, List.length_cons]
    rw [show k + 1 + u.length = k + (u.length + 1) by omega]
    ring

theorem left_append_singleton (m R D : ℕ) (s : Side) (w : List ℕ) (a : ℕ) :
    left m R D s (w ++ [a]) =
      left m R D s w + 4 * (a : ℚ) * lambda m R D (w.length + 1) := by
  simp only [left, pathSum_append, Nat.zero_add, pathSum, add_zero]
  ring

theorem right_append_singleton (m R D : ℕ) (s : Side) (w : List ℕ) (a : ℕ) :
    right m R D s (w ++ [a]) =
      left m R D s w + (4 * (a : ℚ) + 1) * lambda m R D (w.length + 1) := by
  have hn : w ++ [a] ≠ [] := by simp
  rw [right, left_append_singleton, width_of_ne_nil m R D hn]
  simp only [List.length_append, List.length_singleton]
  ring

theorem child_endpoints (m R D : ℕ) (s : Side) (w : List ℕ) {a : ℕ}
    (ha : a ≤ D) :
    left m R D s w ≤ left m R D s (w ++ [a]) ∧
      right m R D s (w ++ [a]) ≤ right m R D s w := by
  have hscale := lambda_pos m R D (w.length + 1)
  have hcast : (a : ℚ) ≤ D := by exact_mod_cast ha
  have ha0 : (0 : ℚ) ≤ a := Nat.cast_nonneg a
  constructor
  · rw [left_append_singleton]
    nlinarith
  · rw [right_append_singleton, right]
    have hmul : (4 * (a : ℚ) + 1) * lambda m R D (w.length + 1) ≤
        (4 * (D : ℚ) + 1) * lambda m R D (w.length + 1) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hscale.le
    by_cases hw : w = []
    · subst w
      have hfirst := first_children_lt_tenth m R D
      simp only [List.length_nil, Nat.zero_add, width_nil] at *
      linarith
    · rw [width_of_ne_nil m R D hw]
      have hchild := children_succ_lt_parent m R D w.length
      linarith

theorem append_endpoints (m R D : ℕ) (s : Side) (u v : List ℕ)
    (hv : BoundedAddress D v) :
    left m R D s u ≤ left m R D s (u ++ v) ∧
      right m R D s (u ++ v) ≤ right m R D s u := by
  induction v generalizing u with
  | nil => simp
  | cons a v ih =>
    have hc := child_endpoints m R D s u (hv a (by simp))
    have ht := ih (u ++ [a]) (fun b hb => hv b (by simp [hb]))
    have heq : (u ++ [a]) ++ v = u ++ a :: v := by simp [List.append_assoc]
    rw [heq] at ht
    exact ⟨hc.1.trans ht.1, ht.2.trans hc.2⟩

theorem prefix_endpoints (m R D : ℕ) (s : Side) {u v : List ℕ}
    (h : u.IsPrefix v) (hv : BoundedAddress D v) :
    left m R D s u ≤ left m R D s v ∧ right m R D s v ≤ right m R D s u := by
  obtain ⟨t, rfl⟩ := h
  exact append_endpoints m R D s u t (fun a ha => hv a (by simp [ha]))

def commonBranchBound (plus minus : UniformTree) : ℕ :=
  max plus.branchBound minus.branchBound

theorem plus_branch_le (plus minus : UniformTree) :
    plus.branchBound ≤ commonBranchBound plus minus := le_max_left _ _

theorem minus_branch_le (plus minus : UniformTree) :
    minus.branchBound ≤ commonBranchBound plus minus := le_max_right _ _

end BinPackingGap.TreeGeometry

namespace BinPackingGap.IntegerPackingArithmetic

def rootOffsetNumerator : TreeGeometry.Side → ℕ
  | .plus => 0
  | .minus => 4

def treeLeftNumerator (m R D L : ℕ) (side : TreeGeometry.Side)
    (w : List ℕ) : ℕ :=
  rootOffsetNumerator side * geomDenominator m R D L + pathNumerator D L 0 w

def treeRightNumerator (m R D L : ℕ) (side : TreeGeometry.Side)
    (w : List ℕ) : ℕ :=
  treeLeftNumerator m R D L side w +
    if w = [] then geomDenominator m R D L else localNumerator D L w.length

end BinPackingGap.IntegerPackingArithmetic

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryScores
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

structure InventoryData where
  graph : GraphInput
  plus : UniformTree
  minus : UniformTree
  d : ℕ
  R : ℕ
  L : ℕ
  quota : ℕ → ℕ
  k : ℕ

namespace InventoryData

variable (D : InventoryData)

abbrev Vertex := D.graph.Vertex
abbrev Edge := D.graph.Edge
abbrev Position := D.graph.Edge × Fin D.R
abbrev JobCopy (v : D.Vertex) := D.graph.JobCopy D.R D.d v
abbrev Depth := {ell : ℕ // ell ∈ Finset.Icc 1 D.L}

def P : ℕ := ∑ ell ∈ Finset.Icc 1 D.L, D.quota ell

def tPlus : ℕ := D.d * Fintype.card D.plus.Node + D.P
def tMinus : ℕ := D.d * Fintype.card D.minus.Node
def t : ℕ := D.tPlus + D.tMinus
def J (v : D.Vertex) : ℕ := D.d * D.R * D.graph.degree v
def B : ℕ := ∑ v : D.Vertex, (D.t + 2 * D.J v)

abbrev TreeRow :=
  (D.plus.Node × Fin D.d) ⊕ ((D.minus.Node × Fin D.d) ⊕ Fin D.P)

abbrev RowAt (v : D.Vertex) := D.TreeRow ⊕ (Bool × D.JobCopy v)

abbrev MBase (v : D.Vertex) := D.TreeRow ⊕ D.JobCopy v

abbrev AnchorAt (v : D.Vertex) := D.MBase v ⊕ D.JobCopy v

abbrev PositiveLocal := Σ ell : D.Depth, Fin (D.quota ell.val)

abbrev ZeroLocalAt (v : D.Vertex) := Fin (D.t - D.P) ⊕ D.JobCopy v
abbrev DMAt (v : D.Vertex) := D.PositiveLocal ⊕ D.ZeroLocalAt v
abbrev LocalAt (v : D.Vertex) := D.DMAt v ⊕ D.JobCopy v

abbrev LocalBin (v : D.Vertex) := D.MBase v ⊕ D.JobCopy v

def plusSlots : ℕ := ∑ v : D.Vertex, (D.tPlus + D.J v)
def minusSlots : ℕ := D.graph.n * D.tMinus
def treeFlags : ℕ := D.graph.n * D.t
def jobFlags : ℕ := ∑ v : D.Vertex, D.J v

end InventoryData

namespace InventoryData

variable (D : InventoryData)

def globalStock : GlobalSpecies D.graph → ℕ
  | .up true => D.d * D.k
  | .up false => D.plusSlots - D.d * D.k
  | .um true => D.d * (D.graph.n - D.k)
  | .um false => D.minusSlots - D.d * (D.graph.n - D.k)
  | .edge _ _ => D.d * D.R

def flagStock : FlagSpecies → ℕ
  | .tree => D.treeFlags
  | .main => D.jobFlags
  | .edge => D.jobFlags

abbrev GlobalCopy := Σ s : GlobalSpecies D.graph, Fin (D.globalStock s)
abbrev FlagCopy := Σ s : FlagSpecies, Fin (D.flagStock s)

def RoleCopies : Role → Type
  | .x => Σ v : D.Vertex, D.RowAt v
  | .anchor => Σ v : D.Vertex, D.AnchorAt v
  | .«global» => D.GlobalCopy
  | .«local» => Σ v : D.Vertex, D.LocalAt v
  | .flag => D.FlagCopy

instance roleCopiesFintype (r : Role) : Fintype (D.RoleCopies r) := by
  cases r <;> dsimp [RoleCopies] <;> infer_instance

abbrev Item := Σ r : Role, D.RoleCopies r

def itemRole (i : D.Item) : Role := i.1

def itemLabel : D.Item → Option D.Vertex
  | ⟨.x, x⟩ => some x.1
  | ⟨.anchor, a⟩ => some a.1
  | ⟨.«global», _⟩ => none
  | ⟨.«local», a⟩ => some a.1
  | ⟨.flag, _⟩ => none

def treeSubclass : D.TreeRow → Subclass
  | .inl _ => .tp
  | .inr (.inl _) => .tm
  | .inr (.inr _) => .tp

def rowSubclass {v : D.Vertex} : D.RowAt v → Subclass
  | .inl t => D.treeSubclass t
  | .inr _ => .s

def itemSubclass : D.Item → Subclass
  | ⟨.x, ⟨_, r⟩⟩ => D.rowSubclass r
  | ⟨.anchor, ⟨_, .inl _⟩⟩ => .z
  | ⟨.anchor, ⟨_, .inr _⟩⟩ => .y
  | ⟨.«global», ⟨.up _, _⟩⟩ => .up
  | ⟨.«global», ⟨.um _, _⟩⟩ => .um
  | ⟨.«global», ⟨.edge _ _, _⟩⟩ => .w
  | ⟨.«local», ⟨_, .inl _⟩⟩ => .dm
  | ⟨.«local», ⟨_, .inr _⟩⟩ => .dg
  | ⟨.flag, ⟨.tree, _⟩⟩ => .ft
  | ⟨.flag, ⟨.main, _⟩⟩ => .fm
  | ⟨.flag, ⟨.edge, _⟩⟩ => .fg

def rowShort {v : D.Vertex} : D.RowAt v → Bool
  | .inl _ => false
  | .inr r => r.1

def jobPosition {v : D.Vertex} (j : D.JobCopy v) : D.Position :=
  (j.1.1.val.1, j.1.2)

end InventoryData

namespace InventoryData

variable (D : InventoryData)

theorem card_treeRow : Fintype.card D.TreeRow = D.t := by
  simp [TreeRow, t, tPlus, tMinus, Nat.mul_comm, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

theorem card_jobCopy (v : D.Vertex) : Fintype.card (D.JobCopy v) = D.J v :=
  D.graph.card_jobCopy D.R D.d v

theorem card_rowAt (v : D.Vertex) : Fintype.card (D.RowAt v) = D.t + 2 * D.J v := by
  change Fintype.card (D.TreeRow ⊕ (Bool × D.JobCopy v)) = _
  rw [Fintype.card_sum, D.card_treeRow, Fintype.card_prod, Fintype.card_bool,
    D.card_jobCopy]

theorem card_mBase (v : D.Vertex) : Fintype.card (D.MBase v) = D.t + D.J v := by
  change Fintype.card (D.TreeRow ⊕ D.JobCopy v) = _
  rw [Fintype.card_sum, D.card_treeRow, D.card_jobCopy]

theorem card_anchorAt (v : D.Vertex) :
    Fintype.card (D.AnchorAt v) = D.t + 2 * D.J v := by
  change Fintype.card (D.MBase v ⊕ D.JobCopy v) = _
  rw [Fintype.card_sum, D.card_mBase, D.card_jobCopy]
  omega

theorem P_le_t : D.P ≤ D.t := by
  dsimp [t, tPlus, tMinus]
  omega

theorem d_le_tPlus : D.d ≤ D.tPlus := by
  have h := Nat.mul_le_mul_left D.d (D.plus.node_card_pos)
  simpa [tPlus] using (show D.d ≤ D.d * Fintype.card D.plus.Node + D.P by omega)

theorem d_le_tMinus : D.d ≤ D.tMinus := by
  have h := Nat.mul_le_mul_left D.d (D.minus.node_card_pos)
  simpa [tMinus] using h

theorem two_mul_d_le_t_sub_P : 2 * D.d ≤ D.t - D.P := by
  have hp := Nat.mul_le_mul_left D.d (D.plus.node_card_pos)
  have hm := D.d_le_tMinus
  dsimp [t, tPlus, tMinus] at *
  omega

theorem card_positiveLocal : Fintype.card D.PositiveLocal = D.P := by
  classical
  simp only [PositiveLocal, Fintype.card_sigma, Fintype.card_fin]
  exact Finset.sum_coe_sort (Finset.Icc 1 D.L) D.quota

theorem card_zeroLocalAt (v : D.Vertex) :
    Fintype.card (D.ZeroLocalAt v) = D.t + D.J v - D.P := by
  simp only [ZeroLocalAt, Fintype.card_sum, Fintype.card_fin, card_jobCopy]
  have h := D.P_le_t
  omega

theorem card_dmAt (v : D.Vertex) : Fintype.card (D.DMAt v) = D.t + D.J v := by
  change Fintype.card (D.PositiveLocal ⊕ D.ZeroLocalAt v) = _
  rw [Fintype.card_sum, D.card_positiveLocal, D.card_zeroLocalAt]
  have h := D.P_le_t
  omega

theorem card_localAt (v : D.Vertex) : Fintype.card (D.LocalAt v) = D.t + 2 * D.J v := by
  change Fintype.card (D.DMAt v ⊕ D.JobCopy v) = _
  rw [Fintype.card_sum, D.card_dmAt, D.card_jobCopy]
  omega

theorem sum_J : (∑ v : D.Vertex, D.J v) = 2 * D.d * D.graph.edges.length * D.R := by
  simpa only [D.card_jobCopy] using D.graph.sum_card_jobCopy D.R D.d

theorem plusSlots_eq : D.plusSlots = D.graph.n * D.tPlus + ∑ v : D.Vertex, D.J v := by
  simp [plusSlots, Finset.sum_add_distrib, Finset.sum_const]

theorem B_eq : D.B = D.graph.n * D.t + 2 * ∑ v : D.Vertex, D.J v := by
  simp [B, Finset.sum_add_distrib, Finset.sum_const, Finset.mul_sum]

theorem B_closed : D.B = D.graph.n * D.t + 4 * D.d * D.graph.edges.length * D.R := by
  rw [B_eq, sum_J]
  ring

theorem unitPlus_le_stock (hk : D.k ≤ D.graph.n) : D.d * D.k ≤ D.plusSlots := by
  calc
    D.d * D.k ≤ D.d * D.graph.n := Nat.mul_le_mul_left D.d hk
    _ ≤ D.graph.n * D.tPlus := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left D.graph.n D.d_le_tPlus
    _ ≤ D.plusSlots := by rw [plusSlots_eq]; omega

theorem unitMinus_le_stock : D.d * (D.graph.n - D.k) ≤ D.minusSlots := by
  calc
    D.d * (D.graph.n - D.k) ≤ D.d * D.graph.n :=
      Nat.mul_le_mul_left D.d (Nat.sub_le _ _)
    _ ≤ D.minusSlots := by
      simpa [minusSlots, Nat.mul_comm] using
        Nat.mul_le_mul_left D.graph.n D.d_le_tMinus

theorem up_species_total (hk : D.k ≤ D.graph.n) :
    D.globalStock (.up true) + D.globalStock (.up false) = D.plusSlots := by
  dsimp [globalStock]
  exact Nat.add_sub_of_le (D.unitPlus_le_stock hk)

theorem um_species_total :
    D.globalStock (.um true) + D.globalStock (.um false) = D.minusSlots := by
  dsimp [globalStock]
  exact Nat.add_sub_of_le D.unitMinus_le_stock

theorem card_globalCopy (hk : D.k ≤ D.graph.n) : Fintype.card D.GlobalCopy = D.B := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [GlobalSpecies.sum_univ]
  rw [D.up_species_total hk]
  rw [show D.plusSlots + D.globalStock (.um true) + D.globalStock (.um false) =
    D.plusSlots + D.minusSlots by rw [Nat.add_assoc, D.um_species_total]]
  simp only [globalStock, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [D.plusSlots_eq, D.B_eq, D.sum_J]
  dsimp [minusSlots, t]
  ring

theorem card_flagCopy : Fintype.card D.FlagCopy = D.B := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [FlagSpecies.sum_univ]
  dsimp [flagStock, treeFlags, jobFlags]
  rw [D.B_eq]
  ring

theorem card_roleCopies (hk : D.k ≤ D.graph.n) (r : Role) :
    Fintype.card (D.RoleCopies r) = D.B := by
  cases r with
  | x => simp [RoleCopies, Fintype.card_sigma, D.card_rowAt, B]
  | anchor => simp [RoleCopies, Fintype.card_sigma, D.card_anchorAt, B]
  | «global» => exact D.card_globalCopy hk
  | «local» => simp [RoleCopies, Fintype.card_sigma, D.card_localAt, B]
  | flag => exact D.card_flagCopy

theorem card_item (hk : D.k ≤ D.graph.n) : Fintype.card D.Item = 5 * D.B := by
  rw [Fintype.card_sigma, Role.sum_univ]
  simp only [D.card_roleCopies hk]
  omega

end InventoryData

end BinPackingGap

noncomputable section

namespace BinPackingGap
namespace InventoryData

variable (D : InventoryData)

def keyItem (j : Σ v : D.Vertex, D.JobCopy v) : D.Item :=
  ⟨.anchor, ⟨j.1, .inr j.2⟩⟩

def keyData : D.Item → Option (Σ v : D.Vertex, D.JobCopy v)
  | ⟨.anchor, ⟨v, .inr j⟩⟩ => some ⟨v, j⟩
  | _ => none

@[simp] theorem keyData_keyItem (j : Σ v : D.Vertex, D.JobCopy v) :
    D.keyData (D.keyItem j) = some j := by cases j; rfl

@[simp] theorem keyItem_role (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemRole (D.keyItem j) = .anchor := rfl

@[simp] theorem keyItem_subclass (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemSubclass (D.keyItem j) = .y := rfl

@[simp] theorem keyItem_label (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemLabel (D.keyItem j) = some j.1 := rfl

def edgeResourceItem (w : (D.Edge × Bool) × Fin (D.d * D.R)) : D.Item :=
  ⟨.«global», ⟨.edge w.1.1 w.1.2, w.2⟩⟩

def edgeResourceData : D.Item → Option ((D.Edge × Bool) × Fin (D.d * D.R))
  | ⟨.«global», ⟨.edge e permit, copy⟩⟩ => some ((e, permit), copy)
  | _ => none

@[simp] theorem edgeResourceData_edgeResourceItem
    (w : (D.Edge × Bool) × Fin (D.d * D.R)) :
    D.edgeResourceData (D.edgeResourceItem w) = some w := by cases w; rfl

end InventoryData
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_GoodAnchorBound
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

open scoped BigOperators

variable {I : Instance} {b n : ℕ}

abbrev RoleItem (cls : I.Item → Subclass) (r : Role) :=
  {i : I.Item // (cls i).role = r}

structure RoleLabelData (cls : I.Item → Subclass) (label : I.Item → Option (Fin n)) where
  row : RoleItem cls .x → Fin n
  anchor : RoleItem cls .anchor → Fin n
  localLabel : RoleItem cls .«local» → Fin n
  row_spec : ∀ i, label i.val = some (row i)
  anchor_spec : ∀ i, label i.val = some (anchor i)
  local_spec : ∀ i, label i.val = some (localLabel i)
  global_spec : ∀ i : RoleItem cls .«global», label i.val = none
  flag_spec : ∀ i : RoleItem cls .flag, label i.val = none

namespace Packing

def roleItemAt (p : Packing I b) (cls : I.Item → Subclass) (r : Role)
    (t : p.TableBin cls) : RoleItem cls r :=
  ⟨p.itemAtRole cls t r, p.itemAtRole_role cls t r⟩

end Packing

namespace Coverage

def badRoleAnchors (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (L : RoleLabelData cls label) (v : Fin n) :
    Finset (RoleItem cls .anchor) := by
  classical
  exact LabelConservation.badAnchors L.anchor L.row L.localLabel
    (p.roleItemAt cls .anchor) (p.roleItemAt cls .x) (p.roleItemAt cls .«local») v

end Coverage
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingSelections
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
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

def subclass (e : D.Item ≃ I.Item) : I.Item → Subclass :=
  D.itemSubclass ∘ e.symm

def label (e : D.Item ≃ I.Item) : I.Item → Option D.Vertex :=
  D.itemLabel ∘ e.symm

def globalResources (e : D.Item ≃ I.Item) (s : GlobalSpecies D.graph) :
    Finset I.Item := by
  classical
  exact Finset.univ.image fun i : Fin (D.globalStock s) => e ⟨.«global», ⟨s, i⟩⟩

@[simp] theorem mem_globalResources (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (x : I.Item) :
    x ∈ globalResources e s ↔
      ∃ i : Fin (D.globalStock s), e ⟨.«global», ⟨s, i⟩⟩ = x := by
  classical
  simp [globalResources]

def fundedTuples (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (v : D.Vertex) : Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    p.itemAtRole (subclass e) t .«global» ∈ globalResources e s

@[simp] theorem mem_fundedTuples (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (v : D.Vertex) (t : p.TableBin (subclass e)) :
    t ∈ fundedTuples p e s v ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
      p.itemAtRole (subclass e) t .«global» ∈ globalResources e s := by
  classical
  simp [fundedTuples]

def positiveLocalResources (e : D.Item ≃ I.Item) (v : D.Vertex) : Finset I.Item := by
  classical
  exact Finset.univ.image fun i : D.PositiveLocal =>
    e ⟨.«local», ⟨v, Sum.inl (Sum.inl i)⟩⟩

@[simp] theorem mem_positiveLocalResources (e : D.Item ≃ I.Item)
    (v : D.Vertex) (x : I.Item) :
    x ∈ positiveLocalResources e v ↔
      ∃ i : D.PositiveLocal, e ⟨.«local», ⟨v, Sum.inl (Sum.inl i)⟩⟩ = x := by
  classical
  simp [positiveLocalResources]

end PackingCounts
end BinPackingGap

end

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TestGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def geometryBound : ℕ := TreeGeometry.commonBranchBound D.plus D.minus

theorem plus_branch_le_geometryBound : D.plus.branchBound ≤ D.geometryBound :=
  TreeGeometry.plus_branch_le D.plus D.minus

theorem minus_branch_le_geometryBound : D.minus.branchBound ≤ D.geometryBound :=
  TreeGeometry.minus_branch_le D.plus D.minus

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingCoordinates
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def treeBaseline : D.TreeRow → ℚ
  | .inl (node, _) =>
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus node.val
  | .inr (.inl (node, _)) =>
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus node.val
  | .inr (.inr _) => 1

def rowBaseline {v : D.Vertex} : D.RowAt v → ℚ
  | .inl r => D.treeBaseline r
  | .inr (_, j) => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j)

def mainBaseline {v : D.Vertex} : D.MBase v → ℚ
  | .inl r => D.treeBaseline r
  | .inr j => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j)

def treeDeadline : D.TreeRow → ℚ
  | .inl (node, _) =>
      if node.val ∈ D.plus.leaves then
        TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus node.val
      else TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus node.val
  | .inr (.inl (node, _)) =>
      if node.val ∈ D.minus.leaves then
        TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus node.val
      else TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus node.val
  | .inr (.inr _) => 1

def deadline {v : D.Vertex} : D.MBase v → ℚ
  | .inl r => D.treeDeadline r
  | .inr j => Geometry.jobLeft D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)

def rowCoordinate {v : D.Vertex} (r : D.RowAt v) : ℚ :=
  D.rowBaseline r - if D.rowShort r then
    Geometry.delta D.graph.edges.length D.R D.geometryBound D.L else 0

def anchorCoordinate {v : D.Vertex} : D.AnchorAt v → ℚ
  | .inl z => -D.deadline z
  | .inr j => -Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) -
      Geometry.beta D.graph.edges.length D.R (D.jobPosition j).1

def globalLength : D.GlobalCopy → ℚ
  | ⟨.up one, _⟩ => if one then 1 else 0
  | ⟨.um one, _⟩ => if one then 1 else 0
  | ⟨.edge _ _, _⟩ => 0

def globalCoordinate : D.GlobalCopy → ℚ
  | ⟨.up one, _⟩ => -(if one then 1 else 0)
  | ⟨.um one, _⟩ => -(if one then 1 else 0)
  | ⟨.edge e permit, _⟩ => Geometry.beta D.graph.edges.length D.R e +
      if permit then 0 else Geometry.delta D.graph.edges.length D.R D.geometryBound D.L

def localLength {v : D.Vertex} : D.LocalAt v → ℚ
  | .inl (.inl ⟨ell, _⟩) =>
      Geometry.lambda D.graph.edges.length D.R D.geometryBound ell.val
  | _ => 0

def localCoordinate {v : D.Vertex} (i : D.LocalAt v) : ℚ := -D.localLength i

def itemCoordinate : D.Item → ℚ
  | ⟨.x, ⟨_, r⟩⟩ => D.rowCoordinate r
  | ⟨.anchor, ⟨_, a⟩⟩ => D.anchorCoordinate a
  | ⟨.«global», u⟩ => D.globalCoordinate u
  | ⟨.«local», ⟨_, l⟩⟩ => D.localCoordinate l
  | ⟨.flag, _⟩ => 0

theorem node_endpoint_bounds {T : UniformTree} (node : T.Node)
    (side : TreeGeometry.Side) (hT : T.branchBound ≤ D.geometryBound) :
    (0 ≤ TreeGeometry.left D.graph.edges.length D.R D.geometryBound side node.val ∧
      TreeGeometry.left D.graph.edges.length D.R D.geometryBound side node.val ≤ 5) ∧
    (0 ≤ TreeGeometry.right D.graph.edges.length D.R D.geometryBound side node.val ∧
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound side node.val ≤ 5) := by
  have hroot := TreeGeometry.prefix_endpoints D.graph.edges.length D.R D.geometryBound side
    (u := []) (v := node.val) List.nil_prefix (TreeGeometry.boundedAddress_node node hT)
  simp only [TreeGeometry.left_nil, TreeGeometry.right_nil] at hroot
  have hwidth := TreeGeometry.left_lt_right D.graph.edges.length D.R D.geometryBound side node.val
  cases side <;> simp only [TreeGeometry.rootOffset] at hroot <;>
    constructor <;> constructor <;> linarith [hroot.1, hroot.2]

theorem treeBaseline_bounds (r : D.TreeRow) :
    0 ≤ D.treeBaseline r ∧ D.treeBaseline r ≤ 5 := by
  rcases r with p | p | padding
  · exact (D.node_endpoint_bounds p.1 .plus D.plus_branch_le_geometryBound).2
  · exact (D.node_endpoint_bounds p.1 .minus D.minus_branch_le_geometryBound).2
  · norm_num [treeBaseline]

theorem treeDeadline_bounds (r : D.TreeRow) :
    0 ≤ D.treeDeadline r ∧ D.treeDeadline r ≤ 5 := by
  rcases r with p | p | padding
  · have h := D.node_endpoint_bounds p.1 .plus D.plus_branch_le_geometryBound
    dsimp only [treeDeadline]
    split_ifs
    · exact h.1
    · exact h.2
  · have h := D.node_endpoint_bounds p.1 .minus D.minus_branch_le_geometryBound
    dsimp only [treeDeadline]
    split_ifs
    · exact h.1
    · exact h.2
  · norm_num [treeDeadline]

theorem deadline_bounds {v : D.Vertex} (r : D.MBase v) :
    0 ≤ D.deadline r ∧ D.deadline r ≤ 5 := by
  rcases r with tree | job
  · exact D.treeDeadline_bounds tree
  · have hl := Geometry.one_tenth_lt_jobLeft D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition job)
    have hu := Geometry.jobLeft_lt_baseline D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition job)
    have hb := Geometry.job_baseline_lt_one D.graph.edges.length D.R (D.jobPosition job)
    change 0 ≤ Geometry.jobLeft _ _ _ _ _ ∧ Geometry.jobLeft _ _ _ _ _ ≤ 5
    constructor <;> linarith

theorem rowCoordinate_bounds {v : D.Vertex} (r : D.RowAt v) :
    0 ≤ D.rowCoordinate r ∧ D.rowCoordinate r ≤ 5 := by
  rcases r with tree | ⟨short, job⟩
  · simpa only [rowCoordinate, rowBaseline, rowShort, Bool.false_eq_true, ite_false,
      sub_zero] using D.treeBaseline_bounds tree
  · have hb := Geometry.baseline_range D.graph.edges.length D.R (D.jobPosition job)
    have hd := Geometry.delta_lt_gap D.graph.edges.length D.R D.geometryBound D.L
    have hg := Geometry.gap_le_one_sixteen D.graph.edges.length D.R
    have hd0 := Geometry.delta_nonneg D.graph.edges.length D.R D.geometryBound D.L
    cases short <;>
      simp only [rowCoordinate, rowBaseline, rowShort, Bool.false_eq_true, ite_false,
        ite_true, if_true, sub_zero] <;>
      constructor <;> linarith [hb.1, hb.2]

theorem anchorCoordinate_bounds {v : D.Vertex} (a : D.AnchorAt v) :
    -5 ≤ D.anchorCoordinate a ∧ D.anchorCoordinate a ≤ 0 := by
  rcases a with deadline | key
  · have h := D.deadline_bounds deadline
    change -5 ≤ -D.deadline deadline ∧ -D.deadline deadline ≤ 0
    constructor <;> linarith [h.1, h.2]
  · have hb := Geometry.baseline_range D.graph.edges.length D.R (D.jobPosition key)
    have hβ0 := Geometry.beta_nonneg D.graph.edges.length D.R (D.jobPosition key).1
    have hβ := Geometry.beta_lt_one_sixteen D.graph.edges.length D.R (D.jobPosition key).1
    dsimp only [anchorCoordinate]
    constructor <;> linarith [hb.1, hb.2]

theorem globalCoordinate_bounds (u : D.GlobalCopy) :
    -1 ≤ D.globalCoordinate u ∧ D.globalCoordinate u ≤ 1 := by
  rcases u with ⟨species, copy⟩
  cases species with
  | up one => cases one <;> norm_num [globalCoordinate]
  | um one => cases one <;> norm_num [globalCoordinate]
  | edge edge permit =>
      have hβ0 := Geometry.beta_nonneg D.graph.edges.length D.R edge
      have hβ := Geometry.beta_lt_one_sixteen D.graph.edges.length D.R edge
      have hd0 := Geometry.delta_nonneg D.graph.edges.length D.R D.geometryBound D.L
      have hd := Geometry.delta_lt_gap D.graph.edges.length D.R D.geometryBound D.L
      have hg := Geometry.gap_le_one_sixteen D.graph.edges.length D.R
      cases permit <;>
        simp only [globalCoordinate, Bool.false_eq_true, ite_false, ite_true, if_true, add_zero] <;>
        constructor <;> linarith

theorem localLength_nonneg {v : D.Vertex} (i : D.LocalAt v) : 0 ≤ D.localLength i := by
  rcases i with (⟨ell, copy⟩ | zero) | edge
  · exact Geometry.lambda_nonneg D.graph.edges.length D.R D.geometryBound ell.val
  · exact le_rfl
  · exact le_rfl

theorem localLength_le_lambda_one {v : D.Vertex} (i : D.LocalAt v) :
    D.localLength i ≤ Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 := by
  rcases i with (⟨ell, copy⟩ | zero) | edge
  · exact Geometry.lambda_antitone D.graph.edges.length D.R D.geometryBound
      (Finset.mem_Icc.mp ell.property).1
  · exact Geometry.lambda_nonneg D.graph.edges.length D.R D.geometryBound 1
  · exact Geometry.lambda_nonneg D.graph.edges.length D.R D.geometryBound 1

theorem localLength_le_one {v : D.Vertex} (i : D.LocalAt v) : D.localLength i ≤ 1 :=
  (D.localLength_le_lambda_one i).trans
    (Geometry.lambda_le_one D.graph.edges.length D.R D.geometryBound 1)

theorem localCoordinate_bounds {v : D.Vertex} (i : D.LocalAt v) :
    -1 ≤ D.localCoordinate i ∧ D.localCoordinate i ≤ 0 := by
  have h0 := D.localLength_nonneg i
  have h1 := D.localLength_le_one i
  unfold localCoordinate
  constructor <;> linarith

theorem itemCoordinate_bounds (i : D.Item) :
    -5 ≤ D.itemCoordinate i ∧ D.itemCoordinate i ≤ 5 := by
  rcases i with ⟨role, i⟩
  cases role with
  | x =>
      rcases i with ⟨v, r⟩
      have h := D.rowCoordinate_bounds r
      change -5 ≤ D.rowCoordinate r ∧ D.rowCoordinate r ≤ 5
      exact ⟨by linarith [h.1], h.2⟩
  | anchor =>
      rcases i with ⟨v, a⟩
      have h := D.anchorCoordinate_bounds a
      change -5 ≤ D.anchorCoordinate a ∧ D.anchorCoordinate a ≤ 5
      exact ⟨h.1, by linarith [h.2]⟩
  | «global» =>
      have h := D.globalCoordinate_bounds i
      change -5 ≤ D.globalCoordinate i ∧ D.globalCoordinate i ≤ 5
      constructor <;> linarith [h.1, h.2]
  | «local» =>
      rcases i with ⟨v, l⟩
      have h := D.localCoordinate_bounds l
      change -5 ≤ D.localCoordinate l ∧ D.localCoordinate l ≤ 5
      constructor <;> linarith [h.1, h.2]
  | flag => norm_num [itemCoordinate]

theorem itemCoordinate_abs_le_six (i : D.Item) : |D.itemCoordinate i| ≤ 6 := by
  have h := D.itemCoordinate_bounds i
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

def stateRowEquiv (v : D.Vertex) (selected : Bool) : D.LocalBin v ≃ D.RowAt v where
  toFun
    | .inl (.inl t) => .inl t
    | .inl (.inr j) => .inr (!selected, j)
    | .inr j => .inr (selected, j)
  invFun
    | .inl t => .inl (.inl t)
    | .inr (short, j) => if short = selected then .inr j else .inl (.inr j)
  left_inv i := by
    rcases i with (t | j) | j <;> cases selected <;> simp
  right_inv r := by
    rcases r with t | ⟨b, j⟩
    · rfl
    · cases b <;> cases selected <;> simp

@[simp] theorem stateRowEquiv_tree (v : D.Vertex) (selected : Bool) (t : D.TreeRow) :
    D.stateRowEquiv v selected (.inl (.inl t)) = .inl t := rfl

@[simp] theorem stateRowEquiv_mainJob (v : D.Vertex) (selected : Bool) (j : D.JobCopy v) :
    D.stateRowEquiv v selected (.inl (.inr j)) = .inr (!selected, j) := rfl

@[simp] theorem stateRowEquiv_edgeJob (v : D.Vertex) (selected : Bool) (j : D.JobCopy v) :
    D.stateRowEquiv v selected (.inr j) = .inr (selected, j) := rfl

def stateMainRow (v : D.Vertex) (selected : Bool) (b : D.MBase v) : D.RowAt v :=
  D.stateRowEquiv v selected (.inl b)

@[simp] theorem stateMainRow_baseline (v : D.Vertex) (selected : Bool) (b : D.MBase v) :
    D.rowBaseline (D.stateMainRow v selected b) = D.mainBaseline b := by
  rcases b with t | j <;> rfl

def stateMainGlobalSpecies {v : D.Vertex} (selected : Bool) :
    D.MBase v → GlobalSpecies D.graph
  | .inl (.inl (node, _)) => .up (selected && decide (node = D.plus.root))
  | .inl (.inr (.inl (node, _))) => .um (!selected && decide (node = D.minus.root))
  | .inl (.inr (.inr _)) => .up false
  | .inr _ => .up false

def globalSpeciesLength : GlobalSpecies D.graph → ℚ
  | .up one => if one then 1 else 0
  | .um one => if one then 1 else 0
  | .edge _ _ => 0

def stateMainLength {v : D.Vertex} (selected : Bool) (b : D.MBase v) : ℚ :=
  D.globalSpeciesLength (D.stateMainGlobalSpecies selected b)

def fundedRoot {v : D.Vertex} (selected : Bool) (j : Fin D.d) : D.MBase v :=
  if selected then .inl (.inl (D.plus.root, j))
  else .inl (.inr (.inl (D.minus.root, j)))

@[simp] theorem stateMainLength_fundedRoot {v : D.Vertex} (selected : Bool) (j : Fin D.d) :
    D.stateMainLength selected (D.fundedRoot (v := v) selected j) = 1 := by
  cases selected <;> simp [fundedRoot, stateMainLength, stateMainGlobalSpecies,
    globalSpeciesLength]

structure LocalState (v : D.Vertex) (selected : Bool) where
  localEquiv : D.MBase v ≃ D.DMAt v
  anchorEquiv : D.MBase v ≃ D.MBase v
  completion_le_deadline : ∀ b,
    D.rowCoordinate (D.stateMainRow v selected b) - D.stateMainLength selected b -
      D.localLength (.inl (localEquiv b)) ≤ D.deadline (anchorEquiv b)

namespace LocalState

variable {D} {v : D.Vertex} {selected : Bool} (S : D.LocalState v selected)

def anchorAtEquiv : D.LocalBin v ≃ D.AnchorAt v :=
  Equiv.sumCongr S.anchorEquiv (Equiv.refl _)

def localAtEquiv : D.LocalBin v ≃ D.LocalAt v :=
  Equiv.sumCongr S.localEquiv (Equiv.refl _)

@[simp] theorem anchorAtEquiv_main (b : D.MBase v) :
    S.anchorAtEquiv (.inl b) = .inl (S.anchorEquiv b) := rfl

@[simp] theorem anchorAtEquiv_edge (j : D.JobCopy v) :
    S.anchorAtEquiv (.inr j) = .inr j := rfl

@[simp] theorem localAtEquiv_main (b : D.MBase v) :
    S.localAtEquiv (.inl b) = .inl (S.localEquiv b) := rfl

@[simp] theorem localAtEquiv_edge (j : D.JobCopy v) :
    S.localAtEquiv (.inr j) = .inr j := rfl

end LocalState

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryPrefixConservation
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
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

def itemSize (i : D.Item) : ℚ :=
  encodedSize (D.itemSubclass i) (D.itemLabel i) (D.itemCoordinate i)

theorem itemSize_mem_interval (i : D.Item) :
    1 / 6 < D.itemSize i ∧ D.itemSize i < 1 :=
  encodedSize_mem_interval _ _ _ (D.itemCoordinate_abs_le_six i)

theorem itemSize_pos (i : D.Item) : 0 < D.itemSize i :=
  lt_trans (by norm_num) (D.itemSize_mem_interval i).1

theorem itemSize_le_one (i : D.Item) : D.itemSize i ≤ 1 :=
  (D.itemSize_mem_interval i).2.le

def packingInstance : Instance :=
  Instance.ofFintype D.itemSize D.itemSize_pos D.itemSize_le_one

def itemEquiv : D.Item ≃ D.packingInstance.Item := Fintype.equivFin D.Item

end InventoryData

end

end BinPackingGap

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

def taggedItem (r : Role) : D.RoleCopies r ↪ D.packingInstance.Item :=
  (Function.Embedding.sigmaMk r).trans D.itemEquiv.toEmbedding

@[simp] theorem taggedItem_apply (r : Role) (c : D.RoleCopies r) :
    D.taggedItem r c = D.itemEquiv ⟨r, c⟩ := rfl

def globalCopyEmbedding (s : GlobalSpecies D.graph) :
    Fin (D.globalStock s) ↪ D.packingInstance.Item :=
  (Function.Embedding.sigmaMk s).trans (D.taggedItem .«global»)

def flagCopyEmbedding (s : FlagSpecies) :
    Fin (D.flagStock s) ↪ D.packingInstance.Item :=
  (Function.Embedding.sigmaMk s).trans (D.taggedItem .flag)

@[simp] theorem globalCopyEmbedding_apply (s : GlobalSpecies D.graph)
    (j : Fin (D.globalStock s)) :
    D.globalCopyEmbedding s j = D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ := rfl

@[simp] theorem flagCopyEmbedding_apply (s : FlagSpecies) (j : Fin (D.flagStock s)) :
    D.flagCopyEmbedding s j = D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ := rfl

def physicalGlobalPool (s : GlobalSpecies D.graph) : Finset D.packingInstance.Item :=
  Finset.univ.map (D.globalCopyEmbedding s)

def physicalFlagPool (s : FlagSpecies) : Finset D.packingInstance.Item :=
  Finset.univ.map (D.flagCopyEmbedding s)

def labeledItems : Finset D.packingInstance.Item :=
  Finset.univ.filter (fun i =>
    (D.itemEquiv.symm i).1 = .x ∨ (D.itemEquiv.symm i).1 = .anchor ∨
      (D.itemEquiv.symm i).1 = .«local»)

@[simp] theorem card_physicalGlobalPool (s : GlobalSpecies D.graph) :
    (D.physicalGlobalPool s).card = D.globalStock s := by
  simp [physicalGlobalPool]

@[simp] theorem card_physicalFlagPool (s : FlagSpecies) :
    (D.physicalFlagPool s).card = D.flagStock s := by
  simp [physicalFlagPool]

@[simp] theorem mem_labeledItems (i : D.packingInstance.Item) :
    i ∈ D.labeledItems ↔
      (D.itemEquiv.symm i).1 = .x ∨ (D.itemEquiv.symm i).1 = .anchor ∨
        (D.itemEquiv.symm i).1 = .«local» := by
  simp [labeledItems]

@[simp] theorem itemEquiv_mem_labeledItems (r : Role) (c : D.RoleCopies r) :
    D.itemEquiv ⟨r, c⟩ ∈ D.labeledItems ↔
      r = .x ∨ r = .anchor ∨ r = .«local» := by
  simp only [mem_labeledItems, Equiv.symm_apply_apply]

end BinPackingGap.InventoryData

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

open Turing BinPackingGames.Foundations.Complexity BinPackingGames.Reduction
open BinaryEncoding

def output : Mode → List Bool → List Bool := MachineTransducer.output transition emit

theorem output_copy (input : List Bool) : output .copy input = input := by
  induction input with
  | nil => rfl
  | cons bit tail ih =>
    simpa only [output, MachineTransducer.output, transition, emit, List.singleton_append] using
      congrArg (bit :: ·) ih

theorem output_frame (bits suffix : List Bool) :
    output .name (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix) = suffix := by
  induction bits with
  | nil => simpa [BinPackingCompleteness.BinaryEncoding.frame, output,
      MachineTransducer.output, transition, emit] using output_copy suffix
  | cons bit bits ih =>
    simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
      output, MachineTransducer.output, transition, emit, List.nil_append] using ih

end BinPackingGap.DropPackingBoundMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TreePruning
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace UniformTree

instance decidableAncestor {T : UniformTree} : DecidableRel (@ancestor T) :=
  fun u v => inferInstanceAs (Decidable (u.val.IsPrefix v.val))

theorem projectMarks_filter_card {T : UniformTree} (A : Finset T.Node)
    (p : List ℕ → Prop) [DecidablePred p] :
    ((projectMarks A).filter p).card =
      (A.filter (fun v => p v.val)).card := by
  classical
  have heq : (projectMarks A).filter p =
      (A.filter (fun v => p v.val)).image Subtype.val := by
    ext w
    constructor
    · intro hw
      obtain ⟨hwA, hp⟩ := Finset.mem_filter.mp hw
      obtain ⟨v, hv, rfl⟩ := (mem_projectMarks A w).mp hwA
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hp⟩, rfl⟩
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_filter.mpr
        ⟨(mem_projectMarks A v.val).mpr ⟨v, (Finset.mem_filter.mp hv).1, rfl⟩,
          (Finset.mem_filter.mp hv).2⟩
  rw [heq, Finset.card_image_of_injective _ Subtype.val_injective]

theorem levelCount_projectMarks {T : UniformTree} (A : Finset T.Node) (ℓ : ℕ) :
    levelCount (projectMarks A) ℓ = (A.filter (fun v => depth v = ℓ)).card :=
  projectMarks_filter_card A (fun w => w.length = ℓ)

theorem colorCount_projectMarks {T : UniformTree} (A : Finset T.Node) (l : T.Node) :
    colorCount (projectMarks A) l.val = (A.filter (fun v => ancestor v l)).card :=
  projectMarks_filter_card A (fun w => w.IsPrefix l.val)

theorem root_not_projectMarks {T : UniformTree} (A : Finset T.Node)
    (h : T.root ∉ A) : [] ∉ projectMarks A := by
  intro hm
  obtain ⟨v, hv, hval⟩ := (mem_projectMarks A []).mp hm
  have heq : v = T.root := Subtype.ext hval
  exact h (heq ▸ hv)

theorem mem_project_retainMarks (T : UniformTree) (marks : Finset (List ℕ))
    (w : List ℕ) : w ∈ projectMarks (T.retainMarks marks) ↔
      w ∈ marks ∧ w ∈ T.vertices := by
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := (mem_projectMarks _ w).mp hw
    exact ⟨(mem_retainMarks T marks v).mp hv, v.property⟩
  · rintro ⟨hw, hv⟩
    exact (mem_projectMarks _ w).mpr
      ⟨⟨w, hv⟩, (mem_retainMarks T marks ⟨w, hv⟩).mpr hw, rfl⟩

theorem retainMarks_root_not_mem (T : UniformTree) (marks : Finset (List ℕ))
    (h : [] ∉ marks) : T.root ∉ T.retainMarks marks := by
  simpa only [mem_retainMarks, root_val] using h

theorem retainMarks_level_le (T : UniformTree) (marks : Finset (List ℕ)) (ℓ : ℕ) :
    ((T.retainMarks marks).filter (fun v => depth v = ℓ)).card ≤
      levelCount marks ℓ := by
  rw [← levelCount_projectMarks]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hw, hlen⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨((T.mem_project_retainMarks marks w).mp hw).1, hlen⟩

theorem retainMarks_leaf_count (T : UniformTree) (marks : Finset (List ℕ))
    (l : T.Node) (hl : leaf l) :
    ((T.retainMarks marks).filter (fun v => ancestor v l)).card =
      colorCount marks l.val := by
  rw [← colorCount_projectMarks]
  apply congrArg Finset.card
  ext w
  constructor
  · intro hw
    obtain ⟨hw, hp⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨((T.mem_project_retainMarks marks w).mp hw).1, hp⟩
  · intro hw
    obtain ⟨hw, hp⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr
      ⟨(T.mem_project_retainMarks marks w).mpr
        ⟨hw, T.mem_vertices_iff.mpr ⟨l.val, hl, hp⟩⟩, hp⟩

end UniformTree

open UniformTree

structure CompetingTrees (d : ℕ) where
  plus : UniformTree
  minus : UniformTree
  height : ℕ
  height_pos : 0 < height
  plus_height : plus.height = height
  minus_height : minus.height = height
  quota : ℕ → ℕ
  quota_pos : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ height → 0 < quota ℓ
  markingPlus : Finset plus.Node
  markingMinus : Finset minus.Node
  plus_root_not_marked : plus.root ∉ markingPlus
  minus_root_not_marked : minus.root ∉ markingMinus
  plus_quota : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ height →
    (markingPlus.filter (fun v => depth v = ℓ)).card ≤ quota ℓ
  minus_quota : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ height →
    (markingMinus.filter (fun v => depth v = ℓ)).card ≤ quota ℓ
  plus_rich : ∀ l : plus.Node, leaf l →
    d ≤ (markingPlus.filter (fun v => ancestor v l)).card
  minus_rich : ∀ l : minus.Node, leaf l →
    d ≤ (markingMinus.filter (fun v => ancestor v l)).card
  shared_obstruction : ∀ (Aplus : Finset plus.Node) (Aminus : Finset minus.Node),
    plus.root ∉ Aplus → minus.root ∉ Aminus →
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ height →
      (Aplus.filter (fun v => depth v = ℓ)).card +
      (Aminus.filter (fun v => depth v = ℓ)).card ≤ quota ℓ) →
    (∃ l : plus.Node, leaf l ∧ ∀ v ∈ Aplus, ¬ ancestor v l) ∨
    (∃ l : minus.Node, leaf l ∧ ∀ v ∈ Aminus, ¬ ancestor v l)

theorem levelCount_project_union {T U : UniformTree}
    (A : Finset T.Node) (B : Finset U.Node) (ℓ : ℕ) :
    levelCount (projectMarks A ∪ projectMarks B) ℓ ≤
      (A.filter (fun v => depth v = ℓ)).card +
      (B.filter (fun v => depth v = ℓ)).card := by
  have heq : (projectMarks A ∪ projectMarks B).filter (fun w => w.length = ℓ) =
      (projectMarks A).filter (fun w => w.length = ℓ) ∪
      (projectMarks B).filter (fun w => w.length = ℓ) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_union, or_and_right]
  unfold levelCount
  rw [heq]
  exact (Finset.card_union_le _ _).trans_eq
    (congrArg₂ (· + ·) (levelCount_projectMarks A ℓ) (levelCount_projectMarks B ℓ))

namespace CompetingTrees

def quotaTotal {d : ℕ} (T : CompetingTrees d) : ℕ :=
  ∑ ℓ ∈ Finset.Icc 1 T.height, T.quota ℓ

theorem markingPlus_depth_pos {d : ℕ} (T : CompetingTrees d)
    (v : T.plus.Node) (hv : v ∈ T.markingPlus) : 0 < depth v := by
  have hne : v ≠ T.plus.root := fun h => T.plus_root_not_marked (h ▸ hv)
  have hn := mt (eq_root_iff_depth_eq_zero v).mpr hne
  exact Nat.pos_of_ne_zero hn

theorem markingMinus_depth_pos {d : ℕ} (T : CompetingTrees d)
    (v : T.minus.Node) (hv : v ∈ T.markingMinus) : 0 < depth v := by
  have hne : v ≠ T.minus.root := fun h => T.minus_root_not_marked (h ▸ hv)
  have hn := mt (eq_root_iff_depth_eq_zero v).mpr hne
  exact Nat.pos_of_ne_zero hn

def ofAuxiliary (d : ℕ) (hd : 0 < d) (aux : AuxiliaryTree (2 * d - 1)) :
    CompetingTrees d := by
  have hdn : d ≤ 2 * d - 1 := by omega
  have hred := aux.richLeaves_nonempty aux.red hdn aux.red_witness
  have hblue := aux.richLeaves_nonempty aux.blue hdn aux.blue_witness
  let plus := aux.richTree aux.red hred
  let minus := aux.richTree aux.blue hblue
  refine
    { plus := plus
      minus := minus
      height := aux.tree.height
      height_pos := aux.height_pos (by omega)
      plus_height := rfl
      minus_height := rfl
      quota := aux.quota
      quota_pos := aux.quota_pos
      markingPlus := plus.retainMarks aux.red
      markingMinus := minus.retainMarks aux.blue
      plus_root_not_marked := plus.retainMarks_root_not_mem aux.red aux.root_not_red
      minus_root_not_marked := minus.retainMarks_root_not_mem aux.blue aux.root_not_blue
      plus_quota := ?_
      minus_quota := ?_
      plus_rich := ?_
      minus_rich := ?_
      shared_obstruction := ?_ }
  · intro ℓ hℓ hℓ'
    exact (plus.retainMarks_level_le aux.red ℓ).trans (aux.red_level ℓ hℓ hℓ')
  · intro ℓ hℓ hℓ'
    exact (minus.retainMarks_level_le aux.blue ℓ).trans (aux.blue_level ℓ hℓ hℓ')
  · intro l hl
    rw [plus.retainMarks_leaf_count aux.red l hl]
    exact (Finset.mem_filter.mp hl).2
  · intro l hl
    rw [minus.retainMarks_leaf_count aux.blue l hl]
    exact (Finset.mem_filter.mp hl).2
  · intro A B hA hB hquota
    have hproject : RespectsTreeQuota aux.tree aux.quota (projectMarks A ∪ projectMarks B) := by
      constructor
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · exact root_not_projectMarks A hA h
        · exact root_not_projectMarks B hB h
      · intro ℓ hℓ hℓ'
        exact (levelCount_project_union A B ℓ).trans (hquota ℓ hℓ hℓ')
    obtain ⟨l, hl, havoid⟩ := aux.avoids _ hproject
    rcases aux.richLeaves_cover l hl with hredLeaf | hblueLeaf
    · left
      have hlplus : l ∈ plus.leaves := hredLeaf
      refine ⟨⟨l, plus.leaf_mem_vertices hlplus⟩, hlplus, ?_⟩
      intro v hv hp
      exact Finset.disjoint_left.mp havoid
        (Finset.mem_union_left _ ((mem_projectMarks A v.val).mpr ⟨v, hv, rfl⟩))
        (mem_prefixes_iff.mpr hp)
    · right
      have hlminus : l ∈ minus.leaves := hblueLeaf
      refine ⟨⟨l, minus.leaf_mem_vertices hlminus⟩, hlminus, ?_⟩
      intro v hv hp
      exact Finset.disjoint_left.mp havoid
        (Finset.mem_union_right _ ((mem_projectMarks B v.val).mpr ⟨v, hv, rfl⟩))
        (mem_prefixes_iff.mpr hp)

end CompetingTrees

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_InventoryFromTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

def ofCompetingTrees (G : GraphInput) {d : ℕ} (T : CompetingTrees d) (R k : ℕ) :
    InventoryData where
  graph := G
  plus := T.plus
  minus := T.minus
  d := d
  R := R
  L := T.height
  quota := T.quota
  k := k

@[simp] theorem ofCompetingTrees_P (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) :
    (ofCompetingTrees G T R k).P = T.quotaTotal := rfl

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_ItemEnumeration
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def treeRowList : List D.TreeRow :=
  ((Finset.univ : Finset D.plus.Node).toList.flatMap fun v =>
    (List.finRange D.d).map fun j => Sum.inl (v, j)) ++
  ((Finset.univ : Finset D.minus.Node).toList.flatMap fun v =>
    (List.finRange D.d).map fun j => Sum.inr (Sum.inl (v, j))) ++
  (List.finRange D.P).map (fun j => Sum.inr (Sum.inr j))

def positiveLocalList : List D.PositiveLocal :=
  (Finset.univ : Finset D.PositiveLocal).toList

theorem mem_treeRowList (r : D.TreeRow) : r ∈ D.treeRowList := by
  classical
  rcases r with ⟨v, j⟩ | (⟨v, j⟩ | j) <;>
    simp [treeRowList]

theorem mem_positiveLocalList (r : D.PositiveLocal) : r ∈ D.positiveLocalList := by
  classical
  simp [positiveLocalList]

theorem treeRowList_length : D.treeRowList.length = D.t := by
  classical
  have hp := length_flatMap_constant (Finset.univ : Finset D.plus.Node).toList
    (fun v => (List.finRange D.d).map fun j => (Sum.inl (v, j) : D.TreeRow)) D.d
    (fun _ => by simp)
  have hm := length_flatMap_constant (Finset.univ : Finset D.minus.Node).toList
    (fun v => (List.finRange D.d).map fun j =>
      (Sum.inr (Sum.inl (v, j)) : D.TreeRow)) D.d (fun _ => by simp)
  simp only [treeRowList, List.length_append, hp, hm, List.length_map,
    List.length_finRange, Finset.length_toList, Finset.card_univ]
  dsimp [t, tPlus, tMinus]
  ring

theorem positiveLocalList_length : D.positiveLocalList.length = D.P := by
  classical
  simpa only [positiveLocalList, Finset.length_toList, Finset.card_univ] using
    D.card_positiveLocal

def vertexChunk (v : D.Vertex) : List D.Item :=
  (D.treeRowList.map fun r => ⟨.x, ⟨v, .inl r⟩⟩) ++
  (D.treeRowList.map fun r => ⟨.anchor, ⟨v, .inl (.inl r)⟩⟩) ++
  (D.positiveLocalList.map fun r => ⟨.«local», ⟨v, .inl (.inl r)⟩⟩) ++
  ((List.finRange (D.t - D.P)).map fun j =>
    ⟨.«local», ⟨v, .inl (.inr (.inl j))⟩⟩)

def vertexItems : List D.Item :=
  (List.finRange D.graph.n).flatMap D.vertexChunk

def listedJobCopy (e : D.Edge) (j : Fin D.R) (s : Fin 2) (r : Fin D.d) :
    D.JobCopy (D.graph.endpoint e s) :=
  ((⟨(e, s), rfl⟩, j), r)

def jobChunk (e : D.Edge) (j : Fin D.R) (s : Fin 2) : List D.Item :=
  let v := D.graph.endpoint e s
  let copy := D.listedJobCopy e j s
  ((List.finRange D.d).map fun r => ⟨.x, ⟨v, .inr (true, copy r)⟩⟩) ++
  ((List.finRange D.d).map fun r => ⟨.x, ⟨v, .inr (false, copy r)⟩⟩) ++
  ((List.finRange D.d).map fun r => ⟨.anchor, ⟨v, .inl (.inr (copy r))⟩⟩) ++
  ((List.finRange D.d).map fun r => ⟨.anchor, ⟨v, .inr (copy r)⟩⟩) ++
  ((List.finRange D.d).map fun r =>
    ⟨.«local», ⟨v, .inl (.inr (.inr (copy r)))⟩⟩) ++
  ((List.finRange D.d).map fun r => ⟨.«local», ⟨v, .inr (copy r)⟩⟩)

def jobItems : List D.Item :=
  (List.finRange D.graph.edges.length).flatMap fun e =>
    (List.finRange D.R).flatMap fun j =>
      (List.finRange 2).flatMap fun s => D.jobChunk e j s

def globalPool (s : GlobalSpecies D.graph) : List D.Item :=
  (List.finRange (D.globalStock s)).map fun r => ⟨.«global», ⟨s, r⟩⟩

def globalItems : List D.Item :=
  D.globalPool (.up true) ++ D.globalPool (.up false) ++
  D.globalPool (.um true) ++ D.globalPool (.um false) ++
  (List.finRange D.graph.edges.length).flatMap fun e =>
    D.globalPool (.edge e true) ++ D.globalPool (.edge e false)

def flagPool (s : FlagSpecies) : List D.Item :=
  (List.finRange (D.flagStock s)).map fun r => ⟨.flag, ⟨s, r⟩⟩

def flagItems : List D.Item :=
  D.flagPool .tree ++ D.flagPool .main ++ D.flagPool .edge

def itemList : List D.Item :=
  D.vertexItems ++ D.jobItems ++ D.globalItems ++ D.flagItems

theorem vertexChunk_length (v : D.Vertex) : (D.vertexChunk v).length = 3 * D.t := by
  simp only [vertexChunk, List.length_append, List.length_map, D.treeRowList_length,
    D.positiveLocalList_length, List.length_finRange]
  have h := D.P_le_t
  omega

theorem vertexItems_length : D.vertexItems.length = 3 * D.graph.n * D.t := by
  rw [vertexItems, length_flatMap_constant _ _ _ D.vertexChunk_length,
    List.length_finRange]
  ring

theorem jobChunk_length (e : D.Edge) (j : Fin D.R) (s : Fin 2) :
    (D.jobChunk e j s).length = 6 * D.d := by
  simp only [jobChunk, List.length_append, List.length_map, List.length_finRange]
  omega

theorem jobItems_length :
    D.jobItems.length = 12 * D.d * D.graph.edges.length * D.R := by
  have hs (e : D.Edge) (j : Fin D.R) :
      ((List.finRange 2).flatMap fun s => D.jobChunk e j s).length = 2 * (6 * D.d) := by
    rw [length_flatMap_constant _ _ _ (D.jobChunk_length e j), List.length_finRange]
  have hj (e : D.Edge) :
      ((List.finRange D.R).flatMap fun j =>
        (List.finRange 2).flatMap fun s => D.jobChunk e j s).length =
      D.R * (2 * (6 * D.d)) := by
    rw [length_flatMap_constant _ _ _ (hs e), List.length_finRange]
  rw [jobItems, length_flatMap_constant _ _ _ hj, List.length_finRange]
  ring

theorem globalPool_length (s : GlobalSpecies D.graph) :
    (D.globalPool s).length = D.globalStock s := by simp [globalPool]

theorem globalItems_length (hk : D.k ≤ D.graph.n) : D.globalItems.length = D.B := by
  have he (e : D.Edge) :
      (D.globalPool (.edge e true) ++ D.globalPool (.edge e false)).length =
      2 * (D.d * D.R) := by simp [globalPool_length, globalStock, two_mul]
  have hu := D.up_species_total hk
  have hm := D.um_species_total
  have hlen : D.globalItems.length = D.plusSlots + D.minusSlots +
      D.graph.edges.length * (2 * (D.d * D.R)) := by
    simp only [globalItems, List.length_append, D.globalPool_length,
      length_flatMap_constant _ _ _ he, List.length_finRange]
    omega
  rw [hlen, D.plusSlots_eq, D.sum_J, D.B_closed]
  dsimp [minusSlots, t]
  ring

theorem flagPool_length (s : FlagSpecies) :
    (D.flagPool s).length = D.flagStock s := by simp [flagPool]

theorem flagItems_length : D.flagItems.length = D.B := by
  simp only [flagItems, List.length_append, D.flagPool_length, flagStock,
    treeFlags, jobFlags, D.B_eq]
  omega

theorem itemList_length (hk : D.k ≤ D.graph.n) : D.itemList.length = 5 * D.B := by
  simp only [itemList, List.length_append, D.vertexItems_length, D.jobItems_length,
    D.globalItems_length hk, D.flagItems_length]
  rw [D.B_closed]
  ring

theorem mem_itemList_of_vertex {v : D.Vertex} {i : D.Item}
    (hi : i ∈ D.vertexChunk v) : i ∈ D.itemList := by
  have hv : i ∈ D.vertexItems :=
    List.mem_flatMap.mpr ⟨v, List.mem_finRange v, hi⟩
  simp only [itemList, List.mem_append]
  exact Or.inl (Or.inl (Or.inl hv))

theorem mem_itemList_of_job {e : D.Edge} {j : Fin D.R} {s : Fin 2} {i : D.Item}
    (hi : i ∈ D.jobChunk e j s) : i ∈ D.itemList := by
  have hj : i ∈ D.jobItems := List.mem_flatMap.mpr ⟨e, List.mem_finRange e,
    List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
      List.mem_flatMap.mpr ⟨s, List.mem_finRange s, hi⟩⟩⟩
  simp only [itemList, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hj))

theorem mem_globalItems (g : D.GlobalCopy) :
    (⟨.«global», g⟩ : D.Item) ∈ D.globalItems := by
  rcases g with ⟨s, r⟩
  cases s with
  | up b => cases b <;> simp [globalItems, globalPool]
  | um b => cases b <;> simp [globalItems, globalPool]
  | edge e b =>
    have hp : (⟨.«global», ⟨.edge e b, r⟩⟩ : D.Item) ∈
        D.globalPool (.edge e true) ++ D.globalPool (.edge e false) := by
      cases b <;> simp [globalPool]
    have he : (⟨.«global», ⟨.edge e b, r⟩⟩ : D.Item) ∈
        (List.finRange D.graph.edges.length).flatMap
          (fun e => D.globalPool (.edge e true) ++ D.globalPool (.edge e false)) :=
      List.mem_flatMap.mpr ⟨e, List.mem_finRange e, hp⟩
    exact List.mem_append_right _ he

theorem mem_flagItems (g : D.FlagCopy) : (⟨.flag, g⟩ : D.Item) ∈ D.flagItems := by
  rcases g with ⟨s, r⟩
  cases s <;> simp [flagItems, flagPool]

theorem mem_itemList (i : D.Item) : i ∈ D.itemList := by
  classical
  rcases i with ⟨role, i⟩
  cases role with
  | x =>
    rcases i with ⟨v, tree | ⟨short, job⟩⟩
    · apply D.mem_itemList_of_vertex (v := v)
      simp only [vertexChunk, List.mem_append]
      exact Or.inl (Or.inl (Or.inl
        (List.mem_map.mpr ⟨tree, D.mem_treeRowList tree, rfl⟩)))
    · rcases job with ⟨⟨⟨⟨e, s⟩, hv⟩, j⟩, r⟩
      cases hv
      apply D.mem_itemList_of_job (e := e) (j := j) (s := s)
      cases short <;> simp [jobChunk, listedJobCopy]
  | anchor =>
    rcases i with ⟨v, (tree | job) | job⟩
    · apply D.mem_itemList_of_vertex (v := v)
      simp only [vertexChunk, List.mem_append]
      exact Or.inl (Or.inl (Or.inr
        (List.mem_map.mpr ⟨tree, D.mem_treeRowList tree, rfl⟩)))
    · rcases job with ⟨⟨⟨⟨e, s⟩, hv⟩, j⟩, r⟩
      cases hv
      apply D.mem_itemList_of_job (e := e) (j := j) (s := s)
      simp [jobChunk, listedJobCopy]
    · rcases job with ⟨⟨⟨⟨e, s⟩, hv⟩, j⟩, r⟩
      cases hv
      apply D.mem_itemList_of_job (e := e) (j := j) (s := s)
      simp [jobChunk, listedJobCopy]
  | «global» =>
    simp only [itemList, List.mem_append]
    exact Or.inl (Or.inr (D.mem_globalItems i))
  | «local» =>
    rcases i with ⟨v, (positive | (zero | job)) | job⟩
    · apply D.mem_itemList_of_vertex (v := v)
      simp only [vertexChunk, List.mem_append]
      exact Or.inl (Or.inr
        (List.mem_map.mpr ⟨positive, D.mem_positiveLocalList positive, rfl⟩))
    · apply D.mem_itemList_of_vertex (v := v)
      simp [vertexChunk]
    · rcases job with ⟨⟨⟨⟨e, s⟩, hv⟩, j⟩, r⟩
      cases hv
      apply D.mem_itemList_of_job (e := e) (j := j) (s := s)
      simp [jobChunk, listedJobCopy]
    · rcases job with ⟨⟨⟨⟨e, s⟩, hv⟩, j⟩, r⟩
      cases hv
      apply D.mem_itemList_of_job (e := e) (j := j) (s := s)
      simp [jobChunk, listedJobCopy]
  | flag =>
    simp only [itemList, List.mem_append]
    exact Or.inr (D.mem_flagItems i)

open scoped Classical in
theorem itemList_toFinset : D.itemList.toFinset = Finset.univ := by
  classical
  ext i
  simp [D.mem_itemList i]

theorem itemList_nodup (hk : D.k ≤ D.graph.n) : D.itemList.Nodup := by
  classical
  have hcard : D.itemList.toFinset.card = D.itemList.length := by
    rw [D.itemList_toFinset, Finset.card_univ, D.card_item hk, D.itemList_length hk]
  exact (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (D.itemList : Multiset D.Item))).mp hcard

def itemListEquiv (hk : D.k ≤ D.graph.n) : Fin D.itemList.length ≃ D.Item := by
  classical
  exact List.Nodup.getEquivOfForallMemList D.itemList (D.itemList_nodup hk) D.mem_itemList

@[simp] theorem itemListEquiv_apply (hk : D.k ≤ D.graph.n)
    (i : Fin D.itemList.length) : D.itemListEquiv hk i = D.itemList.get i := rfl

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalarExpression
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

open IntegerPackingArithmetic

variable (D : InventoryData)

def coordinateDenominator : ℕ :=
  geomDenominator D.graph.edges.length D.R D.geometryBound D.L

def treeBaselineInteger : D.TreeRow → ℤ
  | .inl (node, _) =>
      treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val
  | .inr (.inl (node, _)) =>
      treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val
  | .inr (.inr _) => D.coordinateDenominator

def rowBaselineInteger {v : D.Vertex} : D.RowAt v → ℤ
  | .inl r => D.treeBaselineInteger r
  | .inr (_, j) => baselineNumerator D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)

def treeDeadlineInteger : D.TreeRow → ℤ
  | .inl (node, _) =>
      if node.val ∈ D.plus.leaves then
        treeLeftNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val
      else treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val
  | .inr (.inl (node, _)) =>
      if node.val ∈ D.minus.leaves then
        treeLeftNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val
      else treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val
  | .inr (.inr _) => D.coordinateDenominator

def deadlineInteger {v : D.Vertex} : D.MBase v → ℤ
  | .inl r => D.treeDeadlineInteger r
  | .inr j => baselineNumerator D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j) - 1

def rowIntegerCoordinate {v : D.Vertex} (r : D.RowAt v) : ℤ :=
  D.rowBaselineInteger r - if D.rowShort r then 1 else 0

def anchorIntegerCoordinate {v : D.Vertex} : D.AnchorAt v → ℤ
  | .inl z => -D.deadlineInteger z
  | .inr j =>
      -baselineNumerator D.graph.edges.length D.R D.geometryBound D.L (D.jobPosition j) -
        betaNumerator D.graph.edges.length D.R D.geometryBound D.L (D.jobPosition j).1

def globalIntegerCoordinate : D.GlobalCopy → ℤ
  | ⟨.up one, _⟩ => -(if one then (D.coordinateDenominator : ℤ) else 0)
  | ⟨.um one, _⟩ => -(if one then (D.coordinateDenominator : ℤ) else 0)
  | ⟨.edge e permit, _⟩ =>
      betaNumerator D.graph.edges.length D.R D.geometryBound D.L e +
        if permit then 0 else 1

def localIntegerCoordinate {v : D.Vertex} : D.LocalAt v → ℤ
  | .inl (.inl ⟨ell, _⟩) => -(localNumerator D.geometryBound D.L ell.val : ℤ)
  | _ => 0

def itemIntegerCoordinate : D.Item → ℤ
  | ⟨.x, ⟨_, r⟩⟩ => D.rowIntegerCoordinate r
  | ⟨.anchor, ⟨_, a⟩⟩ => D.anchorIntegerCoordinate a
  | ⟨.«global», u⟩ => D.globalIntegerCoordinate u
  | ⟨.«local», ⟨_, l⟩⟩ => D.localIntegerCoordinate l
  | ⟨.flag, _⟩ => 0

variable (hplus : D.plus.height ≤ D.L) (hminus : D.minus.height ≤ D.L)

def itemRawPair (i : D.Item) : ℕ × ℕ :=
  rawItem D.coordinateDenominator (D.itemSubclass i) (D.itemLabel i)
    (D.itemIntegerCoordinate i)

end BinPackingGap.InventoryData

namespace BinPackingGap.NaturalPackingNumerator

open IntegerPackingArithmetic

section Coordinates

variable (D : InventoryData)

def treeBaselineParts : D.TreeRow → NatDifference
  | .inl (node, _) => NatDifference.ofNat
      (treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val)
  | .inr (.inl (node, _)) => NatDifference.ofNat
      (treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val)
  | .inr (.inr _) => NatDifference.ofNat D.coordinateDenominator

def rowBaselineParts {v : D.Vertex} : D.RowAt v → NatDifference
  | .inl r => treeBaselineParts D r
  | .inr (_, j) => baselineParts D.graph.edges.length D.R D.geometryBound D.L (D.jobPosition j)

def treeDeadlineParts : D.TreeRow → NatDifference
  | .inl (node, _) => NatDifference.ofNat
      (if node.val ∈ D.plus.leaves then
        treeLeftNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val
      else treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .plus node.val)
  | .inr (.inl (node, _)) => NatDifference.ofNat
      (if node.val ∈ D.minus.leaves then
        treeLeftNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val
      else treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L .minus node.val)
  | .inr (.inr _) => NatDifference.ofNat D.coordinateDenominator

def deadlineParts {v : D.Vertex} : D.MBase v → NatDifference
  | .inl r => treeDeadlineParts D r
  | .inr j => (baselineParts D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)).sub (NatDifference.ofNat 1)

def rowParts {v : D.Vertex} (r : D.RowAt v) : NatDifference :=
  (rowBaselineParts D r).sub (NatDifference.ofNat (if D.rowShort r then 1 else 0))

def anchorParts {v : D.Vertex} : D.AnchorAt v → NatDifference
  | .inl z => (deadlineParts D z).negate
  | .inr j => (baselineParts D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)).negate.sub
        (betaParts D.graph.edges.length D.R D.geometryBound D.L (D.jobPosition j).1)

def globalParts : D.GlobalCopy → NatDifference
  | ⟨.up one, _⟩ => (NatDifference.ofNat (if one then D.coordinateDenominator else 0)).negate
  | ⟨.um one, _⟩ => (NatDifference.ofNat (if one then D.coordinateDenominator else 0)).negate
  | ⟨.edge edge permit, _⟩ =>
      (betaParts D.graph.edges.length D.R D.geometryBound D.L edge).add
        (NatDifference.ofNat (if permit then 0 else 1))

def localParts {v : D.Vertex} : D.LocalAt v → NatDifference
  | .inl (.inl ⟨ell, _⟩) =>
      (NatDifference.ofNat (localNumerator D.geometryBound D.L ell.val)).negate
  | _ => NatDifference.ofNat 0

def coordinateParts : D.Item → NatDifference
  | ⟨.x, ⟨_, r⟩⟩ => rowParts D r
  | ⟨.anchor, ⟨_, a⟩⟩ => anchorParts D a
  | ⟨.«global», u⟩ => globalParts D u
  | ⟨.«local», ⟨_, l⟩⟩ => localParts D l
  | ⟨.flag, _⟩ => NatDifference.ofNat 0

@[simp] theorem eval_treeBaselineParts (r : D.TreeRow) :
    (treeBaselineParts D r).eval = D.treeBaselineInteger r := by
  rcases r with ⟨node, j⟩ | (⟨node, j⟩ | j) <;>
    simp [treeBaselineParts, InventoryData.treeBaselineInteger]

@[simp] theorem eval_rowBaselineParts {v : D.Vertex} (r : D.RowAt v) :
    (rowBaselineParts D r).eval = D.rowBaselineInteger r := by
  rcases r with r | ⟨b, j⟩ <;>
    simp [rowBaselineParts, InventoryData.rowBaselineInteger]

@[simp] theorem eval_treeDeadlineParts (r : D.TreeRow) :
    (treeDeadlineParts D r).eval = D.treeDeadlineInteger r := by
  rcases r with ⟨node, j⟩ | (⟨node, j⟩ | j)
  · by_cases h : node.val ∈ D.plus.leaves <;>
      simp [treeDeadlineParts, InventoryData.treeDeadlineInteger, h]
  · by_cases h : node.val ∈ D.minus.leaves <;>
      simp [treeDeadlineParts, InventoryData.treeDeadlineInteger, h]
  · simp [treeDeadlineParts, InventoryData.treeDeadlineInteger]

@[simp] theorem eval_deadlineParts {v : D.Vertex} (r : D.MBase v) :
    (deadlineParts D r).eval = D.deadlineInteger r := by
  rcases r with r | j <;>
    simp [deadlineParts, InventoryData.deadlineInteger]

@[simp] theorem eval_rowParts {v : D.Vertex} (r : D.RowAt v) :
    (rowParts D r).eval = D.rowIntegerCoordinate r := by
  cases h : D.rowShort r <;>
    simp [rowParts, InventoryData.rowIntegerCoordinate, h]

@[simp] theorem eval_anchorParts {v : D.Vertex} (r : D.AnchorAt v) :
    (anchorParts D r).eval = D.anchorIntegerCoordinate r := by
  rcases r with r | j <;>
    simp [anchorParts, InventoryData.anchorIntegerCoordinate]

@[simp] theorem eval_globalParts (r : D.GlobalCopy) :
    (globalParts D r).eval = D.globalIntegerCoordinate r := by
  rcases r with ⟨species, j⟩
  cases species with
  | up b => cases b <;> simp [globalParts, InventoryData.globalIntegerCoordinate]
  | um b => cases b <;> simp [globalParts, InventoryData.globalIntegerCoordinate]
  | edge e b => cases b <;> simp [globalParts, InventoryData.globalIntegerCoordinate]

@[simp] theorem eval_localParts {v : D.Vertex} (r : D.LocalAt v) :
    (localParts D r).eval = D.localIntegerCoordinate r := by
  rcases r with (⟨ell, j⟩ | j) | j <;>
    simp [localParts, InventoryData.localIntegerCoordinate]

@[simp] theorem eval_coordinateParts (i : D.Item) :
    (coordinateParts D i).eval = D.itemIntegerCoordinate i := by
  rcases i with ⟨role, i⟩
  cases role with
  | x => exact eval_rowParts D i.2
  | anchor => exact eval_anchorParts D i.2
  | «global» => exact eval_globalParts D i
  | «local» => exact eval_localParts D i.2
  | flag => simp [coordinateParts, InventoryData.itemIntegerCoordinate]

end Coordinates

def primaryParts (subclass : Subclass) : NatDifference := NatDifference.ofInt (primaryScore subclass)

@[simp] theorem eval_primaryParts (subclass : Subclass) :
    (primaryParts subclass).eval = primaryScore subclass :=
  NatDifference.eval_ofInt _

def secondaryParts {n : Nat} (subclass : Subclass) (label : Option (Fin n)) : NatDifference :=
  match subclass.role with
  | .x => NatDifference.ofNat (labelPower label)
  | .anchor => (NatDifference.ofNat (2 * labelPower label)).negate
  | .«global» => NatDifference.ofNat 0
  | .«local» => NatDifference.ofNat (labelPower label)
  | .flag => NatDifference.ofNat 0

@[simp] theorem eval_secondaryParts {n : Nat} (subclass : Subclass) (label : Option (Fin n)) :
    (secondaryParts subclass label).eval = secondaryScore subclass label := by
  cases label <;> cases h : subclass.role <;>
    simp [secondaryParts, secondaryScore, labelPower, labelWeight, h]

@[simp] theorem eval_signedParts (n geom : Nat) (p q W : NatDifference) :
    (signedParts n geom p q W).eval = signedNumerator n geom p.eval q.eval W.eval := by
  simp only [signedParts, NatDifference.eval_add, NatDifference.eval_ofNat,
    NatDifference.eval_scale, signedNumerator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

def numeratorParts {n : Nat} (geom : Nat) (subclass : Subclass) (label : Option (Fin n))
    (W : NatDifference) : NatDifference :=
  signedParts n geom (primaryParts subclass) (secondaryParts subclass label) W

@[simp] theorem eval_numeratorParts {n : Nat} (geom : Nat) (subclass : Subclass)
    (label : Option (Fin n)) (W : NatDifference) :
    (numeratorParts geom subclass label W).eval = itemNumerator geom subclass label W.eval := by
  simp [numeratorParts, itemNumerator]

end BinPackingGap.NaturalPackingNumerator

namespace BinPackingGap.PackingCoordinateExpression

open IntegerPackingArithmetic
open NaturalPackingNumerator
open NatExpressionCompiler

namespace Parts

def eval (values : Input → Nat) (p : Parts) : NatDifference :=
  ⟨NatExpressionCompiler.eval values p.pos, NatExpressionCompiler.eval values p.neg⟩

@[simp] theorem eval_ofExpr (values : Input → Nat) (e : Expr Input) :
    (ofExpr e).eval values = NatDifference.ofNat (NatExpressionCompiler.eval values e) := rfl

@[simp] theorem eval_negate (values : Input → Nat) (p : Parts) :
    p.negate.eval values = (p.eval values).negate := rfl

@[simp] theorem eval_add (values : Input → Nat) (p q : Parts) :
    (p.add q).eval values = (p.eval values).add (q.eval values) := rfl

@[simp] theorem eval_sub (values : Input → Nat) (p q : Parts) :
    (p.sub q).eval values = (p.eval values).sub (q.eval values) := rfl

end Parts

inductive TreeDescriptor (plus minus : UniformTree)
  | plusNode (node : plus.Node)
  | minusNode (node : minus.Node)
  | padding
  deriving DecidableEq

inductive Descriptor (plus minus : UniformTree) (L : Nat)
  | treeRow (tree : TreeDescriptor plus minus)
  | jobRow (short : Bool)
  | treeAnchor (tree : TreeDescriptor plus minus)
  | jobAnchor
  | jobKey
  | globalUnit (one : Bool)
  | globalEdge (permit : Bool)
  | localDepth (depth : Fin (L + 1))
  | zero
  deriving DecidableEq

def treeLeftExpr (bound L : Nat) (side : TreeGeometry.Side) (address : List Nat) :
    Expr Input :=
  .add (.mul (.constant (rootOffsetNumerator side)) (.input .geometryDg))
    (.constant (pathNumerator bound L 0 address))

def treeRightExpr (bound L : Nat) (side : TreeGeometry.Side) (address : List Nat) :
    Expr Input :=
  .add (treeLeftExpr bound L side address)
    (if address = [] then .input .geometryDg
      else .constant (localNumerator bound L address.length))

def treeBaselineExpr {plus minus : UniformTree} (bound L : Nat) :
    TreeDescriptor plus minus → Parts
  | .plusNode node => Parts.ofExpr (treeRightExpr bound L .plus node.val)
  | .minusNode node => Parts.ofExpr (treeRightExpr bound L .minus node.val)
  | .padding => Parts.ofExpr (.input .geometryDg)

def treeDeadlineExpr {plus minus : UniformTree} (bound L : Nat) :
    TreeDescriptor plus minus → Parts
  | .plusNode node => Parts.ofExpr
      (if node.val ∈ plus.leaves then treeLeftExpr bound L .plus node.val
        else treeRightExpr bound L .plus node.val)
  | .minusNode node => Parts.ofExpr
      (if node.val ∈ minus.leaves then treeLeftExpr bound L .minus node.val
        else treeRightExpr bound L .minus node.val)
  | .padding => Parts.ofExpr (.input .geometryDg)

def baselineExpr (bound L : Nat) : Parts :=
  ⟨.add
      (.mul (.mul (.constant 80) (.input .totalPowerA))
        (.constant (widthRadix bound ^ L)))
      (.mul
        (.mul (.constant (10 * widthRadix bound ^ L)) (.input .repetitionOne))
        (.input .edgePower)),
    .constant (10 * widthRadix bound ^ L)⟩

def betaExpr (bound L : Nat) : Parts :=
  ⟨.mul (.constant (10 * widthRadix bound ^ L)) (.input .edgePower),
    .constant (10 * widthRadix bound ^ L)⟩

def expression {plus minus : UniformTree} {L : Nat} (bound : Nat) :
    Descriptor plus minus L → Parts
  | .treeRow tree => (treeBaselineExpr bound L tree).sub (Parts.ofExpr (.constant 0))
  | .jobRow short => (baselineExpr bound L).sub
      (Parts.ofExpr (.constant (if short then 1 else 0)))
  | .treeAnchor tree => (treeDeadlineExpr bound L tree).negate
  | .jobAnchor => ((baselineExpr bound L).sub (Parts.ofExpr (.constant 1))).negate
  | .jobKey => (baselineExpr bound L).negate.sub (betaExpr bound L)
  | .globalUnit one =>
      (Parts.ofExpr (if one then .input .geometryDg else .constant 0)).negate
  | .globalEdge permit => (betaExpr bound L).add
      (Parts.ofExpr (.constant (if permit then 0 else 1)))
  | .localDepth depth =>
      (Parts.ofExpr (.constant (localNumerator bound L depth.val))).negate
  | .zero => Parts.ofExpr (.constant 0)

def registers (D : InventoryData) (edge repetitionOne : Nat) : Input → Nat
  | .geometryDg => D.coordinateDenominator
  | .totalPowerA => (D.R + 1) ^ D.graph.edges.length
  | .edgePower => (D.R + 1) ^ edge
  | .repetitionOne => repetitionOne

def treeDescriptor (D : InventoryData) : D.TreeRow → TreeDescriptor D.plus D.minus
  | .inl (node, _) => .plusNode node
  | .inr (.inl (node, _)) => .minusNode node
  | .inr (.inr _) => .padding

@[simp] theorem eval_treeLeftExpr (D : InventoryData) (edge rep : Nat)
    (side : TreeGeometry.Side) (address : List Nat) :
    NatExpressionCompiler.eval (registers D edge rep)
        (treeLeftExpr D.geometryBound D.L side address) =
      treeLeftNumerator D.graph.edges.length D.R D.geometryBound D.L side address := rfl

@[simp] theorem eval_treeRightExpr (D : InventoryData) (edge rep : Nat)
    (side : TreeGeometry.Side) (address : List Nat) :
    NatExpressionCompiler.eval (registers D edge rep)
        (treeRightExpr D.geometryBound D.L side address) =
      treeRightNumerator D.graph.edges.length D.R D.geometryBound D.L side address := by
  by_cases h : address = [] <;>
    simp [treeRightExpr, treeRightNumerator, h, registers, InventoryData.coordinateDenominator]

@[simp] theorem eval_treeBaselineExpr (D : InventoryData) (edge rep : Nat) (r : D.TreeRow) :
    (treeBaselineExpr D.geometryBound D.L (treeDescriptor D r)).eval (registers D edge rep) =
      treeBaselineParts D r := by
  rcases r with ⟨node, copy⟩ | (⟨node, copy⟩ | copy) <;>
    simp [treeDescriptor, treeBaselineExpr, treeBaselineParts, registers]

@[simp] theorem eval_treeDeadlineExpr (D : InventoryData) (edge rep : Nat) (r : D.TreeRow) :
    (treeDeadlineExpr D.geometryBound D.L (treeDescriptor D r)).eval (registers D edge rep) =
      treeDeadlineParts D r := by
  rcases r with ⟨node, copy⟩ | (⟨node, copy⟩ | copy)
  · by_cases h : node.val ∈ D.plus.leaves <;>
      simp [treeDescriptor, treeDeadlineExpr, treeDeadlineParts, h]
  · by_cases h : node.val ∈ D.minus.leaves <;>
      simp [treeDescriptor, treeDeadlineExpr, treeDeadlineParts, h]
  · simp [treeDescriptor, treeDeadlineExpr, treeDeadlineParts, registers]

@[simp] theorem eval_baselineExpr (D : InventoryData) (edge rep : Nat) :
    (baselineExpr D.geometryBound D.L).eval (registers D edge rep) =
      ⟨80 * (D.R + 1) ^ D.graph.edges.length * widthRadix D.geometryBound ^ D.L +
        10 * widthRadix D.geometryBound ^ D.L * rep * (D.R + 1) ^ edge,
        10 * widthRadix D.geometryBound ^ D.L⟩ := rfl

@[simp] theorem eval_betaExpr (D : InventoryData) (edge rep : Nat) :
    (betaExpr D.geometryBound D.L).eval (registers D edge rep) =
      ⟨10 * widthRadix D.geometryBound ^ D.L * (D.R + 1) ^ edge,
        10 * widthRadix D.geometryBound ^ D.L⟩ := rfl

end BinPackingGap.PackingCoordinateExpression

namespace BinPackingGap.PackingScalarExpression

open NatExpressionCompiler NaturalPackingNumerator IntegerPackingArithmetic

def baseTerm : Expr Variable :=
  .mul (.mul (.constant (200000000 * primaryBound)) (.input .vertexPower))
    (.input .geometry)

def primaryFactor : Expr Variable :=
  .mul (.mul (.constant 1000000) (.input .vertexPower)) (.input .geometry)

def secondaryFactor : Expr Variable := .mul (.constant 1000) (.input .geometry)

def negativeLabel (subclass : Subclass) : Expr Variable :=
  match subclass.role with
  | .anchor => .mul (.constant 2) (.input .labelPower)
  | _ => .constant 0

def negativeTerm (subclass : Subclass) : Expr Variable :=
  .add (.add (.mul primaryFactor (.constant (primaryParts subclass).neg))
    (.mul secondaryFactor (negativeLabel subclass))) (.input .coordinateNegative)

end BinPackingGap.PackingScalarExpression

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

variable [DecidableEq Other] [DecidableEq Extra]

def tapes (num : Descriptor → Expr Input) (den : Expr Input)
    (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) : Tape num den Other Extra → List Bool :=
  registerTapes (registers num den) base (values num den input other)

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra] in
@[simp] theorem tapes_extra (num : Descriptor → Expr Input) (den : Expr Input)
    (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (k : Extra) :
    tapes num den base input other (.inr k) = base (.inr k) := by
  apply registerTapes_other
  rintro ⟨i, hi⟩
  cases hi

end BinPackingGap.PackingMachineLayout

namespace BinPackingGap.PackingVertexUpdate

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input]

def updateRegisters (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary) :
    Fin 3 ↪ PackingMachineLayout.Reg num den Other where
  toFun := ![Sum.inl (Sum.inr three), Sum.inl (Sum.inl power),
    Sum.inl (Sum.inr temporary)]
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Ne.symm distinct]

omit [DecidableEq Descriptor] [DecidableEq Input] in
@[simp] theorem updateRegisters_zero (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary) :
    updateRegisters num den power three temporary distinct 0 =
      PackingMachineLayout.others num den three := rfl

omit [DecidableEq Descriptor] [DecidableEq Input] in
@[simp] theorem updateRegisters_one (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary) :
    updateRegisters num den power three temporary distinct 1 =
      PackingMachineLayout.inputs num den power := rfl

omit [DecidableEq Descriptor] [DecidableEq Input] in
@[simp] theorem updateRegisters_two (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary) :
    updateRegisters num den power three temporary distinct 2 =
      PackingMachineLayout.others num den temporary := rfl

end BinPackingGap.PackingVertexUpdate

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

namespace BinPackingGap.NatExpressionCompiler

variable {α β : Type}

def substitute (replacement : α → Expr β) : Expr α → Expr β
  | .constant n => .constant n
  | .input a => replacement a
  | .add a b => .add (substitute replacement a) (substitute replacement b)
  | .mul a b => .mul (substitute replacement a) (substitute replacement b)
  | .monus a b => .monus (substitute replacement a) (substitute replacement b)

def rename (f : α → β) : Expr α → Expr β := substitute (fun a => .input (f a))

end BinPackingGap.NatExpressionCompiler

namespace BinPackingGap.PackingItemExpression

open NatExpressionCompiler

def coordinateVariable : PackingCoordinateExpression.Input → Variable
  | .geometryDg => .geometry
  | .totalPowerA => .totalPower
  | .edgePower => .edgePower
  | .repetitionOne => .repetitionOne

def scalarReplacement (coordinate : PackingCoordinateExpression.Parts) :
    PackingScalarExpression.Variable → Expr Variable
  | .vertexPower => .input .vertexPower
  | .geometry => .input .geometry
  | .labelPower => .input .labelPower
  | .coordinatePositive => rename coordinateVariable coordinate.pos
  | .coordinateNegative => rename coordinateVariable coordinate.neg

def denominator : Expr Variable :=
  .mul (.mul (.constant (10 ^ 9 * primaryBound))
    (.input .vertexPower)) (.input .geometry)

end BinPackingGap.PackingItemExpression

end

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionAgreementMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionAgreementMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition

theorem run_step (view : View) (active : ¬ Terminal view.label) :
    run view = run (next view) := by
  rw [run, dite_eq_right active]

theorem run_terminal (view : View) (stopped : Terminal view.label) : run view = view := by
  rw [run, dite_eq_left stopped]

theorem runTrace (view : View) :
    ∃ steps, steps ≤ potential view ∧
      (advance machine.step)^[steps] (some view.cfg) = some (run view).cfg := by
  induction view using (measure potential).wf.induction with
  | h view ih =>
      by_cases stopped : Terminal view.label
      · refine ⟨0, Nat.zero_le _, ?_⟩
        simp only [Function.iterate_zero, id_eq, run_terminal view stopped]
      · have smaller := next_decreases view stopped
        obtain ⟨steps, bounded, trace⟩ := ih (next view) smaller
        refine ⟨steps + 1, by omega, ?_⟩
        rw [Function.iterate_succ_apply]
        simp only [advance_some, step_view view stopped]
        rw [trace, run_step view stopped]

theorem run_isTerminal (view : View) : Terminal (run view).label := by
  induction view using (measure potential).wf.induction with
  | h view ih =>
      by_cases stopped : Terminal view.label
      · rw [run_terminal view stopped]
        exact stopped
      · rw [run_step view stopped]
        exact ih (next view) (next_decreases view stopped)

theorem run_drainAssignments (assignments : List Bool) :
    run ⟨.drainAssignments, [], assignments⟩ = resultView false := by
  induction assignments with
  | nil =>
      rw [run_step _ (by simp [Terminal])]
      exact run_terminal _ (Or.inr rfl)
  | cons bit assignments ih =>
      rw [run_step _ (by simp [Terminal])]
      exact ih

theorem run_drainFixed (fixed assignments : List Bool) :
    run ⟨.drainFixed, fixed, assignments⟩ = resultView false := by
  induction fixed with
  | nil =>
      rw [run_step _ (by simp [Terminal])]
      exact run_drainAssignments assignments
  | cons bit fixed ih =>
      rw [run_step _ (by simp [Terminal])]
      exact ih

theorem run_checkEnd_empty : run ⟨.checkEnd, [], []⟩ = resultView true := by
  rw [run_step _ (by simp [Terminal])]
  exact run_terminal _ (Or.inl rfl)

theorem run_skipFrame (bits fixed suffix : List Bool) :
    run ⟨.skipFlag, fixed, BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix⟩ =
      run ⟨.entry, fixed, suffix⟩ := by
  induction bits with
  | nil =>
      rw [run_step _ (by simp [Terminal])]
      rfl
  | cons bit bits ih =>
      rw [run_step _ (by simp [Terminal])]
      change run ⟨.skipDigit, fixed,
        bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix)⟩ = _
      rw [run_step _ (by simp [Terminal])]
      exact ih

theorem run_compareFrame (left right fixedSuffix assignmentSuffix : List Bool) :
    run ⟨.compareFlag,
        BinPackingCompleteness.BinaryEncoding.frame left ++ fixedSuffix,
        BinPackingCompleteness.BinaryEncoding.frame right ++ assignmentSuffix⟩ =
      if left = right then run ⟨.entry, fixedSuffix, assignmentSuffix⟩
        else resultView false := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          rw [run_step _ (by simp [Terminal])]
          simp [next, bothView, BinPackingCompleteness.BinaryEncoding.frame]
      | cons bit right =>
          rw [run_step _ (by simp [Terminal])]
          simp [next, bothView, BinPackingCompleteness.BinaryEncoding.frame, run_drainFixed]
  | cons bit left ih =>
      cases right with
      | nil =>
          rw [run_step _ (by simp [Terminal])]
          simp [next, bothView, BinPackingCompleteness.BinaryEncoding.frame, run_drainFixed]
      | cons digit right =>
          rw [run_step _ (by simp [Terminal])]
          change run ⟨.compareDigit,
            bit :: (BinPackingCompleteness.BinaryEncoding.frame left ++ fixedSuffix),
            digit :: (BinPackingCompleteness.BinaryEncoding.frame right ++ assignmentSuffix)⟩ = _
          rw [run_step _ (by simp [Terminal])]
          by_cases equal : bit = digit
          · subst digit
            cases bit <;> simpa [next, bothView, BinPackingCompleteness.BinaryEncoding.frame] using ih right
          · simp [next, bothView, equal, run_drainFixed]

noncomputable def rawInTime (fixed assignments : List Bool) : RawRun fixed assignments := by
  let view : View := ⟨.entry, fixed, assignments⟩
  let trace := runTrace view
  let steps := Classical.choose trace
  let result := Classical.choose_spec trace
  refine ⟨run view, run_isTerminal view, ?_⟩
  exact {
    steps := steps
    evals_in_steps := by
      change (advance machine.step)^[steps] (some view.cfg) = some (run view).cfg
      exact result.2
    steps_le_m := by
      simpa only [steps, view, potential, rank, agreementTime, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_ofNat] using result.1 }

end BinPackingGap.ExtensionAgreementMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionCapacityBounds
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionCapacityMachine

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

abbrev State (A : Type) := BinaryAddMachine.State (A × Ordering)

def numberTapes : Field → (Fin 3 ↪ Tape)
  | .numerator => ⟨![2, 5, 10], by decide⟩
  | .denominator => ⟨![2, 6, 10], by decide⟩
  | .label => ⟨![3, 7, 10], by decide⟩

def compareTapes : Compare → (Fin 5 ↪ Tape)
  | .label => ⟨![7, 4, 8, 9, 10], by decide⟩
  | .capacity => ⟨![11, 12, 8, 9, 10], by decide⟩

def fractionTapes : ExtensionFractionMachine.Tape ↪ Tape :=
  ⟨![0, 1, 5, 6, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21], by decide⟩

def afterNumber {Λ : Type} (labels : Label → Λ) : Field → Option Λ
  | .numerator => some (labels (.number .denominator .scan))
  | .denominator => some (labels (.number .label .scan))
  | .label => some (labels (.compare .label .leftOut))

variable {K Λ A : Type} [DecidableEq K]

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => BinaryAddMachine.clean state.1.1.1)
    (match exit with | none => .halt | some label => .goto fun _ => label)

def finalTapes (result : Bool) : Tape → List Bool := fun k => if k = 0 then [result] else []

end BinPackingGap.ExtensionCapacityMachine

namespace BinPackingGap.ExtensionArithmeticBounds

open BinPackingGames.Foundations.Complexity

theorem fractionTime_le (operandLength inputLength : Nat)
    (bounded : operandLength ≤ 4 * (inputLength + 1)) :
    ExtensionFractionMachine.timePolynomial.eval operandLength ≤
      timePolynomial.eval inputLength := by
  apply (MachineComposition.natPolynomial_eval_mono
    ExtensionFractionMachine.timePolynomial bounded).trans
  simp only [ExtensionFractionMachine.timePolynomial, timePolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  nlinarith

end BinPackingGap.ExtensionArithmeticBounds

namespace BinPackingGap.ExtensionCapacityMachine

section

open Turing
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

def clean : State Unit := BinaryAddMachine.clean ((), .eq)

def work (numerator denominator items assignments selected a d j nextNumerator nextDenominator
    : List Bool) (scratch : List Bool := []) : Tape → List Bool
  | 0 => numerator
  | 1 => denominator
  | 2 => items
  | 3 => assignments
  | 4 => selected
  | 5 => a
  | 6 => d
  | 7 => j
  | 10 => scratch
  | 11 => nextNumerator
  | 12 => nextDenominator
  | _ => []

theorem update0 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 0 r = work r D i w s a d j U V t := by
  funext k; fin_cases k <;> rfl
theorem update1 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 1 r = work N r i w s a d j U V t := by
  funext k; fin_cases k <;> rfl
theorem update2 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 2 r = work N D r w s a d j U V t := by
  funext k; fin_cases k <;> rfl
theorem update3 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 3 r = work N D i r s a d j U V t := by
  funext k; fin_cases k <;> rfl
theorem update5 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 5 r = work N D i w s r d j U V t := by
  funext k; fin_cases k <;> rfl
theorem update6 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 6 r = work N D i w s a r j U V t := by
  funext k; fin_cases k <;> rfl
theorem update7 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 7 r = work N D i w s a d r U V t := by
  funext k; fin_cases k <;> rfl
theorem update10 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 10 r = work N D i w s a d j U V r := by
  funext k; fin_cases k <;> rfl
theorem update11 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 11 r = work N D i w s a d j r V t := by
  funext k; fin_cases k <;> rfl
theorem update12 (N D i w s a d j U V t r : List Bool) :
    Function.update (work N D i w s a d j U V t) 12 r = work N D i w s a d j U r t := by
  funext k; fin_cases k <;> rfl

end

end BinPackingGap.ExtensionCapacityMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionPairMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionPairMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition

abbrev Label := BinPackingCompleteness.BinaryPairMachine.Label
abbrev State := BinPackingCompleteness.BinaryPairMachine.State
abbrev machine := BinPackingCompleteness.BinaryPairMachine.machine
abbrev cfg (label : Option Label) (input counter saved : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  BinPackingCompleteness.BinaryPairMachine.cfg label input counter saved register

abbrev pairHaltInTime := BinPackingCompleteness.BinaryPairMachine.pairHaltInTime

@[instance_reducible] def alphabetFintype (k : machine.K) : Fintype (machine.Γ k) :=
  inferInstanceAs (Fintype Bool)

end BinPackingGap.ExtensionPairMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionShapeMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionShapeMachine

open BinaryEncoding
open BinPackingCompleteness.BinaryNameMachine (finalDigit canonical)

theorem finalDigit_true_iff (bits : List Bool) :
    finalDigit bits (some true) = some true ↔ canonical bits = true := by
  cases bits with
  | nil => simp [finalDigit, canonical]
  | cons bit bits =>
      simp only [finalDigit, canonical]
      have hsome : ∀ (ds : List Bool) (b : Bool),
          ∃ last, finalDigit ds (some b) = some last := by
        intro ds
        induction ds with
        | nil => intro b; exact ⟨b, rfl⟩
        | cons d ds ih => intro b; exact ih d
      obtain ⟨last, hlast⟩ := hsome bits bit
      rw [hlast]
      simp

theorem run_frame (next : Continuation) (bits rest : List Bool) (last : Bool)
    (valid : finalDigit bits (some last) = some true) :
    run (.name next last) (BinPackingCompleteness.BinaryEncoding.frame bits ++ rest) =
      run (afterName next) rest := by
  induction bits generalizing last with
  | nil =>
      have hlast : last = true := by simpa [finalDigit] using valid
      subst last
      simp [BinPackingCompleteness.BinaryEncoding.frame, run, nextMode]
  | cons bit bits ih =>
      have hvalid : finalDigit bits (some bit) = some true := valid
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append, run, nextMode]
        using ih bit hvalid

theorem frame_inverse (next : Continuation) (last : Bool) (input : List Bool)
    (accepted : run (.name next last) input = .done) :
    ∃ bits rest, input = BinPackingCompleteness.BinaryEncoding.frame bits ++ rest ∧
      finalDigit bits (some last) = some true ∧
      run (afterName next) rest = .done := by
  induction input using List.twoStepInduction generalizing last with
  | nil => simp [run] at accepted
  | singleton flag =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], [], rfl, rfl, by simpa [run, nextMode] using accepted⟩
      | true => simp [run, nextMode] at accepted
  | cons_cons flag bit input ih _ =>
      cases flag with
      | false =>
          cases last with
          | false => simp [run, nextMode] at accepted
          | true =>
              exact ⟨[], bit :: input, rfl, rfl,
                by simpa [run, nextMode] using accepted⟩
      | true =>
          have haccepted : run (.name next bit) input = .done := by
            simpa only [run, nextMode] using accepted
          obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := ih bit haccepted
          refine ⟨bit :: bits, rest, ?_, hvalid, hrest⟩
          simp [BinPackingCompleteness.BinaryEncoding.frame, hinput]

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution

def instruction (kind : Kind) : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop 0 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push 2 (fun state => state.2.getD false)
            (.load (fun state => (nextMode state.1 (state.2.getD false), none))
              (.goto fun _ => .scan)))
          (.load (fun state => (state.1, none)) (.goto fun _ => .restore)))
  | .restore => loopAt 2 1 id false .restore (some .finish)
  | .finish =>
      .push 1 (fun state => decide (state.1 = .done))
        (.load (fun _ => (start kind, none)) .halt)

abbrev machine (kind : Kind) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (start kind, none)
  m := instruction kind

def cfg (kind : Kind) (label : Option Label) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool := none) : (machine kind).Cfg :=
  ⟨label, (mode, register), tapes input output saved⟩

theorem step_scan_empty (kind : Kind) (output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    (machine kind).step (cfg kind (some .scan) [] output saved mode register) =
      some (cfg kind (some .restore) [] output saved mode) := by
  change some (TM2.stepAux (instruction kind .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input]
  all_goals rfl

theorem step_scan_cons (kind : Kind) (bit : Bool) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    (machine kind).step (cfg kind (some .scan) (bit :: input) output saved mode register) =
      some (cfg kind (some .scan) input output (bit :: saved) (nextMode mode bit)) := by
  change some (TM2.stepAux (instruction kind .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input, update_saved]
  all_goals rfl

theorem scanTrace (kind : Kind) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    (advance (machine kind).step)^[input.length + 1]
      (some (cfg kind (some .scan) input output saved mode register)) =
      some (cfg kind (some .restore) [] output (input.reverse ++ saved) (run mode input)) := by
  induction input generalizing saved mode register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run, List.reverse_nil, List.nil_append] using
          step_scan_empty kind output saved mode register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_scan_cons]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (bit :: saved) (nextMode mode bit) none

theorem restoreTrace (kind : Kind) (saved output : List Bool)
    (mode : Mode) (register : Option Bool) :
    (advance (machine kind).step)^[saved.length + 1]
      (some (cfg kind (some .restore) [] output saved mode register)) =
      some (cfg kind (some .finish) [] (saved.reverse ++ output) [] mode) := by
  change (nextAt (1 : Fin 3) (instruction kind))^[saved.length + 1]
    (some ⟨some .restore, (mode, register), tapes [] output saved⟩) =
    some ⟨some .finish, (mode, none), tapes [] (saved.reverse ++ output) []⟩
  have trace := transferAt_steps (2 : Fin 3) 1 (by decide) id false .restore (some .finish)
    (instruction kind) rfl (tapes [] [] []) saved output mode register
  simpa only [tapesAt, update_saved, update_output, List.map_id_fun, id_eq] using trace

theorem step_finish (kind : Kind) (output : List Bool) (mode : Mode)
    (register : Option Bool) :
    (machine kind).step (cfg kind (some .finish) [] output [] mode register) =
      some (cfg kind none [] (decide (mode = .done) :: output) [] (start kind)) := by
  change some (TM2.stepAux (instruction kind .finish) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_output]
  all_goals rfl

theorem rawTrace (kind : Kind) (input : List Bool) :
    (advance (machine kind).step)^[2 * input.length + 3]
      (some (cfg kind (some .scan) input [] [] (start kind))) =
      some (cfg kind none [] (accepts kind input :: input) [] (start kind)) := by
  have first := scanTrace kind input [] [] (start kind) none
  simp only [List.append_nil] at first
  have second := restoreTrace kind input.reverse [] (run (start kind) input) none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at second
  have third : (advance (machine kind).step)^[1]
      (some (cfg kind (some .finish) [] input [] (run (start kind) input))) =
      some (cfg kind none [] (accepts kind input :: input) [] (start kind)) := by
    simpa only [Function.iterate_one, advance_some, accepts] using
      step_finish kind input (run (start kind) input) none
  have time : 2 * input.length + 3 = (input.length + 1) + (input.length + 1) + 1 := by omega
  rw [time]
  exact joinTrace (joinTrace first second) third

theorem initList_eq (kind : Kind) (input : List Bool) :
    initList (machine kind) input = cfg kind (some .scan) input [] [] (start kind) := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem haltList_eq (kind : Kind) (output : List Bool) :
    haltList (machine kind) output = cfg kind none [] output [] (start kind) := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

end BinPackingGap.ExtensionShapeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionValidationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionValidationMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition

abbrev State := BinaryAddMachine.State (Unit × Ordering)

def clean : State := BinaryAddMachine.clean ((), .eq)

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => clean) (.goto fun _ => label)

theorem bits_eq_nil_iff (n : Nat) : n.bits = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg BinPackingCompleteness.BinaryEncoding.bitsValue h
    simpa only [BinPackingCompleteness.BinaryEncoding.bitsValue_bits,
      BinPackingCompleteness.BinaryEncoding.bitsValue] using hv
  · rintro rfl
    rfl

end BinPackingGap.ExtensionValidationMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionVerifierMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionVerifierMachine.Fields

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer

theorem run_frame (field : Field) (bits suffix : List Bool) (words : Words) :
    run (.flag field) words (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix) =
      run (afterField field)
        (prepend words field.block (BinPackingCompleteness.BinaryEncoding.frame bits).reverse)
        suffix := by
  induction bits generalizing words with
  | nil => simp [BinPackingCompleteness.BinaryEncoding.frame, run, nextMode, Mode.block]
  | cons bit bits ih =>
      simp only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append, run,
        nextMode, Mode.block]
      rw [ih]
      simp only [prepend_prepend, List.reverse_cons, List.append_assoc,
        List.singleton_append]

def instruction : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop 0 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.branch (fun state => decide (state.1.block = .bins))
            (.push 1 (fun state => state.2.getD false) scanFinish)
            (.branch (fun state => decide (state.1.block = .items))
              (.push 2 (fun state => state.2.getD false) scanFinish)
              (.push 3 (fun state => state.2.getD false) scanFinish)))
          (.load (fun _ => (.flag .bins, none)) (.goto fun _ => .restoreBins)))
  | .restoreBins => loopAt 1 4 id false .restoreBins (some .restoreItems)
  | .restoreItems => loopAt 2 5 id false .restoreItems (some .restoreFixed)
  | .restoreFixed => loopAt 3 6 id false .restoreFixed none

abbrev machine : FinTM2 where
  K := Fin 7
  k₀ := 0
  k₁ := 4
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (.flag .bins, none)
  m := instruction

def cfg (label : Option Label) (input : List Bool) (saved output : Words)
    (mode : Mode := .flag .bins) (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (mode, register), tapes input saved output⟩

theorem step_scan_empty (saved output : Words) (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) [] saved output mode register) =
      some (cfg (some .restoreBins) [] saved output) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, tapes, update_input]
  all_goals rfl

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .scan) input empty empty := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

end BinPackingGap.ExtensionVerifierMachine.Fields

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

theorem workBound (B : Nat) (N D i w s a d j U V : List Bool)
    (hN : N.length ≤ B + 2) (hD : D.length ≤ B + 2)
    (hi : i.length ≤ B + 2) (hw : w.length ≤ B + 2) (hs : s.length ≤ B + 2)
    (ha : a.length ≤ B + 2) (hd : d.length ≤ B + 2) (hj : j.length ≤ B + 2)
    (hU : U.length ≤ B + 2) (hV : V.length ≤ B + 2) :
    ∀ k : Tape, (work N D i w s a d j U V [] k).length ≤ B + 2 := by
  intro k
  fin_cases k <;> simp_all [work]

end BinPackingGap.ExtensionCapacityMachine

namespace BinPackingGap.ExtensionCapacityOuterMachine

open Turing BinPackingGames.Foundations.Complexity BinPackingGames.Reduction

abbrev State := ExtensionCapacityMachine.State Unit

def clean : State := BinaryAddMachine.clean ((), .eq)

end BinPackingGap.ExtensionCapacityOuterMachine

namespace BinPackingGap.ExtensionVerifierMachine

open Turing BinPackingGames.Foundations.Complexity
open ExtensionMachineRegisters (Lens)

abbrev LocalState : Helper → Type
  | .pair => ExtensionPairMachine.State
  | .query | .witness => ExtensionShapeMachine.State
  | .fields => Fields.State
  | .validation => ExtensionValidationMachine.State
  | .agreement => ExtensionAgreementMachine.State
  | .capacity => ExtensionCapacityOuterMachine.State

instance instFintypeLocalState (h : Helper) : Fintype (LocalState h) := by cases h <;> infer_instance
instance instDecidableEqLocalState (h : Helper) : DecidableEq (LocalState h) := by cases h <;> infer_instance

abbrev Registers := (h : Helper) → LocalState h
abbrev State := Registers × Option Bool

def register (h : Helper) : Lens State (LocalState h) where
  get state := state.1 h
  set state value := (Function.update state.1 h value, state.2)
  get_set := by intros; simp
  set_get := by intros; simp
  set_set := by intros; simp

end BinPackingGap.ExtensionVerifierMachine

end OAI
end


