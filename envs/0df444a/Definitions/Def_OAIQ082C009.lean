-- Prove2me | Definitions.Def_OAIQ082C009
-- name    : OAIQ082C009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:28:54.989311+00:00
-- url     : https://prove2.me/theorems/b384fa38-65bc-4fac-9a86-a2baa823b5bb
-- title:
--   Definitions bundle OAIQ082C009 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 218 declarations of OpenAI's Lean: 111 definitions, 9 inductive types or structures, 9 instances and 89 theorems. The definitions and types are `OAI.BinPackingGames.Foundations.PCP.CodeComposition.singletonMask`, `OAI.BinPackingGap.GraphPackingJobs.prefixTimePolynomial`, `OAI.BinPackingGap.GraphPackingProgram.endpointTimePolynomial`, `OAI.BinPackingGap.GraphPackingRegisters.CountSource`, `OAI.BinPackingGap.IndividualConfiguration.singleton`, `OAI.BinPackingGap.IndividualFeasible`, `OAI.BinPackingGap.Instance.Reindexing`, `OAI.BinPackingGap.Instance.Reindexing.symm`, `OAI.BinPackingGap.LabelConservation.prefixOutside`, `OAI.BinPackingGap.LiteralSlotGraphMachine.Program`, `OAI.BinPackingGap.LiteralSlotGraphMachine.State`, `OAI.BinPackingGap.LiteralSlotGraphMachine.changeControl`, `OAI.BinPackingGap.LiteralSlotGraphMachine.compareGuard`, `OAI.BinPackingGap.LiteralSlotGraphMachine.compareVariables`, `OAI.BinPackingGap.LiteralSlotGraphMachine.countHeader`, `OAI.BinPackingGap.LiteralSlotGraphMachine.initialState`, `OAI.BinPackingGap.LiteralSlotGraphMachine.isEdge`, `OAI.BinPackingGap.LiteralSlotGraphMachine.mapControl`, `OAI.BinPackingGap.LiteralSlotGraphMachine.pushBit`, `OAI.BinPackingGap.LiteralSlotGraphMachine.readSign`, `OAI.BinPackingGap.LiteralSlotGraphMachine.readVariable`, `OAI.BinPackingGap.LiteralSlotGraphMachine.resetHead`, `OAI.BinPackingGap.LiteralSlotGraphMachine.saveHead`, `OAI.BinPackingGap.LiteralSlotGraphMachine.sequence`, `OAI.BinPackingGap.LiteralSlotGraphMachine.skip`, `OAI.BinPackingGap.LiteralSlotGraphMachine.skipField`, `OAI.BinPackingGap.MachineBoundedIteration.GrowthBound`, `OAI.BinPackingGap.MachineBoundedIteration.inputBits`, `OAI.BinPackingGap.MachineControlEmbedding.configuration`, `OAI.BinPackingGap.MachineKeepDecision.Symbols`, `OAI.BinPackingGap.MachineKeepDecision.auxProgram`, `OAI.BinPackingGap.MachineKeepDecision.inputConfig`, `OAI.BinPackingGap.MachineKeepDecision.inputTapes`, `OAI.BinPackingGap.MachineKeepDecision.returnConfig`, `OAI.BinPackingGap.MachineKeepDecision.returnTapes`, `OAI.BinPackingGap.NumericalSize.ofItem`, `OAI.BinPackingGap.PCPFoundation.gap`, `OAI.BinPackingGap.PCPFoundation.rho`, `OAI.BinPackingGap.Packing.configuration`, `OAI.BinPackingGap.Packing.enlarge` and 80 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_BinaryToTallyMachine`, `BinPacking_Arithmetic_GraphPackingRegisters`, `BinPacking_Arithmetic_NatExpression`, `BinPacking_Arithmetic_PackingRegisterFrame`, `BinPacking_Arithmetic_ResetExpressionCompiler`, `BinPacking_Configurations_ConfigurationLP`, `BinPacking_Hardness_LiteralSlotGraphEnumeration`, `BinPacking_Hardness_PCPPackingGap`, `BinPacking_Inventory_CurrentMatches`, `BinPacking_Inventory_IntegralSpeciesCounts`, `BinPacking_Inventory_LabelConservation`, `BinPacking_Inventory_PhysicalPoolLift`, `BinPacking_Machines_GraphPackingGlobalExecution`, `BinPacking_Machines_GraphPackingJobEdge`, `BinPacking_Machines_GraphPackingPreparation`, `BinPacking_Machines_GraphPackingPreparationFinish`, `BinPacking_Machines_GraphPackingVerticesBound`, `BinPacking_Machines_IntegerPackingArithmetic`, `BinPacking_Machines_MachineBoundedIteration`, `BinPacking_Machines_MachineControlEmbedding`, `BinPacking_Machines_MachineKeepDecisionTyped`, `BinPacking_Machines_PackingJobLoop`, `BinPacking_Machines_PackingPowerProgram`, `BinPacking_Machines_PackingSetupGraph`, `BinPacking_Machines_PackingVertexUpdate`, `BinPacking_PCP_Queries`, `BinPacking_Packing_FractionWidth`, `BinPacking_Packing_K4Graph`, `BinPacking_Packing_PackingScalar`, `BinPacking_Packing_PackingScalarExpression`, `BinPacking_Packing_PairExpressionCompiler`, `BinPacking_Search_SearchFinalizeMachine`, `BinPacking_Search_SearchFixedReplaceMachine`, `BinPacking_Search_SearchInitialItemsMachine`, `BinPacking_Search_SearchInitialShapeMachine`, `BinPacking_Search_SearchInitializeEncoding`, `BinPacking_Search_SearchPrepareMachine`, `BinPacking_Search_SearchStageMachines`, `BinPacking_Search_SearchUpdateMachine`, `BinPacking_Trees_IntegerTreeGeometry`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C000`, `OAIQ082C001`, `OAIQ082C002`, `OAIQ082C003` and `OAIQ082C004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C014` and `OAIQ082C015`.
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
import Definitions.Def_OAIQ082C004

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.NatExpressionCompiler

universe u

variable {α : Type u}

instance nodeFintype : (expression : Expr α) → Fintype (Node expression)
  | .constant _ => inferInstanceAs (Fintype Unit)
  | .input _ => inferInstanceAs (Fintype Unit)
  | .add left right =>
      letI : Fintype (Node left) := nodeFintype left
      letI : Fintype (Node right) := nodeFintype right
      inferInstanceAs (Fintype (Unit ⊕ (Node left ⊕ Node right)))
  | .mul left right =>
      letI : Fintype (Node left) := nodeFintype left
      letI : Fintype (Node right) := nodeFintype right
      inferInstanceAs (Fintype (Unit ⊕ (Node left ⊕ Node right)))
  | .monus left right =>
      letI : Fintype (Node left) := nodeFintype left
      letI : Fintype (Node right) := nodeFintype right
      inferInstanceAs (Fintype (Unit ⊕ (Node left ⊕ Node right)))

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

noncomputable section

namespace BinPackingGap.PackingRegisterFrame

open BinaryRegisterProgram

variable {Local Global K : Type}

@[simp] theorem localSlots_reg (slot : (Global ⊕ Fin 6) ↪ K)
    (register : Local ↪ Global) (r : Local) :
    localSlots slot register (.inl r) = slot (.inl (register r)) := rfl

@[simp] theorem localSlots_scratch (slot : (Global ⊕ Fin 6) ↪ K)
    (register : Local ↪ Global) (i : Fin 6) :
    localSlots slot register (.inr i) = slot (.inr i) := rfl

end BinPackingGap.PackingRegisterFrame

end

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

def singletonMask {A : Type*} [DecidableEq A] (a : A) : Cube A :=
  fun i => decide (i = a)

end BinPackingGames.Foundations.PCP.CodeComposition

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_K4Graph
attribute [-instance] _root_.OAI.BinPackingGap.instFintypeGlobalSpecies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

def completeFourGraph : GraphInput where
  n := 4
  edges := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
  ordered := by decide
  distinct := by decide

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

def inputBits {α : Type} (encode : α → List Bool) (p : Nat × α) : List Bool :=
  encodeWord p.1 ++ encode p.2

@[simp] theorem inputBits_length {α : Type} (encode : α → List Bool) (p : Nat × α) :
    (inputBits encode p).length = p.1 + 1 + (encode p.2).length := by
  simp [inputBits, encodeWord_length]

def GrowthBound {α : Type} (encode : α → List Bool) (step : α → α)
    (growth : Polynomial Nat) : Prop :=
  ∀ (p : Nat × α) (i : Nat), i ≤ p.1 →
    (encode (step^[i] p.2)).length ≤ growth.eval (inputBits encode p).length

end BinPackingGap.MachineBoundedIteration

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_MachineKeepDecisionTyped
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.MachineKeepDecision

section

open Turing BinPackingGames.Foundations
open Complexity

abbrev Symbols (M : FinTM2) :=
  MachineEmbedding.Alphabet M.Γ (fun _ : ExtraTape => M.Γ M.k₀)

def auxProgram (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool)
    (output : M.Γ M.k₁ ≃ Bool) : Phase → TM2.Stmt (Symbols M) (Label M) (State M)
  | .parse => .pop (.inl M.k₀) (fun s bit => (s.1, bit))
      (.branch (fun s => input (s.2.getD (input.symm false)))
        (.pop (.inl M.k₀) (fun s bit => (s.1, bit))
          (.push (.inr .saved) (fun s => s.2.getD (input.symm false))
            (.load (fun s => (s.1, none)) (.goto (fun _ => .inr .parse)))))
        (.load (fun s => (s.1, none)) (.goto (fun _ => .inl M.main))))
  | .transfer => BinPackingGames.Reduction.MachineTransfer.loopAt
      (K := Tape M) (Λ := Label M) (σ := M.σ) (Γ := Symbols M) (.inr .saved) (.inr .output)
      id (input.symm false) (.inr .transfer) (some (.inr .finish))
  | .finish => .pop (.inl M.k₁)
      (fun s bit => (s.1, bit.map (fun b => input.symm (output b))))
      (.push (.inr .output) (fun s => s.2.getD (input.symm false))
        (.load (fun _ => (M.initialState, none)) .halt))

def inputTapes (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    (k : Tape M) → List (Symbols M k) :=
  MachineEmbedding.tapes (initList M word).stk (extraTapes M saved [])

@[simp] theorem inputTapes_input (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    inputTapes M word saved (.inl M.k₀) = word := by
  simp [inputTapes, initList]

@[simp] theorem inputTapes_saved (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    inputTapes M word saved (.inr .saved) = saved := rfl

def inputConfig (M : FinTM2) (word saved : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr .parse), (M.initialState, none), inputTapes M word saved⟩

def returnTapes (M : FinTM2) (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    (k : Tape M) → List (Symbols M k) :=
  MachineEmbedding.tapes (haltList M [answer]).stk (extraTapes M [] word)

def returnConfig (M : FinTM2) (answer : M.Γ M.k₁) (word : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr .finish), (M.initialState, none), returnTapes M answer word⟩

theorem inputTapes_update_input (M : FinTM2)
    (word saved replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word saved) (.inl M.k₀) replacement =
      inputTapes M replacement saved := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList]
    · simp [inputTapes, initList, h]
  | inr k => simp [inputTapes]

theorem inputTapes_update_saved (M : FinTM2)
    (word saved replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word saved) (.inr .saved) replacement =
      inputTapes M word replacement := by
  funext k
  cases k with
  | inl k => simp [inputTapes]
  | inr k => cases k <;> simp [inputTapes, extraTapes]

end

open Turing BinPackingGames.Foundations.Complexity

end BinPackingGap.MachineKeepDecision

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_FractionWidth
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace Packing

variable {I : Instance} {b : ℕ}

theorem bin_capacity (p : Packing I b) (j : Fin b) :
    ∑ i ∈ p.binItems j, I.size i ≤ 1 := by
  simpa [binItems, Finset.sum_filter] using p.capacity j

def enlarge (p : Packing I b) {c : ℕ} (hbc : b ≤ c) : Packing I c where
  assignment i := Fin.castLE hbc (p.assignment i)
  capacity j := by
    by_cases hj : j.val < b
    · let k : Fin b := ⟨j.val, hj⟩
      have heq : ∀ i, Fin.castLE hbc (p.assignment i) = j ↔ p.assignment i = k := by
        intro i
        simp [Fin.ext_iff, k]
      simpa only [heq] using p.capacity k
    · have heq : ∀ i, Fin.castLE hbc (p.assignment i) ≠ j := by
        intro i h
        have hv := congrArg Fin.val h
        have hi := (p.assignment i).isLt
        exact hj (hv ▸ hi)
      simp [heq]

end Packing

theorem opt_attained (I : Instance) : HasPacking I (opt I) := by
  classical
  exact Nat.find_spec (exists_packing I)

theorem opt_le_of_hasPacking {I : Instance} {b : ℕ} (h : HasPacking I b) :
    opt I ≤ b := by
  classical
  exact Nat.find_min' (exists_packing I) h

theorem opt_le_n (I : Instance) : opt I ≤ I.n :=
  opt_le_of_hasPacking ⟨singletonPacking I⟩

theorem opt_eq_zero_of_n_eq_zero (I : Instance) (h : I.n = 0) : opt I = 0 := by
  have := opt_le_n I
  omega

theorem HasPacking.mono {I : Instance} {b c : ℕ} (h : HasPacking I b) (hbc : b ≤ c) :
    HasPacking I c := by
  obtain ⟨p⟩ := h
  exact ⟨p.enlarge hbc⟩

theorem hasPacking_iff_opt_le (I : Instance) (b : ℕ) :
    HasPacking I b ↔ opt I ≤ b :=
  ⟨opt_le_of_hasPacking, fun h => (opt_attained I).mono h⟩

noncomputable def packingOfFintype {ι : Type*} [Fintype ι]
    (s : ι → ℚ) (hpos : ∀ i, 0 < s i) (hle : ∀ i, s i ≤ 1)
    {b : ℕ} (a : ι → Fin b)
    (hcap : ∀ j, (∑ i, if a i = j then s i else 0) ≤ 1) :
    Packing (Instance.ofFintype s hpos hle) b where
  assignment i := a ((Fintype.equivFin ι).symm i)
  capacity j := by
    change (∑ i : Fin (Fintype.card ι),
      if a ((Fintype.equivFin ι).symm i) = j
      then s ((Fintype.equivFin ι).symm i) else 0) ≤ 1
    rw [(Fintype.equivFin ι).symm.sum_comp
      (fun i : ι => if a i = j then s i else 0)]
    exact hcap j

namespace IndividualConfiguration

variable {I : Instance}

def singleton (i : I.Item) : IndividualConfiguration I :=
  ⟨{i}, by simpa using I.size_le_one i⟩

end IndividualConfiguration

namespace Packing

def configuration {I : Instance} {b : ℕ} (p : Packing I b) (j : Fin b) :
    IndividualConfiguration I := ⟨p.binItems j, p.bin_capacity j⟩

end Packing

namespace Instance

structure Reindexing (I J : Instance) where
  equiv : I.Item ≃ J.Item
  size_eq : ∀ i, I.size i = J.size (equiv i)

namespace Reindexing

variable {I J : Instance}

def symm (e : Reindexing I J) : Reindexing J I where
  equiv := e.equiv.symm
  size_eq j := by
    simpa using (e.size_eq (e.equiv.symm j)).symm

end Reindexing

end Instance

namespace Packing

def reindex {I J : Instance} {b : ℕ} (p : Packing I b)
    (e : Instance.Reindexing I J) : Packing J b where
  assignment j := p.assignment (e.equiv.symm j)
  capacity k := by
    calc
      (∑ j : J.Item, if p.assignment (e.equiv.symm j) = k then J.size j else 0) =
          ∑ i : I.Item, if p.assignment (e.equiv.symm (e.equiv i)) = k
            then J.size (e.equiv i) else 0 :=
        (e.equiv.sum_comp (fun j =>
          if p.assignment (e.equiv.symm j) = k then J.size j else 0)).symm
      _ = ∑ i : I.Item, if p.assignment i = k then I.size i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Equiv.symm_apply_apply, ← e.size_eq i]
      _ ≤ 1 := p.capacity k

end Packing

namespace RawPacking

def ofPacking {I : Instance} {b : ℕ} (q : Packing I b) : RawPacking where
  bins := b
  assignments := List.ofFn (fun i => (q.assignment i).val)

theorem ofPacking_feasible (r : RawInstance) (hr : r.Valid) {b : ℕ}
    (q : Packing (r.toInstance hr) b) : Feasible r (ofPacking q) := by
  refine ⟨by simp [ofPacking, RawInstance.toInstance], ?_, ?_⟩
  · intro j hj
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
    exact (q.assignment i).isLt
  · intro j hj
    have hcap := q.capacity ⟨j, hj⟩
    change load r (List.ofFn (fun i : Fin r.length => (q.assignment i).val)) j ≤ 1
    rw [load_ofFn]
    simpa only [RawInstance.toInstance, Fin.ext_iff] using! hcap

theorem hasPacking_iff_exists_feasible (r : RawInstance) (hr : r.Valid) (b : ℕ) :
    HasPacking (r.toInstance hr) b ↔
      ∃ a : List ℕ, Feasible r ⟨b, a⟩ := by
  constructor
  · rintro ⟨q⟩
    exact ⟨(ofPacking q).assignments, ofPacking_feasible r hr q⟩
  · rintro ⟨a, ha⟩
    exact ⟨toPacking r hr ⟨b, a⟩ ha⟩

end RawPacking

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitializeEncoding
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchSemantics

open ExtensionQuery

theorem agrees_set {fixed : List (Option Nat)} {a : List Nat} {i j : Nat}
    (ha : Agrees fixed a) (hi : i < fixed.length) (hij : a[i]? = some j) :
    Agrees (fixed.set i (some j)) a := by
  refine ⟨by simpa using ha.1, ?_⟩
  intro t q hq
  by_cases hti : t = i
  · subst t
    rw [get_set_same fixed i (some j) hi] at hq
    have : j = q := by simpa using hq
    simpa [this] using hij
  · exact ha.2 t q ((get_set_other fixed i t (some j) hti).symm.trans hq)

theorem labels_eq_of_complete {fixed : List (Option Nat)} {a : List Nat}
    (ha : Agrees fixed a) (hp : Prefix fixed.length fixed) : labels fixed = a := by
  have hlen := ha.1
  apply List.ext_getElem?
  intro i
  by_cases hi : i < fixed.length
  · obtain ⟨j, hj⟩ := hp.1 i hi
    have haj := ha.2 i j hj
    simp [labels, List.getElem?_map, hj, haj]
  · have hai : a.length ≤ i := by omega
    have hfi : fixed.length ≤ i := by omega
    simp [labels, List.getElem?_map,
      List.getElem?_eq_none hai, List.getElem?_eq_none hfi]

end BinPackingGap.SearchSemantics

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialItemsMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialItemsMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer

inductive Label
  | control (phase : Control)
  | number (which : Number) (phase : ExtensionNatMachine.Label)
  | order (phase : BinaryOrderMachine.PreserveLabel)
  deriving DecidableEq, Fintype

abbrev State := BinaryAddMachine.State (Bool × Ordering)

def clean (valid : Bool) : State := BinaryAddMachine.clean (valid, .eq)

def validity (s : State) : Bool := s.1.1.1.1

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun s => clean (validity s)) (.goto fun _ => label)

def scanPorts (which : Number) : Fin 3 ↪ Tape :=
  ⟨scanTape which, by
    intro i j h
    cases which <;> fin_cases i <;> fin_cases j <;> simp_all [scanTape]⟩

def orderPorts : Fin 5 ↪ Tape :=
  ⟨orderTape, by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [orderTape]⟩

def scanSuccess : Number → Label
  | .numerator => .control .positive
  | .denominator => .order .leftOut

def orderExit : Ordering → Option Label
  | .lt | .eq => some (.control .clearNumerator)
  | .gt => some (.control .failed)

theorem bits_eq_nil_iff (n : Nat) : n.bits = [] ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg BinPackingCompleteness.BinaryEncoding.bitsValue h
    simpa only [BinPackingCompleteness.BinaryEncoding.bitsValue_bits,
      BinPackingCompleteness.BinaryEncoding.bitsValue] using hv
  · rintro rfl; rfl

end BinPackingGap.SearchInitialItemsMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPowerProgram
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.LiteralSlotGraphMachine.instDecidableBodyEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

open Turing BinPackingGames.Foundations BinPackingGames.Foundations.Target
open FiniteTapeProgram

abbrev State := BooleanTapeCode.State Control
abbrev Program := BooleanTapeCode.Program Tape Control

def initialState : State := BooleanTapeCode.clean initialControl

def saveHead (s : State) (head : Option Bool) : State := (s.1, head)
def mapControl (f : Control → Control) (s : State) : State := ((f s.1.1, ()), s.2)
def resetHead (s : State) : State := (s.1, none)

def skip : Program := .atom .done

def sequence : List Program → Program
  | [] => skip
  | c :: cs => .seq c (sequence cs)

def pushBit (tape : Tape) (bit : Bool) : Program := .atom (.push tape (fun _ => bit) .done)
def changeControl (f : Control → Control) : Program := .atom (.load (mapControl f) .done)

def readVariable (source destination : Tape) : Program :=
  .seq (.loop (.pop source saveHead .done) (fun s => s.2.getD false)
    (.atom (.push destination (fun _ => true) .done)))
    (.atom (.load resetHead .done))

def skipField (source : Tape) : Program :=
  .loop (.pop source saveHead .done) (fun s => s.2.getD false) skip

def readSign (source : Tape) (setSign : Control → Bool → Control) : Program :=
  .atom (.pop source saveHead
    (.load (fun s => ((setSign s.1.1 (s.2.getD false), ()), s.2))
      (.branch (fun s => s.2.getD false)
        (.pop source saveHead (.load resetHead .done))
        (.load resetHead .done))))

def countHeader : Program :=
  .loop (.pop .input saveHead .done) (fun s => s.2.getD false)
    (.atom (.push .unary (fun _ => true) (.push .unary (fun _ => true)
      (.push .vertexCount (fun _ => true) (.push .vertexCount (fun _ => true)
        (.push .vertexCount (fun _ => true) .done))))))

def compareGuard : Action Tape State :=
  .pop .comparison (fun s h => mapControl (fun a => {a with otherHead := h}) s)
    (.pop .innerVariable saveHead
      (.load (fun s => mapControl
        (fun a => {a with equal := a.equal && decide (a.otherHead = s.2)}) s) .done))

def compareVariables : Program :=
  .seq (changeControl (fun a => {a with equal := true}))
    (.loop compareGuard (fun s => s.1.1.otherHead.isSome || s.2.isSome) skip)

def isEdge (s : State) : Bool :=
  decide (0 < s.1.1.remaining.val) ||
    (s.1.1.equal && (s.1.1.outerSign != s.1.1.innerSign))

end BinPackingGap.LiteralSlotGraphMachine

namespace BinPackingGap.PackingFieldDecodeMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open FiniteTapeProgram

abbrev State (A : Type) := BinaryAddMachine.State A

end BinPackingGap.PackingFieldDecodeMachine

namespace BinPackingGap.PackingPowerProgram

open Turing
open BinPackingGames.Foundations.Complexity
open FiniteTapeProgram

variable {K A : Type} [DecidableEq K]

structure Ready (slots : Fin 11 ↪ K) (base : K → List Bool) (a n : Nat) : Prop where
  baseWord : base (slots 0) = a.bits
  outputEmpty : base (slots 1) = []
  tallyWord : base (slots 9) = List.replicate n true
  workspace : BinaryPowerMachine.Workspace slots base

noncomputable def budget (a n : Nat) : Nat :=
  BinaryPowerMachine.timePolynomial.eval (a.size + n)

end BinPackingGap.PackingPowerProgram

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryToTallyMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.RegisterFrameEmission

open Turing BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram FiniteTapeProgram
open BinPackingGames.Reduction.MachineTransfer

variable {Reg K A : Type} [DecidableEq Reg] [DecidableEq K]

def code (source output : K) : Code (K := K) (S := BinaryAddMachine.State A) :=
  .routine Unit inferInstance ()
    (fun _ => FrameEmitMachine.instruction source output () none)

end BinPackingGap.RegisterFrameEmission

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

section

def labelSecondary {n : ℕ} (x d a : Fin n) : ℤ :=
  labelWeight x + labelWeight d - 2 * labelWeight a

@[simp] theorem labelSecondary_self {n : ℕ} (a : Fin n) :
    labelSecondary a a a = 0 := by
  unfold labelSecondary
  linarith

open scoped BigOperators

theorem sum_primaryScore_eq_zero_of_coefficients {I : Type*} [Fintype I]
    (t : I → Subclass) (h : ∀ j : Fin 10, (∑ i, primaryCoeff j (t i)) = 0) :
    (∑ i, primaryScore (t i)) = 0 := by
  rw [sum_primaryScore_eq]
  simp [h]

end

section

def tableRoleLabel {n : ℕ} (x d a : Fin n) : Role → Option (Fin n)
  | .x => some x
  | .anchor => some a
  | .«global» => none
  | .«local» => some d
  | .flag => none

open scoped BigOperators

end

open scoped BigOperators

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_CurrentMatches
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.IntervalCoverage

variable {ι κ τ α : Type*} [LinearOrder α]

theorem completion_prefix_identity [Fintype ι] (h b : ι → α)
    (hle : ∀ i, h i ≤ b i) (a : α) :
    prefixCount h a = prefixCount b a + coverageCount h b a := by
  classical
  simpa only [prefixCount, coverageCount, prefixSet, coverageSet] using
    CoverageCounts.interval_prefix_card Finset.univ h b (fun i _ => hle i) a

namespace ShiftData

variable {d : ℕ} (D : ShiftData ι τ d α)

attribute [local instance] OAI.BinPackingGap.IntervalCoverage.ShiftData.instDecidableEq
theorem deadline_prefix_of_agrees [Fintype ι] [Fintype τ]
    (z : ι → α)
    (hdesignated : ∀ q, z (D.designated q) = D.left q.1)
    (hother : ∀ i, (∀ q, D.designated q ≠ i) → z i = D.baseline i)
    (a : α) :
    prefixCount z a = prefixCount D.baseline a + d * (D.activeTests a).card := by
  classical
  have hle : ∀ i, z i ≤ D.baseline i := by
    intro i
    by_cases hi : ∃ q, D.designated q = i
    · obtain ⟨q, rfl⟩ := hi
      rw [hdesignated, D.baseline_designated]
      exact D.left_le_right q.1
    · rw [hother i (by simpa only [not_exists] using hi)]
  have hset : coverageSet z D.baseline a =
      ((D.activeTests a).product (Finset.univ : Finset (Fin d))).map D.designated := by
    ext i
    simp only [mem_coverageSet, Finset.mem_map, Finset.product_eq_sprod, Finset.mem_product,
      mem_activeTests, Finset.mem_univ, and_true]
    constructor
    · intro hi
      have hex : ∃ q, D.designated q = i := by
        by_contra hn
        have he := hother i (by simpa only [not_exists] using hn)
        exact (not_lt_of_ge (he ▸ hi.1)) hi.2
      obtain ⟨q, rfl⟩ := hex
      exact ⟨q, by simpa only [hdesignated, D.baseline_designated] using hi, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      simpa only [hdesignated, D.baseline_designated] using hq
  rw [completion_prefix_identity z D.baseline hle a]
  unfold coverageCount
  rw [hset, Finset.card_map, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]
  rw [Nat.mul_comm]

end ShiftData

theorem exists_equiv_of_prefix_dominance [Fintype ι] [Fintype κ]
    (h : ι → α) (z : κ → α) (hcard : Fintype.card ι = Fintype.card κ)
    (hprefix : ∀ a, prefixCount z a ≤ prefixCount h a) :
    ∃ e : ι ≃ κ, ∀ i, h i ≤ z (e i) := by
  classical
  let neighbors : ι → Finset κ := fun i => Finset.univ.filter fun j => h i ≤ z j
  have hall : ∀ s : Finset ι, s.card ≤ (s.biUnion neighbors).card := by
    intro s
    let N := s.biUnion neighbors
    let bad := (Finset.univ : Finset κ) \ N
    have hpartition : bad.card + N.card = Fintype.card κ := by
      simpa only [bad, Finset.card_univ] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ N)
    by_cases hbad : bad.Nonempty
    · obtain ⟨j, hj, hmax⟩ := bad.exists_max_image z hbad
      have hN : j ∉ N := (Finset.mem_sdiff.mp hj).2
      have hd : Disjoint s (prefixSet h (z j)) := by
        apply Finset.disjoint_left.mpr
        intro i hi hip
        apply hN
        exact Finset.mem_biUnion.mpr ⟨i, hi, by
          simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and,
            mem_prefixSet] using hip⟩
      have hsum : s.card + prefixCount h (z j) ≤ Fintype.card ι := by
        rw [prefixCount, ← Finset.card_union_of_disjoint hd]
        exact Finset.card_le_univ _
      have hb : bad.card ≤ prefixCount z (z j) := by
        apply Finset.card_le_card
        intro k hk
        exact (mem_prefixSet z (z j) k).mpr (hmax k hk)
      have hp := hprefix (z j)
      change s.card ≤ N.card
      omega
    · have hb : bad.card = 0 := Finset.card_eq_zero.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hbad)
      have hs := Finset.card_le_univ s
      change s.card ≤ N.card
      omega
  obtain ⟨f, hf, hmatch⟩ :=
    (FiniteHall.all_card_le_biUnion_card_iff_existsInjective neighbors).mp hall
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro i
  change h i ≤ z (f i)
  have hi := hmatch i
  simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using hi

end BinPackingGap.IntervalCoverage

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

theorem widthRadix_pos (D : ℕ) : 0 < widthRadix D := by
  unfold widthRadix
  positivity

theorem geomDenominator_pos (m R D L : ℕ) : 0 < geomDenominator m R D L := by
  unfold geomDenominator
  exact Nat.mul_pos (by positivity) (pow_pos (widthRadix_pos D) L)

theorem sizeDenominator_pos (n geom : ℕ) (hgeom : 0 < geom) :
    0 < sizeDenominator n geom := by
  unfold sizeDenominator primaryBound
  positivity

theorem signedNumerator_ratio (n geom : ℕ) (hgeom : 0 < geom)
    (p q W : ℤ) :
    (signedNumerator n geom p q W : ℚ) / (sizeDenominator n geom : ℚ) =
      1 / 5 + gamma * (p : ℚ) + mu n * (q : ℚ) +
        nu n * ((W : ℚ) / geom) := by
  have hg : (geom : ℚ) ≠ 0 := by exact_mod_cast hgeom.ne'
  have hp : (primaryBound : ℚ) ≠ 0 := by norm_num [primaryBound]
  have hq : (3 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  simp only [signedNumerator, sizeDenominator, nu, mu, gamma]
  push_cast
  field_simp [hg, hp, hq]
  ring

theorem geomDenominator_mul_gap (m R D L : ℕ) :
    (geomDenominator m R D L : ℚ) * Geometry.gap m R =
      10 * (widthRadix D : ℚ) ^ L := by
  have hp : ((R : ℚ) + 1) ^ m ≠ 0 :=
    pow_ne_zero m (by positivity)
  unfold geomDenominator Geometry.gap
  push_cast
  field_simp [hp]
  ring

theorem geomDenominator_mul_lambda (m R D L ell : ℕ) (hell : ell ≤ L) :
    (geomDenominator m R D L : ℚ) * Geometry.lambda m R D ell =
      (localNumerator D L ell : ℚ) := by
  have hc : (widthRadix D : ℚ) ≠ 0 := by
    exact_mod_cast (widthRadix_pos D).ne'
  have hpow : (widthRadix D : ℚ) ^ L =
      (widthRadix D : ℚ) ^ ell * (widthRadix D : ℚ) ^ (L - ell) := by
    rw [← pow_add, Nat.add_sub_of_le hell]
  have hrad : (100 * ((D : ℚ) + 1)) = (widthRadix D : ℚ) := by
    simp [widthRadix]
  rw [Geometry.lambda, ← mul_div_assoc, geomDenominator_mul_gap, hrad, hpow]
  simp only [localNumerator, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  field_simp [hc]

theorem geomDenominator_mul_delta (m R D L : ℕ) :
    (geomDenominator m R D L : ℚ) * Geometry.delta m R D L = 1 := by
  rw [Geometry.delta, ← mul_div_assoc, geomDenominator_mul_lambda m R D L L le_rfl]
  norm_num [localNumerator]

theorem geomDenominator_mul_baseline (m R D L : ℕ) (r : Geometry.Position m R) :
    (geomDenominator m R D L : ℚ) * Geometry.baseline m R r =
      (baselineNumerator m R D L r : ℚ) := by
  rw [Geometry.baseline, mul_add, ← mul_assoc, geomDenominator_mul_gap]
  simp only [baselineNumerator, Geometry.heightCode, geomDenominator]
  push_cast
  ring

theorem geomDenominator_mul_beta (m R D L : ℕ) (e : Fin m) :
    (geomDenominator m R D L : ℚ) * Geometry.beta m R e =
      (betaNumerator m R D L e : ℚ) := by
  rw [Geometry.beta, ← mul_assoc, geomDenominator_mul_gap]
  simp only [betaNumerator, Geometry.theta]
  push_cast
  ring

end BinPackingGap.IntegerPackingArithmetic

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_IntegerTreeGeometry
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.TreeGeometry

open _root_.OAI.BinPackingGap.Geometry UniformTree

instance instFintypeSide : Fintype Side where
  elems := {.plus, .minus}
  complete s := by cases s <;> simp

def cell (m R D : ℕ) (s : Side) (w : List ℕ) : Set ℚ :=
  Set.Icc (left m R D s w) (right m R D s w)

theorem exists_snoc_of_length_succ {w : List ℕ} {ell : ℕ}
    (h : w.length = ell + 1) :
    ∃ u a, w = u ++ [a] ∧ u.length = ell := by
  induction w using List.reverseRecOn with
  | nil => simp at h
  | append_singleton u a _ =>
    exact ⟨u, a, rfl, by simpa using h⟩

end BinPackingGap.TreeGeometry

namespace BinPackingGap.IntegerPackingArithmetic

theorem geomDenominator_mul_pathSum (m R D L k : ℕ) (w : List ℕ)
    (hdepth : k + w.length ≤ L) :
    (geomDenominator m R D L : ℚ) * TreeGeometry.pathSum m R D k w =
      (pathNumerator D L k w : ℚ) := by
  induction w generalizing k with
  | nil => simp [TreeGeometry.pathSum, pathNumerator]
  | cons a w ih =>
      have hdepth' : k + (w.length + 1) ≤ L := hdepth
      have hfirst : k + 1 ≤ L := by omega
      have htail : (k + 1) + w.length ≤ L := by
        omega
      have hlocal := geomDenominator_mul_lambda m R D L (k + 1) hfirst
      have hrest := ih (k + 1) htail
      simp only [TreeGeometry.pathSum, pathNumerator, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_pow]
      calc
        _ = 4 * (a : ℚ) * ((geomDenominator m R D L : ℚ) *
              Geometry.lambda m R D (k + 1)) +
            (geomDenominator m R D L : ℚ) * TreeGeometry.pathSum m R D (k + 1) w := by ring
        _ = _ := by
          rw [hlocal, hrest]
          simp only [localNumerator, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
          ring

end BinPackingGap.IntegerPackingArithmetic

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

def prefixOutside (label : A → Fin n) (f : T → A) (h : ℕ) : Finset A :=
  (outsideItems f).filter fun x => (label x).val < h

@[simp] theorem prefixOutside_zero (label : A → Fin n) (f : T → A) :
    prefixOutside label f 0 = ∅ := by
  simp [prefixOutside]

end LabelConservation
end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalarExpression
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.NaturalPackingNumerator

open IntegerPackingArithmetic

namespace NatDifference

theorem toNat_eq (a : NatDifference) : a.toNat = a.eval.toNat := by
  unfold toNat eval
  omega

end NatDifference

end BinPackingGap.NaturalPackingNumerator

namespace BinPackingGap.PackingCoordinateExpression

open IntegerPackingArithmetic
open NaturalPackingNumerator
open NatExpressionCompiler

instance instFintypeInput : Fintype Input where
  elems := {.geometryDg, .totalPowerA, .edgePower, .repetitionOne}
  complete i := by cases i <;> simp

end BinPackingGap.PackingCoordinateExpression

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_MachineControlEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.MachineControlEmbedding

open Turing
open BinPackingGames.Foundations.Complexity

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

def configuration (control : Control σ τ) (labels : Λ → Λ') (exit : Option Λ')
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' τ :=
  ⟨MachineSubroutine.label labels exit c.l, control.put c.var, c.stk⟩

variable [DecidableEq K]

theorem stepAux_simulation (control : Control σ τ) (labels : Λ → Λ')
    (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) (state : σ)
    (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement control labels exit q) (control.put state) tapes =
      configuration control labels exit (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
      simpa only [statement, TM2.stepAux, control.get_put] using
        ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [statement, TM2.stepAux, control.get_put] using
        ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simpa only [statement, TM2.stepAux, control.get_put] using
        ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [statement, TM2.stepAux, control.get_put] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false =>
          simpa only [statement, TM2.stepAux, control.get_put, h, Bool.cond_false]
            using ihNo state tapes
      | true =>
          simpa only [statement, TM2.stepAux, control.get_put, h, Bool.cond_true]
            using ihYes state tapes
  | goto f => simp only [statement, TM2.stepAux, control.get_put, configuration,
      MachineSubroutine.label]
  | halt => cases exit <;> rfl

theorem step_simulation (control : Control σ τ) (labels : Λ → Λ')
    (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' τ)
    (atLabels : ∀ l, target (labels l) = statement control labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration control labels exit a) =
      some (configuration control labels exit b) := by
  cases a with
  | mk l state tapes =>
      cases l with
      | none => simp [TM2.step] at h
      | some l =>
          have hb : TM2.stepAux (source l) state tapes = b := Option.some.inj h
          rw [← hb]
          change some (TM2.stepAux (target (labels l)) (control.put state) tapes) = _
          rw [atLabels, stepAux_simulation]

theorem trace (control : Control σ τ) (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' τ)
    (atLabels : ∀ l, target (labels l) = statement control labels exit (source l))
    (steps : Nat) (a b : TM2.Cfg Γ Λ σ)
    (run : (MachineComposition.advance (TM2.step source))^[steps] (some a) = some b) :
    (MachineComposition.advance (TM2.step target))^[steps]
      (some (configuration control labels exit a)) =
      some (configuration control labels exit b) :=
  MachineComposition.liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (configuration control labels exit)
    (step_simulation control labels exit source target atLabels) steps a b run

end BinPackingGap.MachineControlEmbedding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PairExpressionCompiler
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PairExpressionCompiler

open NatExpressionCompiler BinaryRegisterProgram

variable {α : Type} [DecidableEq α]

abbrev Reg (num den : Expr α) := α ⊕ (Node num ⊕ Node den)

def input (num den : Expr α) : α → Reg num den := Sum.inl

def numNodes (num den : Expr α) : Node num ↪ Reg num den where
  toFun n := .inr (.inl n)
  inj' := by intro a b h; exact Sum.inl.inj (Sum.inr.inj h)

def denNodes (num den : Expr α) : Node den ↪ Reg num den where
  toFun n := .inr (.inr n)
  inj' := by intro a b h; exact Sum.inr.inj (Sum.inr.inj h)

def initial (num den : Expr α) (values : α → Nat) : Reg num den → Nat
  | .inl a => values a
  | .inr _ => 0

def numRoot (num den : Expr α) : Reg num den := numNodes num den (root num)
def denRoot (num den : Expr α) : Reg num den := denNodes num den (root den)

omit [DecidableEq α] in
theorem numRoot_ne_denRoot (num den : Expr α) : numRoot num den ≠ denRoot num den := by
  intro equal
  change (Sum.inr (Sum.inl (root num)) : Reg num den) = Sum.inr (Sum.inr (root den)) at equal
  cases Sum.inr.inj equal

def temporaryList (num den : Expr α) : List (Reg num den) :=
  (Finset.univ : Finset (Node num ⊕ Node den)).toList.map Sum.inr

omit [DecidableEq α] in
theorem mem_temporaryList (num den : Expr α) (r : Reg num den) :
    r ∈ temporaryList num den ↔ ∃ n : Node num ⊕ Node den, r = Sum.inr n := by
  simp [temporaryList, eq_comm]

def consumed (num den : Expr α) (values : Reg num den → Nat) : Reg num den → Nat :=
  Function.update (Function.update values (numRoot num den) 0) (denRoot num den) 0

theorem consumed_input (num den : Expr α) (values : Reg num den → Nat) (a : α) :
    consumed num den values (input num den a) = values (input num den a) := by
  simp [consumed, input, numRoot, denRoot, numNodes, denNodes]

omit [DecidableEq α] in
theorem initial_width (num den : Expr α) (values : α → Nat) (width : Nat)
    (h : ∀ a, (values a).size ≤ width) :
    ∀ r, (initial num den values r).size ≤ width := by
  intro r
  cases r with
  | inl a => exact h a
  | inr n => simp [initial]

end BinPackingGap.PairExpressionCompiler

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingVertexUpdate
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingMachineLayout

open NatExpressionCompiler PairExpressionCompiler BinaryRegisterProgram
open PackingRegisterFrame

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input]

instance regDecidableEq (num : Descriptor → Expr Input) (den : Expr Input)
    [DecidableEq Other] : DecidableEq (Reg num den Other) :=
  inferInstanceAs (DecidableEq ((Input ⊕ Other) ⊕ (Σ d : Descriptor, Node (num d) ⊕ Node den)))

instance tapeDecidableEq (num : Descriptor → Expr Input) (den : Expr Input)
    [DecidableEq Other] [DecidableEq Extra] : DecidableEq (Tape num den Other Extra) :=
  inferInstanceAs (DecidableEq ((Reg num den Other ⊕ Fin 6) ⊕ Extra))

def itemRegisters (num : Descriptor → Expr Input) (den : Expr Input) (d : Descriptor) :
    PairExpressionCompiler.Reg (num d) den ↪ Reg num den Other where
  toFun
    | .inl a => inputs num den a
    | .inr node => .inr ⟨d, node⟩
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl ((inputs num den).injective h)
        | inr b => cases h
    | inr a =>
        cases b with
        | inl b => cases h
        | inr b =>
            have hs : (⟨d, a⟩ : Σ d : Descriptor, Node (num d) ⊕ Node den) = ⟨d, b⟩ :=
              Sum.inr.inj h
            exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj_iff.mp hs).2)

def itemSlots (num : Descriptor → Expr Input) (den : Expr Input) (d : Descriptor) :
    (PairExpressionCompiler.Reg (num d) den ⊕ Fin 6) ↪ Tape num den Other Extra :=
  localSlots (registers num den) (itemRegisters num den d)

omit [DecidableEq Descriptor] [DecidableEq Input] in
theorem values_itemRegisters (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (d : Descriptor) :
    values num den input other ∘ itemRegisters num den d =
      initial (num d) den input := by
  funext r
  cases r <;> rfl

variable [DecidableEq Other] [DecidableEq Extra]

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra] in
theorem itemSlots_outside (num : Descriptor → Expr Input) (den : Expr Input)
    (d : Descriptor) (output : Extra) (i : PairExpressionCompiler.Reg (num d) den ⊕ Fin 6) :
    itemSlots (Other := Other) num den d i ≠ Sum.inr output := by
  simp only [itemSlots, localSlots, Function.Embedding.trans_apply, registers,
    Function.Embedding.inl_apply, ne_eq, Sum.inl_ne_inr, not_false_eq_true]

end BinPackingGap.PackingMachineLayout

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingJobLoop
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

namespace BinPackingGap.PackingItemExpression

open NatExpressionCompiler

instance instFintypeVariable : Fintype Variable where
  elems := {.vertexPower, .geometry, .labelPower, .totalPower, .edgePower, .repetitionOne}
  complete v := by cases v <;> simp

end BinPackingGap.PackingItemExpression

end

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_ResetExpressionCompiler
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.ResetExpressionCompiler

open NatExpressionCompiler BinaryRegisterProgram PairExpressionCompiler

variable {α Reg : Type} [DecidableEq Reg]

def nodeList (expression : Expr α) (nodes : Node expression ↪ Reg) : List Reg :=
  (Finset.univ : Finset (Node expression)).toList.map nodes

omit [DecidableEq Reg] in
theorem mem_nodeList (expression : Expr α) (nodes : Node expression ↪ Reg) (r : Reg) :
    r ∈ nodeList expression nodes ↔ ∃ n, r = nodes n := by
  simp [nodeList, eq_comm]

end BinPackingGap.ResetExpressionCompiler

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingSetupGraph
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingSetupExpression

section

open NatExpressionCompiler

protected abbrev Input.enumList : List Input := [.n, .m, .k]

protected theorem Input.enumList_nodup : Input.enumList.Nodup := by decide

instance instFintypeInput : Fintype Input where
  elems := ⟨Input.enumList, Input.enumList_nodup⟩
  complete x := by cases x <;> decide

protected abbrev Output.enumList : List Output := [.repetitions, .base, .edgeRepetitions, .bins,
  .upOne, .upZero, .umOne, .umZero, .edgeStock, .treeFlags, .jobFlags, .one, .three]

protected theorem Output.enumList_nodup : Output.enumList.Nodup := by decide

instance instFintypeOutput : Fintype Output where
  elems := ⟨Output.enumList, Output.enumList_nodup⟩
  complete x := by cases x <;> decide

def outputValues (p : Parameters) (n m k : Nat) : Output → Nat
  | .repetitions => 100 * (p.P + n * p.K + 1)
  | .base => 100 * (p.P + n * p.K + 1) + 1
  | .edgeRepetitions => m * (100 * (p.P + n * p.K + 1))
  | .bins => n * (p.tPlus + p.tMinus) +
      (4 * p.d) * (m * (100 * (p.P + n * p.K + 1)))
  | .upOne => p.d * k
  | .upZero => n * p.tPlus + (2 * p.d) * (m * (100 * (p.P + n * p.K + 1))) - p.d * k
  | .umOne => p.d * (n - k)
  | .umZero => n * p.tMinus - p.d * (n - k)
  | .edgeStock => p.d * (100 * (p.P + n * p.K + 1))
  | .treeFlags => n * (p.tPlus + p.tMinus)
  | .jobFlags => (2 * p.d) * (m * (100 * (p.P + n * p.K + 1)))
  | .one => 1
  | .three => 3

theorem eval_expression (p : Parameters) (n m k : Nat) (o : Output) :
    eval (inputs n m k) (expression p o) = outputValues p n m k o := by
  cases o <;> rfl

end

end BinPackingGap.PackingSetupExpression

namespace BinPackingGap.PackingSetupMachine

section

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram
open PackingSetupExpression

theorem frame_update (p : Parameters) (ins : Input → Nat) (outs : Output → Nat)
    (o : Output) (v : Nat) :
    Function.update (frame p ins outs) (output p o) v =
      frame p ins (Function.update outs o v) := by
  funext r
  rcases r with a | (q | n)
  · simp [frame, output]
  · by_cases h : q = o <;> simp [frame, output, h]
  · simp [frame, output]

theorem mem_outputOrder (o : Output) : o ∈ outputOrder := by
  cases o <;> simp [outputOrder]

def outputsAfter (p : Parameters) (ins : Input → Nat) :
    List Output → (Output → Nat) → Output → Nat
  | [], outs => outs
  | o :: tail, outs => outputsAfter p ins tail
      (Function.update outs o (eval ins (expression p o)))

theorem outputsAfter_eq (p : Parameters) (ins : Input → Nat) (order : List Output)
    (outs : Output → Nat) (o : Output) :
    outputsAfter p ins order outs o =
      if o ∈ order then eval ins (expression p o) else outs o := by
  induction order generalizing outs with
  | nil => simp [outputsAfter]
  | cons q tail ih =>
      rw [outputsAfter, ih]
      by_cases ht : o ∈ tail
      · simp [ht]
      · by_cases he : o = q
        · subst o; simp [ht]
        · simp [ht, he]

end

open BinaryRegisterProgram FiniteTapeProgram PackingSetupExpression

end BinPackingGap.PackingSetupMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_GraphPackingRegisters
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingRegisters

open PackingItemExpression
open PackingMachineLayout PackingRegisterFrame

instance instFintypeWork : Fintype Work where
  elems := {.leftEndpoint, .rightEndpoint, .leftPower, .rightPower, .counter,
    .one, .temporary, .reverse, .geometryFactor, .header}
  complete w := by cases w <;> simp

inductive CountSource
  | input (i : PackingSetupExpression.Input)
  | output (o : PackingSetupExpression.Output)
  | endpoint (right : Bool)
  deriving DecidableEq, Fintype

end BinPackingGap.GraphPackingRegisters

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Configurations_ConfigurationLP
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap

open scoped BigOperators

namespace NumericalSize

variable {I : Instance}

def ofItem (i : I.Item) : NumericalSize I :=
  ⟨I.size i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

@[simp] theorem ofItem_val (i : I.Item) : (ofItem i).val = I.size i := rfl

end NumericalSize

namespace TypeConfiguration

variable {I : Instance}

def ofIndividual (H : IndividualConfiguration I) : TypeConfiguration I where
  val s := (H.val.filter fun i => I.size i = s.val).card
  property := by
    classical
    have hsum : (∑ s : NumericalSize I,
        s.val * ((H.val.filter fun i => I.size i = s.val).card : ℚ)) =
        ∑ i ∈ H.val, I.size i := by
      calc
        _ = ∑ s : NumericalSize I, ∑ i ∈ H.val,
            if I.size i = s.val then I.size i else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          rw [← Finset.sum_filter]
          rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
          simp [mul_comm]
        _ = ∑ i ∈ H.val, ∑ s : NumericalSize I,
            if I.size i = s.val then I.size i else 0 := by rw [Finset.sum_comm]
        _ = ∑ i ∈ H.val, I.size i := by
          apply Finset.sum_congr rfl
          intro i _
          have heq : ∀ s : NumericalSize I, I.size i = s.val ↔ NumericalSize.ofItem i = s := by
            intro s
            constructor
            · intro h
              exact Subtype.ext h
            · intro h
              exact congrArg Subtype.val h
          simp [heq]
    rw [hsum]
    exact H.property

@[simp] theorem ofIndividual_count (H : IndividualConfiguration I) (s : NumericalSize I) :
    (ofIndividual H).val s = (H.val.filter fun i => I.size i = s.val).card := rfl

end TypeConfiguration

def IndividualFeasible (I : Instance) (w : IndividualConfiguration I → ℝ) : Prop :=
  FractionalCover.Feasible (individualMatrix I) (fun _ => 1) w

def TypeFeasible (I : Instance) (w : TypeConfiguration I → ℝ) : Prop :=
  FractionalCover.Feasible (typeMatrix I) (fun s => (s.multiplicity : ℝ)) w

def singletonWeights (I : Instance) : IndividualConfiguration I → ℝ :=
  FractionalCover.pushforward IndividualConfiguration.singleton (fun _ : I.Item => 1)

def projectWeights (I : Instance) (w : IndividualConfiguration I → ℝ) :
    TypeConfiguration I → ℝ :=
  FractionalCover.pushforward TypeConfiguration.ofIndividual w

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_LiteralSlotGraphEnumeration
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.LiteralSlotGraphMachine

section

open FiniteTapeProgram BinPackingGames.Foundations.Complexity

theorem compareGuard_eval (base : Tape → List Bool) (a : Control)
    (register : Option Bool) (n m : Nat) :
    compareGuard.eval
      ⟨((a, ()), register), twoTapes base .comparison .innerVariable
        (List.replicate n true) (List.replicate m true)⟩ =
    ⟨((comparedControl a (counterHead n) (counterHead m), ()), counterHead m),
      twoTapes base .comparison .innerVariable
        (List.replicate (n - 1) true) (List.replicate (m - 1) true)⟩ := by
  cases n <;> cases m <;>
    simp [compareGuard, Action.eval, mapControl, saveHead, comparedControl, counterHead,
      List.replicate_succ, twoTapes_source, twoTapes_update_source,
      show Tape.comparison ≠ Tape.innerVariable by decide]

end

open BinPackingGames.Foundations.Target BinPackingGames.Foundations.Complexity

end BinPackingGap.LiteralSlotGraphMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_IntegralSpeciesCounts
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

open scoped BigOperators

theorem root_copy_indicator_sum (T : UniformTree) (d : ℕ) :
    (∑ node : T.Node, ∑ _j : Fin d, if node = T.root then (1 : ℕ) else 0) = d := by
  classical
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true, Nat.cast_id]

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Hardness_PCPPackingGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PCPFoundation

section

open BinPackingGames.Foundations
open Target
open BinPackingCompleteness

def gap : ℚ := PCPSource.sourceGap

def rho : ℝ := (gap : ℝ) / 6

end

open BinPackingGames.Foundations.Target

end BinPackingGap.PCPFoundation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_PhysicalPoolLift
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace BinPackingGap

structure PoolTemplates (I : Instance) (T U F : Type*) where
  base : T → Finset I.Item
  globalPool : U → Finset I.Item
  flagPool : F → Finset I.Item
  globalSpecies : T → U
  flagSpecies : T → F
  global_nonempty : ∀ t, (globalPool (globalSpecies t)).Nonempty
  flag_nonempty : ∀ t, (flagPool (flagSpecies t)).Nonempty
  base_global : ∀ t, Disjoint (base t) (globalPool (globalSpecies t))
  base_flag : ∀ t, Disjoint (base t) (flagPool (flagSpecies t))
  global_flag : ∀ t,
    Disjoint (globalPool (globalSpecies t)) (flagPool (flagSpecies t))
  capacity : ∀ t (u : {i // i ∈ globalPool (globalSpecies t)})
    (f : {i // i ∈ flagPool (flagSpecies t)}),
    (∑ i ∈ base t ∪ {u.val, f.val}, I.size i) ≤ 1

namespace PoolTemplates

variable {I : Instance} {T U F : Type*} [Fintype T]

variable (D : PoolTemplates I T U F)

abbrev Globals (t : T) := {i // i ∈ D.globalPool (D.globalSpecies t)}
abbrev Flags (t : T) := {i // i ∈ D.flagPool (D.flagSpecies t)}
abbrev Sample := (t : T) × (D.Globals t × D.Flags t)

def column (t : T) (u : D.Globals t) (f : D.Flags t) : IndividualConfiguration I :=
  ⟨D.base t ∪ {u.val, f.val}, D.capacity t u f⟩

def sampleColumn (s : D.Sample) : IndividualConfiguration I :=
  D.column s.1 s.2.1 s.2.2

def templateMass (t : T) : ℝ :=
  1 / (2 * ((D.globalPool (D.globalSpecies t)).card : ℝ) *
    ((D.flagPool (D.flagSpecies t)).card : ℝ))

def sampleMass (s : D.Sample) : ℝ := D.templateMass s.1

def weights : IndividualConfiguration I → ℝ :=
  FractionalCover.pushforward D.sampleColumn D.sampleMass

end PoolTemplates

end BinPackingGap

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

def tallyRegister : BinaryToTallyMachine.Reg ↪ Fin 7 where
  toFun
    | .source => 0
    | .counter => 3
    | .one => 4
    | .temporary => 5
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def tallySlots (slots : (Fin 7 ⊕ Fin 6) ↪ K) :
    (BinaryToTallyMachine.Reg ⊕ Fin 6) ↪ K :=
  (Function.Embedding.sumMap tallyRegister (Function.Embedding.refl _)).trans slots

omit [DecidableEq K] in
@[simp] theorem tallySlots_reg (slots : (Fin 7 ⊕ Fin 6) ↪ K)
    (r : BinaryToTallyMachine.Reg) :
    tallySlots slots (.inl r) = slots (.inl (tallyRegister r)) := rfl

omit [DecidableEq K] in
@[simp] theorem tallySlots_scratch (slots : (Fin 7 ⊕ Fin 6) ↪ K) (j : Fin 6) :
    tallySlots slots (.inr j) = slots (.inr j) := rfl

def updateRegister : Fin 3 ↪ Fin 7 where
  toFun := ![1, 2, 5]
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def updateSlots (slots : (Fin 7 ⊕ Fin 6) ↪ K) : (Fin 3 ⊕ Fin 6) ↪ K :=
  (Function.Embedding.sumMap updateRegister (Function.Embedding.refl _)).trans slots

omit [DecidableEq K] in
@[simp] theorem updateSlots_reg (slots : (Fin 7 ⊕ Fin 6) ↪ K) (r : Fin 3) :
    updateSlots slots (.inl r) = slots (.inl (updateRegister r)) := rfl

omit [DecidableEq K] in
@[simp] theorem updateSlots_scratch (slots : (Fin 7 ⊕ Fin 6) ↪ K) (j : Fin 6) :
    updateSlots slots (.inr j) = slots (.inr j) := rfl

def powerSlots (slots : (Fin 7 ⊕ Fin 6) ↪ K) (tally : K)
    (outside : ∀ q, slots q ≠ tally) : Fin 11 ↪ K where
  toFun := ![slots (.inl 1), slots (.inl 2), slots (.inl 5),
    slots (.inr 0), slots (.inr 1), slots (.inr 2), slots (.inr 3),
    slots (.inr 4), slots (.inr 5), tally, slots (.inl 6)]
  inj' := by
    intro i j h
    have hs (a b : Fin 7 ⊕ Fin 6) : slots a = slots b ↔ a = b := slots.injective.eq_iff
    have ht (a : Fin 7 ⊕ Fin 6) : tally ≠ slots a := (outside a).symm
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem timePolynomial_eval (v : Nat) :
    timePolynomial.eval v =
      40 * (v + 1) ^ 3 + 100 * (v + 4) ^ 5 + 64 * (2 * v + 4) ^ 2 + 2 := by
  simp [timePolynomial]

theorem tally_budget_le (v : Nat) :
    BinaryToTallyMachine.runtimeBound v ≤ 40 * (v + 1) ^ 3 := by
  have hs : v.size ≤ v := Nat.size_le.mpr Nat.lt_two_pow_self
  have hsq := Nat.mul_le_mul (Nat.add_le_add_right hs 1) (Nat.add_le_add_right hs 1)
  have hm := Nat.mul_le_mul_left (40 * (v + 1)) hsq
  simpa only [BinaryToTallyMachine.runtimeBound, pow_succ, pow_two, pow_one,
    pow_zero, Nat.one_mul, Nat.mul_assoc] using hm

theorem power_budget (v : Nat) : PackingPowerProgram.budget 3 v = 100 * (v + 4) ^ 5 := by
  simp only [PackingPowerProgram.budget, BinaryPowerMachine.timePolynomial,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, size_three]
  congr 2
  omega

end BinPackingGap.PackingEndpointPower

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingProgram

open BinPackingGames.Foundations.Complexity
open FiniteTapeProgram BinaryRegisterProgram
open GraphPackingRegisters PackingRegisterFrame

variable (K : Nat)

def endpointTimePolynomial : Polynomial Nat :=
  PackingEndpointPower.timePolynomial + Polynomial.X + Polynomial.C 3

end BinPackingGap.GraphPackingProgram

namespace BinPackingGap.GraphPackingJobs

section

open FiniteTapeProgram BinaryRegisterProgram
open GraphPackingRegisters PackingItemExpression
open PackingMachineLayout (values)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes )
open BinPackingGames.Foundations.Complexity

variable (K : Nat)

theorem repeat_tally_bound (n width : Nat) (hn : n ≤ width) :
    BinaryToTallyMachine.runtimeBound n ≤ 40 * (width + 1) ^ 3 := by
  have hs : n.size ≤ width := (nat_size_le_self n).trans hn
  calc
    BinaryToTallyMachine.runtimeBound n = 40 * (n + 1) * (n.size + 1) ^ 2 := rfl
    _ ≤ 40 * (width + 1) * (width + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 40 (Nat.add_le_add_right hn 1))
        (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2)
    _ = 40 * (width + 1) ^ 3 := by ring

end

section

open FiniteTapeProgram BinaryRegisterProgram
open GraphPackingRegisters PackingItemExpression
open PackingMachineLayout (values)
open BinPackingGames.Foundations.Complexity

variable (K : Nat)

def prefixTimePolynomial : Polynomial Nat :=
  1 + 2 * GraphPackingProgram.endpointTimePolynomial.comp (4 * (Polynomial.X + 1))

theorem prefixTimePolynomial_eval (s : Nat) :
    prefixTimePolynomial.eval s =
      1 + 2 * GraphPackingProgram.endpointTimePolynomial.eval (4 * (s + 1)) := by
  simp [prefixTimePolynomial]

end

open FiniteTapeProgram GraphPackingRegisters
open PackingItemExpression
open PackingItemBlockMachine (outputTapes)

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingGlobalExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPoolRuntime

open BinPackingGames.Foundations.Complexity
open GraphPackingRegisters

theorem tally_le (n s : Nat) (N : Polynomial Nat) (hn : n ≤ N.eval s) :
    BinaryToTallyMachine.runtimeBound n ≤ (tallyPolynomial N).eval s := by
  have hsize : n.size ≤ N.eval s := (nat_size_le_self n).trans hn
  rw [tallyPolynomial_eval]
  unfold BinaryToTallyMachine.runtimeBound
  calc
    40 * (n + 1) * (n.size + 1) ^ 2 ≤
        40 * (N.eval s + 1) * (N.eval s + 1) ^ 2 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left 40 (Nat.add_le_add_right hn 1))
        (Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) 2)
    _ = 40 * (N.eval s + 1) ^ 3 := by ring

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

open BinPackingGames.Foundations.Complexity

variable (K : Nat)

theorem tally_bound {n s : Nat} (h : n ≤ s) :
    BinaryToTallyMachine.runtimeBound n ≤ 40 * (s + 1) ^ 3 := by
  have size := (nat_size_le_self n).trans h
  calc
    BinaryToTallyMachine.runtimeBound n = 40 * (n + 1) * (n.size + 1) ^ 2 := rfl
    _ ≤ 40 * (s + 1) * (s + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 40 (by omega))
        (Nat.pow_le_pow_left (by omega) 2)
    _ = _ := by ring

end

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram
open GraphPackingProgram

end BinPackingGap.GraphPackingPreparation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingVerticesBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingVerticesBound

open FiniteTapeProgram
open GraphPackingRegisters PackingItemExpression
open BinPackingGames.Foundations.Complexity

variable (K : Nat)

theorem tallyBound_le (n size : Nat) (hn : n ≤ size) :
    BinaryToTallyMachine.runtimeBound n ≤ 40 * (size + 1) ^ 3 := by
  have hs : n.size ≤ size := (nat_size_le_self n).trans hn
  calc
    BinaryToTallyMachine.runtimeBound n = 40 * (n + 1) * (n.size + 1) ^ 2 := rfl
    _ ≤ 40 * (size + 1) * (size + 1) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 40 (Nat.add_le_add_right hn 1))
        (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2)
    _ = 40 * (size + 1) ^ 3 := by ring

end BinPackingGap.GraphPackingVerticesBound

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

inductive Label
  | start
  | convert (label : UnaryToBinaryMachine.Label)
  | emitBinary | skipItem | skipLabel | items
  | numerator | numeratorDigit | denominator | denominatorDigit
  | fixed | option | name | nameDigit | reverse
  deriving DecidableEq, Fintype

def go (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .load (fun _ => ((), none)) (.goto fun _ => next)

def reject : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .push .output (fun _ => false) (.load (fun _ => ((), none)) .halt)

def skipUnary (again next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun _ head => ((), head))
    (.branch (fun state => state.2.getD false) (go again) (go next))

def skipDigit (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun _ head => ((), head)) (go next)

end BinPackingGap.SearchFinalizeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchFixedReplaceMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
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

theorem oneStepTrace {X : Type} {f : X → Option X} {a b : X}
    (h : f a = some b) : (advance f)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

theorem frame_cons_clock (bit : Bool) (bits : List Bool) :
    1 + 1 + (BinPackingCompleteness.BinaryEncoding.frame bits).length =
      (BinPackingCompleteness.BinaryEncoding.frame (bit :: bits)).length := by
  simp only [BinPackingCompleteness.BinaryEncoding.frame, List.length_cons]
  omega

include distinct atLabels

theorem one (label : Label) (w : Words) :
    tick^[1] (some (C (some label) w)) = some (C (next label w).1 (next label w).2) := by
  simpa only [Function.iterate_one, advance_some] using
    step_eq place distinct labels exit program atLabels base ambient label w

theorem nameTrace (action : Action) (bits source index payload reversed : List Bool) :
    tick^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (C (some (.name action))
        (words (BinPackingCompleteness.BinaryEncoding.frame bits ++ source)
          index payload reversed))) =
      some (C (some action.next)
        (words source index payload
          (saved action (BinPackingCompleteness.BinaryEncoding.frame bits) reversed))) := by
  induction bits generalizing reversed with
  | nil =>
      have h := one place distinct labels exit program atLabels base ambient
        (.name action) (words (false :: source) index payload reversed)
      cases action <;> simpa [next, consume, emit, put_words, words, saved,
        Action.writes, Action.next, BinPackingCompleteness.BinaryEncoding.frame] using h
  | cons bit bits ih =>
      have first := one place distinct labels exit program atLabels base ambient
        (.name action) (words (true :: bit ::
          (BinPackingCompleteness.BinaryEncoding.frame bits ++ source)) index payload reversed)
      have second := one place distinct labels exit program atLabels base ambient
        (.digit action) (words (bit ::
          (BinPackingCompleteness.BinaryEncoding.frame bits ++ source)) index payload
          (if action.writes then true :: reversed else reversed))
      have third := ih (if action.writes then bit :: true :: reversed else reversed)
      cases action <;>
        simp only [saved, Action.writes, Action.next, Bool.false_eq_true,
          ↓reduceIte] at third ⊢ <;>
        simp [next, consume, emit, put_words, words, Action.writes] at first second <;>
        have full := joinTrace (joinTrace (oneStepTrace first) (oneStepTrace second)) third <;>
        rw [frame_cons_clock bit bits] at full <;>
        simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
          List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using full

theorem payloadTrace (bits source index payload reversed : List Bool) :
    tick^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (C (some .payload) (words source index
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload) reversed))) =
      some (C (some (.option .discard)) (words source index payload
        ((BinPackingCompleteness.BinaryEncoding.frame bits).reverse ++ reversed))) := by
  induction bits generalizing reversed with
  | nil =>
      simpa [next, consume, emit, put_words, words, BinPackingCompleteness.BinaryEncoding.frame] using
        one place distinct labels exit program atLabels base ambient .payload
          (words source index (false :: payload) reversed)
  | cons bit bits ih =>
      have first := one place distinct labels exit program atLabels base ambient .payload
        (words source index (true :: bit ::
          (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload)) reversed)
      have second := one place distinct labels exit program atLabels base ambient .payloadDigit
        (words source index (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload))
          (true :: reversed))
      have third := ih (bit :: true :: reversed)
      simp [next, consume, emit, put_words, words] at first second
      have full := joinTrace (joinTrace (oneStepTrace first) (oneStepTrace second)) third
      rw [frame_cons_clock bit bits] at full
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using full

theorem drainPayloadTrace (bits source index payload reversed : List Bool) :
    tick^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (C (some .drainPayload) (words source index
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload) reversed))) =
      some (C none (words source index payload reversed)) := by
  induction bits with
  | nil =>
      simpa [next, consume, put_words, words, BinPackingCompleteness.BinaryEncoding.frame] using
        one place distinct labels exit program atLabels base ambient .drainPayload
          (words source index (false :: payload) reversed)
  | cons bit bits ih =>
      have first := one place distinct labels exit program atLabels base ambient .drainPayload
        (words source index (true :: bit ::
          (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload)) reversed)
      have second := one place distinct labels exit program atLabels base ambient .drainPayloadDigit
        (words source index (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload)) reversed)
      simp [next, consume, put_words, words] at first second
      have full := joinTrace (joinTrace (oneStepTrace first) (oneStepTrace second)) ih
      rw [frame_cons_clock bit bits] at full
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append] using full

theorem drainIndexTrace (n : Nat) (source index payload reversed : List Bool) :
    tick^[n + 1]
      (some (C (some .drainIndex) (words source (encodeWord n ++ index) payload reversed))) =
      some (C (some .drainPayload) (words source index payload reversed)) := by
  induction n with
  | zero =>
      simpa [next, consume, put_words, words, encodeWord] using
        one place distinct labels exit program atLabels base ambient .drainIndex
          (words source (false :: index) payload reversed)
  | succ n ih =>
      have first := one place distinct labels exit program atLabels base ambient .drainIndex
        (words source (true :: (encodeWord n ++ index)) payload reversed)
      simp [next, consume, put_words, words] at first
      have full := joinTrace (oneStepTrace first) ih
      simpa [encodeWord, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

end BinPackingGap.SearchFixedReplaceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialShapeMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialShapeMachine

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

def instruction : Label → TM2.Stmt Alphabet Label State
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
        (.load (fun _ => (Mode.items, none)) .halt)

abbrev machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (Mode.items, none)
  m := instruction

def cfg (label : Option Label) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (mode, register), tapes input output saved⟩

theorem step_scan_empty (output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) [] output saved mode register) =
      some (cfg (some .restore) [] output saved mode) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input]
  all_goals rfl

theorem step_scan_cons (bit : Bool) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) (bit :: input) output saved mode register) =
      some (cfg (some .scan) input output (bit :: saved) (nextMode mode bit)) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input, update_saved]
  all_goals rfl

theorem scanTrace (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .scan) input output saved mode register)) =
      some (cfg (some .restore) [] output (input.reverse ++ saved) (run mode input)) := by
  induction input generalizing saved mode register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run, List.reverse_nil, List.nil_append] using
          step_scan_empty output saved mode register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_scan_cons]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (bit :: saved) (nextMode mode bit) none

theorem restoreTrace (saved output : List Bool)
    (mode : Mode) (register : Option Bool) :
    (advance machine.step)^[saved.length + 1]
      (some (cfg (some .restore) [] output saved mode register)) =
      some (cfg (some .finish) [] (saved.reverse ++ output) [] mode) := by
  change (nextAt (1 : Fin 3) instruction)^[saved.length + 1]
    (some ⟨some .restore, (mode, register), tapes [] output saved⟩) =
    some ⟨some .finish, (mode, none), tapes [] (saved.reverse ++ output) []⟩
  have trace := transferAt_steps (2 : Fin 3) 1 (by decide) id false .restore (some .finish)
    instruction rfl (tapes [] [] []) saved output mode register
  simpa only [tapesAt, update_saved, update_output, List.map_id_fun, id_eq] using trace

theorem step_finish (output : List Bool) (mode : Mode)
    (register : Option Bool) :
    machine.step (cfg (some .finish) [] output [] mode register) =
      some (cfg none [] (decide (mode = .done) :: output) [] Mode.items) := by
  change some (TM2.stepAux (instruction .finish) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_output]
  all_goals rfl

theorem rawTrace (input : List Bool) :
    (advance machine.step)^[2 * input.length + 3]
      (some (cfg (some .scan) input [] [] Mode.items)) =
      some (cfg none [] (accepts input :: input) [] Mode.items) := by
  have first := scanTrace input [] [] Mode.items none
  simp only [List.append_nil] at first
  have second := restoreTrace input.reverse [] (run Mode.items input) none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at second
  have third : (advance machine.step)^[1]
      (some (cfg (some .finish) [] input [] (run Mode.items input))) =
      some (cfg none [] (accepts input :: input) [] Mode.items) := by
    simpa only [Function.iterate_one, advance_some, accepts] using
      step_finish input (run Mode.items input) none
  have time : 2 * input.length + 3 = (input.length + 1) + (input.length + 1) + 1 := by omega
  rw [time]
  exact joinTrace (joinTrace first second) third

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .scan) input [] [] Mode.items := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] output [] Mode.items := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem machine_finiteAlphabet (k : machine.K) :
    Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

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

inductive Label
  | save | saveRestore | frameSaved | phase
  | convertBins (label : UnaryToBinaryMachine.Label)
  | emitBins | seedIndex | index
  | convertLabel (label : UnaryToBinaryMachine.Label)
  | emitLabel | restoreLabel
  | items | numerator | numeratorDigit | denominator | denominatorDigit
  | dispatch
  | replace (label : SearchFixedReplaceMachine.Label)
  | fixed | reverse
  deriving DecidableEq, Fintype

def go (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .load (fun state => (state.1, none)) (.goto fun _ => next)

def copyFlag (yes no : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun state head => (state.1, head))
    (.push .reversed (fun state => state.2.getD false)
      (.branch (fun state => state.2.getD false) (go yes) (go no)))

def copyDigit (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun state head => (state.1, head))
    (.push .reversed (fun state => state.2.getD false) (go next))

theorem savedFrame_eq (word : List Bool) :
    MachineKeepDecision.frame word = BinPackingCompleteness.BinaryEncoding.frame word := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
      simp only [MachineKeepDecision.frame, BinPackingCompleteness.BinaryEncoding.frame, ih]

end BinPackingGap.SearchPrepareMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchUpdateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchUpdateMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open SearchSemantics SearchEncoding BinaryEncoding

inductive Label
  | start | copyRest | reverse | finish
  | findBins | skipItem | skipLabel | zeroControls
  | fillNoBins | fillNoItem | incrementLabel
  | fillYesBins | startItem | fillYesItem
  | convert (label : UnaryToBinaryMachine.Label)
  | frame | restorePayload | zeroLabel
  | items | numerator | numeratorDigit | denominator | denominatorDigit
  | replace (label : SearchFixedReplaceMachine.Label)
  deriving DecidableEq, Fintype

def go (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .load (fun state => (state.1, none)) (.goto (fun _ => next))

def copyBit (zero one : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun state head => (state.1, head))
    (.push .reversed (fun state => state.2.getD false)
      (.branch (fun state => state.2.getD false) (go one) (go zero)))

def copyDigit (next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun state head => (state.1, head))
    (.push .reversed (fun state => state.2.getD false) (go next))

def skipUnary (again next : Label) : TM2.Stmt (fun _ : Tape => Bool) Label Register :=
  .pop .input (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false) (go again) (go next))

def itemWork (base : Tapes) (n : Nat) (input reversed : List Bool) : Tapes :=
  io (put (put base .index (encodeWord n)) .compare (encodeWord n)) input reversed

end BinPackingGap.SearchUpdateMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchStageMachines
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialEmitMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution
abbrev Register := MachineUnaryMultiply.State Flags

inductive Label
  | start | count | fixed | reverseRaw | prependRaw | pushHeader | zeroFuel
  | multiply (phase : MachineUnaryMultiply.Label)
  deriving DecidableEq, Fintype

def clean (flags : Flags) : Register := ((flags, ()), none)

def dispatch (valid : Bool) : Label := if valid then .fixed else .reverseRaw

def finishLabel (valid : Bool) : Label :=
  if valid then .multiply .copyDrain else .zeroFuel

def residualFixed (valid : Bool) (n : Nat) : List Bool :=
  if valid then [] else encodeWord n

def fuelTime (valid : Bool) (n : Nat) : Nat :=
  if valid then MachineUnaryMultiply.steps n (n + 1) else 1

def rawSteps (valid : Bool) (n inputLength : Nat) : Nat :=
  (2 * n + 3) + 2 * (inputLength + 1) + 1 + fuelTime valid n

end BinPackingGap.SearchInitialEmitMachine

end OAI
end


