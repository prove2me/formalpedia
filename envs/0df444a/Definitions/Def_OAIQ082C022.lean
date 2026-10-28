-- Prove2me | Definitions.Def_OAIQ082C022
-- name    : OAIQ082C022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:47:58.225614+00:00
-- url     : https://prove2.me/theorems/d052e8aa-719e-45ef-899d-3184bd5dbf05
-- title:
--   Definitions bundle OAIQ082C022 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 103 declarations of OpenAI's Lean: 43 definitions, 4 inductive types or structures and 56 theorems. The definitions and types are `OAI.BinPackingGap.SearchInitialEmitMachine.cfg`, `OAI.BinPackingGap.SearchInitialEmitMachine.code`, `OAI.BinPackingGap.SearchInitialEmitMachine.enlarge`, `OAI.BinPackingGap.SearchInitialEmitMachine.join`, `OAI.BinPackingGap.SearchInitialEmitMachine.machine`, `OAI.BinPackingGap.SearchInitialEmitMachine.oneStep`, `OAI.BinPackingGap.SearchInitialEmitMachine.prependRawInTime`, `OAI.BinPackingGap.SearchInitialEmitMachine.program`, `OAI.BinPackingGap.SearchInitialItemsMachine.cfg`, `OAI.BinPackingGap.SearchInitialItemsMachine.clearInTime`, `OAI.BinPackingGap.SearchInitialItemsMachine.comparisonInTime`, `OAI.BinPackingGap.SearchInitialItemsMachine.copyInTime`, `OAI.BinPackingGap.SearchInitialItemsMachine.countInTime`, `OAI.BinPackingGap.SearchInitialItemsMachine.denominatorInTime`, `OAI.BinPackingGap.SearchInitialItemsMachine.enlarge`, `OAI.BinPackingGap.SearchInitialItemsMachine.join`, `OAI.BinPackingGap.SearchInitialItemsMachine.machine`, `OAI.BinPackingGap.SearchInitialItemsMachine.numeratorInTime`, `OAI.BinPackingGap.SearchInitialItemsMachine.oneStep`, `OAI.BinPackingGap.SearchInitialItemsMachine.program`, `OAI.BinPackingGap.SearchInitializeEncoding.shapeBits`, `OAI.BinPackingGap.SearchInitializeMachine.shapeComputation`, `OAI.BinPackingGap.SearchMachineComposition.Stages`, `OAI.BinPackingGap.SearchMachineComposition.applyAnswer`, `OAI.BinPackingGap.SearchMachineComposition.bodyComputation`, `OAI.BinPackingGap.SearchMachineComposition.prepare`, `OAI.BinPackingGap.SearchPrepareMachine.activeBits`, `OAI.BinPackingGap.SearchPrepareMachine.activeSteps`, `OAI.BinPackingGap.SearchPrepareMachine.bodyBits`, `OAI.BinPackingGap.SearchPrepareMachine.cfg`, `OAI.BinPackingGap.SearchPrepareMachine.inactiveRun`, `OAI.BinPackingGap.SearchPrepareMachine.initialSteps`, `OAI.BinPackingGap.SearchPrepareMachine.machine`, `OAI.BinPackingGap.SearchPrepareMachine.prefixSteps`, `OAI.BinPackingGap.SearchPrepareMachine.program`, `OAI.BinPackingGap.SearchPrepareMachine.queryBits`, `OAI.BinPackingGap.SearchPrepareMachine.selectedFixed`, `OAI.BinPackingGap.SearchPrepareMachine.suffixSteps`, `OAI.BinPackingGap.SearchSemantics.DoneInvariant`, `OAI.BinPackingGap.SearchSemantics.FillInvariant` and 7 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`BinPacking_Packing_ExtractedCover`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/ExtractedCover.lean), [`BinPacking_Search_SearchFixedReplaceMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchFixedReplaceMachine.lean), [`BinPacking_Search_SearchInitialItemsMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchInitialItemsMachine.lean), [`BinPacking_Search_SearchInitializeEncoding`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchInitializeEncoding.lean), [`BinPacking_Search_SearchPrepareMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchPrepareMachine.lean), [`BinPacking_Search_SearchStageMachines`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchStageMachines.lean), [`BinPacking_Search_SearchUpdateMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchUpdateMachine.lean).
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C010`, `OAIQ082C011`, `OAIQ082C013`, `OAIQ082C014` and `OAIQ082C015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C025` and `OAIQ082C026`; the statements `OAI_BinPackingGap_extractedCover_card_le` and `OAI.BinPackingGap.extractedCover_card_le_oaiq082`; the proofs of `OAI_BinPackingGap_extractedCover_card_le` and `OAI.BinPackingGap.extractedCover_card_le_oaiq082`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C010
import Definitions.Def_OAIQ082C011
import Definitions.Def_OAIQ082C013
import Definitions.Def_OAIQ082C014
import Definitions.Def_OAIQ082C015

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_ExtractedCover
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.SideChoice

open UniformTree

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable {d : ℕ} (T : CompetingTrees d)

def taggedDepth : T.plus.Node ⊕ T.minus.Node → ℕ := Sum.elim depth depth

end BinPackingGap.SideChoice

namespace BinPackingGap

section

def reductionInstance (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) : Instance :=
  (reductionInventory c ρ G k).packingInstance

open UniformTree

end

def extractedCover (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) {b : ℕ}
    (p : Packing (reductionInstance c ρ G k) b) : Finset G.Vertex :=
  thresholdCover (depthDemand c ρ)
    (PackingCounts.xplus p (reductionInventory c ρ G k).itemEquiv)

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitializeEncoding
attribute [-instance] _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchSemantics

open ExtensionQuery

theorem ext_next_exists {b : Nat} {r : RawInstance} {fixed : List (Option Nat)}
    (he : Ext b r fixed) {i : Nat} (hi : i < fixed.length) :
    ∃ j < b, Ext b r (fixed.set i (some j)) := by
  rcases he with ⟨hr, a, hfeas, ha⟩
  have hlen := ha.1
  obtain ⟨j, hj⟩ := get_some_of_lt a i (by omega)
  refine ⟨j, hfeas.2.1 j (mem_of_get_some hj), hr, a, hfeas, ?_⟩
  exact agrees_set ha hi hj

theorem ext_complete {b : Nat} {r : RawInstance} {fixed : List (Option Nat)}
    (he : Ext b r fixed) (hp : Prefix fixed.length fixed) :
    RawPacking.Feasible r ⟨b, labels fixed⟩ := by
  obtain ⟨_, a, hfeas, ha⟩ := he
  simpa only [labels_eq_of_complete ha hp] using hfeas

theorem run_done (D : List Bool → Bool) (s : State) (h : s.phase = .done) (t : Nat) :
    run D t s = s := by
  induction t with
  | zero => rfl
  | succ t ih => simpa [run, step_done D s h] using ih

theorem ext_none_opt_iff (r : RawInstance) (hr : r.Valid) (b : Nat) :
    Ext b r (List.replicate r.length none) ↔ opt (r.toInstance hr) ≤ b := by
  rw [ext_none_iff]
  constructor
  · rintro ⟨_, ha⟩
    exact opt_le_of_hasPacking
      ((RawPacking.hasPacking_iff_exists_feasible r hr b).mpr ha)
  · intro hb
    exact ⟨hr, (RawPacking.hasPacking_iff_exists_feasible r hr b).mp
      ((hasPacking_iff_opt_le (r.toInstance hr) b).mpr hb)⟩

theorem opt_pos (r : RawInstance) (hr : r.Valid) (hn : 0 < r.length) :
    0 < opt (r.toInstance hr) := by
  obtain ⟨p⟩ := opt_attained (r.toInstance hr)
  have := (p.assignment ⟨0, hn⟩).isLt
  omega

structure FindInvariant (r : RawInstance) (hr : r.Valid) (s : State) : Prop where
  bins_pos : 0 < s.bins
  bins_le : s.bins ≤ opt (r.toInstance hr)
  item_zero : s.item = 0
  label_zero : s.label = 0
  fixed_none : s.fixed = List.replicate r.length none

structure FillInvariant (r : RawInstance) (hr : r.Valid) (s : State) : Prop where
  bins_eq : s.bins = opt (r.toInstance hr)
  bins_pos : 0 < s.bins
  item_lt : s.item < r.length
  label_lt : s.label < s.bins
  fixed_length : s.fixed.length = r.length
  «prefix» : Prefix s.item s.fixed
  «extends» : Ext s.bins r s.fixed
  rejected : ∀ j < s.label, ¬ Ext s.bins r (s.fixed.set s.item (some j))

structure DoneInvariant (r : RawInstance) (hr : r.Valid) (s : State) : Prop where
  bins_eq : s.bins = opt (r.toInstance hr)
  item_eq : s.item = r.length
  label_zero : s.label = 0
  fixed_length : s.fixed.length = r.length
  «prefix» : Prefix r.length s.fixed
  «extends» : Ext s.bins r s.fixed

def Invariant (r : RawInstance) (hr : r.Valid) (s : State) : Prop :=
  s.items = r ∧ match s.phase with
  | .find => FindInvariant r hr s
  | .fill => FillInvariant r hr s
  | .done => DoneInvariant r hr s
  | .invalid => False

theorem initial_invariant (r : RawInstance) (hr : r.Valid) :
    Invariant r hr (initial r true) := by
  by_cases hn : r.length = 0
  · have ho := opt_eq_zero_of_n_eq_zero (r.toInstance hr) hn
    have he : Ext 0 r [] := by
      simpa [hn] using (ext_none_opt_iff r hr 0).mpr (by omega)
    have hi : initial r true = ⟨r, .done, 0, 0, 0, []⟩ := by simp [initial, hn]
    rw [hi]
    refine ⟨rfl, ?_⟩
    change DoneInvariant r hr ⟨r, .done, 0, 0, 0, []⟩
    exact ⟨ho.symm, hn.symm, rfl, hn.symm,
      by simpa [hn] using prefix_none 0, he⟩
  · have ho := opt_pos r hr (by omega)
    have hi : initial r true = ⟨r, .find, 1, 0, 0, List.replicate r.length none⟩ := by
      simp [initial, hn]
    rw [hi]
    refine ⟨rfl, ?_⟩
    change FindInvariant r hr ⟨r, .find, 1, 0, 0, List.replicate r.length none⟩
    exact ⟨by change 0 < 1; decide, by dsimp; omega, rfl, rfl, rfl⟩

theorem ext_label_lt {b : Nat} {r : RawInstance} {fixed : List (Option Nat)}
    (he : Ext b r fixed) {j : Nat} (hj : some j ∈ fixed) : j < b := by
  obtain ⟨_, a, hfeas, ha⟩ := he
  obtain ⟨i, hi⟩ := index_of_mem hj
  exact hfeas.2.1 j (mem_of_get_some (ha.2 i j hi))

theorem invariant_bounds {r : RawInstance} {hr : r.Valid} {s : State}
    (hs : Invariant r hr s) :
    s.items = r ∧ s.bins ≤ r.length ∧ s.item ≤ r.length ∧ s.label ≤ r.length ∧
      s.fixed.length = r.length ∧ ∀ j, some j ∈ s.fixed → j < r.length := by
  rcases hs with ⟨hitems, hs⟩
  refine ⟨hitems, ?_⟩
  have hopt := opt_le_n (r.toInstance hr)
  change opt (r.toInstance hr) ≤ r.length at hopt
  cases hp : s.phase with
  | invalid => simp only [hp] at hs
  | find =>
      simp only [hp] at hs
      change FindInvariant r hr s at hs
      have hitem := hs.item_zero
      have hlabel := hs.label_zero
      refine ⟨hs.bins_le.trans hopt, by omega, by omega, ?_, ?_⟩
      · simp [hs.fixed_none]
      · intro j hj
        simp [hs.fixed_none] at hj
  | fill =>
      simp only [hp] at hs
      change FillInvariant r hr s at hs
      have hbins := hs.bins_eq
      have hlabel := hs.label_lt
      have hb : s.bins ≤ r.length := by omega
      refine ⟨hb, Nat.le_of_lt hs.item_lt, by omega, hs.fixed_length, ?_⟩
      intro j hj
      exact lt_of_lt_of_le (ext_label_lt hs.extends hj) hb
  | done =>
      simp only [hp] at hs
      change DoneInvariant r hr s at hs
      have hbins := hs.bins_eq
      have hitem := hs.item_eq
      have hlabel := hs.label_zero
      have hb : s.bins ≤ r.length := by omega
      refine ⟨hb, by omega, by omega, hs.fixed_length, ?_⟩
      intro j hj
      exact lt_of_lt_of_le (ext_label_lt hs.extends hj) hb

def rank (s : State) : Nat :=
  match s.phase with
  | .find => s.items.length * s.items.length + (s.items.length + 1 - s.bins)
  | .fill => (s.items.length - s.item) * s.bins - s.label
  | .done | .invalid => 0

theorem rank_pos {r : RawInstance} {hr : r.Valid} {s : State}
    (hs : Invariant r hr s) (hd : s.phase ≠ .done) : 0 < rank s := by
  have hb := (invariant_bounds hs).2.1
  rcases hs with ⟨hitems, hs⟩
  cases hp : s.phase with
  | invalid => simp only [hp] at hs
  | done => exact False.elim (hd hp)
  | find =>
      simp only [rank, hp, hitems]
      omega
  | fill =>
      simp only [hp] at hs
      change FillInvariant r hr s at hs
      have hitem := hs.item_lt
      have hm : s.bins ≤ (r.length - s.item) * s.bins := by
        simpa using Nat.mul_le_mul_right s.bins
          (show 1 ≤ r.length - s.item by omega)
      simp only [rank, hp, hitems]
      have := hs.label_lt
      omega

theorem rank_step_lt {D : List Bool → Bool} {r : RawInstance} {hr : r.Valid}
    {s : State} (hs : Invariant r hr s) (hd : s.phase ≠ .done) :
    rank (step D s) < rank s := by
  have hb := (invariant_bounds hs).2.1
  rcases hs with ⟨hitems, hs⟩
  cases hp : s.phase with
  | invalid => simp only [hp] at hs
  | done => exact False.elim (hd hp)
  | find =>
      simp only [hp] at hs
      change FindInvariant r hr s at hs
      by_cases ha : D (query s) = true
      · have hm := Nat.mul_le_mul_left r.length hb
        simp only [rank, step, update, hp, ha, ↓reduceIte, hitems, Nat.sub_zero]
        omega
      · simp only [rank, step, update, hp, ha, Bool.false_eq_true, ↓reduceIte, hitems]
        omega
  | fill =>
      simp only [hp] at hs
      change FillInvariant r hr s at hs
      have hitem := hs.item_lt
      have hm : s.bins ≤ (r.length - s.item) * s.bins := by
        simpa using Nat.mul_le_mul_right s.bins
          (show 1 ≤ r.length - s.item by omega)
      have hlabel := hs.label_lt
      by_cases ha : D (query s) = true
      · have hsub : r.length - s.item = (r.length - (s.item + 1)) + 1 := by omega
        have hmul : (r.length - s.item) * s.bins =
            (r.length - (s.item + 1)) * s.bins + s.bins := by
          rw [hsub, Nat.add_mul]
          simp
        by_cases hlast : s.item + 1 = r.length
        · simp only [rank, step, update, hp, ha, hitems, hlast, ↓reduceIte]
          omega
        · simp only [rank, step, update, hp, ha, hitems, hlast, ↓reduceIte,
            Nat.sub_zero]
          omega
      · simp only [rank, step, update, hp, ha, Bool.false_eq_true, ↓reduceIte, hitems]
        omega

theorem rank_initial_le (r : RawInstance) : rank (initial r true) ≤ fuel r := by
  by_cases hn : r.length = 0
  · simp [rank, initial, hn, fuel]
  · simp [rank, initial, hn, fuel, Nat.mul_add, Nat.add_comm]

end BinPackingGap.SearchSemantics

namespace BinPackingGap.SearchMachineComposition

open Turing BinPackingGames.Foundations.Complexity
open SearchSemantics SearchEncoding

def prepare (s : State) : State × List Bool := (s, query s)

def applyAnswer (p : State × Bool) : State := update p.1 p.2

structure Stages where
  initializeComputation : TM2ComputableInPolyTime (id : List Bool → List Bool)
    (MachineBoundedIteration.inputBits stateBits) «initialize_»
  initializeFinite : MachineFiniteAlphabet.FiniteAlphabet initializeComputation.tm
  prepareComputation : TM2ComputableInPolyTime stateBits
    (MachineKeepDecision.typedInputBits stateBits) prepare
  prepareFinite : MachineFiniteAlphabet.FiniteAlphabet prepareComputation.tm
  updateComputation : TM2ComputableInPolyTime
    (MachineKeepDecision.typedOutputBits stateBits) stateBits applyAnswer
  updateFinite : MachineFiniteAlphabet.FiniteAlphabet updateComputation.tm
  finalizeComputation : TM2ComputableInPolyTime stateBits
    BinaryEncoding.packingResultBits output
  finalizeFinite : MachineFiniteAlphabet.FiniteAlphabet finalizeComputation.tm

noncomputable def bodyComputation (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D) :
    TM2ComputableInPolyTime stateBits stateBits (step D) :=
  MachineSequential.composeBits (f := prepare)
    (g := fun p => applyAnswer (MachineKeepDecision.typedKeep D p))
    stages.prepareComputation
    (MachineSequential.composeBits (f := MachineKeepDecision.typedKeep D) (g := applyAnswer)
      (MachineKeepDecision.computationWithSavedCodec stateBits D decision)
      stages.updateComputation)

theorem bodyComputation_finiteAlphabet (stages : Stages) (D : List Bool → Bool)
    (decision : TM2ComputableInPolyTime (id : List Bool → List Bool)
      (fun answer => [answer]) D)
    (finite : MachineFiniteAlphabet.FiniteAlphabet decision.tm) :
    MachineFiniteAlphabet.FiniteAlphabet (bodyComputation stages D decision).tm := by
  exact MachineFiniteAlphabet.composeBits stages.prepareComputation _
    stages.prepareFinite (MachineFiniteAlphabet.composeBits _ stages.updateComputation
      (MachineKeepDecision.computationWithSavedCodec_finiteAlphabet
        stateBits D decision finite) stages.updateFinite)

end BinPackingGap.SearchMachineComposition

namespace BinPackingGap.SearchInitializeEncoding

open BinPackingGames.Foundations.Complexity

def shapeBits (input : List Bool) : List Bool :=
  (BinaryEncoding.decodeRawInstance input).isSome :: input

end BinPackingGap.SearchInitializeEncoding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchFixedReplaceMachine
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

theorem copyTrace (fixed : List (Option Nat)) (source index payload reversed : List Bool) :
    tick^[(fixedBits fixed).length]
      (some (C (some (.entry false)) (words (fixedBits fixed ++ source) index payload reversed))) =
      some (C none (words source index payload ((fixedBits fixed).reverse ++ reversed))) := by
  induction fixed generalizing reversed with
  | nil =>
      simpa [next, consume, emit, put_words, words, fixedBits, listBits] using
        one place distinct labels exit program atLabels base ambient (.entry false)
          (words (false :: source) index payload reversed)
  | cons entry fixed ih =>
      have first := one place distinct labels exit program atLabels base ambient (.entry false)
        (words (true :: (optionBits natBits entry ++ fixedBits fixed ++ source))
          index payload reversed)
      have second := optionTrace place distinct labels exit program atLabels base ambient .after
        entry (fixedBits fixed ++ source) index payload (true :: reversed)
      have third := ih ((optionBits natBits entry).reverse ++ true :: reversed)
      simp [next, consume, emit, put_words, words, saved, Action.writes,
        Action.next] at first second
      have full := joinTrace (joinTrace (oneStepTrace first) second) third
      simpa [fixedBits, listBits, List.reverse_cons, List.reverse_append,
        List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem replaceTrace (fixed : List (Option Nat)) (i value : Nat)
    (source index payload reversed : List Bool) :
    tick^[(fixedBits fixed).length + (i + 1) + (natBits value).length]
      (some (C (some (.entry true)) (words (fixedBits fixed ++ source)
        (encodeWord i ++ index) (natBits value ++ payload) reversed))) =
      some (C none (words source index payload
        ((fixedBits (fixed.set i (some value))).reverse ++ reversed))) := by
  induction fixed generalizing i reversed with
  | nil =>
      have first := one place distinct labels exit program atLabels base ambient (.entry true)
        (words (false :: source) (encodeWord i ++ index) (natBits value ++ payload) reversed)
      have second := drainIndexTrace place distinct labels exit program atLabels base ambient
        i source index (natBits value ++ payload) (false :: reversed)
      have third := drainPayloadTrace place distinct labels exit program atLabels base ambient
        value.bits source index payload (false :: reversed)
      simp [next, consume, emit, put_words, words] at first
      have full := joinTrace (joinTrace (oneStepTrace first) second) third
      simpa [fixedBits, listBits, natBits, BinPackingCompleteness.BinaryEncoding.nameBits] using full
  | cons entry fixed ih =>
      cases i with
      | zero =>
          have first := one place distinct labels exit program atLabels base ambient (.entry true)
            (words (true :: (optionBits natBits entry ++ fixedBits fixed ++ source))
              (false :: index) (natBits value ++ payload) reversed)
          have second := one place distinct labels exit program atLabels base ambient .index
            (words (optionBits natBits entry ++ fixedBits fixed ++ source)
              (false :: index) (natBits value ++ payload) (true :: reversed))
          have third := payloadTrace place distinct labels exit program atLabels base ambient
            value.bits (optionBits natBits entry ++ fixedBits fixed ++ source)
              index payload (true :: true :: reversed)
          have fourth := optionTrace place distinct labels exit program atLabels base ambient .discard
            entry (fixedBits fixed ++ source) index payload
              ((natBits value).reverse ++ true :: true :: reversed)
          have fifth := copyTrace place distinct labels exit program atLabels base ambient
            fixed source index payload ((natBits value).reverse ++ true :: true :: reversed)
          simp [next, consume, emit, put_words, words] at first second
          simp only [List.append_assoc] at third
          simp only [saved, Action.writes, Bool.false_eq_true, ↓reduceIte, Action.next] at fourth
          have full := joinTrace (joinTrace (joinTrace (joinTrace (oneStepTrace first) (oneStepTrace second)) third) fourth) fifth
          have clock : 1 + 1 + (BinPackingCompleteness.BinaryEncoding.frame value.bits).length +
              (optionBits natBits entry).length + (fixedBits fixed).length =
              (fixedBits (entry :: fixed)).length + (0 + 1) + (natBits value).length := by
            simp only [fixedBits, listBits, List.length_cons, List.length_append,
              natBits, BinPackingCompleteness.BinaryEncoding.nameBits]
            omega
          rw [clock] at full
          simpa [fixedBits, listBits, optionBits, natBits,
            BinPackingCompleteness.BinaryEncoding.nameBits, encodeWord,
            List.reverse_cons, List.reverse_append, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
      | succ i =>
          have first := one place distinct labels exit program atLabels base ambient (.entry true)
            (words (true :: (optionBits natBits entry ++ fixedBits fixed ++ source))
              (true :: (encodeWord i ++ index)) (natBits value ++ payload) reversed)
          have second := one place distinct labels exit program atLabels base ambient .index
            (words (optionBits natBits entry ++ fixedBits fixed ++ source)
              (true :: (encodeWord i ++ index)) (natBits value ++ payload) (true :: reversed))
          have third := optionTrace place distinct labels exit program atLabels base ambient .before
            entry (fixedBits fixed ++ source) (encodeWord i ++ index) (natBits value ++ payload)
              (true :: reversed)
          have fourth := ih i ((optionBits natBits entry).reverse ++ true :: reversed)
          simp [next, consume, emit, put_words, words] at first second
          simp only [saved, Action.writes, ↓reduceIte, Action.next] at third
          have full := joinTrace (joinTrace (joinTrace (oneStepTrace first) (oneStepTrace second)) third) fourth
          simpa [fixedBits, listBits, encodeWord, List.replicate_succ,
            List.reverse_cons, List.reverse_append, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end BinPackingGap.SearchFixedReplaceMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchInitialItemsMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialItemsMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchInitializeEncoding
open BinPackingGames.Reduction.MachineTransfer

def program : Label → TM2.Stmt Alphabet Label State
  | .control phase => instruction phase
  | .number which phase => ExtensionNatMachine.statement (scanPorts which)
      (Label.number which) (some (scanSuccess which))
      (some (.control .malformedDrain)) phase
  | .order phase => ExtensionNatMachine.orderStatement orderPorts Label.order orderExit phase

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 0
  Γ := Alphabet
  Λ := Label
  main := .control .entry
  σ := State
  initialState := clean true
  m := program

def cfg (label : Option Label) (valid : Bool) (base : Tape → List Bool) : machine.Cfg :=
  ⟨label, clean valid, base⟩

def oneStep {start finish : machine.Cfg} (step : machine.step start = some finish) :
    StateTransition.EvalsToInTime machine.step start (some finish) 1 where
  steps := 1
  evals_in_steps := by
    change machine.step start = some finish
    exact step
  steps_le_m := Nat.le_refl _

def join {start middle finish : machine.Cfg} {a b : Nat}
    (first : StateTransition.EvalsToInTime machine.step start (some middle) a)
    (second : StateTransition.EvalsToInTime machine.step middle (some finish) b) :
    StateTransition.EvalsToInTime machine.step start (some finish) (a + b) := by
  simpa only [Nat.add_comm] using StateTransition.EvalsToInTime.trans machine.step
    a b start middle (some finish) first second

def enlarge {start finish : machine.Cfg} {a b : Nat}
    (run : StateTransition.EvalsToInTime machine.step start (some finish) a)
    (bound : a ≤ b) : StateTransition.EvalsToInTime machine.step start (some finish) b where
  toEvalsTo := run.toEvalsTo
  steps_le_m := Nat.le_trans run.steps_le_m bound

theorem entryStep (flag : Bool) (raw : List Bool) :
    machine.step (cfg (some (.control .entry)) true (tapes (flag :: raw) [] [] [] [] [])) =
      some (cfg (some (.control (if flag then .copyOut else .malformedDrain))) true
        (tapes raw [] [] [] [] [])) := by
  change some (TM2.stepAux (program (.control .entry)) (clean true)
    (tapes (flag :: raw) [] [] [] [] [])) = _
  cases flag <;>
    simp [program, instruction, jump, cfg, clean, validity, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, tapes, update_raw] <;> rfl

theorem markerStep (valid flag : Bool) (raw stream count : List Bool) :
    machine.step (cfg (some (.control .marker)) valid
      (tapes raw (flag :: stream) [] [] [] count)) =
      some (cfg (some (if flag then .number .numerator .scan else .control .countOut))
        valid (tapes raw stream [] [] [] (if flag then true :: count else count))) := by
  change some (TM2.stepAux (program (.control .marker)) (clean valid)
    (tapes raw (flag :: stream) [] [] [] count)) = _
  cases flag <;>
    simp [program, instruction, jump, cfg, clean, validity, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, tapes, update_stream, update_count] <;> rfl

theorem positiveStep (valid : Bool) (raw stream numerator count : List Bool) :
    machine.step (cfg (some (.control .positive)) valid
      (tapes raw stream [] numerator [] count)) =
      some (cfg (some (.number .denominator .scan))
        (valid && decide (numerator ≠ [])) (tapes raw stream [] numerator [] count)) := by
  change some (TM2.stepAux (program (.control .positive)) (clean valid)
    (tapes raw stream [] numerator [] count)) = _
  cases numerator <;>
    simp [program, instruction, jump, cfg, clean, validity, BinaryAddMachine.clean,
      BinaryAddMachine.state, TM2.stepAux, tapes, update_numerator] <;> rfl

def numeratorInTime (valid : Bool) (raw suffix count : List Bool) (n : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.number .numerator .scan)) valid
        (tapes raw (BinaryEncoding.natBits n ++ suffix) [] [] [] count))
      (some (cfg (some (.control .positive)) valid (tapes raw suffix [] n.bits [] count)))
      (2 * n.size + 2) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.number .numerator .scan), BinaryAddMachine.clean (valid, .eq),
      tapes raw (BinaryEncoding.natBits n ++ suffix) [] [] [] count⟩
    (some ⟨some (.control .positive), BinaryAddMachine.clean (valid, .eq),
      tapes raw suffix [] n.bits [] count⟩) _
  have result : ExtensionNatMachine.resultTapes (scanPorts .numerator)
      (tapes raw (BinaryEncoding.natBits n ++ suffix) [] [] [] count) n suffix =
      tapes raw suffix [] n.bits [] count := by
    simp only [scanPorts]
    funext k
    fin_cases k <;> first | rfl | exact List.append_nil _
  simpa only [cfg, result, scanSuccess] using!
    ExtensionNatMachine.natInTime (scanPorts .numerator) (Label.number .numerator)
      (some (scanSuccess .numerator)) (some (.control .malformedDrain)) program
      (fun _ => rfl) (tapes raw (BinaryEncoding.natBits n ++ suffix) [] [] [] count)
      n suffix rfl rfl (valid, .eq)

def denominatorInTime (valid : Bool) (raw suffix count : List Bool) (n d : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.number .denominator .scan)) valid
        (tapes raw (BinaryEncoding.natBits d ++ suffix) [] n.bits [] count))
      (some (cfg (some (.order .leftOut)) valid (tapes raw suffix [] n.bits d.bits count)))
      (2 * d.size + 2) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.number .denominator .scan), BinaryAddMachine.clean (valid, .eq),
      tapes raw (BinaryEncoding.natBits d ++ suffix) [] n.bits [] count⟩
    (some ⟨some (.order .leftOut), BinaryAddMachine.clean (valid, .eq),
      tapes raw suffix [] n.bits d.bits count⟩) _
  have result : ExtensionNatMachine.resultTapes (scanPorts .denominator)
      (tapes raw (BinaryEncoding.natBits d ++ suffix) [] n.bits [] count) d suffix =
      tapes raw suffix [] n.bits d.bits count := by
    simp only [scanPorts]
    funext k
    fin_cases k <;> first | rfl | exact List.append_nil _
  simpa only [cfg, result, scanSuccess] using!
    ExtensionNatMachine.natInTime (scanPorts .denominator) (Label.number .denominator)
      (some (scanSuccess .denominator)) (some (.control .malformedDrain)) program
      (fun _ => rfl) (tapes raw (BinaryEncoding.natBits d ++ suffix) [] n.bits [] count)
      d suffix rfl rfl (valid, .eq)

def comparisonInTime (valid : Bool) (raw stream count : List Bool) (a d : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.order .leftOut)) valid (tapes raw stream [] a.bits d.bits count))
      (some (cfg (some (.control .clearNumerator)) (valid && decide (a ≤ d))
        (tapes raw stream [] a.bits d.bits count)))
      (BinaryOrderMachine.preservingSteps a.size d.size + 1) := by
  have trace := ExtensionNatMachine.preservingOrderInTime orderPorts Label.order orderExit
    program (fun _ => rfl) (tapes raw stream [] a.bits d.bits count) a d
    rfl rfl rfl rfl rfl valid
  have exit : orderExit (BinaryOrderMachine.orderNat a d .eq) =
      some (.control (if a ≤ d then .clearNumerator else .failed)) := by
    unfold BinaryOrderMachine.orderNat
    split_ifs <;> simp_all [orderExit] <;> omega
  rw [exit] at trace
  by_cases h : a ≤ d
  · simpa only [h, ite_true, if_true, decide_true, Bool.and_true, cfg, clean] using
      enlarge (b := BinaryOrderMachine.preservingSteps a.size d.size + 1) trace (by omega)
  · have failure : machine.step (cfg (some (.control .failed)) valid
        (tapes raw stream [] a.bits d.bits count)) =
        some (cfg (some (.control .clearNumerator)) false
          (tapes raw stream [] a.bits d.bits count)) := by rfl
    simp only [h, ite_false] at trace
    simpa only [h, ite_false, decide_false, Bool.and_false, cfg, clean] using
      join trace (oneStep failure)

def clearInTime (valid : Bool) (raw stream numerator denominator count : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.control .clearNumerator)) valid
        (tapes raw stream [] numerator denominator count))
      (some (cfg (some (.control .marker)) valid (tapes raw stream [] [] [] count)))
      (numerator.length + denominator.length + 2) := by
  have first := MachineDrain.drainInTime (3 : Tape) (.control .clearNumerator)
    (some (.control .clearDenominator)) program rfl
    (tapes raw stream [] numerator denominator count) (((valid, Ordering.eq), false), none) none
  have second := MachineDrain.drainInTime (4 : Tape) (.control .clearDenominator)
    (some (.control .marker)) program rfl
    (tapes raw stream [] [] denominator count) (((valid, Ordering.eq), false), none) none
  simp only [update_numerator, tapes] at first
  simp only [update_denominator, tapes] at second
  have both := join first second
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.control .clearNumerator), BinaryAddMachine.clean (valid, .eq),
      tapes raw stream [] numerator denominator count⟩
    (some ⟨some (.control .marker), BinaryAddMachine.clean (valid, .eq),
      tapes raw stream [] [] [] count⟩) _
  exact { toEvalsTo := both.toEvalsTo
          steps_le_m := by
            have bound := both.steps_le_m
            omega }

theorem validItems_cons (a d : Nat) (items : RawInstance) :
    ExtensionCertificate.validItems ((a, d) :: items) =
      (decide (0 < a) && decide (a ≤ d) && ExtensionCertificate.validItems items) := by
  simp [ExtensionCertificate.validItems, Bool.and_assoc]

def copyInTime (raw : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.control .copyOut)) true (tapes raw [] [] [] [] []))
      (some (cfg (some (.control .seed)) true (tapes raw raw [] [] [] [])))
      (2 * (raw.length + 1)) := by
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.control .copyOut), BinaryAddMachine.clean (true, .eq),
      tapes raw [] [] [] [] []⟩
    (some ⟨some (.control .seed), BinaryAddMachine.clean (true, .eq),
      tapes raw raw [] [] [] []⟩) _
  simpa only [cfg, clean, BinaryAddMachine.clean, BinaryAddMachine.state,
    update_stream, tapes, List.append_nil] using
    MachineCopy.copyInTime (0 : Tape) 1 2 (by decide) (by decide) (by decide)
      false (.control .copyOut) (.control .copyBack) (some (.control .seed)) program
      rfl rfl (tapes raw [] [] [] [] []) rfl (((true, Ordering.eq), false), none) none

theorem seedStep (raw : List Bool) :
    machine.step (cfg (some (.control .seed)) true (tapes raw raw [] [] [] [])) =
      some (cfg (some (.control .marker)) true (tapes raw raw [] [] [] (encodeWord 0))) := by
  change some (TM2.stepAux (program (.control .seed)) (clean true)
    (tapes raw raw [] [] [] [])) = _
  simp [program, instruction, jump, cfg, clean, validity, BinaryAddMachine.clean,
    BinaryAddMachine.state, TM2.stepAux, tapes, update_count, encodeWord]
  rfl

def countInTime (valid : Bool) (raw : List Bool) (count : Nat) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (.control .countOut)) valid (tapes raw [] [] [] [] (encodeWord count)))
      (some (cfg (some (.control .finish)) valid
        (tapes (encodeWord count ++ raw) [] [] [] [] [])))
      (2 * (count + 2)) := by
  have first := transferAtInTime (7 : Tape) 2 (by decide) id false
    (.control .countOut) (some (.control .countBack)) program rfl
    (tapes raw [] [] [] [] (encodeWord count)) (((valid, Ordering.eq), false), none) none
  simp only [tapesAt, update_count, update_scratch, tapes, List.map_id_fun, id_eq,
    List.append_nil] at first
  have second := transferAtInTime (2 : Tape) 0 (by decide) id false
    (.control .countBack) (some (.control .finish)) program rfl
    (tapes raw [] (encodeWord count).reverse [] [] [])
    (((valid, Ordering.eq), false), none) none
  simp only [tapesAt, update_scratch, update_raw, tapes, List.map_id_fun, id_eq,
    List.reverse_reverse, List.length_reverse] at second
  have length : (encodeWord count).length = count + 1 := by simp [encodeWord]
  have both := join first second
  change StateTransition.EvalsToInTime (TM2.step program)
    ⟨some (.control .countOut), BinaryAddMachine.clean (valid, .eq),
      tapes raw [] [] [] [] (encodeWord count)⟩
    (some ⟨some (.control .finish), BinaryAddMachine.clean (valid, .eq),
      tapes (encodeWord count ++ raw) [] [] [] [] []⟩) _
  exact { toEvalsTo := both.toEvalsTo
          steps_le_m := by
            have bound := both.steps_le_m
            simp only [length] at bound
            omega }

theorem finishStep (valid : Bool) (output : List Bool) :
    machine.step (cfg (some (.control .finish)) valid (tapes output [] [] [] [] [])) =
      some (cfg none true (tapes (valid :: output) [] [] [] [] [])) := by
  change some (TM2.stepAux (program (.control .finish)) (clean valid)
    (tapes output [] [] [] [] [])) = _
  simp [program, instruction, cfg, clean, validity, BinaryAddMachine.clean,
    BinaryAddMachine.state, TM2.stepAux, tapes, update_raw]
  rfl

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some (.control .entry)) true (tapes input [] [] [] [] []) := by
  unfold initList cfg
  congr 1
  funext k; fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none true (tapes output [] [] [] [] []) := by
  unfold haltList cfg
  congr 1
  funext k; fin_cases k <;> rfl

theorem item_count_le (items : RawInstance) :
    items.length ≤ (BinaryEncoding.rawInstanceBits items).length := by
  induction items with
  | nil => simp
  | cons item items ih =>
      rcases item with ⟨a, d⟩
      simp only [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits,
        BinaryEncoding.pairBits, List.length_cons, List.length_append] at ih ⊢
      omega

end BinPackingGap.SearchInitialItemsMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchPrepareMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchPrepareMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open SearchSemantics SearchEncoding BinaryEncoding SearchMachineComposition
open BinPackingGames.Reduction.MachineTransfer

def program : MachineCanonicalOutput.Program Tape Label Register where
  input := .input
  output := .output
  main := .save
  initial := (false, none)
  code := code

abbrev machine := MachineCanonicalOutput.sourceMachine program

def cfg (label : Option Label) (fill : Bool)
    (input binary scratch index payload reversed output : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (fill, register), tapes input binary scratch index payload reversed output⟩

theorem oneStepTrace {a b : machine.Cfg} (h : machine.step a = some b) :
    (advance machine.step)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

theorem actualStep : TM2.step code = machine.step := rfl

theorem transferNext (dst : Tape) : nextAt dst code = advance machine.step := by
  funext state
  rfl

theorem saveTrace (word : List Bool) :
    (advance machine.step)^[2 * (word.length + 1)]
      (some (cfg (some .save) false word [] [] [] [] [] [])) =
      some (cfg (some .frameSaved) false word [] [] [] word [] []) := by
  have h := MachineCopy.copyTrace (K := Tape) (σ := Bool) .input .payload .scratch
    (by decide) (by decide) (by decide) false .save .saveRestore (some .frameSaved)
    code rfl rfl (tapes word [] [] [] [] [] []) rfl false none
  rw [actualStep] at h
  simpa only [cfg, tapes_input, tapes_payload, update_payload, List.append_nil] using! h

theorem frameSavedTrace (word : List Bool) :
    (advance machine.step)^[word.length + 1]
      (some (cfg (some .frameSaved) false word [] [] [] word [] [])) =
      some (cfg (some .phase) false word [] [] [] []
        ((BinPackingCompleteness.BinaryEncoding.frame word).reverse) []) := by
  have h := FrameEmitMachine.trace (K := Tape) (A := Bool) .payload .reversed (by decide)
    .frameSaved (some .phase) code rfl (tapes word [] [] [] [] [] []) false word []
  rw [actualStep] at h
  simpa only [cfg, tapesAt, update_payload, update_reversed, List.append_nil] using! h

theorem phaseActive (fill : Bool) (word reversed : List Bool) :
    machine.step (cfg (some .phase) false (false :: fill :: word) [] [] [] [] reversed []) =
      some (cfg (some (.convertBins .scan)) fill word [] [] [] [] reversed []) := by
  change some (TM2.stepAux (code .phase) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem phaseInactive (bit : Bool) (word reversed : List Bool) :
    machine.step (cfg (some .phase) false (true :: bit :: word) [] [] [] [] reversed []) =
      some (cfg (some .reverse) false (bit :: word) [] [] [] [] reversed []) := by
  change some (TM2.stepAux (code .phase) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem convertBinsTrace (fill : Bool) (n : Nat) (word reversed : List Bool) :
    (advance machine.step)^[UnaryToBinaryMachine.steps n 0]
      (some (cfg (some (.convertBins .scan)) fill (encodeWord n ++ word)
        [] [] [] [] reversed [])) =
      some (cfg (some .emitBins) fill word n.bits [] [] [] reversed []) := by
  have h := UnaryToBinaryMachine.convertTrace (K := Tape) (A := Bool)
    .input .binary .scratch (by decide) (by decide) (by decide)
    Label.convertBins (some .emitBins) code (fun _ => rfl)
    (tapes [] [] [] [] [] reversed []) fill n 0 word
  rw [actualStep] at h
  simpa [UnaryToBinaryMachine.tapes, cfg] using! h

theorem emitBinsTrace (fill : Bool) (n : Nat) (word reversed : List Bool) :
    (advance machine.step)^[n.bits.length + 1]
      (some (cfg (some .emitBins) fill word n.bits [] [] [] reversed [])) =
      some (cfg (some .seedIndex) fill word [] [] [] []
        ((natBits n).reverse ++ reversed) []) := by
  have h := FrameEmitMachine.trace (K := Tape) (A := Bool) .binary .reversed (by decide)
    .emitBins (some .seedIndex) code rfl (tapes word [] [] [] [] [] []) fill n.bits reversed
  rw [actualStep] at h
  simpa only [cfg, tapesAt, update_binary, update_reversed, natBits,
    BinPackingCompleteness.BinaryEncoding.nameBits] using! h

theorem seedIndexStep (fill : Bool) (word reversed : List Bool) :
    machine.step (cfg (some .seedIndex) fill word [] [] [] [] reversed []) =
      some (cfg (some .index) fill word [] [] [false] [] reversed []) := by
  change some (TM2.stepAux (code .seedIndex) _ _) = _
  simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem indexStep (fill bit : Bool) (word index reversed : List Bool) :
    machine.step (cfg (some .index) fill (bit :: word) [] [] index [] reversed []) =
      some (cfg (some (if bit then .index else .convertLabel .scan))
        fill word [] [] (if bit then true :: index else index) [] reversed []) := by
  change some (TM2.stepAux (code .index) _ _) = _
  cases bit <;> simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem indexTrace (fill : Bool) (n m : Nat) (word reversed : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some .index) fill (encodeWord n ++ word) [] []
        (encodeWord m) [] reversed [])) =
      some (cfg (some (.convertLabel .scan)) fill word [] []
        (encodeWord (m + n)) [] reversed []) := by
  induction n generalizing m with
  | zero =>
      simpa only [encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
        Nat.zero_add, Nat.add_zero, Function.iterate_one, advance_some,
        Bool.false_eq_true, ↓reduceIte] using
        indexStep fill false word (encodeWord m) reversed
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      simp only [encodeWord, List.replicate_succ, List.cons_append, advance_some]
      rw [indexStep fill true]
      simpa only [encodeWord, List.replicate_succ, List.cons_append,
        Bool.true_eq, ↓reduceIte, Nat.add_assoc, Nat.add_comm 1 n] using ih (m + 1)

theorem convertLabelTrace (fill : Bool) (n : Nat) (word index reversed : List Bool) :
    (advance machine.step)^[UnaryToBinaryMachine.steps n 0]
      (some (cfg (some (.convertLabel .scan)) fill (encodeWord n ++ word)
        [] [] index [] reversed [])) =
      some (cfg (some .emitLabel) fill word n.bits [] index [] reversed []) := by
  have h := UnaryToBinaryMachine.convertTrace (K := Tape) (A := Bool)
    .input .binary .scratch (by decide) (by decide) (by decide)
    Label.convertLabel (some .emitLabel) code (fun _ => rfl)
    (tapes [] [] [] index [] reversed []) fill n 0 word
  rw [actualStep] at h
  simpa [UnaryToBinaryMachine.tapes, cfg] using! h

theorem emitLabelTrace (fill : Bool) (n : Nat) (word index reversed : List Bool) :
    (advance machine.step)^[n.bits.length + 1]
      (some (cfg (some .emitLabel) fill word n.bits [] index [] reversed [])) =
      some (cfg (some .restoreLabel) fill word [] (natBits n).reverse index [] reversed []) := by
  have h := FrameEmitMachine.trace (K := Tape) (A := Bool) .binary .scratch (by decide)
    .emitLabel (some .restoreLabel) code rfl (tapes word [] [] index [] reversed []) fill n.bits []
  rw [actualStep] at h
  simpa only [cfg, tapesAt, update_binary, update_scratch, natBits,
    BinPackingCompleteness.BinaryEncoding.nameBits, List.append_nil] using! h

theorem restoreLabelTrace (fill : Bool) (n : Nat) (word index reversed : List Bool) :
    (advance machine.step)^[(natBits n).length + 1]
      (some (cfg (some .restoreLabel) fill word [] (natBits n).reverse index [] reversed [])) =
      some (cfg (some .items) fill word [] [] index (natBits n) reversed []) := by
  have h := transferAt_fromTapes (Γ := fun _ : Tape => Bool) .scratch .payload (by decide)
    id false .restoreLabel (some .items) code rfl
    (tapes word [] (natBits n).reverse index [] reversed []) fill none
  simpa only [cfg, transferNext, tapes_scratch, tapes_payload, tapesAt,
    update_scratch, update_payload, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, List.append_nil] using! h

theorem copyFlagStep (yes no current : Label) (h : code current = copyFlag yes no)
    (fill bit : Bool) (a index payload reversed : List Bool) :
    machine.step (cfg (some current) fill (bit :: a) [] [] index payload reversed []) =
      some (cfg (some (if bit then yes else no)) fill a [] [] index payload
        (bit :: reversed) []) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [h]
  cases bit <;> simp [copyFlag, go, TM2.stepAux, cfg]
  all_goals rfl

theorem copyDigitStep (next current : Label) (h : code current = copyDigit next)
    (fill bit : Bool) (a index payload reversed : List Bool) :
    machine.step (cfg (some current) fill (bit :: a) [] [] index payload reversed []) =
      some (cfg (some next) fill a [] [] index payload (bit :: reversed) []) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [h]
  simp [copyDigit, go, TM2.stepAux, cfg]
  all_goals rfl

theorem copyNameTrace (current digit next : Label)
    (hc : code current = copyFlag digit next) (hd : code digit = copyDigit current)
    (fill : Bool) (bits a index payload reversed : List Bool) :
    (advance machine.step)^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (cfg (some current) fill (BinPackingCompleteness.BinaryEncoding.frame bits ++ a)
        [] [] index payload reversed [])) =
      some (cfg (some next) fill a [] [] index payload
        ((BinPackingCompleteness.BinaryEncoding.frame bits).reverse ++ reversed) []) := by
  induction bits generalizing reversed with
  | nil =>
      simpa [BinPackingCompleteness.BinaryEncoding.frame, advance] using!
        copyFlagStep digit next current hc fill false a index payload reversed
  | cons bit bits ih =>
      have first := copyFlagStep digit next current hc fill true
        (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ a)) index payload reversed
      have second := copyDigitStep current digit hd fill bit
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ a) index payload (true :: reversed)
      simp only [↓reduceIte] at first
      have full := joinTrace (joinTrace
        (oneStepTrace first)
        (oneStepTrace second)) (ih (bit :: true :: reversed))
      have clock : 1 + 1 + (BinPackingCompleteness.BinaryEncoding.frame bits).length =
          (BinPackingCompleteness.BinaryEncoding.frame (bit :: bits)).length := by
        simp only [BinPackingCompleteness.BinaryEncoding.frame, List.length_cons]
        omega
      rw [clock] at full
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using full

theorem copyItemsTrace (fill : Bool) (r : RawInstance)
    (a index payload reversed : List Bool) :
    (advance machine.step)^[(rawInstanceBits r).length]
      (some (cfg (some .items) fill (rawInstanceBits r ++ a) [] [] index payload reversed [])) =
      some (cfg (some .dispatch) fill a [] [] index payload
        ((rawInstanceBits r).reverse ++ reversed) []) := by
  induction r generalizing reversed with
  | nil =>
      simpa [rawInstanceBits, listBits, advance] using!
        copyFlagStep .numerator .dispatch .items rfl fill false a index payload reversed
  | cons q r ih =>
      have first := copyFlagStep .numerator .dispatch .items rfl fill true
        (natBits q.1 ++ (natBits q.2 ++ (rawInstanceBits r ++ a))) index payload reversed
      have second := copyNameTrace .numerator .numeratorDigit .denominator rfl rfl fill q.1.bits
        (natBits q.2 ++ (rawInstanceBits r ++ a)) index payload (true :: reversed)
      have third := copyNameTrace .denominator .denominatorDigit .items rfl rfl fill q.2.bits
        (rawInstanceBits r ++ a) index payload ((natBits q.1).reverse ++ true :: reversed)
      simp only [↓reduceIte] at first
      have last := ih ((natBits q.2).reverse ++ ((natBits q.1).reverse ++ true :: reversed))
      simp only [natBits, BinPackingCompleteness.BinaryEncoding.nameBits] at first second third last
      have full := joinTrace (joinTrace (joinTrace
        (oneStepTrace first) second) third) last
      have clock : 1 + (BinPackingCompleteness.BinaryEncoding.frame q.1.bits).length +
          (BinPackingCompleteness.BinaryEncoding.frame q.2.bits).length +
          (rawInstanceBits r).length = (rawInstanceBits (q :: r)).length := by
        simp only [rawInstanceBits, listBits, pairBits, natBits,
          BinPackingCompleteness.BinaryEncoding.nameBits, List.length_cons, List.length_append]
        omega
      rw [clock] at full
      simpa only [rawInstanceBits, listBits, pairBits, natBits,
        BinPackingCompleteness.BinaryEncoding.nameBits, List.cons_append,
        List.reverse_cons, List.reverse_append, List.append_assoc,
        List.singleton_append, List.nil_append] using full

theorem dispatchStep (fill : Bool) (word index payload reversed : List Bool) :
    machine.step (cfg (some .dispatch) fill word [] [] index payload reversed []) =
      some (cfg (some (if fill then .replace (.entry true) else .fixed)) fill
        word [] [] index payload reversed []) := by
  change some (TM2.stepAux (code .dispatch) _ _) = _
  cases fill <;> simp [code, go, TM2.stepAux, cfg]
  all_goals rfl

theorem copyFixedTrace (word index payload reversed : List Bool) :
    (advance machine.step)^[word.length + 1]
      (some (cfg (some .fixed) false word [] [] index payload reversed [])) =
      some (cfg (some .reverse) false [] [] [] index payload (word.reverse ++ reversed) []) := by
  have h := transferAt_fromTapes (Γ := fun _ : Tape => Bool) .input .reversed (by decide)
    id false .fixed (some .reverse) code rfl
    (tapes word [] [] index payload reversed []) false none
  simpa only [cfg, transferNext, tapes_input, tapes_reversed, tapesAt,
    update_input, update_reversed, List.map_id_fun, id_eq] using! h

theorem replaceFixedTrace (fixed : List (Option Nat)) (index value : Nat)
    (reversed : List Bool) :
    (advance machine.step)^[(fixedBits fixed).length + (index + 1) + (natBits value).length]
      (some (cfg (some (.replace (.entry true))) true (fixedBits fixed) [] []
        (encodeWord index) (natBits value) reversed [])) =
      some (cfg (some .reverse) true [] [] [] [] []
        ((fixedBits (fixed.set index (some value))).reverse ++ reversed) []) := by
  have h := SearchFixedReplaceMachine.replaceTrace replacePlace replacePlace_injective
    Label.replace (some .reverse) code (fun _ => rfl)
    (tapes [] [] [] [] [] [] []) true fixed index value [] [] [] reversed
  rw [actualStep] at h
  simpa only [SearchFixedReplaceMachine.configuration, replaceTapes_eq,
    List.append_nil, cfg] using! h

theorem reverseTrace (fill : Bool) (word index payload reversed : List Bool) :
    (advance machine.step)^[reversed.length + 1]
      (some (cfg (some .reverse) fill word [] [] index payload reversed [])) =
      some (cfg none fill word [] [] index payload [] reversed.reverse) := by
  have h := transferAt_fromTapes (Γ := fun _ : Tape => Bool) .reversed .output (by decide)
    id false .reverse none code rfl (tapes word [] [] index payload reversed []) fill none
  simpa only [cfg, transferNext, tapes_reversed, tapes_output, tapesAt,
    update_reversed, update_output, List.map_id_fun, id_eq, List.append_nil] using! h

def bodyBits (s : State) : List Bool :=
  encodeWord s.bins ++ (encodeWord s.item ++ (encodeWord s.label ++
    (rawInstanceBits s.items ++ fixedBits s.fixed)))

def selectedFixed (fill : Bool) (s : State) : List (Option Nat) :=
  if fill then s.fixed.set s.item (some s.label) else s.fixed

def queryBits (fill : Bool) (s : State) : List Bool :=
  extensionBits s.bins s.items (selectedFixed fill s)

def prefixSteps (s : State) : Nat :=
  UnaryToBinaryMachine.steps s.bins 0 + (s.bins.bits.length + 1) + 1 +
    (s.item + 1) + UnaryToBinaryMachine.steps s.label 0 + (s.label.bits.length + 1) +
    ((natBits s.label).length + 1) + (rawInstanceBits s.items).length

theorem prefixTrace (fill : Bool) (s : State) (saved : List Bool) :
    (advance machine.step)^[prefixSteps s]
      (some (cfg (some (.convertBins .scan)) fill (bodyBits s) [] [] [] [] saved [])) =
      some (cfg (some .dispatch) fill (fixedBits s.fixed) [] []
        (encodeWord s.item) (natBits s.label)
        ((rawInstanceBits s.items).reverse ++ (natBits s.bins).reverse ++ saved) []) := by
  let rest := encodeWord s.item ++ (encodeWord s.label ++
    (rawInstanceBits s.items ++ fixedBits s.fixed))
  let tail := rawInstanceBits s.items ++ fixedBits s.fixed
  let header := (natBits s.bins).reverse ++ saved
  have first := convertBinsTrace fill s.bins rest saved
  have second := emitBinsTrace fill s.bins rest saved
  have third := seedIndexStep fill rest header
  have fourth := indexTrace fill s.item 0 (encodeWord s.label ++ tail) header
  simp only [Nat.zero_add, encodeWord, List.replicate_zero, List.nil_append] at fourth
  have fifth := convertLabelTrace fill s.label tail (encodeWord s.item) header
  have sixth := emitLabelTrace fill s.label tail (encodeWord s.item) header
  have seventh := restoreLabelTrace fill s.label tail (encodeWord s.item) header
  have eighth := copyItemsTrace fill s.items (fixedBits s.fixed)
    (encodeWord s.item) (natBits s.label) header
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace first second)
      (oneStepTrace third)) fourth) fifth) sixth) seventh) eighth
  simpa only [prefixSteps, bodyBits, rest, tail, header, List.append_assoc,
    Nat.add_assoc] using full

def suffixSteps (fill : Bool) (s : State) : Nat :=
  1 + if fill then (fixedBits s.fixed).length + (s.item + 1) + (natBits s.label).length
    else (fixedBits s.fixed).length + 1

theorem suffixTrace (fill : Bool) (s : State) (acc : List Bool) :
    (advance machine.step)^[suffixSteps fill s]
      (some (cfg (some .dispatch) fill (fixedBits s.fixed) [] []
        (encodeWord s.item) (natBits s.label) acc [])) =
      some (cfg (some .reverse) fill [] [] []
        (if fill then [] else encodeWord s.item) (if fill then [] else natBits s.label)
        ((fixedBits (selectedFixed fill s)).reverse ++ acc) []) := by
  cases fill with
  | false =>
      have first := dispatchStep false (fixedBits s.fixed)
        (encodeWord s.item) (natBits s.label) acc
      have second := copyFixedTrace (fixedBits s.fixed)
        (encodeWord s.item) (natBits s.label) acc
      simp only [Bool.false_eq_true, ↓reduceIte] at first
      have full := joinTrace (oneStepTrace first) second
      simpa only [suffixSteps, selectedFixed, Bool.false_eq_true, ↓reduceIte] using full
  | true =>
      have first := dispatchStep true (fixedBits s.fixed)
        (encodeWord s.item) (natBits s.label) acc
      have second := replaceFixedTrace s.fixed s.item s.label acc
      simp only [↓reduceIte] at first
      have full := joinTrace (oneStepTrace first) second
      simpa only [suffixSteps, selectedFixed, Bool.true_eq, ↓reduceIte] using full

def activeBits (fill : Bool) (s : State) : List Bool :=
  BinPackingCompleteness.BinaryEncoding.frame (stateBits s) ++ queryBits fill s

def activeSteps (fill : Bool) (s : State) : Nat :=
  prefixSteps s + suffixSteps fill s + (activeBits fill s).length + 1

theorem activeTrace (fill : Bool) (s : State) :
    (advance machine.step)^[activeSteps fill s]
      (some (cfg (some (.convertBins .scan)) fill (bodyBits s) [] [] [] []
        ((BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).reverse) [])) =
      some (cfg none fill [] [] []
        (if fill then [] else encodeWord s.item) (if fill then [] else natBits s.label)
        [] (activeBits fill s)) := by
  let saved := (BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).reverse
  let header := (rawInstanceBits s.items).reverse ++ (natBits s.bins).reverse ++ saved
  have first := prefixTrace fill s saved
  have second := suffixTrace fill s header
  have third := reverseTrace fill []
    (if fill then [] else encodeWord s.item) (if fill then [] else natBits s.label)
    ((fixedBits (selectedFixed fill s)).reverse ++ header)
  have full := joinTrace (joinTrace first second) third
  simpa only [activeSteps, activeBits, queryBits, extensionBits, fixedBits,
    saved, header, List.reverse_append, List.reverse_reverse, List.length_reverse,
    List.length_append, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using full

def initialSteps (s : State) : Nat := 2 * ((stateBits s).length + 1) + ((stateBits s).length + 1)

theorem initialTrace (s : State) :
    (advance machine.step)^[initialSteps s]
      (some (cfg (some .save) false (stateBits s) [] [] [] [] [] [])) =
      some (cfg (some .phase) false (stateBits s) [] [] [] []
        ((BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).reverse) []) :=
  joinTrace (saveTrace (stateBits s)) (frameSavedTrace (stateBits s))

theorem inactiveSteps_le (s : State) :
    initialSteps s + 1 + ((BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).length + 1) ≤
      rawTime.eval (stateBits s).length := by
  simp only [initialSteps, rawTime, BinPackingCompleteness.BinaryEncoding.frame_length,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  nlinarith [Nat.zero_le (stateBits s).length]

theorem init_eq (input : List Bool) :
    initList machine input = cfg (some .save) false input [] [] [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  cases k <;> rfl

def inactiveRun (bit : Bool) (s : State)
    (hphase : phaseBits s.phase = [true, bit]) (hquery : query s = []) :
    MachineCanonicalOutput.TerminalRun program (stateBits s)
      (MachineKeepDecision.typedInputBits stateBits (prepare s))
      (rawTime.eval (stateBits s).length) := by
  let saved := (BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).reverse
  have middle : (advance machine.step)^[1]
      (some (cfg (some .phase) false (stateBits s) [] [] [] [] saved [])) =
      some (cfg (some .reverse) false (bit :: bodyBits s) [] [] [] [] saved []) := by
    simpa only [stateBits, hphase, bodyBits, List.cons_append, List.nil_append,
      List.append_assoc, Function.iterate_one, advance_some] using
      phaseInactive bit (bodyBits s) saved
  have last := reverseTrace false (bit :: bodyBits s) [] [] saved
  simp only [saved, List.length_reverse, List.reverse_reverse] at last
  have full := joinTrace (joinTrace (initialTrace s) middle) last
  refine {
    state := (false, none)
    tapes := tapes (bit :: bodyBits s) [] [] [] [] []
      (BinPackingCompleteness.BinaryEncoding.frame (stateBits s))
    execution := {
      steps := initialSteps s + 1 +
        ((BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).length + 1)
      evals_in_steps := ?_
      steps_le_m := inactiveSteps_le s }
    output_eq := ?_ }
  · change (advance machine.step)^[initialSteps s + 1 +
        ((BinPackingCompleteness.BinaryEncoding.frame (stateBits s)).length + 1)]
      (some (initList machine (stateBits s))) =
        some (cfg none false (bit :: bodyBits s) [] [] [] [] []
          (BinPackingCompleteness.BinaryEncoding.frame (stateBits s)))
    simpa only [init_eq] using full
  · change BinPackingCompleteness.BinaryEncoding.frame (stateBits s) =
      MachineKeepDecision.typedInputBits stateBits (prepare s)
    simp only [MachineKeepDecision.typedInputBits,
      MachineKeepDecision.inputBits, prepare, hquery, savedFrame_eq, List.append_nil]

theorem cleanup_complete (k : Tape) : k ∈ cleanupTapes ↔ k ≠ program.output := by
  cases k <;> simp [cleanupTapes, program]

end BinPackingGap.SearchPrepareMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchUpdateMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchUpdateMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open SearchSemantics SearchEncoding BinaryEncoding

def countedPhase (counter : List Bool × Bool) : Phase :=
  if !counter.2 && !(counter.1.head?.getD false) then .done else .fill

theorem countedPhase_counterAfter (m n : Nat) :
    countedPhase (counterAfter m (encodeWord n, false)) =
      if m = n then .done else .fill := by
  induction m generalizing n with
  | zero => cases n <;> simp [counterAfter, countedPhase, encodeWord, List.replicate_succ]
  | succ m ih =>
      cases n with
      | zero => simp [counterAfter, decrement, encodeWord, countedPhase]
      | succ n => simpa [counterAfter, decrement, encodeWord, List.replicate_succ] using ih n

end BinPackingGap.SearchUpdateMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchStageMachines
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
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
open SearchInitializeEncoding

def code : Label → TM2.Stmt Alphabet Label Register
  | .start =>
      .pop 0 (fun _ bit => clean (bit.getD false, false))
        (.push 1 (fun _ => false)
          (.push 2 (fun _ => false)
            (.push 3 (fun _ => false)
              (.push 5 (fun _ => false) (.goto fun _ => .count)))))
  | .count =>
      .pop 0 (fun state bit => (state.1, bit))
        (.branch (fun state => state.2.getD false)
          (.push 2 (fun _ => true)
            (.push 3 (fun _ => true)
              (.push 5 (fun _ => true)
                (.load (fun state => clean (state.1.1.1, true))
                  (.goto fun _ => .count)))))
          (.push 3 (fun _ => true)
            (.load (fun state => clean state.1.1)
              (.goto fun state => dispatch state.1.1.1))))
  | .fixed =>
      .pop 5 (fun state bit => (state.1, bit))
        (.branch (fun state => state.2.getD false)
          (.push 1 (fun _ => false)
            (.push 1 (fun _ => true)
              (.load (fun state => clean state.1.1) (.goto fun _ => .fixed))))
          (.load (fun state => clean state.1.1) (.goto fun _ => .reverseRaw)))
  | .reverseRaw => loopAt 0 4 id false .reverseRaw (some .prependRaw)
  | .prependRaw => loopAt 4 1 id false .prependRaw (some .pushHeader)
  | .pushHeader =>
      .branch (fun state => state.1.1.1)
        (.branch (fun state => state.1.1.2)
          (pushWord 1 (header (true, true)).reverse
            (.goto fun _ => .multiply .copyDrain))
          (pushWord 1 (header (true, false)).reverse
            (.goto fun _ => .multiply .copyDrain)))
        (pushWord 1 (header (false, false)).reverse (.goto fun _ => .zeroFuel))
  | .zeroFuel => .push 1 (fun _ => false) .halt
  | .multiply phase => MachineUnaryMultiply.statement mulSlots Label.multiply none phase

def program : MachineCanonicalOutput.Program Tape Label Register where
  input := 0
  output := 1
  main := .start
  initial := clean (false, false)
  code := code

abbrev machine := MachineCanonicalOutput.sourceMachine program

def cfg (label : Option Label) (flags : Flags)
    (input output left right scratch fixed counter : List Bool) : machine.Cfg :=
  ⟨label, clean flags, tapes input output left right scratch fixed counter⟩

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
  steps_le_m := run.steps_le_m.trans bounded

def prependRawInTime (flags : Flags) (input output left right fixed : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .reverseRaw) flags input output left right [] fixed [])
      (some (cfg (some .pushHeader) flags [] (input ++ output) left right [] fixed []))
      (2 * (input.length + 1)) := by
  have first := transferAtInTime (0 : Tape) 4 (by decide) id false
    .reverseRaw (some .prependRaw) code rfl
    (tapes input output left right [] fixed []) (flags, ()) none
  have second := transferAtInTime (4 : Tape) 1 (by decide) id false
    .prependRaw (some .pushHeader) code rfl
    (tapes [] output left right input.reverse fixed []) (flags, ()) none
  have first' : StateTransition.EvalsToInTime machine.step
      (cfg (some .reverseRaw) flags input output left right [] fixed [])
      (some (cfg (some .prependRaw) flags [] output left right input.reverse fixed []))
      (input.length + 1) := by
    change StateTransition.EvalsToInTime (TM2.step code)
      ⟨some .reverseRaw, clean flags, tapes input output left right [] fixed []⟩
      (some ⟨some .prependRaw, clean flags, tapes [] output left right input.reverse fixed []⟩)
      (input.length + 1)
    simpa only [tapesAt, update_input, update_scratch, tapes_input, tapes_scratch,
      List.map_id_fun, id_eq, List.append_nil, cfg, clean] using first
  have second' : StateTransition.EvalsToInTime machine.step
      (cfg (some .prependRaw) flags [] output left right input.reverse fixed [])
      (some (cfg (some .pushHeader) flags [] (input ++ output) left right [] fixed []))
      (input.length + 1) := by
    change StateTransition.EvalsToInTime (TM2.step code)
      ⟨some .prependRaw, clean flags, tapes [] output left right input.reverse fixed []⟩
      (some ⟨some .pushHeader, clean flags, tapes [] (input ++ output) left right [] fixed []⟩)
      (input.length + 1)
    simpa only [tapesAt, update_scratch, update_output, tapes_scratch, tapes_output,
      List.map_id_fun, id_eq, List.reverse_reverse, List.length_reverse, cfg, clean] using second
  exact enlarge (join first' second') (by omega)

theorem init_eq (input : List Bool) :
    initList machine input = cfg (some .start) (false, false) input [] [] [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  change Tape at k
  fin_cases k <;> rfl

end BinPackingGap.SearchInitialEmitMachine

namespace BinPackingGap.SearchInitializeMachine

open Turing BinPackingGames.Foundations.Complexity
open SearchInitializeEncoding

noncomputable def shapeComputation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) shapeBits
      (id : List Bool → List Bool) where
  tm := SearchInitialShapeMachine.machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun input := by
    change TM2OutputsInTime SearchInitialShapeMachine.machine (input.map id)
      (some ((shapeBits input).map id))
      ((2 * Polynomial.X + 3 : Polynomial Nat).eval input.length)
    simpa only [List.map_id_fun, id_eq, shapeBits, SearchInitialShapeMachine.decodeAccepts,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
      using SearchInitialShapeMachine.outputsInTime input

theorem shapeFinite : MachineFiniteAlphabet.FiniteAlphabet shapeComputation.tm :=
  SearchInitialShapeMachine.machine_finiteAlphabet

end BinPackingGap.SearchInitializeMachine

end OAI
end


