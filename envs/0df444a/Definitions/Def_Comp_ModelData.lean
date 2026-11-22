-- Prove2me | Definitions.Def_Comp_ModelData
-- name    : Comp_ModelData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:35:23.833067+00:00
-- url     : https://prove2.me/theorems/60523077-0bcd-42b0-ae16-1fb714b4bbdc
-- title:
--   Model Data
-- statement:
--   Definitions and structural lemmas for Model Data, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean

import Definitions.Def_Comp_Objective
import Theorems.Thm_Comp_CsgQ_castIcc_coe
import Theorems.Thm_Comp_CsgQ_coe_supportF
import Theorems.Thm_Comp_CsgQ_mem_aF
import Theorems.Thm_Comp_CsgQ_mem_apre1F
import Theorems.Thm_Comp_CsgQ_mem_bF
import Theorems.Thm_Comp_CsgQ_mem_gStepF
import Theorems.Thm_Comp_CsgQ_mem_lpre1F
import Theorems.Thm_Comp_CsgQ_mem_pre1F
import Theorems.Thm_Comp_CsgQ_mem_supportF
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.CsgQ.castIcc_coe
attribute [local simp] Comp.CsgQ.coe_supportF
attribute [local simp] Comp.CsgQ.mem_aF
attribute [local simp] Comp.CsgQ.mem_apre1F
attribute [local simp] Comp.CsgQ.mem_bF
attribute [local simp] Comp.CsgQ.mem_gStepF
attribute [local simp] Comp.CsgQ.mem_lpre1F
attribute [local simp] Comp.CsgQ.mem_pre1F
attribute [local simp] Comp.CsgQ.mem_supportF
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A


set_option autoImplicit true
namespace Comp
def denseOf (n : ℕ) : List (ℕ × ℚ) → Fin n → ℚ
  | [], _ => 0
  | (t, q) :: rest, s' => (if (s' : ℕ) = t then q else 0) + denseOf n rest s'
def keysNat (dist : List (ℕ × ℚ)) : Finset ℕ :=
  (dist.map Prod.fst).toFinset
@[simp]
theorem mem_keysNat (dist : List (ℕ × ℚ)) (m : ℕ) :
    m ∈ keysNat dist ↔ ∃ p ∈ dist, p.1 = m := by
  simp only [keysNat, List.mem_toFinset, List.mem_map]
theorem keysNat_lt {n : ℕ} (dist : List (ℕ × ℚ)) (h : ∀ p ∈ dist, p.1 < n) :
    ∀ m ∈ keysNat dist, m < n := by
  intro m hm
  rw [mem_keysNat] at hm
  obtain ⟨p, hp, rfl⟩ := hm
  exact h p hp
structure Transition where
  /-- The row player's action, as a global index. -/
  act1 : ℕ
  /-- The column player's action, as a global index. -/
  act2 : ℕ
  /-- Successors with their weights. Only the ones that occur. -/
  dist : List (ℕ × ℚ)
  /-- Reward for taking this joint action in this state. -/
  rew : ℚ
instance : Inhabited Transition := ⟨⟨0, 0, [], 0⟩⟩
structure StateEntry where
  /-- Reward for being in this state. -/
  rew : ℚ
  /-- The transitions available here, each carrying its joint action. -/
  trans : List Transition
instance : Inhabited StateEntry := ⟨⟨0, []⟩⟩
structure ModelData where
  /-- Size of the row player's global action namespace. -/
  nAct1 : ℕ
  /-- Size of the column player's global action namespace. -/
  nAct2 : ℕ
  /-- The states, in index order. -/
  states : List StateEntry
def ModelData.nStates (d : ModelData) : ℕ := d.states.length
def ModelData.stateAt (d : ModelData) (s : ℕ) : StateEntry := d.states.getD s default
def ModelData.transOf (d : ModelData) (s : ℕ) : List Transition :=
  match (d.stateAt s).trans with
  | [] => [{ act1 := 0, act2 := 0, dist := [(s, 1)], rew := 0 }]
  | t :: ts => t :: ts
theorem ModelData.transOf_ne_nil (d : ModelData) (s : ℕ) : d.transOf s ≠ [] := by
  unfold ModelData.transOf
  split <;> simp
theorem ModelData.headD_mem (d : ModelData) (s : ℕ) :
    (d.transOf s).headD default ∈ d.transOf s := by
  cases h : d.transOf s with
  | nil => exact absurd h (d.transOf_ne_nil s)
  | cons u rest => simp
def ModelData.keys1 (d : ModelData) (s : ℕ) : Finset ℕ :=
  ((d.transOf s).map Transition.act1).toFinset
def ModelData.keys2 (d : ModelData) (s : ℕ) : Finset ℕ :=
  ((d.transOf s).map Transition.act2).toFinset
@[simp]
theorem ModelData.mem_keys1 (d : ModelData) (s m : ℕ) :
    m ∈ d.keys1 s ↔ ∃ t ∈ d.transOf s, t.act1 = m := by
  simp only [ModelData.keys1, List.mem_toFinset, List.mem_map]
@[simp]
theorem ModelData.mem_keys2 (d : ModelData) (s m : ℕ) :
    m ∈ d.keys2 s ↔ ∃ t ∈ d.transOf s, t.act2 = m := by
  simp only [ModelData.keys2, List.mem_toFinset, List.mem_map]
def ModelData.pad1 (d : ModelData) (s a1 : ℕ) : ℕ :=
  if a1 ∈ d.keys1 s then a1 else ((d.transOf s).headD default).act1
def ModelData.pad2 (d : ModelData) (s a2 : ℕ) : ℕ :=
  if a2 ∈ d.keys2 s then a2 else ((d.transOf s).headD default).act2
def ModelData.transAt (d : ModelData) (s a1 a2 : ℕ) : Transition :=
  ((d.transOf s).find? fun t => t.act1 == d.pad1 s a1 && t.act2 == d.pad2 s a2).getD default
theorem ModelData.pad1_mem_keys1 (d : ModelData) (s a1 : ℕ) : d.pad1 s a1 ∈ d.keys1 s := by
  unfold ModelData.pad1
  split_ifs with hmem
  · exact hmem
  · rw [ModelData.mem_keys1]
    exact ⟨(d.transOf s).headD default, d.headD_mem s, rfl⟩
theorem ModelData.pad2_mem_keys2 (d : ModelData) (s a2 : ℕ) : d.pad2 s a2 ∈ d.keys2 s := by
  unfold ModelData.pad2
  split_ifs with hmem
  · exact hmem
  · rw [ModelData.mem_keys2]
    exact ⟨(d.transOf s).headD default, d.headD_mem s, rfl⟩
def ModelData.ActInRange (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ t ∈ d.transOf s, t.act1 < d.nAct1 ∧ t.act2 < d.nAct2
instance (d : ModelData) : Decidable d.ActInRange := by
  unfold ModelData.ActInRange; infer_instance
def ModelData.InRange (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ t ∈ d.transOf s, ∀ p ∈ t.dist, p.1 < d.nStates
instance (d : ModelData) : Decidable d.InRange := by
  unfold ModelData.InRange; infer_instance
def ModelData.Functional (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ((d.transOf s).map fun t => (t.act1, t.act2)).Nodup
instance (d : ModelData) : Decidable d.Functional := by
  unfold ModelData.Functional; infer_instance
def ModelData.Total (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ a1 ∈ d.keys1 s, ∀ a2 ∈ d.keys2 s,
    ∃ t ∈ d.transOf s, t.act1 = a1 ∧ t.act2 = a2
instance (d : ModelData) : Decidable d.Total := by
  unfold ModelData.Total; infer_instance
def ModelData.Shape (d : ModelData) : Prop :=
  d.ActInRange ∧ d.InRange ∧ d.Functional ∧ d.Total
instance (d : ModelData) : Decidable d.Shape := by
  unfold ModelData.Shape; infer_instance
theorem ModelData.Shape.actInRange {d : ModelData} (hs : d.Shape) : d.ActInRange := hs.1
theorem ModelData.Shape.inRange {d : ModelData} (hs : d.Shape) : d.InRange := hs.2.1
theorem ModelData.Shape.total {d : ModelData} (hs : d.Shape) : d.Total := hs.2.2.2
def ModelData.Nonneg (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ t ∈ d.transOf s, ∀ p ∈ t.dist, 0 ≤ p.2
instance (d : ModelData) : Decidable d.Nonneg := by
  unfold ModelData.Nonneg; infer_instance
def ModelData.Nonzero (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ t ∈ d.transOf s, ∀ p ∈ t.dist, p.2 ≠ 0
instance (d : ModelData) : Decidable d.Nonzero := by
  unfold ModelData.Nonzero; infer_instance
def ModelData.Stochastic (d : ModelData) : Prop :=
  ∀ s : Fin d.nStates, ∀ t ∈ d.transOf s,
    (∀ p ∈ t.dist, 0 ≤ p.2) ∧ (t.dist.map Prod.snd).sum = 1
instance (d : ModelData) : Decidable d.Stochastic := by
  unfold ModelData.Stochastic; infer_instance
theorem ModelData.transAt_mem (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a1 a2 : ℕ) :
    d.transAt s a1 a2 ∈ d.transOf s := by
  obtain ⟨t, ht, h1, h2⟩ := hs.total s _ (d.pad1_mem_keys1 s a1) _ (d.pad2_mem_keys2 s a2)
  have hne : ((d.transOf s).find? fun u =>
      u.act1 == d.pad1 s a1 && u.act2 == d.pad2 s a2) ≠ none := by
    intro hnone
    have hcontra := List.find?_eq_none.mp hnone t ht
    simp only [h1, h2, beq_self_eq_true, Bool.and_self] at hcontra
    exact hcontra trivial
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hne
  unfold ModelData.transAt
  rw [hu]
  exact List.mem_of_find?_eq_some hu
theorem ModelData.inRange_transAt (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a1 a2 : ℕ) :
    ∀ p ∈ (d.transAt s a1 a2).dist, p.1 < d.nStates :=
  hs.inRange s _ (d.transAt_mem hs s a1 a2)
theorem ModelData.keys1_lt (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    ∀ m ∈ d.keys1 s, m < d.nAct1 := by
  intro m hm
  rw [ModelData.mem_keys1] at hm
  obtain ⟨t, ht, rfl⟩ := hm
  exact (hs.actInRange s t ht).1
theorem ModelData.keys2_lt (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    ∀ m ∈ d.keys2 s, m < d.nAct2 := by
  intro m hm
  rw [ModelData.mem_keys2] at hm
  obtain ⟨t, ht, rfl⟩ := hm
  exact (hs.actInRange s t ht).2
def ModelData.enabled1 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    Finset (Fin d.nAct1) :=
  Finset.attachFin (d.keys1 s) (d.keys1_lt hs s)
def ModelData.enabled2 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) :
    Finset (Fin d.nAct2) :=
  Finset.attachFin (d.keys2 s) (d.keys2_lt hs s)
def ModelData.padFin1 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a1 : Fin d.nAct1) :
    Fin d.nAct1 :=
  ⟨d.pad1 s a1, d.keys1_lt hs s _ (d.pad1_mem_keys1 s a1)⟩
def ModelData.padFin2 (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a2 : Fin d.nAct2) :
    Fin d.nAct2 :=
  ⟨d.pad2 s a2, d.keys2_lt hs s _ (d.pad2_mem_keys2 s a2)⟩
def ModelData.toCsgQ (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2] :
    CsgQ (Fin d.nStates) (Fin d.nAct1) (Fin d.nAct2) where
  K s a1 a2 := denseOf d.nStates (d.transAt s a1 a2).dist
  r s a1 a2 := (d.stateAt s).rew + (d.transAt s a1 a2).rew
def ModelData.supportOf (d : ModelData) (hs : d.Shape) (s : Fin d.nStates) (a1 : Fin d.nAct1)
    (a2 : Fin d.nAct2) : Finset (Fin d.nStates) :=
  Finset.attachFin (keysNat (d.transAt s a1 a2).dist)
    (keysNat_lt _ (d.inRange_transAt hs s a1 a2))
end Comp


