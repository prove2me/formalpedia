-- Prove2me | Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
-- name    : AutomataTheory_Mathlib_InfGraphRamsey
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T04:08:20.894427+00:00
-- url     : https://prove2.me/theorems/8df3c8a4-116a-4c0c-9a6e-324aacb6ddfe
-- title:
--   Inf Graph Ramsey
-- statement:
--   Definitions and structural lemmas for Inf Graph Ramsey, from Ching-Tsun Chou's pinned Omega-regular languages and deterministic Muller automata development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Mathlib/InfGraphRamsey.lean

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
set_option autoImplicit true
open Function Set
section InfGraphRamsey
open Classical
lemma AutomataTheory.Compatibility.pigeonhole_principle {X Y : Type*} [Finite Y] (f : X → Y) {s : Set X} (h_inf : s.Infinite) :
    ∃ y, ∃ t, t.Infinite ∧ t ⊆ s ∧ ∀ x ∈ t, f x = y := by
  have := h_inf.to_subtype
  obtain ⟨y, h_inf'⟩ := Finite.exists_infinite_fiber (s.restrict f)
  have h_inf_iff := Equiv.infinite_iff <| Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (fun x ↦ f x = y)
  have h_inf' := h_inf_iff.mp h_inf'
  have h_inf'' := (infinite_coe_iff (s := { x | x ∈ s ∧ f x = y })).mp h_inf'
  use y, {x | x ∈ s ∧ f x = y}
  simpa
variable {Color Vertex : Type*} [Finite Color]
abbrev Edge := Finset Vertex
variable (color : (e : Edge) → Color)
structure InfVSet (Vertex : Type*) where
  set : Set Vertex
  inf : set.Infinite
structure Selection (Color Vertex : Type*) where
  vs : InfVSet Vertex
  v : Vertex
  c : Color
def selection_prop (ivs : InfVSet Vertex) (S : Selection Color Vertex) : Prop :=
  S.vs.set ⊆ ivs.set ∧ S.v ∈ ivs.set \ S.vs.set ∧ ∀ u ∈ S.vs.set, color {S.v, u} = S.c
lemma selection_exists (ivs : InfVSet Vertex) :
    ∃ S : Selection Color Vertex, selection_prop color ivs S := by
  obtain ⟨v, h_v⟩ := Set.Infinite.nonempty ivs.inf
  let f u := color {v, u}
  obtain ⟨c, vs, h_inf, h_vs, h_col⟩ := AutomataTheory.Compatibility.pigeonhole_principle f <| Set.Infinite.diff ivs.inf (finite_singleton v)
  simp [subset_diff] at h_vs
  obtain ⟨h_vs, h_v'⟩ := h_vs
  let ivs' := InfVSet.mk vs h_inf
  use {vs := ivs', v := v, c := c}
  simp [selection_prop, ivs', h_vs, h_v, h_v']
  exact h_col
variable [Infinite Vertex]
noncomputable def selection_seq : ℕ → Selection Color Vertex
  | 0 => choose (selection_exists color (InfVSet.mk univ infinite_univ))
  | n + 1 => choose (selection_exists color (selection_seq n).vs)
end InfGraphRamsey


