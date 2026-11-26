-- Prove2me | Definitions.Def_CARDB
-- name    : CARDB
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:43:28.851807+00:00
-- url     : https://prove2.me/theorems/385fcde6-f283-5822-8af2-da19755fe65c
-- title:
--   CARDB
-- statement:
--   Definitions and structural lemmas for CARDB, from Lars Warren Ericson (catskillsresearch/cardb; see pinned Apache-2.0 LICENSE and NOTICE)'s pinned CARDB: The number of distinct topological bases of a finite set development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/cardb/blob/d8c1d63052a18db0c43d44c1c77fb10ca8902ed0/CARDB.lean

import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Sum
set_option autoImplicit true
open Set TopologicalSpace
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]
def IsBasis (B : Set (Set α)) : Prop :=
  (⋃₀ B = univ) ∧
  ∀ ⦃U V⦄, U ∈ B → V ∈ B → ∀ x ∈ U ∩ V, ∃ W ∈ B, x ∈ W ∧ W ⊆ U ∩ V
def ValidBasis (α : Type*) [Fintype α] := { B : Set (Set α) // IsBasis B }
def opensOf (t : TopologicalSpace α) : Set (Set α) := {U | t.IsOpen U}
omit [Fintype α] [DecidableEq α] in
theorem opensOf_injective :
    Function.Injective (opensOf : TopologicalSpace α → Set (Set α)) :=
  leftInverse_generateFrom.injective
noncomputable instance instDecidableEqTopologicalSpace : DecidableEq (TopologicalSpace α) :=
  opensOf_injective.decidableEq
noncomputable instance instFintypeTopologicalSpace : Fintype (TopologicalSpace α) :=
  Fintype.ofInjective opensOf opensOf_injective
noncomputable instance instDecidablePredIsBasis : DecidablePred (IsBasis : Set (Set α) → Prop) :=
  fun _ => Classical.dec _
noncomputable instance instFintypeValidBasis : Fintype (ValidBasis α) :=
  Subtype.fintype _
variable (t : TopologicalSpace α)
abbrev Fiber (t : TopologicalSpace α) :=
  { B : ValidBasis α // generateFrom B.1 = t }
abbrev minimalOpen (x : α) : Set α :=
  @nhdsKer α t {x}
def minimalBasis : Set (Set α) :=
  range (minimalOpen t)
omit [Fintype α] [DecidableEq α] in
theorem mem_minimalOpen_self (x : α) : x ∈ minimalOpen t x :=
  @subset_nhdsKer α t {x} x (mem_singleton x)
omit [Fintype α] [DecidableEq α] in
theorem minimalOpen_subset_of_isOpen {x : α} {U : Set α}
    (hU : t.IsOpen U) (hx : x ∈ U) : minimalOpen t x ⊆ U :=
  @nhdsKer_minimal α t {x} U (singleton_subset_iff.mpr hx) hU
omit [DecidableEq α] in
/-- Finite spaces are Alexandrov-discrete, so `nhdsKer {x}` is open. -/
theorem isOpen_minimalOpen (x : α) : t.IsOpen (minimalOpen t x) :=
  letI := t
  isOpen_nhdsKer
omit [DecidableEq α] in
/-- The minimal basis alone generates the topology `t`. -/
theorem generateFrom_minimalBasis : generateFrom (minimalBasis t) = t := by
  ext U
  constructor
  · intro h
    letI := t
    induction h with
    | basic s hs =>
      obtain ⟨x, rfl⟩ := hs
      exact isOpen_minimalOpen t x
    | univ => exact isOpen_univ
    | inter _ _ _ _ hs ht => exact hs.inter ht
    | sUnion S _ hS => exact isOpen_sUnion fun s hs => hS s hs
  · intro hU
    have : U = ⋃₀ (minimalOpen t '' U) := by
      ext y
      constructor
      · intro hy
        exact ⟨minimalOpen t y, ⟨y, hy, rfl⟩, mem_minimalOpen_self t y⟩
      · rintro ⟨_, ⟨x, hx, rfl⟩, hy⟩
        exact minimalOpen_subset_of_isOpen t hU hx hy
    rw [this]
    exact GenerateOpen.sUnion _ fun V hV =>
      let ⟨x, _, hx⟩ := hV
      hx ▸ GenerateOpen.basic _ (mem_range_self x)
omit [Fintype α] [DecidableEq α] in
/-- `IsBasis` plus `generateFrom B = t` is Mathlib's `IsTopologicalBasis`. -/
theorem isTopologicalBasis_generateFrom {B : Set (Set α)} (hB : IsBasis B) :
    @IsTopologicalBasis α (generateFrom B) B := by
  letI := generateFrom B
  refine ⟨?_, hB.1, rfl⟩
  intro t₁ ht₁ t₂ ht₂ x hx
  exact hB.2 ht₁ ht₂ x hx
omit [DecidableEq α] in
/-- Core lemma: `B` generates `t` iff `B` contains the minimal basis
    and only contains open sets of `t`. -/
theorem isBasis_and_generates_iff (B : Set (Set α)) :
    (IsBasis B ∧ generateFrom B = t) ↔
    (minimalBasis t ⊆ B ∧ B ⊆ {U | t.IsOpen U}) := by
  constructor
  · rintro ⟨hB, rfl⟩
    constructor
    · rintro _ ⟨x, rfl⟩
      letI := generateFrom B
      have hb : IsTopologicalBasis B := isTopologicalBasis_generateFrom hB
      have hx : x ∈ minimalOpen (generateFrom B) x := mem_minimalOpen_self _ x
      have hUo : IsOpen (minimalOpen (generateFrom B) x) := isOpen_minimalOpen _ x
      obtain ⟨W, hW, hxW, hWU⟩ := hb.exists_subset_of_mem_open hx hUo
      have hUW : minimalOpen (generateFrom B) x ⊆ W :=
        minimalOpen_subset_of_isOpen _ (isOpen_generateFrom_of_mem hW) hxW
      rwa [← Subset.antisymm hWU hUW]
    · intro U hU
      exact isOpen_generateFrom_of_mem hU
  · rintro ⟨h_min, h_sub⟩
    constructor
    · constructor
      · ext x
        simp only [mem_sUnion, mem_univ, iff_true]
        exact ⟨minimalOpen t x, h_min ⟨x, rfl⟩, mem_minimalOpen_self t x⟩
      · intro U V hU hV x hx
        refine ⟨minimalOpen t x, h_min ⟨x, rfl⟩, mem_minimalOpen_self t x, ?_⟩
        intro y hy
        exact ⟨minimalOpen_subset_of_isOpen t (h_sub hU) hx.1 hy,
          minimalOpen_subset_of_isOpen t (h_sub hV) hx.2 hy⟩
    · refine le_antisymm ?_ ?_
      · exact generateFrom_anti h_min |>.trans (generateFrom_minimalBasis t).le
      · exact le_generateFrom_iff_subset_isOpen.2 h_sub
def fiberEquiv (t : TopologicalSpace α) :
    Fiber t ≃
      Set { U : Set α // t.IsOpen U ∧ U ∉ minimalBasis t } where
  toFun B := { U | U.1 ∈ B.1.1 }
  invFun S :=
    let Bset : Set (Set α) := minimalBasis t ∪ (Subtype.val '' S)
    have h : IsBasis Bset ∧ generateFrom Bset = t :=
      (isBasis_and_generates_iff t Bset).2 ⟨subset_union_left, by
        intro U hU
        rcases hU with hM | hS
        · obtain ⟨x, rfl⟩ := hM
          exact isOpen_minimalOpen t x
        · obtain ⟨U', _, rfl⟩ := hS
          exact U'.2.1⟩
    ⟨⟨Bset, h.1⟩, h.2⟩
  left_inv B := by
    have hiff := (isBasis_and_generates_iff t B.1.1).1 ⟨B.1.2, B.2⟩
    refine Subtype.ext (Subtype.ext ?_)
    ext U
    constructor
    · rintro (hM | ⟨U', hU', rfl⟩)
      · exact hiff.1 hM
      · exact hU'
    · intro hU
      by_cases hM : U ∈ minimalBasis t
      · exact Or.inl hM
      · exact Or.inr ⟨⟨U, hiff.2 hU, hM⟩, hU, rfl⟩
  right_inv S := by
    ext U
    constructor
    · intro h
      rcases h with hM | ⟨U', hU', hEq⟩
      · exact (U.2.2 hM).elim
      · exact (Subtype.ext hEq : U' = U) ▸ hU'
    · intro hU
      exact Or.inr ⟨U, hU, rfl⟩


