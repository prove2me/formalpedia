-- Prove2me | solution 1 for AssumptionsOfPhysics.possibility_card_le_continuum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:03:16.754576+00:00
-- url     : https://prove2.me/submissions/f5de4b87-d9e3-475d-8991-1ee019b12d26

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

universe u

namespace P94188469

open AssumptionsOfPhysics

theorem fcd_mem {Ω : Type u} (D : ExperimentalDomain Ω) {B : Set (Set Ω)}
    (hB : B ⊆ D.stmts) {s : Set Ω} (h : FinConjCountDisj B s) : s ∈ D.stmts := by
  induction h with
  | basic hs => exact hB hs
  | univ => exact D.univ_mem
  | empty => exact D.empty_mem
  | inter _ _ ihs iht => exact D.inter_mem _ _ ihs iht
  | iUnion f _ ih => exact D.iUnion_mem f ih

theorem stmts_theo {Ω : Type u} (D : ExperimentalDomain Ω) {s : Set Ω}
    (hs : s ∈ D.stmts) : s ∈ D.theoretical :=
  NegFinConjCountDisj.basic hs

/-- For a possibility, being contained in a theoretical statement is the same as meeting it. -/
theorem sub_iff {Ω : Type u} (D : ExperimentalDomain Ω) {x : Set Ω}
    (hx : D.IsPossibility x) {s : Set Ω} (hs : s ∈ D.theoretical) :
    x ⊆ s ↔ (x ∩ s).Nonempty := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := hx.2.1
    exact ⟨a, ha, h ha⟩
  · intro h
    rcases hx.2.2 s hs with h1 | h1
    · exact h1
    · exact absurd h (Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp h1))

theorem sub_compl_iff {Ω : Type u} (D : ExperimentalDomain Ω) {x : Set Ω}
    (hx : D.IsPossibility x) {s : Set Ω} (hs : s ∈ D.theoretical) :
    x ⊆ sᶜ ↔ ¬ x ⊆ s := by
  rw [sub_iff D hx hs]
  constructor
  · rintro h ⟨a, hax, has⟩
    exact h hax has
  · intro h a ha has
    exact h ⟨a, ha, has⟩

theorem sub_iUnion_iff {Ω : Type u} (D : ExperimentalDomain Ω) {x : Set Ω}
    (hx : D.IsPossibility x) (f : ℕ → Set Ω) (hf : ∀ n, f n ∈ D.theoretical)
    (hU : (⋃ n, f n) ∈ D.theoretical) :
    x ⊆ (⋃ n, f n) ↔ ∃ n, x ⊆ f n := by
  rw [sub_iff D hx hU]
  constructor
  · rintro ⟨a, hax, haU⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp haU
    exact ⟨n, (sub_iff D hx (hf n)).mpr ⟨a, hax, hn⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨a, ha⟩ := hx.2.1
    exact ⟨a, ha, Set.mem_iUnion.mpr ⟨n, hn ha⟩⟩

theorem agree_fcd {Ω : Type u} (D : ExperimentalDomain Ω) {B : Set (Set Ω)}
    (hB : B ⊆ D.stmts) {x y : Set Ω} (hx : D.IsPossibility x) (hy : D.IsPossibility y)
    (hxy : ∀ b ∈ B, (x ⊆ b ↔ y ⊆ b)) {s : Set Ω} (h : FinConjCountDisj B s) :
    (x ⊆ s ↔ y ⊆ s) := by
  induction h with
  | basic hs => exact hxy _ hs
  | univ => simp
  | empty =>
    constructor
    · intro h; exact absurd (Set.subset_empty_iff.mp h) hx.2.1.ne_empty
    · intro h; exact absurd (Set.subset_empty_iff.mp h) hy.2.1.ne_empty
  | inter _ _ ihs iht =>
    simp only [Set.subset_inter_iff]
    rw [ihs, iht]
  | iUnion f hf ih =>
    have hft : ∀ n, f n ∈ D.theoretical := fun n => stmts_theo D (fcd_mem D hB (hf n))
    have hU : (⋃ n, f n) ∈ D.theoretical :=
      stmts_theo D (fcd_mem D hB (FinConjCountDisj.iUnion f hf))
    rw [sub_iUnion_iff D hx f hft hU, sub_iUnion_iff D hy f hft hU]
    exact exists_congr ih

theorem agree_theo {Ω : Type u} (D : ExperimentalDomain Ω) {B : Set (Set Ω)}
    (hBasis : IsBasis D.stmts B) {x y : Set Ω} (hx : D.IsPossibility x)
    (hy : D.IsPossibility y)
    (hxy : ∀ b ∈ B, (x ⊆ b ↔ y ⊆ b)) {s : Set Ω} (h : NegFinConjCountDisj D.stmts s) :
    (x ⊆ s ↔ y ⊆ s) := by
  induction h with
  | basic hs => exact agree_fcd D hBasis.1 hx hy hxy (hBasis.2 _ hs)
  | univ => simp
  | compl hs ih =>
    rw [sub_compl_iff D hx hs, sub_compl_iff D hy hs, ih]
  | inter _ _ ihs iht =>
    simp only [Set.subset_inter_iff]
    rw [ihs, iht]
  | iUnion f hf ih =>
    have hU : (⋃ n, f n) ∈ D.theoretical := NegFinConjCountDisj.iUnion f hf
    rw [sub_iUnion_iff D hx f hf hU, sub_iUnion_iff D hy f hf hU]
    exact exists_congr ih

end P94188469

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) :
    Cardinal.mk D.Possibility ≤ Cardinal.continuum := by
  obtain ⟨B, hBc, hB⟩ := D.exists_countable_basis
  let F : D.Possibility → Set B := fun x => {b | x.val ⊆ (b : Set Ω)}
  have hF : Function.Injective F := by
    intro x y hxy
    have hag : ∀ b ∈ B, (x.val ⊆ b ↔ y.val ⊆ b) := by
      intro b hb
      have := congrArg (fun S : Set B => (⟨b, hb⟩ : B) ∈ S) hxy
      simpa [F] using this
    have h1 := P94188469.agree_theo D hB x.isPossibility y.isPossibility hag x.isPossibility.1
    have h2 := P94188469.agree_theo D hB y.isPossibility x.isPossibility
      (fun b hb => (hag b hb).symm) y.isPossibility.1
    have e : x.val = y.val := Set.Subset.antisymm (h2.mp le_rfl) (h1.mp le_rfl)
    cases x; cases y; simp_all
  have hBle : Cardinal.mk B ≤ Cardinal.aleph0 := by
    have : Countable B := hBc.to_subtype
    exact Cardinal.mk_le_aleph0
  calc Cardinal.mk D.Possibility ≤ Cardinal.mk (Set B) := Cardinal.mk_le_of_injective hF
    _ = 2 ^ Cardinal.mk B := Cardinal.mk_set
    _ ≤ 2 ^ Cardinal.aleph0 := Cardinal.power_le_power_left two_ne_zero hBle
    _ = Cardinal.continuum := Cardinal.two_power_aleph0
