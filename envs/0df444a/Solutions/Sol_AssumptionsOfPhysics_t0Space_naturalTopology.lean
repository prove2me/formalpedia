-- Prove2me | solution 1 for AssumptionsOfPhysics.t0Space_naturalTopology
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:37:41.120552+00:00
-- url     : https://prove2.me/submissions/a45a5c1a-3a47-4c63-984c-31e20f23f9a4

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

namespace AoPT0b120

open AssumptionsOfPhysics AssumptionsOfPhysics.ExperimentalDomain

universe u

variable {Ω : Type u} (D : ExperimentalDomain Ω)

theorem stmts_theoretical {s : Set Ω} (hs : s ∈ D.stmts) : s ∈ D.theoretical :=
  NegFinConjCountDisj.basic hs

theorem nonempty_iff_subset (x : D.Possibility) {t : Set Ω} (ht : t ∈ D.theoretical) :
    (x.val ∩ t).Nonempty ↔ x.val ⊆ t := by
  obtain ⟨_, hne, hx⟩ := x.isPossibility
  constructor
  · intro h
    rcases hx t ht with h1 | h1
    · exact h1
    · exact absurd h1 (Set.not_disjoint_iff_nonempty_inter.mpr h)
  · intro h
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, h ha⟩

theorem subset_compl_iff (x : D.Possibility) {s : Set Ω} (hs : s ∈ D.theoretical) :
    x.val ⊆ sᶜ ↔ ¬ x.val ⊆ s := by
  rw [Set.subset_compl_iff_disjoint_right, ← nonempty_iff_subset D x hs,
    ← Set.not_disjoint_iff_nonempty_inter, not_not]

theorem subset_iUnion_iff (x : D.Possibility) (f : ℕ → Set Ω) (hf : ∀ n, f n ∈ D.theoretical) :
    x.val ⊆ ⋃ n, f n ↔ ∃ n, x.val ⊆ f n := by
  rw [← nonempty_iff_subset D x (NegFinConjCountDisj.iUnion f hf), Set.inter_iUnion,
    Set.nonempty_iUnion]
  exact exists_congr fun n => nonempty_iff_subset D x (hf n)

theorem sep (x y : D.Possibility) (h : ∀ s ∈ D.stmts, (x.val ⊆ s ↔ y.val ⊆ s)) : x = y := by
  have key : ∀ t, NegFinConjCountDisj D.stmts t → (x.val ⊆ t ↔ y.val ⊆ t) := by
    intro t ht
    induction ht with
    | basic hs => exact h _ hs
    | univ => simp
    | compl hs ih =>
        rw [subset_compl_iff D x hs, subset_compl_iff D y hs, ih]
    | inter _ _ ih1 ih2 =>
        rw [Set.subset_inter_iff, Set.subset_inter_iff, ih1, ih2]
    | iUnion f hf ih =>
        rw [subset_iUnion_iff D x f hf, subset_iUnion_iff D y f hf]
        exact exists_congr ih
  have hxy : x.val = y.val :=
    Set.Subset.antisymm ((key _ y.isPossibility.1).mpr subset_rfl)
      ((key _ x.isPossibility.1).mp subset_rfl)
  obtain ⟨xv, hx⟩ := x
  obtain ⟨yv, hy⟩ := y
  simp only at hxy
  subst hxy
  rfl

theorem t0 : T0Space D.Possibility := by
  rw [t0Space_iff_inseparable]
  intro x y hxy
  apply sep D x y
  intro s hs
  have h1 := (inseparable_iff_forall_isOpen.mp hxy) (D.verifiableSet s)
    (TopologicalSpace.isOpen_generateFrom_of_mem ⟨s, hs, rfl⟩)
  change (x.val ∩ s).Nonempty ↔ (y.val ∩ s).Nonempty at h1
  rwa [nonempty_iff_subset D x (stmts_theoretical D hs),
    nonempty_iff_subset D y (stmts_theoretical D hs)] at h1

end AoPT0b120

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) :
    T0Space D.Possibility := by
  exact AoPT0b120.t0 D
