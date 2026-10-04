-- Prove2me | solution 1 for AssumptionsOfPhysics.secondCountable_naturalTopology
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:30:54.054824+00:00
-- url     : https://prove2.me/submissions/bdffade2-dfcf-49b0-b2b2-a4b46be79a9f

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

namespace AoPNT4a733b95

open AssumptionsOfPhysics AssumptionsOfPhysics.ExperimentalDomain

universe u

variable {Ω : Type u} (D : ExperimentalDomain Ω)

theorem stmts_theoretical {s : Set Ω} (hs : s ∈ D.stmts) : s ∈ D.theoretical :=
  NegFinConjCountDisj.basic hs

theorem fccd_theoretical {B : Set (Set Ω)} (hB : B ⊆ D.stmts) {s : Set Ω}
    (h : FinConjCountDisj B s) : s ∈ D.theoretical := by
  induction h with
  | basic hs => exact NegFinConjCountDisj.basic (hB hs)
  | univ => exact NegFinConjCountDisj.univ
  | empty =>
      have h0 : NegFinConjCountDisj D.stmts (Set.univ : Set Ω)ᶜ :=
        NegFinConjCountDisj.compl NegFinConjCountDisj.univ
      rw [Set.compl_univ] at h0
      exact h0
  | inter _ _ ih1 ih2 => exact NegFinConjCountDisj.inter ih1 ih2
  | iUnion f _ ih => exact NegFinConjCountDisj.iUnion f ih

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

theorem vs_univ : D.verifiableSet Set.univ = Set.univ := by
  ext x
  simp only [verifiableSet, Set.mem_setOf_eq, Set.inter_univ, Set.mem_univ, iff_true]
  exact x.isPossibility.2.1

theorem vs_empty : D.verifiableSet ∅ = ∅ := by
  ext x
  simp [verifiableSet]

theorem vs_inter {s t : Set Ω} (hs : s ∈ D.theoretical) (ht : t ∈ D.theoretical) :
    D.verifiableSet (s ∩ t) = D.verifiableSet s ∩ D.verifiableSet t := by
  ext x
  simp only [verifiableSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [nonempty_iff_subset D x hs, nonempty_iff_subset D x ht,
    nonempty_iff_subset D x (NegFinConjCountDisj.inter hs ht), Set.subset_inter_iff]

theorem vs_iUnion (f : ℕ → Set Ω) :
    D.verifiableSet (⋃ n, f n) = ⋃ n, D.verifiableSet (f n) := by
  ext x
  simp only [verifiableSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.inter_iUnion,
    Set.nonempty_iUnion]

theorem gen_eq {B : Set (Set Ω)} (hB : IsBasis D.stmts B) :
    TopologicalSpace.generateFrom (D.verifiableSet '' B) = D.naturalTopology := by
  have key : ∀ s, FinConjCountDisj B s →
      TopologicalSpace.GenerateOpen (D.verifiableSet '' B) (D.verifiableSet s) := by
    intro s h
    induction h with
    | basic hs => exact TopologicalSpace.GenerateOpen.basic _ ⟨_, hs, rfl⟩
    | univ => rw [vs_univ]; exact TopologicalSpace.GenerateOpen.univ
    | empty =>
        rw [vs_empty, ← Set.sUnion_empty]
        exact TopologicalSpace.GenerateOpen.sUnion _ (by simp)
    | inter h1 h2 ih1 ih2 =>
        rw [vs_inter D (fccd_theoretical D hB.1 h1) (fccd_theoretical D hB.1 h2)]
        exact TopologicalSpace.GenerateOpen.inter _ _ ih1 ih2
    | iUnion f _ ih =>
        rw [vs_iUnion, ← Set.sUnion_range]
        exact TopologicalSpace.GenerateOpen.sUnion _ (by rintro _ ⟨n, rfl⟩; exact ih n)
  apply le_antisymm
  · show _ ≤ TopologicalSpace.generateFrom _
    rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro _ ⟨s, hs, rfl⟩
    exact key s (hB.2 s hs)
  · show TopologicalSpace.generateFrom _ ≤ _
    rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro _ ⟨s, hs, rfl⟩
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨s, hB.1 hs, rfl⟩

theorem secondCountable : SecondCountableTopology D.Possibility := by
  obtain ⟨B, hBc, hB⟩ := D.exists_countable_basis
  exact ⟨⟨D.verifiableSet '' B, hBc.image _, (gen_eq D hB).symm⟩⟩

end AoPNT4a733b95

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) :
    SecondCountableTopology D.Possibility := by
  exact AoPNT4a733b95.secondCountable D
