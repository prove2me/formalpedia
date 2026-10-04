-- Prove2me | solution 1 for AssumptionsOfPhysics.naturalTopology_main
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:43:05.948991+00:00
-- url     : https://prove2.me/submissions/be9a7e19-14b4-452b-8d41-8342d37cd36b

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

namespace AoPNT1092

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

theorem isOpen_iff (U : Set D.Possibility) :
    IsOpen U ↔ ∃ s ∈ D.stmts, D.verifiableSet s = U := by
  have := secondCountable D
  constructor
  · intro hU
    have hU' : TopologicalSpace.GenerateOpen (D.verifiableSet '' D.stmts) U := hU
    clear hU
    induction hU' with
    | basic s hs =>
        obtain ⟨t, ht, rfl⟩ := hs
        exact ⟨t, ht, rfl⟩
    | univ => exact ⟨Set.univ, D.univ_mem, vs_univ D⟩
    | inter s t _ _ ih1 ih2 =>
        obtain ⟨a, ha, rfl⟩ := ih1
        obtain ⟨b, hb, rfl⟩ := ih2
        exact ⟨a ∩ b, D.inter_mem _ _ ha hb,
          vs_inter D (stmts_theoretical D ha) (stmts_theoretical D hb)⟩
    | sUnion S hS ih =>
        obtain ⟨T, hTc, hTS, hunion⟩ :=
          TopologicalSpace.isOpen_sUnion_countable S (fun s hs => hS s hs)
        rcases T.eq_empty_or_nonempty with hT | hT
        · refine ⟨∅, D.empty_mem, ?_⟩
          rw [vs_empty, ← hunion, hT, Set.sUnion_empty]
        · obtain ⟨g, hg⟩ := hTc.exists_eq_range hT
          have hex : ∀ n, ∃ s ∈ D.stmts, D.verifiableSet s = g n := fun n =>
            ih _ (hTS (by rw [hg]; exact ⟨n, rfl⟩))
          choose f hf1 hf2 using hex
          refine ⟨⋃ n, f n, D.iUnion_mem f hf1, ?_⟩
          rw [vs_iUnion, ← hunion, hg, Set.sUnion_range]
          exact Set.iUnion_congr hf2
  · rintro ⟨s, hs, rfl⟩
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨s, hs, rfl⟩

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

end AoPNT1092

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) :
    (∀ U : Set D.Possibility, IsOpen U ↔ ∃ s ∈ D.stmts, D.verifiableSet s = U) ∧
      SecondCountableTopology D.Possibility ∧ T0Space D.Possibility := by
  exact ⟨AoPNT1092.isOpen_iff D, AoPNT1092.secondCountable D, AoPNT1092.t0 D⟩
