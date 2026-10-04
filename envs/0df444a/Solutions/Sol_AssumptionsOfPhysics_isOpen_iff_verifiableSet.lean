-- Prove2me | solution 1 for AssumptionsOfPhysics.isOpen_iff_verifiableSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T03:43:59.827481+00:00
-- url     : https://prove2.me/submissions/920a7f85-bbf7-4c89-984a-5fb20549ca86

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

namespace AoP4594

open AssumptionsOfPhysics

/-- A countable subfamily of `D` has its union in `D`. -/
theorem sUnion_mem_of_countable {Ω : Type*} (D : ExperimentalDomain Ω) (T : Set (Set Ω))
    (hT : T.Countable) (hTD : T ⊆ D.stmts) : ⋃₀ T ∈ D.stmts := by
  rcases T.eq_empty_or_nonempty with h | h
  · subst h; simpa using D.empty_mem
  · obtain ⟨f, rfl⟩ := hT.exists_eq_range h
    rw [Set.sUnion_range]
    exact D.iUnion_mem f (fun n => hTD ⟨n, rfl⟩)

/-- Finite intersections of basis elements lie in `D`. -/
theorem sInter_mem_of_finite {Ω : Type*} (D : ExperimentalDomain Ω) (B : Set (Set Ω))
    (hB : B ⊆ D.stmts) (F : Set (Set Ω)) (hF : F.Finite) (hFB : F ⊆ B) : ⋂₀ F ∈ D.stmts := by
  induction F, hF using Set.Finite.induction_on with
  | empty => simpa using D.univ_mem
  | @insert a s _ _ ih =>
    rw [Set.sInter_insert]
    exact D.inter_mem _ _ (hB (hFB (Set.mem_insert _ _)))
      (ih (fun x hx => hFB (Set.mem_insert_of_mem _ hx)))

/-- `D` is closed under arbitrary unions. -/
theorem sUnion_mem {Ω : Type*} (D : ExperimentalDomain Ω) (S : Set (Set Ω))
    (hS : S ⊆ D.stmts) : ⋃₀ S ∈ D.stmts := by
  obtain ⟨B, hBc, hBD, hgen⟩ := D.exists_countable_basis
  set C : Set (Set Ω) := (fun F => ⋂₀ F) '' {F | F.Finite ∧ F ⊆ B} with hCdef
  have hCc : C.Countable := (Set.countable_setOf_finite_subset hBc).image _
  have hCD : C ⊆ D.stmts := by
    rintro _ ⟨F, ⟨hF, hFB⟩, rfl⟩
    exact sInter_mem_of_finite D B hBD F hF hFB
  have hCinter : ∀ a ∈ C, ∀ b ∈ C, a ∩ b ∈ C := by
    rintro _ ⟨F, ⟨hF, hFB⟩, rfl⟩ _ ⟨G, ⟨hG, hGB⟩, rfl⟩
    exact ⟨F ∪ G, ⟨hF.union hG, Set.union_subset hFB hGB⟩, Set.sInter_union F G⟩
  have hloc : ∀ t, FinConjCountDisj B t → ∀ x ∈ t, ∃ c ∈ C, x ∈ c ∧ c ⊆ t := by
    intro t ht
    induction ht with
    | @basic s hs =>
      intro x hx
      exact ⟨s, ⟨{s}, ⟨Set.finite_singleton s, Set.singleton_subset_iff.mpr hs⟩,
        Set.sInter_singleton s⟩, hx, le_rfl⟩
    | univ =>
      intro x _
      exact ⟨Set.univ, ⟨∅, ⟨Set.finite_empty, Set.empty_subset _⟩, Set.sInter_empty⟩,
        Set.mem_univ x, le_rfl⟩
    | empty =>
      intro x hx
      exact absurd hx (Set.notMem_empty x)
    | @inter s t _ _ ihs iht =>
      intro x hx
      obtain ⟨c1, hc1, hx1, hs1⟩ := ihs x hx.1
      obtain ⟨c2, hc2, hx2, hs2⟩ := iht x hx.2
      exact ⟨c1 ∩ c2, hCinter c1 hc1 c2 hc2, ⟨hx1, hx2⟩, Set.inter_subset_inter hs1 hs2⟩
    | iUnion f _ ih =>
      intro x hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      obtain ⟨c, hc, hxc, hcs⟩ := ih n x hn
      exact ⟨c, hc, hxc, hcs.trans (Set.subset_iUnion f n)⟩
  have heq : ⋃₀ S = ⋃₀ {c | c ∈ C ∧ ∃ t ∈ S, c ⊆ t} := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, htS, hxt⟩
      obtain ⟨c, hc, hxc, hct⟩ := hloc t (hgen t (hS htS)) x hxt
      exact ⟨c, ⟨hc, t, htS, hct⟩, hxc⟩
    · rintro x ⟨c, ⟨_, t, htS, hct⟩, hxc⟩
      exact ⟨t, htS, hct hxc⟩
  rw [heq]
  exact sUnion_mem_of_countable D _ (hCc.mono (fun c hc => hc.1)) (fun c hc => hCD hc.1)

theorem mem_verifiableSet_iff {Ω : Type*} (D : ExperimentalDomain Ω) (s : Set Ω)
    (hs : s ∈ D.stmts) (x : D.Possibility) : x ∈ D.verifiableSet s ↔ x.val ⊆ s := by
  constructor
  · intro h
    rcases x.isPossibility.2.2 s (NegFinConjCountDisj.basic hs) with h' | h'
    · exact h'
    · exact absurd h (Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp h'))
  · intro h
    obtain ⟨y, hy⟩ := x.isPossibility.2.1
    exact ⟨y, hy, h hy⟩

end AoP4594

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω)
    (U : Set D.Possibility) : IsOpen U ↔ ∃ s ∈ D.stmts, D.verifiableSet s = U := by
  constructor
  · intro h
    induction h with
    | basic u hu =>
      obtain ⟨s, hs, rfl⟩ := hu
      exact ⟨s, hs, rfl⟩
    | univ =>
      refine ⟨Set.univ, D.univ_mem, ?_⟩
      ext x
      simp only [Set.mem_univ, iff_true]
      rw [AoP4594.mem_verifiableSet_iff D _ D.univ_mem]
      exact Set.subset_univ _
    | inter u v _ _ ihu ihv =>
      obtain ⟨s, hs, rfl⟩ := ihu
      obtain ⟨t, ht, rfl⟩ := ihv
      refine ⟨s ∩ t, D.inter_mem s t hs ht, ?_⟩
      ext x
      rw [Set.mem_inter_iff, AoP4594.mem_verifiableSet_iff D _ (D.inter_mem s t hs ht),
        AoP4594.mem_verifiableSet_iff D _ hs, AoP4594.mem_verifiableSet_iff D _ ht,
        Set.subset_inter_iff]
    | sUnion S _ ih =>
      refine ⟨⋃₀ {s | s ∈ D.stmts ∧ D.verifiableSet s ∈ S},
        AoP4594.sUnion_mem D _ (fun s hs => hs.1), ?_⟩
      ext x
      constructor
      · rintro ⟨y, hyx, hy⟩
        obtain ⟨s, ⟨_, hsS⟩, hys⟩ := hy
        exact ⟨_, hsS, ⟨y, hyx, hys⟩⟩
      · rintro ⟨u, huS, hxu⟩
        obtain ⟨s, hs, rfl⟩ := ih u huS
        obtain ⟨y, hyx, hys⟩ := hxu
        exact ⟨y, hyx, s, ⟨hs, huS⟩, hys⟩
  · rintro ⟨s, hs, rfl⟩
    exact TopologicalSpace.GenerateOpen.basic _ ⟨s, hs, rfl⟩
