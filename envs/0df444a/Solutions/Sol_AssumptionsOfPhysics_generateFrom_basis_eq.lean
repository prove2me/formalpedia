-- Prove2me | solution 1 for AssumptionsOfPhysics.generateFrom_basis_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:14:56.768987+00:00
-- url     : https://prove2.me/submissions/58f4bded-52e6-4848-849d-c9600629b2cc

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

open AssumptionsOfPhysics in
theorem aop033e_mem_verifiableSet_iff {Ω : Type*} (D : ExperimentalDomain Ω)
    (s : Set Ω) (hs : s ∈ D.theoretical) (x : D.Possibility) :
    x ∈ D.verifiableSet s ↔ x.val ⊆ s := by
  obtain ⟨_, hne, h⟩ := x.isPossibility
  constructor
  · intro hx
    rcases h s hs with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨y, hy1, hy2⟩ := hx
      exact Set.disjoint_left.mp h1 hy1 hy2
  · intro hsub
    show (x.val ∩ s).Nonempty
    rw [Set.inter_eq_left.mpr hsub]
    exact hne

open AssumptionsOfPhysics in
theorem aop033e_key {Ω : Type*} (D : ExperimentalDomain Ω) (B : Set (Set Ω))
    (hBD : B ⊆ D.stmts) (s : Set Ω) (hs : FinConjCountDisj B s) :
    s ∈ D.stmts ∧
      @IsOpen _ (TopologicalSpace.generateFrom (D.verifiableSet '' B ∪ {Set.univ}))
        (D.verifiableSet s) := by
  induction hs with
  | basic hb =>
    refine ⟨hBD hb, ?_⟩
    apply TopologicalSpace.isOpen_generateFrom_of_mem
    exact Or.inl ⟨_, hb, rfl⟩
  | univ =>
    refine ⟨D.univ_mem, ?_⟩
    have : D.verifiableSet (Set.univ : Set Ω) = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      show (x.val ∩ Set.univ).Nonempty
      rw [Set.inter_univ]
      exact x.isPossibility.2.1
    rw [this]
    exact @isOpen_univ _ (TopologicalSpace.generateFrom _)
  | empty =>
    refine ⟨D.empty_mem, ?_⟩
    have : D.verifiableSet (∅ : Set Ω) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨y, _, hy⟩ := hx
      exact hy
    rw [this]
    exact @isOpen_empty _ (TopologicalSpace.generateFrom _)
  | @inter s t _ _ ihs iht =>
    refine ⟨D.inter_mem s t ihs.1 iht.1, ?_⟩
    have hst : s ∩ t ∈ D.theoretical :=
      NegFinConjCountDisj.basic (D.inter_mem s t ihs.1 iht.1)
    have hs' : s ∈ D.theoretical := NegFinConjCountDisj.basic ihs.1
    have ht' : t ∈ D.theoretical := NegFinConjCountDisj.basic iht.1
    have : D.verifiableSet (s ∩ t) = D.verifiableSet s ∩ D.verifiableSet t := by
      ext x
      rw [Set.mem_inter_iff, aop033e_mem_verifiableSet_iff D _ hst,
        aop033e_mem_verifiableSet_iff D _ hs', aop033e_mem_verifiableSet_iff D _ ht',
        Set.subset_inter_iff]
    rw [this]
    exact @IsOpen.inter _ (TopologicalSpace.generateFrom _) _ _ ihs.2 iht.2
  | iUnion f _ ih =>
    refine ⟨D.iUnion_mem f (fun n => (ih n).1), ?_⟩
    have : D.verifiableSet (⋃ n, f n) = ⋃ n, D.verifiableSet (f n) := by
      ext x
      simp only [Set.mem_iUnion]
      show (x.val ∩ ⋃ n, f n).Nonempty ↔ ∃ n, (x.val ∩ f n).Nonempty
      rw [Set.inter_iUnion, Set.nonempty_iUnion]
    rw [this]
    exact @isOpen_iUnion _ _ (TopologicalSpace.generateFrom _) _ (fun n => (ih n).2)

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) (B : Set (Set Ω))
    (hB : IsBasis D.stmts B) :
    TopologicalSpace.generateFrom (D.verifiableSet '' B ∪ {Set.univ}) =
      ExperimentalDomain.naturalTopology D := by
  unfold ExperimentalDomain.naturalTopology
  apply le_antisymm
  · rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro _ ⟨s, hs, rfl⟩
    exact (aop033e_key D B hB.1 s (hB.2 s hs)).2
  · rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro _ (⟨b, hb, rfl⟩ | h)
    · apply TopologicalSpace.isOpen_generateFrom_of_mem
      exact ⟨b, hB.1 hb, rfl⟩
    · rw [Set.mem_singleton_iff] at h
      subst h
      exact @isOpen_univ _ (TopologicalSpace.generateFrom _)
