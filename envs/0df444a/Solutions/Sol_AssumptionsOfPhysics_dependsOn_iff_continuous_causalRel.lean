-- Prove2me | solution 1 for AssumptionsOfPhysics.dependsOn_iff_continuous_causalRel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:49:41.25331+00:00
-- url     : https://prove2.me/submissions/07df44b5-bbf0-413e-b97a-658aa59a5950

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_DomainRelationships

set_option autoImplicit false

namespace AoP708

open AssumptionsOfPhysics
open AssumptionsOfPhysics.ExperimentalDomain

universe u

variable {Ω : Type u}

lemma negFin_sInter {C : Set (Set Ω)} (S : Set (Set Ω)) (hS : S.Countable)
    (h : ∀ s ∈ S, NegFinConjCountDisj C s) : NegFinConjCountDisj C (⋂₀ S) := by
  rcases S.eq_empty_or_nonempty with he | hne
  · subst he; simpa using (NegFinConjCountDisj.univ : NegFinConjCountDisj C Set.univ)
  · obtain ⟨g, rfl⟩ := hS.exists_eq_range hne
    have key : NegFinConjCountDisj C (⋃ n, (g n)ᶜ)ᶜ :=
      .compl (.iUnion _ (fun n => .compl (h _ ⟨n, rfl⟩)))
    rw [Set.compl_iUnion] at key
    simpa [Set.sInter_range] using key

lemma stmts_sUnion (D : ExperimentalDomain Ω) (S : Set (Set Ω)) (hS : S.Countable)
    (h : S ⊆ D.stmts) : ⋃₀ S ∈ D.stmts := by
  rcases S.eq_empty_or_nonempty with he | hne
  · subst he; simpa using D.empty_mem
  · obtain ⟨g, rfl⟩ := hS.exists_eq_range hne
    rw [Set.sUnion_range]
    exact D.iUnion_mem g (fun n => h ⟨n, rfl⟩)

lemma finConj_mem (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hB : B ⊆ D.stmts)
    {s : Set Ω} (hs : FinConjCountDisj B s) : s ∈ D.stmts := by
  induction hs with
  | basic hb => exact hB hb
  | univ => exact D.univ_mem
  | empty => exact D.empty_mem
  | inter _ _ ih₁ ih₂ => exact D.inter_mem _ _ ih₁ ih₂
  | iUnion f _ ih => exact D.iUnion_mem f ih

lemma poss_dich (D : ExperimentalDomain Ω) (x : D.Possibility) {s : Set Ω}
    (hs : s ∈ D.stmts) : x.val ⊆ s ∨ Disjoint x.val s :=
  x.isPossibility.2.2 s (NegFinConjCountDisj.basic hs)

lemma poss_sub_of_inter (D : ExperimentalDomain Ω) (x : D.Possibility) {s : Set Ω}
    (hs : s ∈ D.stmts) (hne : (x.val ∩ s).Nonempty) : x.val ⊆ s := by
  rcases poss_dich D x hs with h | h
  · exact h
  · exact absurd hne (Set.disjoint_iff_inter_eq_empty.mp h ▸ Set.not_nonempty_empty)

/-- Minterm construction: any nonempty set that is decided by every statement of the domain
lies inside some possibility. -/
lemma exists_possibility_superset (D : ExperimentalDomain Ω) (x : Set Ω) (hx : x.Nonempty)
    (h : ∀ s ∈ D.stmts, x ⊆ s ∨ Disjoint x s) : ∃ y : D.Possibility, x ⊆ y.val := by
  obtain ⟨B, hBc, hBsub, hBgen⟩ := D.exists_countable_basis
  classical
  let piece : Set Ω → Set Ω := fun b => if x ⊆ b then b else bᶜ
  let y : Set Ω := ⋂₀ (piece '' B)
  have hxy : x ⊆ y := by
    intro ω hω
    simp only [y, Set.mem_sInter, Set.mem_image]
    rintro _ ⟨b, hb, rfl⟩
    by_cases hxb : x ⊆ b
    · simp only [piece, if_pos hxb]; exact hxb hω
    · simp only [piece, if_neg hxb]
      rcases h b (hBsub hb) with h1 | h1
      · exact absurd h1 hxb
      · exact fun hωb => Set.disjoint_left.mp h1 hω hωb
  have hy_piece : ∀ b ∈ B, y ⊆ piece b := fun b hb =>
    Set.sInter_subset_of_mem ⟨b, hb, rfl⟩
  have hyT : y ∈ D.theoretical := by
    apply negFin_sInter _ (hBc.image _)
    rintro _ ⟨b, hb, rfl⟩
    by_cases hxb : x ⊆ b
    · simp only [piece, if_pos hxb]; exact .basic (hBsub hb)
    · simp only [piece, if_neg hxb]; exact .compl (.basic (hBsub hb))
  have hdichB : ∀ {s : Set Ω}, FinConjCountDisj B s → y ⊆ s ∨ Disjoint y s := by
    intro s hs
    induction hs with
    | basic hb =>
      rename_i b
      by_cases hxb : x ⊆ b
      · left; have := hy_piece b hb; simp only [piece, if_pos hxb] at this; exact this
      · right; have := hy_piece b hb; simp only [piece, if_neg hxb] at this
        exact Set.disjoint_left.mpr (fun ω h1 h2 => this h1 h2)
    | univ => left; exact Set.subset_univ _
    | empty => right; exact Set.disjoint_empty _
    | inter _ _ ih₁ ih₂ =>
      rcases ih₁ with h1 | h1
      · rcases ih₂ with h2 | h2
        · left; exact Set.subset_inter h1 h2
        · right; exact h2.mono_right Set.inter_subset_right
      · right; exact h1.mono_right Set.inter_subset_left
    | iUnion f _ ih =>
      by_cases hex : ∃ n, y ⊆ f n
      · obtain ⟨n, hn⟩ := hex
        left; exact hn.trans (Set.subset_iUnion f n)
      · push Not at hex
        right
        rw [Set.disjoint_iUnion_right]
        intro n
        rcases ih n with h1 | h1
        · exact absurd h1 (hex n)
        · exact h1
  have hdich : ∀ s ∈ D.theoretical, y ⊆ s ∨ Disjoint y s := by
    intro s hs
    induction hs with
    | basic hb => exact hdichB (hBgen _ hb)
    | univ => left; exact Set.subset_univ _
    | compl _ ih =>
      rcases ih with h1 | h1
      · right; exact Set.disjoint_left.mpr (fun ω h1' h2 => h2 (h1 h1'))
      · left; exact Set.subset_compl_iff_disjoint_right.mpr h1
    | inter _ _ ih₁ ih₂ =>
      rcases ih₁ with h1 | h1
      · rcases ih₂ with h2 | h2
        · left; exact Set.subset_inter h1 h2
        · right; exact h2.mono_right Set.inter_subset_right
      · right; exact h1.mono_right Set.inter_subset_left
    | iUnion f _ ih =>
      by_cases hex : ∃ n, y ⊆ f n
      · obtain ⟨n, hn⟩ := hex
        left; exact hn.trans (Set.subset_iUnion f n)
      · push Not at hex
        right
        rw [Set.disjoint_iUnion_right]
        intro n
        rcases ih n with h1 | h1
        · exact absurd h1 (hex n)
        · exact h1
  exact ⟨⟨y, hyT, hx.mono hxy, hdich⟩, hxy⟩

lemma exists_poss_mem (D : ExperimentalDomain Ω) (ω : Ω) : ∃ x : D.Possibility, ω ∈ x.val := by
  obtain ⟨x, hx⟩ := exists_possibility_superset D {ω} (Set.singleton_nonempty ω) (by
    intro s _
    by_cases h : ω ∈ s
    · left; simpa using h
    · right; simpa using h)
  exact ⟨x, hx rfl⟩

lemma vs_univ (D : ExperimentalDomain Ω) : D.verifiableSet Set.univ = Set.univ := by
  ext x; simp [verifiableSet, x.isPossibility.2.1]

lemma vs_empty (D : ExperimentalDomain Ω) : D.verifiableSet ∅ = ∅ := by
  ext x; simp [verifiableSet]

lemma vs_inter (D : ExperimentalDomain Ω) {s t : Set Ω} (hs : s ∈ D.stmts) (ht : t ∈ D.stmts) :
    D.verifiableSet (s ∩ t) = D.verifiableSet s ∩ D.verifiableSet t := by
  ext x
  simp only [verifiableSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨h.mono (Set.inter_subset_inter_right _ Set.inter_subset_left),
      h.mono (Set.inter_subset_inter_right _ Set.inter_subset_right)⟩
  · rintro ⟨h1, h2⟩
    have a := poss_sub_of_inter D x hs h1
    have b := poss_sub_of_inter D x ht h2
    obtain ⟨ω, hω⟩ := x.isPossibility.2.1
    exact ⟨ω, hω, a hω, b hω⟩

lemma vs_iUnion (D : ExperimentalDomain Ω) (f : ℕ → Set Ω) :
    D.verifiableSet (⋃ n, f n) = ⋃ n, D.verifiableSet (f n) := by
  ext x
  simp only [verifiableSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.inter_iUnion,
    Set.nonempty_iUnion]

lemma vs_sUnion (D : ExperimentalDomain Ω) (A : Set (Set Ω)) :
    D.verifiableSet (⋃₀ A) = ⋃ a ∈ A, D.verifiableSet a := by
  ext x
  simp only [verifiableSet, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨ω, hω, a, ha, hωa⟩
    exact ⟨a, ha, ω, hω, hωa⟩
  · rintro ⟨a, ha, ω, hω, hωa⟩
    exact ⟨ω, hω, a, ha, hωa⟩

lemma genOpen_of_basis (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hB : B ⊆ D.stmts)
    {t : Set Ω} (ht : FinConjCountDisj B t) :
    TopologicalSpace.GenerateOpen (D.verifiableSet '' B) (D.verifiableSet t) := by
  induction ht with
  | basic hb => exact .basic _ ⟨_, hb, rfl⟩
  | univ => rw [vs_univ]; exact .univ
  | empty =>
    rw [vs_empty, ← Set.sUnion_empty]
    exact .sUnion _ (fun _ h => absurd h (Set.notMem_empty _))
  | inter h1 h2 ih₁ ih₂ =>
    rw [vs_inter D (finConj_mem D hB h1) (finConj_mem D hB h2)]
    exact .inter _ _ ih₁ ih₂
  | iUnion f _ ih =>
    rw [vs_iUnion, ← Set.sUnion_range]
    exact .sUnion _ (by rintro _ ⟨n, rfl⟩; exact ih n)

lemma secondCountable (D : ExperimentalDomain Ω) : SecondCountableTopology D.Possibility := by
  obtain ⟨B, hBc, hBsub, hBgen⟩ := D.exists_countable_basis
  refine ⟨⟨D.verifiableSet '' B, hBc.image _, ?_⟩⟩
  apply le_antisymm
  · rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro _ ⟨b, hb, rfl⟩
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨b, hBsub hb, rfl⟩
  · show TopologicalSpace.generateFrom _ ≤ TopologicalSpace.generateFrom _
    rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro _ ⟨t, ht, rfl⟩
    exact genOpen_of_basis D hBsub (hBgen t ht)

lemma open_eq_vs (D : ExperimentalDomain Ω) (O : Set D.Possibility)
    (hO : TopologicalSpace.GenerateOpen (D.verifiableSet '' D.stmts) O) :
    ∃ t ∈ D.stmts, O = D.verifiableSet t := by
  haveI := secondCountable D
  induction hO with
  | basic s hs =>
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨t, ht, rfl⟩
  | univ => exact ⟨Set.univ, D.univ_mem, (vs_univ D).symm⟩
  | inter s t _ _ ih₁ ih₂ =>
    obtain ⟨a, ha, rfl⟩ := ih₁
    obtain ⟨b, hb, rfl⟩ := ih₂
    exact ⟨a ∩ b, D.inter_mem _ _ ha hb, (vs_inter D ha hb).symm⟩
  | sUnion S hS ih =>
    obtain ⟨T, hTc, hTS, hTeq⟩ := TopologicalSpace.isOpen_sUnion_countable S hS
    choose! tf htf hEq using ih
    refine ⟨⋃₀ (tf '' T), stmts_sUnion D _ (hTc.image _)
      (by rintro _ ⟨s, hs, rfl⟩; exact htf s (hTS hs)), ?_⟩
    rw [← hTeq, vs_sUnion, Set.biUnion_image, Set.sUnion_eq_biUnion]
    refine Set.iUnion₂_congr (fun s hs => hEq s (hTS hs))

lemma preimage_vs (DX DY : ExperimentalDomain Ω) (f : DX.Possibility → DY.Possibility)
    (hf : IsCausalRel DX DY f) {t : Set Ω} (ht : t ∈ DY.stmts) :
    f ⁻¹' (DY.verifiableSet t) = DX.verifiableSet t := by
  ext x
  simp only [Set.mem_preimage, verifiableSet, Set.mem_setOf_eq]
  constructor
  · intro h
    have := poss_sub_of_inter DY (f x) ht h
    obtain ⟨ω, hω⟩ := x.isPossibility.2.1
    exact ⟨ω, hω, this (hf x hω)⟩
  · intro h
    exact h.mono (Set.inter_subset_inter_left _ (hf x))

lemma negFin_mono {B C : Set (Set Ω)} (h : B ⊆ C) {s : Set Ω} (hs : NegFinConjCountDisj B s) :
    NegFinConjCountDisj C s := by
  induction hs with
  | basic hb => exact .basic (h hb)
  | univ => exact .univ
  | compl _ ih => exact .compl ih
  | inter _ _ ih₁ ih₂ => exact .inter ih₁ ih₂
  | iUnion f _ ih => exact .iUnion f ih

theorem main (DX DY : ExperimentalDomain Ω) :
    DependsOn DY DX ↔ ∃ f : DX.Possibility → DY.Possibility, IsCausalRel DX DY f ∧ Continuous f := by
  constructor
  · rintro ⟨r, hr⟩
    have hsub : DY.stmts ⊆ DX.stmts := by
      intro s hs
      have := (r ⟨s, hs⟩).2
      rwa [hr ⟨s, hs⟩] at this
    have hex : ∀ x : DX.Possibility, ∃ y : DY.Possibility, x.val ⊆ y.val := fun x =>
      exists_possibility_superset DY x.val x.isPossibility.2.1
        (fun s hs => poss_dich DX x (hsub hs))
    choose f hf using hex
    refine ⟨f, hf, ?_⟩
    rw [continuous_generateFrom_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [preimage_vs DX DY f hf ht]
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨t, hsub ht, rfl⟩
  · rintro ⟨f, hf, hc⟩
    have hmem : ∀ s ∈ DY.stmts, s ∈ DX.stmts := by
      intro s hs
      have hopen : IsOpen (DY.verifiableSet s) :=
        TopologicalSpace.isOpen_generateFrom_of_mem ⟨s, hs, rfl⟩
      have h2 := hc.isOpen_preimage _ hopen
      rw [preimage_vs DX DY f hf hs] at h2
      obtain ⟨t, ht, heq⟩ := open_eq_vs DX _ h2
      have hst : s = t := by
        ext ω
        obtain ⟨x, hx⟩ := exists_poss_mem DX ω
        have key : x ∈ DX.verifiableSet s ↔ x ∈ DX.verifiableSet t := by rw [heq]
        rw [← preimage_vs DX DY f hf hs] at key
        simp only [Set.mem_preimage, verifiableSet, Set.mem_setOf_eq] at key
        constructor
        · intro hω
          have h1 : (x.val ∩ t).Nonempty :=
            key.mp ⟨ω, hf x hx, hω⟩
          exact poss_sub_of_inter DX x ht h1 hx
        · intro hω
          have h1 := key.mpr ⟨ω, hx, hω⟩
          exact poss_sub_of_inter DY (f x) hs h1 (hf x hx)
      exact hst ▸ ht
    exact ⟨fun s => ⟨s.1, hmem s.1 s.2⟩, fun s => rfl⟩

end AoP708

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (DX DY : ExperimentalDomain Ω) :
    ExperimentalDomain.DependsOn DY DX ↔
      ∃ f : DX.Possibility → DY.Possibility,
        ExperimentalDomain.IsCausalRel DX DY f ∧ Continuous f := by
  exact AoP708.main DX DY
