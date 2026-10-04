-- Prove2me | solution 1 for AssumptionsOfPhysics.domainEquiv_iff_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:49:12.975658+00:00
-- url     : https://prove2.me/submissions/65581225-2874-4cb3-8388-3eadad8635bc

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_DomainRelationships

set_option autoImplicit false

namespace P2M8bf0e063

open AssumptionsOfPhysics AssumptionsOfPhysics.ExperimentalDomain

universe u

variable {Ω : Type u}

lemma stmts_sub_theo (D : ExperimentalDomain Ω) {s : Set Ω} (hs : s ∈ D.stmts) :
    s ∈ D.theoretical :=
  NegFinConjCountDisj.basic hs

lemma poss_sub (D : ExperimentalDomain Ω) (x : D.Possibility) {s : Set Ω}
    (hs : s ∈ D.theoretical) (h : (x.val ∩ s).Nonempty) : x.val ⊆ s := by
  rcases x.isPossibility.2.2 s hs with h1 | h1
  · exact h1
  · exact absurd h (Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp h1))

lemma vs_inter (D : ExperimentalDomain Ω) {a b : Set Ω} (ha : a ∈ D.theoretical)
    (hb : b ∈ D.theoretical) :
    D.verifiableSet (a ∩ b) = D.verifiableSet a ∩ D.verifiableSet b := by
  ext x
  simp only [verifiableSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨w, hw1, hw2, hw3⟩
    exact ⟨⟨w, hw1, hw2⟩, ⟨w, hw1, hw3⟩⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨w, hw⟩ := x.isPossibility.2.1
    exact ⟨w, hw, poss_sub D x ha h1 hw, poss_sub D x hb h2 hw⟩

lemma vs_iUnion (D : ExperimentalDomain Ω) (f : ℕ → Set Ω) :
    D.verifiableSet (⋃ n, f n) = ⋃ n, D.verifiableSet (f n) := by
  ext x
  simp only [verifiableSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.inter_iUnion,
    Set.nonempty_iUnion]

lemma vs_univ (D : ExperimentalDomain Ω) : D.verifiableSet Set.univ = Set.univ := by
  ext x
  simp only [verifiableSet, Set.mem_ofPred_eq, Set.inter_univ, Set.mem_univ, iff_true]
  exact x.isPossibility.2.1

lemma vs_empty (D : ExperimentalDomain Ω) : D.verifiableSet ∅ = ∅ := by
  ext x; simp [verifiableSet]

lemma fccd_mem (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hB : B ⊆ D.stmts) {s : Set Ω}
    (hs : FinConjCountDisj B s) : s ∈ D.stmts := by
  induction hs with
  | basic h => exact hB h
  | univ => exact D.univ_mem
  | empty => exact D.empty_mem
  | inter _ _ ih1 ih2 => exact D.inter_mem _ _ ih1 ih2
  | iUnion f _ ih => exact D.iUnion_mem f ih

lemma isOpen_vs_gen (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hB : B ⊆ D.stmts)
    {s : Set Ω} (hs : FinConjCountDisj B s) :
    TopologicalSpace.GenerateOpen (D.verifiableSet '' B) (D.verifiableSet s) := by
  induction hs with
  | basic h => exact TopologicalSpace.GenerateOpen.basic _ ⟨_, h, rfl⟩
  | univ => rw [vs_univ]; exact TopologicalSpace.GenerateOpen.univ
  | empty => rw [vs_empty]; exact @isOpen_empty _ (TopologicalSpace.generateFrom _)
  | inter h1 h2 ih1 ih2 =>
      rw [vs_inter D (stmts_sub_theo D (fccd_mem D hB h1)) (stmts_sub_theo D (fccd_mem D hB h2))]
      exact TopologicalSpace.GenerateOpen.inter _ _ ih1 ih2
  | iUnion f _ ih =>
      rw [vs_iUnion]
      exact @isOpen_iUnion _ _ (TopologicalSpace.generateFrom _) _ ih

instance secondCountable (D : ExperimentalDomain Ω) :
    SecondCountableTopology D.Possibility := by
  obtain ⟨B, hBc, hB1, hB2⟩ := D.exists_countable_basis
  refine ⟨⟨D.verifiableSet '' B, hBc.image _, ?_⟩⟩
  apply le_antisymm
  · rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro _ ⟨b, hb, rfl⟩
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨b, hB1 hb, rfl⟩
  · show TopologicalSpace.generateFrom _ ≤ TopologicalSpace.generateFrom _
    rw [TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro _ ⟨s, hs, rfl⟩
    exact isOpen_vs_gen D hB1 (hB2 s hs)

lemma open_eq_vs (D : ExperimentalDomain Ω) {W : Set D.Possibility} (hW : IsOpen W) :
    ∃ t ∈ D.stmts, W = D.verifiableSet t := by
  have hW' : TopologicalSpace.GenerateOpen (D.verifiableSet '' D.stmts) W := hW
  clear hW
  induction hW' with
  | basic s hs => obtain ⟨t, ht, rfl⟩ := hs; exact ⟨t, ht, rfl⟩
  | univ => exact ⟨_, D.univ_mem, (vs_univ D).symm⟩
  | inter s1 s2 _ _ ih1 ih2 =>
      obtain ⟨t1, h1, rfl⟩ := ih1
      obtain ⟨t2, h2, rfl⟩ := ih2
      exact ⟨_, D.inter_mem _ _ h1 h2,
        (vs_inter D (stmts_sub_theo D h1) (stmts_sub_theo D h2)).symm⟩
  | sUnion S hS ih =>
      obtain ⟨T, hTc, hTS, hTU⟩ :=
        TopologicalSpace.isOpen_sUnion_countable S (fun s hs => hS s hs)
      rw [← hTU]
      rcases T.eq_empty_or_nonempty with hTe | hTne
      · refine ⟨∅, D.empty_mem, ?_⟩
        rw [hTe, vs_empty, Set.sUnion_empty]
      · obtain ⟨g, hg⟩ := hTc.exists_eq_range hTne
        have hex : ∀ n, ∃ t ∈ D.stmts, g n = D.verifiableSet t := by
          intro n
          have hn : g n ∈ T := by rw [hg]; exact Set.mem_range_self n
          exact ih _ (hTS hn)
        choose tt htt hU using hex
        refine ⟨⋃ n, tt n, D.iUnion_mem _ htt, ?_⟩
        rw [hg, Set.sUnion_range, vs_iUnion]
        exact Set.iUnion_congr hU

lemma exists_poss (D : ExperimentalDomain Ω) (ω : Ω) : ∃ x : D.Possibility, ω ∈ x.val := by
  classical
  obtain ⟨B, hBc, hB1, hB2⟩ := D.exists_countable_basis
  let R : Ω → Ω → Prop := fun a b => ∀ c ∈ B, (a ∈ c ↔ b ∈ c)
  have satF : ∀ s, FinConjCountDisj B s → ∀ a b, R a b → (a ∈ s ↔ b ∈ s) := by
    intro s hs
    induction hs with
    | basic h => intro a b hab; exact hab _ h
    | univ => intro a b _; simp
    | empty => intro a b _; simp
    | inter _ _ ih1 ih2 =>
        intro a b hab; simp only [Set.mem_inter_iff, ih1 a b hab, ih2 a b hab]
    | iUnion f _ ih =>
        intro a b hab; simp only [Set.mem_iUnion]; exact exists_congr fun n => ih n a b hab
  have satN : ∀ s, NegFinConjCountDisj D.stmts s → ∀ a b, R a b → (a ∈ s ↔ b ∈ s) := by
    intro s hs
    induction hs with
    | basic h => exact satF _ (hB2 _ h)
    | univ => intro a b _; simp
    | compl _ ih => intro a b hab; simp only [Set.mem_compl_iff, ih a b hab]
    | inter _ _ ih1 ih2 =>
        intro a b hab; simp only [Set.mem_inter_iff, ih1 a b hab, ih2 a b hab]
    | iUnion f _ ih =>
        intro a b hab; simp only [Set.mem_iUnion]; exact exists_congr fun n => ih n a b hab
  have hInter : ∀ f : ℕ → Set Ω, (∀ n, NegFinConjCountDisj D.stmts (f n)) →
      NegFinConjCountDisj D.stmts (⋂ n, f n) := by
    intro f hf
    have := NegFinConjCountDisj.compl (NegFinConjCountDisj.iUnion (fun n => (f n)ᶜ)
      (fun n => NegFinConjCountDisj.compl (hf n)))
    simpa [Set.compl_iUnion] using this
  let A : Set Ω := {b | R ω b}
  have hAω : ω ∈ A := fun c _ => Iff.rfl
  have hAth : A ∈ D.theoretical := by
    rcases B.eq_empty_or_nonempty with hBe | hBne
    · have hA : A = Set.univ := by
        ext b; simp [A, R, hBe]
      rw [hA]; exact NegFinConjCountDisj.univ
    · obtain ⟨g, hg⟩ := hBc.exists_eq_range hBne
      have hA : A = ⋂ n, (if ω ∈ g n then g n else (g n)ᶜ) := by
        ext b
        simp only [A, R, hg, Set.mem_ofPred_eq, Set.forall_mem_range, Set.mem_iInter]
        refine forall_congr' fun n => ?_
        split_ifs with h <;> simp [h]
      rw [hA]
      refine hInter _ fun n => ?_
      have hn : g n ∈ D.stmts := hB1 (by rw [hg]; exact Set.mem_range_self n)
      split_ifs
      · exact NegFinConjCountDisj.basic hn
      · exact NegFinConjCountDisj.compl (NegFinConjCountDisj.basic hn)
  refine ⟨⟨A, hAth, ⟨ω, hAω⟩, fun s hs => ?_⟩, hAω⟩
  by_cases hω : ω ∈ s
  · left; intro b hb; exact (satN s hs ω b hb).1 hω
  · right; rw [Set.disjoint_left]; intro b hb hbs; exact hω ((satN s hs ω b hb).2 hbs)

lemma sub_of_homeo (DX DY : ExperimentalDomain Ω) (f : DX.Possibility ≃ₜ DY.Possibility)
    (hf : ∀ x, (f x).val = x.val) : DX.stmts ⊆ DY.stmts := by
  intro s hs
  have hfs : ∀ y, (f.symm y).val = y.val := fun y => by
    have := hf (f.symm y)
    rw [Homeomorph.apply_symm_apply] at this
    exact this.symm
  have hpre : f.symm ⁻¹' (DX.verifiableSet s) = DY.verifiableSet s := by
    ext y; simp only [Set.mem_preimage, verifiableSet, Set.mem_ofPred_eq, hfs]
  have hopen : IsOpen (DY.verifiableSet s) := by
    rw [← hpre]
    exact f.symm.continuous.isOpen_preimage _
      (TopologicalSpace.isOpen_generateFrom_of_mem ⟨s, hs, rfl⟩)
  obtain ⟨t, ht, hst⟩ := open_eq_vs DY hopen
  have hst' : s = t := by
    ext ω
    constructor
    · intro hω
      obtain ⟨x, hx⟩ := exists_poss DX ω
      have h1 : f x ∈ DY.verifiableSet s := by
        show ((f x).val ∩ s).Nonempty
        rw [hf]; exact ⟨ω, hx, hω⟩
      rw [hst] at h1
      exact poss_sub DY (f x) (stmts_sub_theo DY ht) h1 (by rw [hf]; exact hx)
    · intro hω
      obtain ⟨y, hy⟩ := exists_poss DY ω
      have h1 : y ∈ DY.verifiableSet t := ⟨ω, hy, hω⟩
      rw [← hst] at h1
      have h2 : f.symm y ∈ DX.verifiableSet s := by
        show ((f.symm y).val ∩ s).Nonempty
        rw [hfs]; exact h1
      exact poss_sub DX (f.symm y) (stmts_sub_theo DX hs) h2 (by rw [hfs]; exact hy)
  exact hst' ▸ ht

lemma eq_of_stmts (DX DY : ExperimentalDomain Ω) (h : DX.stmts = DY.stmts) : DX = DY := by
  cases DX; cases DY; simp only [ExperimentalDomain.mk.injEq]; exact h

end P2M8bf0e063

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (DX DY : ExperimentalDomain Ω) :
    ExperimentalDomain.DomainEquiv DX DY ↔
      ∃ f : DX.Possibility ≃ₜ DY.Possibility, ∀ x : DX.Possibility, (f x).val = x.val := by
  constructor
  · rintro ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
    have h1 : DX.stmts ⊆ DY.stmts := by
      intro s hs
      have := (r ⟨s, hs⟩).2
      rwa [hr ⟨s, hs⟩] at this
    have h2 : DY.stmts ⊆ DX.stmts := by
      intro s hs
      have := (r' ⟨s, hs⟩).2
      rwa [hr' ⟨s, hs⟩] at this
    have hXY : DX = DY := P2M8bf0e063.eq_of_stmts DX DY (Set.Subset.antisymm h1 h2)
    subst hXY
    exact ⟨Homeomorph.refl _, fun x => rfl⟩
  · rintro ⟨f, hf⟩
    have hfs : ∀ y, (f.symm y).val = y.val := fun y => by
      have := hf (f.symm y)
      rw [Homeomorph.apply_symm_apply] at this
      exact this.symm
    exact ⟨⟨fun s => ⟨s.1, P2M8bf0e063.sub_of_homeo DX DY f hf s.2⟩, fun s => rfl⟩,
      ⟨fun s => ⟨s.1, P2M8bf0e063.sub_of_homeo DY DX f.symm hfs s.2⟩, fun s => rfl⟩⟩
