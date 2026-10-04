-- Prove2me | solution 1 for AssumptionsOfPhysics.discreteTopology_iff_isDecidable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:21:12.298457+00:00
-- url     : https://prove2.me/submissions/cfeecabd-f835-4c10-8ba5-a7c19269e0b2

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

namespace AoPDiscHelpers
open AssumptionsOfPhysics

universe u

variable {Ω : Type u}

lemma theo_iInter (D : ExperimentalDomain Ω) (g : ℕ → Set Ω)
    (hg : ∀ n, g n ∈ D.theoretical) : (⋂ n, g n) ∈ D.theoretical := by
  have h : (⋂ n, g n) = (⋃ n, (g n)ᶜ)ᶜ := by simp [Set.compl_iUnion]
  rw [h]
  exact NegFinConjCountDisj.compl
    (NegFinConjCountDisj.iUnion _ (fun n => NegFinConjCountDisj.compl (hg n)))

def Sat (B : Set (Set Ω)) (s : Set Ω) : Prop :=
  ∀ ω ω' : Ω, (∀ b ∈ B, (ω ∈ b ↔ ω' ∈ b)) → ω ∈ s → ω' ∈ s

lemma sat_fin (B : Set (Set Ω)) {s : Set Ω} (h : FinConjCountDisj B s) : Sat B s := by
  induction h with
  | @basic s hs => intro ω ω' hb h; exact (hb s hs).1 h
  | univ => intro _ _ _ _; trivial
  | empty => intro _ _ _ h; exact h.elim
  | inter _ _ ih1 ih2 => intro ω ω' hb h; exact ⟨ih1 ω ω' hb h.1, ih2 ω ω' hb h.2⟩
  | iUnion f _ ih =>
    intro ω ω' hb h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    exact Set.mem_iUnion.2 ⟨n, ih n ω ω' hb hn⟩

lemma sat_theo (D : ExperimentalDomain Ω) (B : Set (Set Ω)) (hB : IsBasis D.stmts B)
    {s : Set Ω} (h : s ∈ D.theoretical) : Sat B s := by
  change NegFinConjCountDisj D.stmts s at h
  induction h with
  | @basic s hs => exact sat_fin B (hB.2 s hs)
  | univ => intro _ _ _ _; trivial
  | compl _ ih =>
    intro ω ω' hb h h'
    exact h (ih ω' ω (fun b hb' => (hb b hb').symm) h')
  | inter _ _ ih1 ih2 => intro ω ω' hb h; exact ⟨ih1 ω ω' hb h.1, ih2 ω ω' hb h.2⟩
  | iUnion f _ ih =>
    intro ω ω' hb h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    exact Set.mem_iUnion.2 ⟨n, ih n ω ω' hb hn⟩

lemma exists_poss (D : ExperimentalDomain Ω) (ω : Ω) :
    ∃ x, D.IsPossibility x ∧ ω ∈ x := by
  classical
  obtain ⟨B, hBc, hB⟩ := D.exists_countable_basis
  obtain ⟨f, hf⟩ := (hBc.insert Set.univ).exists_eq_range (Set.insert_nonempty _ _)
  have hmem : ∀ ω', ω' ∈ (⋂ n, (if ω ∈ f n then f n else (f n)ᶜ)) ↔
      ∀ n, (ω ∈ f n ↔ ω' ∈ f n) := by
    intro ω'
    simp only [Set.mem_iInter]
    refine forall_congr' (fun n => ?_)
    by_cases h : ω ∈ f n <;> simp [h]
  have hfT : ∀ n, f n ∈ D.theoretical := by
    intro n
    have : f n ∈ insert Set.univ B := by rw [hf]; exact Set.mem_range_self n
    rcases this with h | h
    · rw [h]; exact NegFinConjCountDisj.univ
    · exact NegFinConjCountDisj.basic (hB.1 h)
  have haT : (⋂ n, (if ω ∈ f n then f n else (f n)ᶜ)) ∈ D.theoretical := by
    apply theo_iInter
    intro n
    split_ifs
    · exact hfT n
    · exact NegFinConjCountDisj.compl (hfT n)
  have hωa : ω ∈ (⋂ n, (if ω ∈ f n then f n else (f n)ᶜ)) := (hmem ω).2 (fun n => Iff.rfl)
  have hrel : ∀ ω' ∈ (⋂ n, (if ω ∈ f n then f n else (f n)ᶜ)),
      ∀ b ∈ B, (ω ∈ b ↔ ω' ∈ b) := by
    intro ω' h' b hb
    have : b ∈ Set.range f := by rw [← hf]; exact Set.mem_insert_of_mem _ hb
    obtain ⟨n, rfl⟩ := this
    exact (hmem ω').1 h' n
  refine ⟨_, ⟨haT, ⟨ω, hωa⟩, ?_⟩, hωa⟩
  intro s hs
  by_cases hωs : ω ∈ s
  · left
    intro ω' h'
    exact sat_theo D B hB hs ω ω' (hrel ω' h') hωs
  · right
    rw [Set.disjoint_left]
    intro ω' h' h's
    exact hωs (sat_theo D B hB hs ω' ω (fun b hb => (hrel ω' h' b hb).symm) h's)

lemma poss_eq (D : ExperimentalDomain Ω) {x y : Set Ω} (hx : D.IsPossibility x)
    (hy : D.IsPossibility y) (h : (x ∩ y).Nonempty) : x = y := by
  have hnd : ¬ Disjoint x y := Set.not_disjoint_iff_nonempty_inter.2 h
  rcases hx.2.2 y hy.1 with h1 | h1
  · rcases hy.2.2 x hx.1 with h2 | h2
    · exact Set.Subset.antisymm h1 h2
    · exact absurd h2.symm hnd
  · exact absurd h1 hnd

lemma poss_inter_iff (D : ExperimentalDomain Ω) {x s : Set Ω} (hx : D.IsPossibility x)
    (hs : s ∈ D.theoretical) : (x ∩ s).Nonempty ↔ x ⊆ s := by
  constructor
  · intro h
    rcases hx.2.2 s hs with h1 | h1
    · exact h1
    · exact absurd h1 (Set.not_disjoint_iff_nonempty_inter.2 h)
  · intro h
    obtain ⟨ω, hω⟩ := hx.2.1
    exact ⟨ω, hω, h hω⟩

lemma theo_cover (D : ExperimentalDomain Ω) {s : Set Ω} (hs : s ∈ D.theoretical) {ω : Ω}
    (hω : ω ∈ s) : ∃ x, D.IsPossibility x ∧ ω ∈ x ∧ x ⊆ s := by
  obtain ⟨x, hx, hωx⟩ := exists_poss D ω
  exact ⟨x, hx, hωx, (poss_inter_iff D hx hs).1 ⟨ω, hωx, hω⟩⟩

lemma poss_ext (D : ExperimentalDomain Ω) {x y : D.Possibility} (h : x.val = y.val) :
    x = y := by
  cases x; cases y; simp only at h; subst h; rfl

lemma mem_vs (D : ExperimentalDomain Ω) (y : D.Possibility) (t : Set Ω) :
    y ∈ D.verifiableSet t ↔ (y.val ∩ t).Nonempty := Iff.rfl

lemma open_basic (D : ExperimentalDomain Ω) {V : Set D.Possibility} (hV : IsOpen V)
    {x : D.Possibility} (hx : x ∈ V) :
    ∃ t ∈ D.stmts, x ∈ D.verifiableSet t ∧ D.verifiableSet t ⊆ V := by
  change TopologicalSpace.GenerateOpen (D.verifiableSet '' D.stmts) V at hV
  induction hV generalizing x with
  | basic s hs =>
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨t, ht, hx, subset_rfl⟩
  | univ =>
    refine ⟨Set.univ, D.univ_mem, ?_, Set.subset_univ _⟩
    rw [mem_vs, Set.inter_univ]
    exact x.isPossibility.2.1
  | inter s t _ _ ih1 ih2 =>
    obtain ⟨t1, ht1, hx1, h1⟩ := ih1 hx.1
    obtain ⟨t2, ht2, hx2, h2⟩ := ih2 hx.2
    refine ⟨t1 ∩ t2, D.inter_mem _ _ ht1 ht2, ?_, ?_⟩
    · have a1 := (poss_inter_iff D x.isPossibility (NegFinConjCountDisj.basic ht1)).1
        ((mem_vs D x t1).1 hx1)
      have a2 := (poss_inter_iff D x.isPossibility (NegFinConjCountDisj.basic ht2)).1
        ((mem_vs D x t2).1 hx2)
      obtain ⟨ω, hω⟩ := x.isPossibility.2.1
      rw [mem_vs]
      exact ⟨ω, hω, a1 hω, a2 hω⟩
    · intro y hy
      rw [mem_vs] at hy
      obtain ⟨ω, hω1, hω2, hω3⟩ := hy
      exact ⟨h1 ((mem_vs D y t1).2 ⟨ω, hω1, hω2⟩), h2 ((mem_vs D y t2).2 ⟨ω, hω1, hω3⟩)⟩
  | sUnion S _ ih =>
    obtain ⟨V, hVS, hxV⟩ := hx
    obtain ⟨t, ht, hxt, hsub⟩ := ih V hVS hxV
    exact ⟨t, ht, hxt, hsub.trans (Set.subset_sUnion_of_mem hVS)⟩

lemma theo_sub_of_dec (D : ExperimentalDomain Ω) (hd : D.IsDecidable) {s : Set Ω}
    (hs : s ∈ D.theoretical) : s ∈ D.stmts := by
  change NegFinConjCountDisj D.stmts s at hs
  induction hs with
  | basic h => exact h
  | univ => exact D.univ_mem
  | compl _ ih => exact hd _ ih
  | inter _ _ ih1 ih2 => exact D.inter_mem _ _ ih1 ih2
  | iUnion f _ ih => exact D.iUnion_mem f ih

lemma fin_cover (D : ExperimentalDomain Ω) (B : Set (Set Ω)) (hBD : B ⊆ D.stmts) {u : Set Ω}
    (hu : FinConjCountDisj B u) :
    ∀ ω ∈ u, ∃ F : Set (Set Ω), F.Finite ∧ F ⊆ B ∧ ⋂₀ F ∈ D.stmts ∧ ω ∈ ⋂₀ F ∧ ⋂₀ F ⊆ u := by
  induction hu with
  | @basic s hs =>
    intro ω hω
    refine ⟨{s}, Set.finite_singleton _, Set.singleton_subset_iff.2 hs, ?_, ?_, ?_⟩
    · rw [Set.sInter_singleton]; exact hBD hs
    · rw [Set.sInter_singleton]; exact hω
    · rw [Set.sInter_singleton]
  | univ =>
    intro ω _
    refine ⟨∅, Set.finite_empty, Set.empty_subset _, ?_, ?_, Set.subset_univ _⟩
    · rw [Set.sInter_empty]; exact D.univ_mem
    · rw [Set.sInter_empty]; trivial
  | empty => intro ω h; exact h.elim
  | inter _ _ ih1 ih2 =>
    intro ω hω
    obtain ⟨F1, f1, s1, d1, m1, h1⟩ := ih1 ω hω.1
    obtain ⟨F2, f2, s2, d2, m2, h2⟩ := ih2 ω hω.2
    refine ⟨F1 ∪ F2, f1.union f2, Set.union_subset s1 s2, ?_, ?_, ?_⟩
    · rw [Set.sInter_union]; exact D.inter_mem _ _ d1 d2
    · rw [Set.sInter_union]; exact ⟨m1, m2⟩
    · rw [Set.sInter_union]; exact Set.inter_subset_inter h1 h2
  | iUnion f _ ih =>
    intro ω hω
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hω
    obtain ⟨F, hF, hFB, hFD, hωF, hFu⟩ := ih n ω hn
    exact ⟨F, hF, hFB, hFD, hωF, hFu.trans (Set.subset_iUnion f n)⟩

lemma sUnion_mem (D : ExperimentalDomain Ω) {S : Set (Set Ω)} (hS : S.Countable)
    (hSD : ∀ c ∈ S, c ∈ D.stmts) : ⋃₀ S ∈ D.stmts := by
  obtain ⟨f, hf⟩ := (hS.insert ∅).exists_eq_range (Set.insert_nonempty _ _)
  have : ⋃₀ S = ⋃ n, f n := by
    rw [← Set.sUnion_range, ← hf, Set.sUnion_insert, Set.empty_union]
  rw [this]
  apply D.iUnion_mem
  intro n
  have : f n ∈ insert ∅ S := by rw [hf]; exact Set.mem_range_self n
  rcases this with h | h
  · rw [h]; exact D.empty_mem
  · exact hSD _ h

lemma main_iff (D : ExperimentalDomain Ω) :
    DiscreteTopology D.Possibility ↔ D.IsDecidable := by
  constructor
  · intro hdisc s hs
    obtain ⟨B, hBc, hB⟩ := D.exists_countable_basis
    have hposD : ∀ x : D.Possibility, x.val ∈ D.stmts := by
      intro x
      have hopen : IsOpen ({x} : Set D.Possibility) := isOpen_discrete _
      obtain ⟨t, ht, hxt, hsub⟩ := open_basic D hopen (Set.mem_singleton x)
      have h1 : x.val ⊆ t :=
        (poss_inter_iff D x.isPossibility (NegFinConjCountDisj.basic ht)).1 ((mem_vs D x t).1 hxt)
      have h2 : t ⊆ x.val := by
        intro ω hω
        obtain ⟨y, hy, hωy, _⟩ := theo_cover D (NegFinConjCountDisj.basic ht) hω
        have hyU : (⟨y, hy⟩ : D.Possibility) ∈ D.verifiableSet t :=
          (mem_vs D _ t).2 ⟨ω, hωy, hω⟩
        have hyx : (⟨y, hy⟩ : D.Possibility) = x := Set.mem_singleton_iff.1 (hsub hyU)
        rw [← hyx]
        exact hωy
      rw [Set.Subset.antisymm h1 h2]
      exact ht
    have hsc : sᶜ ∈ D.theoretical :=
      NegFinConjCountDisj.compl (NegFinConjCountDisj.basic hs)
    have hC : ((fun F : Set (Set Ω) => ⋂₀ F) '' {F | F.Finite ∧ F ⊆ B}).Countable :=
      (Set.countable_ofPred_finite_subset hBc).image _
    have hS : ({c ∈ (fun F : Set (Set Ω) => ⋂₀ F) '' {F | F.Finite ∧ F ⊆ B} |
        c ∈ D.stmts ∧ c ⊆ sᶜ} : Set (Set Ω)).Countable := hC.mono (fun c hc => hc.1)
    have heq : sᶜ = ⋃₀ {c ∈ (fun F : Set (Set Ω) => ⋂₀ F) '' {F | F.Finite ∧ F ⊆ B} |
        c ∈ D.stmts ∧ c ⊆ sᶜ} := by
      apply Set.Subset.antisymm
      · intro ω hω
        obtain ⟨x, hx, hωx, hxs⟩ := theo_cover D hsc hω
        have hxD : x ∈ D.stmts := hposD ⟨x, hx⟩
        obtain ⟨F, hF, hFB, hFD, hωF, hFx⟩ := fin_cover D B hB.1 (hB.2 x hxD) ω hωx
        exact ⟨⋂₀ F, ⟨⟨F, ⟨hF, hFB⟩, rfl⟩, hFD, hFx.trans hxs⟩, hωF⟩
      · exact Set.sUnion_subset (fun c hc => hc.2.2)
    rw [heq]
    exact sUnion_mem D hS (fun c hc => hc.2.1)
  · intro hd
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    have hxD : x.val ∈ D.stmts := theo_sub_of_dec D hd x.isPossibility.1
    have : ({x} : Set D.Possibility) = D.verifiableSet x.val := by
      ext y
      rw [Set.mem_singleton_iff, mem_vs]
      constructor
      · rintro rfl
        obtain ⟨ω, hω⟩ := y.isPossibility.2.1
        exact ⟨ω, hω, hω⟩
      · intro h
        exact poss_ext D (poss_eq D y.isPossibility x.isPossibility h)
    rw [this]
    exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨x.val, hxD, rfl⟩

end AoPDiscHelpers

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) :
    DiscreteTopology D.Possibility ↔ D.IsDecidable := by
  exact AoPDiscHelpers.main_iff D
