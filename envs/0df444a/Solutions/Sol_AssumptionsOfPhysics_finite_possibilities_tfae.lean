-- Prove2me | solution 1 for AssumptionsOfPhysics.finite_possibilities_tfae
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:38:58.371663+00:00
-- url     : https://prove2.me/submissions/ab97159e-d103-4a9a-ae14-94232355959f

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

namespace P8135

open AssumptionsOfPhysics

universe u

variable {Ω : Type u}

theorem mono_basis {B : Set (Set Ω)} {s : Set Ω} (hs : FinConjCountDisj B s)
    {ω ω' : Ω} (h : ∀ b ∈ B, ω ∈ b → ω' ∈ b) : ω ∈ s → ω' ∈ s := by
  induction hs with
  | basic hb => exact h _ hb
  | univ => intro _; trivial
  | empty => intro hω; simp at hω
  | inter _ _ ih1 ih2 => intro hω; exact ⟨ih1 hω.1, ih2 hω.2⟩
  | iUnion f _ ih =>
    intro hω
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hω
    exact Set.mem_iUnion.2 ⟨n, ih n hn⟩

theorem sep_basis {B : Set (Set Ω)} {s : Set Ω} (hs : FinConjCountDisj B s) {ω ω' : Ω}
    (hω : ω ∈ s) (hω' : ω' ∉ s) : ∃ b ∈ B, ω ∈ b ∧ ω' ∉ b := by
  by_contra hcon
  exact hω' (mono_basis hs (fun b hb hωb => by
    by_contra h
    exact hcon ⟨b, hb, hωb, h⟩) hω)

theorem sat_theo (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hB : IsBasis D.stmts B)
    {ω ω' : Ω} (h : ∀ b ∈ B, ω ∈ b ↔ ω' ∈ b) {s : Set Ω}
    (hs : NegFinConjCountDisj D.stmts s) : (ω ∈ s ↔ ω' ∈ s) := by
  induction hs with
  | basic hb =>
    exact ⟨mono_basis (hB.2 _ hb) (fun b hb => (h b hb).1),
      mono_basis (hB.2 _ hb) (fun b hb => (h b hb).2)⟩
  | univ => simp
  | compl _ ih => simp only [Set.mem_compl_iff]; exact not_congr ih
  | inter _ _ ih1 ih2 => simp only [Set.mem_inter_iff]; exact and_congr ih1 ih2
  | iUnion f _ ih => simp only [Set.mem_iUnion]; exact exists_congr ih

theorem theo_iInter (D : ExperimentalDomain Ω) (g : ℕ → Set Ω)
    (hg : ∀ i, g i ∈ D.theoretical) : (⋂ i, g i) ∈ D.theoretical := by
  have : (⋂ i, g i) = (⋃ i, (g i)ᶜ)ᶜ := by simp [Set.compl_iUnion]
  rw [this]
  exact NegFinConjCountDisj.compl
    (NegFinConjCountDisj.iUnion _ fun i => NegFinConjCountDisj.compl (hg i))

theorem poss_sub (D : ExperimentalDomain Ω) (x : D.Possibility) {s : Set Ω}
    (hs : s ∈ D.theoretical) (h : (x.val ∩ s).Nonempty) : x.val ⊆ s := by
  rcases x.isPossibility.2.2 s hs with h1 | h1
  · exact h1
  · exact absurd h (Set.not_nonempty_iff_eq_empty.2 (Set.disjoint_iff_inter_eq_empty.1 h1))

theorem poss_ext (D : ExperimentalDomain Ω) {x y : D.Possibility} (h : x.val = y.val) :
    x = y := by
  cases x; cases y; cases h; rfl

theorem exists_poss (D : ExperimentalDomain Ω) (ω' : Ω) :
    ∃ y : D.Possibility, ω' ∈ y.val := by
  classical
  obtain ⟨B, hBc, hB⟩ := D.exists_countable_basis
  have hB' : (insert Set.univ B).Countable := hBc.insert _
  obtain ⟨e, he⟩ := hB'.exists_eq_range (Set.insert_nonempty _ _)
  have heB : ∀ i, e i ∈ insert Set.univ B := fun i => by rw [he]; exact Set.mem_range_self i
  let A : Set Ω := ⋂ i, (if ω' ∈ e i then e i else (e i)ᶜ)
  have hi : ∀ ω i, (ω ∈ (if ω' ∈ e i then e i else (e i)ᶜ)) ↔ (ω ∈ e i ↔ ω' ∈ e i) := by
    intro ω i
    split_ifs with h <;> simp [h]
  have hmemA : ∀ ω, ω ∈ A → ∀ b ∈ B, ω ∈ b ↔ ω' ∈ b := by
    intro ω hω b hb
    have hbr : b ∈ Set.range e := by rw [← he]; exact Set.mem_insert_of_mem _ hb
    obtain ⟨i, rfl⟩ := hbr
    exact (hi ω i).1 (Set.mem_iInter.1 hω i)
  have hω'A : ω' ∈ A := by
    refine Set.mem_iInter.2 fun i => ?_
    exact (hi ω' i).2 Iff.rfl
  have hA : A ∈ D.theoretical := by
    apply theo_iInter
    intro i
    have hst : e i ∈ D.stmts := by
      rcases Set.mem_insert_iff.1 (heB i) with h1 | h1
      · rw [h1]; exact D.univ_mem
      · exact hB.1 h1
    split_ifs
    · exact NegFinConjCountDisj.basic hst
    · exact NegFinConjCountDisj.compl (NegFinConjCountDisj.basic hst)
  refine ⟨⟨A, hA, ⟨ω', hω'A⟩, fun s hs => ?_⟩, hω'A⟩
  by_cases hω's : ω' ∈ s
  · left
    intro ω hω
    exact (sat_theo D hB (hmemA ω hω) hs).2 hω's
  · right
    exact Set.disjoint_left.2 fun ω hω hs' => hω's ((sat_theo D hB (hmemA ω hω) hs).1 hs')


theorem fin_poss (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hBf : B.Finite)
    (hB : IsBasis D.stmts B) : Finite D.Possibility := by
  haveI : Finite B := hBf.to_subtype
  let φ : D.Possibility → (B → Prop) := fun x b => x.isPossibility.2.1.some ∈ (b : Set Ω)
  refine Finite.of_injective φ ?_
  intro x y hxy
  have hω := x.isPossibility.2.1.some_mem
  have hω' := y.isPossibility.2.1.some_mem
  have h : ∀ b ∈ B, x.isPossibility.2.1.some ∈ b ↔ y.isPossibility.2.1.some ∈ b := by
    intro b hb
    have := congrFun hxy ⟨b, hb⟩
    simp only [φ] at this
    rw [this]
  have hxT : NegFinConjCountDisj D.stmts x.val := x.isPossibility.1
  have hyT : NegFinConjCountDisj D.stmts y.val := y.isPossibility.1
  have h1 : y.isPossibility.2.1.some ∈ x.val := (sat_theo D hB h hxT).1 hω
  have h2 : x.isPossibility.2.1.some ∈ y.val := (sat_theo D hB h hyT).2 hω'
  apply poss_ext
  apply Set.Subset.antisymm
  · exact poss_sub D x y.isPossibility.1 ⟨_, hω, h2⟩
  · exact poss_sub D y x.isPossibility.1 ⟨_, hω', h1⟩

theorem stmts_fin (D : ExperimentalDomain Ω) [Finite D.Possibility] : D.stmts.Finite := by
  obtain ⟨B, -, hB⟩ := D.exists_countable_basis
  have key : ∀ s t : Set Ω, s ∈ D.theoretical → t ∈ D.theoretical →
      D.verifiableSet s ⊆ D.verifiableSet t → s ⊆ t := by
    intro s t hs ht hst ω hωs
    obtain ⟨y, hy⟩ := exists_poss D ω
    have hys : y ∈ D.verifiableSet s := ⟨ω, hy, hωs⟩
    obtain ⟨ω', hω'y, hω't⟩ := hst hys
    have hyt : y.val ⊆ t := poss_sub D y ht ⟨ω', hω'y, hω't⟩
    exact hyt hy
  refine Set.Finite.of_finite_image (f := D.verifiableSet) (Set.toFinite _) ?_
  intro s hs t ht hst
  exact Set.Subset.antisymm
    (key s t (NegFinConjCountDisj.basic hs) (NegFinConjCountDisj.basic ht) hst.le)
    (key t s (NegFinConjCountDisj.basic ht) (NegFinConjCountDisj.basic hs) hst.ge)

end P8135

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) :
    List.TFAE [Finite D.Possibility, D.stmts.Finite,
      ∃ B : Set (Set Ω), B.Finite ∧ IsBasis D.stmts B] := by
  tfae_have 1 → 2 := fun h => P8135.stmts_fin D
  tfae_have 2 → 3 := fun h => ⟨D.stmts, h, subset_refl _, fun s hs => FinConjCountDisj.basic hs⟩
  tfae_have 3 → 1 := fun ⟨B, hBf, hB⟩ => P8135.fin_poss D hBf hB
  tfae_finish
