-- Prove2me | solution 1 for AssumptionsOfPhysics.t1Space_iff_approxVerifiable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:19:25.323616+00:00
-- url     : https://prove2.me/submissions/3ab6893f-053d-4eb3-ada8-e2b76a12c113

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

set_option autoImplicit false

namespace P711

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

theorem open_basic (D : ExperimentalDomain Ω) (W : Set D.Possibility) (hW : IsOpen W) :
    ∀ x ∈ W, ∃ s ∈ D.stmts, x ∈ D.verifiableSet s ∧ D.verifiableSet s ⊆ W := by
  change TopologicalSpace.GenerateOpen (D.verifiableSet '' D.stmts) W at hW
  induction hW with
  | basic W hW =>
    intro x hx
    obtain ⟨s, hs, rfl⟩ := hW
    exact ⟨s, hs, hx, le_rfl⟩
  | univ =>
    intro x _
    refine ⟨Set.univ, D.univ_mem, ?_, Set.subset_univ _⟩
    show (x.val ∩ Set.univ).Nonempty
    rw [Set.inter_univ]
    exact x.isPossibility.2.1
  | inter W1 W2 _ _ ih1 ih2 =>
    intro x hx
    obtain ⟨s1, hs1, hx1, h1⟩ := ih1 x hx.1
    obtain ⟨s2, hs2, hx2, h2⟩ := ih2 x hx.2
    refine ⟨s1 ∩ s2, D.inter_mem _ _ hs1 hs2, ?_, ?_⟩
    · have sub1 := poss_sub D x (NegFinConjCountDisj.basic hs1) hx1
      have sub2 := poss_sub D x (NegFinConjCountDisj.basic hs2) hx2
      obtain ⟨ω, hω⟩ := x.isPossibility.2.1
      exact ⟨ω, hω, sub1 hω, sub2 hω⟩
    · intro y hy
      have hy' : (y.val ∩ (s1 ∩ s2)).Nonempty := hy
      obtain ⟨ω, hω⟩ := hy'
      exact ⟨h1 ⟨ω, hω.1, hω.2.1⟩, h2 ⟨ω, hω.1, hω.2.2⟩⟩
  | sUnion K _ ih =>
    intro x hx
    obtain ⟨W, hWK, hxW⟩ := Set.mem_sUnion.1 hx
    obtain ⟨s, hs, hxs, hsub⟩ := ih W hWK x hxW
    exact ⟨s, hs, hxs, hsub.trans (Set.subset_sUnion_of_mem hWK)⟩

theorem main (D : ExperimentalDomain Ω) :
    T1Space D.Possibility ↔ ∀ x : D.Possibility, D.IsApproxVerifiable x.val := by
  constructor
  · intro hT x
    obtain ⟨B, hBc, hB⟩ := D.exists_countable_basis
    let C : Set (Set Ω) := insert Set.univ {b ∈ B | x.val ⊆ b}
    have hCc : C.Countable := (hBc.mono (fun b hb => hb.1)).insert _
    obtain ⟨f, hf⟩ := hCc.exists_eq_range (Set.insert_nonempty _ _)
    have hfC : ∀ i, f i ∈ C := fun i => by rw [hf]; exact Set.mem_range_self i
    refine ⟨x.isPossibility.1, f, fun i => ?_, ?_⟩
    · rcases Set.mem_insert_iff.1 (hfC i) with h | h
      · rw [h]; exact D.univ_mem
      · exact hB.1 h.1
    · apply Set.Subset.antisymm
      · intro ω hω
        refine Set.mem_iInter.2 fun i => ?_
        rcases Set.mem_insert_iff.1 (hfC i) with h | h
        · rw [h]; trivial
        · exact h.2 hω
      · intro ω' hω'
        by_contra hnot
        obtain ⟨y, hy⟩ := exists_poss D ω'
        have hxy : x ≠ y := by
          intro h
          subst h
          exact hnot hy
        obtain ⟨W, hWo, hxW, hyW⟩ := (t1Space_iff_exists_open.1 hT) hxy
        obtain ⟨s, hs, hxs, hsW⟩ := open_basic D W hWo x hxW
        have hxs' : (x.val ∩ s).Nonempty := hxs
        obtain ⟨ω, hωx, hωs⟩ := hxs'
        have hω's : ω' ∉ s := fun h => hyW (hsW ⟨ω', hy, h⟩)
        obtain ⟨b, hbB, hωb, hω'b⟩ := sep_basis (hB.2 s hs) hωs hω's
        have hxb : x.val ⊆ b :=
          poss_sub D x (NegFinConjCountDisj.basic (hB.1 hbB)) ⟨ω, hωx, hωb⟩
        have hbC : b ∈ C := Set.mem_insert_of_mem _ ⟨hbB, hxb⟩
        rw [hf] at hbC
        obtain ⟨i, rfl⟩ := hbC
        exact hω'b (Set.mem_iInter.1 hω' i)
  · intro hA
    rw [t1Space_iff_exists_open]
    intro x y hxy
    obtain ⟨_, f, hf, hxf⟩ := hA x
    have hnsub : ¬ y.val ⊆ x.val := by
      intro hyx
      rcases x.isPossibility.2.2 y.val y.isPossibility.1 with h | h
      · exact hxy (poss_ext D (Set.Subset.antisymm h hyx))
      · obtain ⟨ω, hω⟩ := y.isPossibility.2.1
        exact Set.disjoint_left.1 h (hyx hω) hω
    obtain ⟨ω', hω'y, hω'x⟩ := Set.not_subset.1 hnsub
    rw [hxf] at hω'x
    obtain ⟨i, hi⟩ : ∃ i, ω' ∉ f i := by simpa [Set.mem_iInter] using hω'x
    refine ⟨D.verifiableSet (f i),
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨f i, hf i, rfl⟩, ?_, ?_⟩
    · obtain ⟨ω, hω⟩ := x.isPossibility.2.1
      refine ⟨ω, hω, ?_⟩
      have : ω ∈ ⋂ i, f i := hxf ▸ hω
      exact Set.mem_iInter.1 this i
    · intro hy
      exact hi (poss_sub D y (NegFinConjCountDisj.basic (hf i)) hy hω'y)

end P711

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) :
    T1Space D.Possibility ↔ ∀ x : D.Possibility, D.IsApproxVerifiable x.val := by
  exact P711.main D

#print axioms solution
