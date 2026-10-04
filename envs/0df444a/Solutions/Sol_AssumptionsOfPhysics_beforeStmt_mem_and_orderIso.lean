-- Prove2me | solution 1 for AssumptionsOfPhysics.beforeStmt_mem_and_orderIso
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:33:33.218125+00:00
-- url     : https://prove2.me/submissions/2f4d5c8a-3ab7-402d-acdd-05ace7e5a843

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

set_option autoImplicit false

namespace P2MAux_aa0dcf2b
open AssumptionsOfPhysics

universe u

variable {Ω : Type u}

/-- Finite intersections of members of `B`. -/
def finInters (B : Set (Set Ω)) : Set (Set Ω) :=
  (fun t => ⋂₀ t) '' {t | t.Finite ∧ t ⊆ B}

lemma finInters_countable {B : Set (Set Ω)} (hB : B.Countable) : (finInters B).Countable :=
  (Set.countable_ofPred_finite_subset hB).image _

lemma univ_mem_finInters (B : Set (Set Ω)) : Set.univ ∈ finInters B :=
  ⟨∅, ⟨Set.finite_empty, Set.empty_subset _⟩, Set.sInter_empty⟩

lemma mem_finInters_of_mem {B : Set (Set Ω)} {b : Set Ω} (hb : b ∈ B) : b ∈ finInters B :=
  ⟨{b}, ⟨Set.finite_singleton b, Set.singleton_subset_iff.mpr hb⟩, Set.sInter_singleton b⟩

lemma inter_mem_finInters {B : Set (Set Ω)} {c d : Set Ω} (hc : c ∈ finInters B)
    (hd : d ∈ finInters B) : c ∩ d ∈ finInters B := by
  obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hc
  obtain ⟨v, ⟨hv1, hv2⟩, rfl⟩ := hd
  exact ⟨t ∪ v, ⟨ht1.union hv1, Set.union_subset ht2 hv2⟩, Set.sInter_union t v⟩

lemma finInters_subset_stmts (D : ExperimentalDomain Ω) {B : Set (Set Ω)}
    (hB : B ⊆ D.stmts) : finInters B ⊆ D.stmts := by
  rintro c ⟨t, ⟨ht1, ht2⟩, rfl⟩
  revert ht2
  refine Set.Finite.induction_on (motive := fun t _ => t ⊆ B → ⋂₀ t ∈ D.stmts) t ht1 ?_ ?_
  · intro _
    simpa using D.univ_mem
  · intro a s _ _ ih hs
    rw [Set.sInter_insert]
    exact D.inter_mem _ _ (hB (hs (Set.mem_insert _ _)))
      (ih (fun x hx => hs (Set.mem_insert_of_mem _ hx)))

lemma countable_sUnion_mem (D : ExperimentalDomain Ω) {T : Set (Set Ω)} (hT : T.Countable)
    (hs : T ⊆ D.stmts) : ⋃₀ T ∈ D.stmts := by
  rcases T.eq_empty_or_nonempty with h | h
  · rw [h, Set.sUnion_empty]; exact D.empty_mem
  · obtain ⟨f, rfl⟩ := hT.exists_eq_range h
    rw [Set.sUnion_range]
    exact D.iUnion_mem f (fun n => hs (Set.mem_range_self n))

lemma exists_finInters_of_fcd {B : Set (Set Ω)} {s : Set Ω} (hs : FinConjCountDisj B s) :
    ∀ ω ∈ s, ∃ c ∈ finInters B, ω ∈ c ∧ c ⊆ s := by
  induction hs with
  | basic hb => exact fun ω hω => ⟨_, mem_finInters_of_mem hb, hω, le_rfl⟩
  | univ => exact fun ω _ => ⟨Set.univ, univ_mem_finInters B, trivial, le_rfl⟩
  | empty => exact fun ω hω => by simp at hω
  | inter _ _ ih1 ih2 =>
    rintro ω ⟨h1, h2⟩
    obtain ⟨c, hc, hωc, hcs⟩ := ih1 ω h1
    obtain ⟨d, hd, hωd, hdt⟩ := ih2 ω h2
    exact ⟨c ∩ d, inter_mem_finInters hc hd, ⟨hωc, hωd⟩, Set.inter_subset_inter hcs hdt⟩
  | iUnion f _ ih =>
    intro ω hω
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
    obtain ⟨c, hc, hωc, hcs⟩ := ih n ω hn
    exact ⟨c, hc, hωc, hcs.trans (Set.subset_iUnion f n)⟩

/-- Two points with the same membership pattern in `B`. -/
def SameSig (B : Set (Set Ω)) (ω₁ ω₂ : Ω) : Prop := ∀ b ∈ B, ω₁ ∈ b ↔ ω₂ ∈ b

lemma fcd_inv {B : Set (Set Ω)} {s : Set Ω} (hs : FinConjCountDisj B s) {ω₁ ω₂ : Ω}
    (h : SameSig B ω₁ ω₂) : ω₁ ∈ s ↔ ω₂ ∈ s := by
  induction hs with
  | basic hb => exact h _ hb
  | univ => simp
  | empty => simp
  | inter _ _ ih1 ih2 => simp only [Set.mem_inter_iff, ih1, ih2]
  | iUnion f _ ih => simp only [Set.mem_iUnion, ih]

lemma theo_inv (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hB : IsBasis D.stmts B)
    {s : Set Ω} (hs : NegFinConjCountDisj D.stmts s) {ω₁ ω₂ : Ω}
    (h : SameSig B ω₁ ω₂) : ω₁ ∈ s ↔ ω₂ ∈ s := by
  induction hs with
  | basic hb => exact fcd_inv (hB.2 _ hb) h
  | univ => simp
  | compl _ ih => simp only [Set.mem_compl_iff, ih]
  | inter _ _ ih1 ih2 => simp only [Set.mem_inter_iff, ih1, ih2]
  | iUnion f _ ih => simp only [Set.mem_iUnion, ih]

lemma exists_possibility (D : ExperimentalDomain Ω) (ω : Ω) :
    ∃ x : D.Possibility, ω ∈ x.val := by
  classical
  obtain ⟨B, hBc, hB⟩ := D.exists_countable_basis
  obtain ⟨f, hf⟩ := (hBc.insert Set.univ).exists_eq_range (Set.insert_nonempty _ _)
  let m : Set Ω := {ω' | ∀ n, ω ∈ f n ↔ ω' ∈ f n}
  let g : ℕ → Set Ω := fun n => if ω ∈ f n then f n else (f n)ᶜ
  have hmg : m = ⋂ n, g n := by
    ext ω'
    simp only [m, g, Set.mem_setOf_eq, Set.mem_iInter]
    refine forall_congr' (fun n => ?_)
    by_cases h : ω ∈ f n <;> simp [h]
  have hsig : ∀ ω' ∈ m, SameSig B ω ω' := by
    intro ω' hω' b hb
    have : b ∈ Set.range f := hf ▸ Set.mem_insert_of_mem _ hb
    obtain ⟨n, rfl⟩ := this
    exact hω' n
  have hg : ∀ n, NegFinConjCountDisj D.stmts (g n) := by
    intro n
    have hfn : f n ∈ insert Set.univ B := hf ▸ Set.mem_range_self n
    have hb : NegFinConjCountDisj D.stmts (f n) := by
      rcases hfn with h1 | h1
      · rw [h1]; exact NegFinConjCountDisj.univ
      · exact NegFinConjCountDisj.basic (hB.1 h1)
    simp only [g]
    split_ifs
    · exact hb
    · exact NegFinConjCountDisj.compl hb
  have hm : D.IsPossibility m := by
    refine ⟨?_, ⟨ω, fun n => Iff.rfl⟩, ?_⟩
    · show NegFinConjCountDisj D.stmts m
      rw [hmg, ← compl_compl (⋂ n, g n), Set.compl_iInter]
      exact NegFinConjCountDisj.compl
        (NegFinConjCountDisj.iUnion _ (fun n => NegFinConjCountDisj.compl (hg n)))
    · intro s hs
      by_cases hωs : ω ∈ s
      · left
        intro ω' hω'
        exact (theo_inv D hB hs (hsig ω' hω')).mp hωs
      · right
        rw [Set.disjoint_left]
        intro ω' hω' hω's
        exact hωs ((theo_inv D hB hs (hsig ω' hω')).mpr hω's)
  exact ⟨⟨m, hm⟩, fun n => Iff.rfl⟩

lemma sub_of_meet (D : ExperimentalDomain Ω) (x : D.Possibility) {c : Set Ω}
    (hc : c ∈ D.stmts) (h : (x.val ∩ c).Nonempty) : x.val ⊆ c :=
  (x.isPossibility.2.2 c (NegFinConjCountDisj.basic hc)).resolve_right
    (fun hd => h.ne_empty hd.inter_eq)

lemma poss_eq_of_meet (D : ExperimentalDomain Ω) {x y : D.Possibility}
    (h : (x.val ∩ y.val).Nonempty) : x = y := by
  have h1 : x.val ⊆ y.val := (x.isPossibility.2.2 y.val y.isPossibility.1).resolve_right
    (fun hd => h.ne_empty hd.inter_eq)
  have h2 : y.val ⊆ x.val := (y.isPossibility.2.2 x.val x.isPossibility.1).resolve_right
    (fun hd => h.ne_empty (by rw [Set.inter_comm]; exact hd.inter_eq))
  have : x.val = y.val := Set.Subset.antisymm h1 h2
  cases x
  cases y
  simp only at this
  subst this
  rfl

lemma nbhd (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hB : IsBasis D.stmts B)
    (O : Set D.Possibility) (hO : IsOpen O) :
    ∀ x ∈ O, ∃ c ∈ finInters B, (x.val ∩ c).Nonempty ∧ D.verifiableSet c ⊆ O := by
  have hO' : TopologicalSpace.GenerateOpen (D.verifiableSet '' D.stmts) O := hO
  clear hO
  induction hO' with
  | basic s hs =>
    obtain ⟨t, ht, rfl⟩ := hs
    intro x hx
    obtain ⟨ω, hω1, hω2⟩ := hx
    obtain ⟨c, hc, hωc, hct⟩ := exists_finInters_of_fcd (hB.2 t ht) ω hω2
    refine ⟨c, hc, ⟨ω, hω1, hωc⟩, ?_⟩
    intro y hy
    obtain ⟨ω', h1, h2⟩ := hy
    exact ⟨ω', h1, hct h2⟩
  | univ =>
    intro x _
    obtain ⟨ω, hω⟩ := x.isPossibility.2.1
    exact ⟨Set.univ, univ_mem_finInters B, ⟨ω, hω, trivial⟩, Set.subset_univ _⟩
  | inter s t _ _ ih1 ih2 =>
    rintro x ⟨hxs, hxt⟩
    obtain ⟨c, hc, hxc, hcs⟩ := ih1 x hxs
    obtain ⟨d, hd, hxd, hdt⟩ := ih2 x hxt
    have h1 : x.val ⊆ c := sub_of_meet D x (finInters_subset_stmts D hB.1 hc) hxc
    have h2 : x.val ⊆ d := sub_of_meet D x (finInters_subset_stmts D hB.1 hd) hxd
    obtain ⟨ω, hω⟩ := x.isPossibility.2.1
    refine ⟨c ∩ d, inter_mem_finInters hc hd, ⟨ω, hω, h1 hω, h2 hω⟩, fun y hy => ⟨hcs ?_, hdt ?_⟩⟩
    · obtain ⟨ω', h1', h2'⟩ := hy; exact ⟨ω', h1', h2'.1⟩
    · obtain ⟨ω', h1', h2'⟩ := hy; exact ⟨ω', h1', h2'.2⟩
  | sUnion S _ ih =>
    rintro x ⟨T, hT, hxT⟩
    obtain ⟨c, hc, hxc, hcT⟩ := ih T hT x hxT
    exact ⟨c, hc, hxc, hcT.trans (Set.subset_sUnion_of_mem hT)⟩

end P2MAux_aa0dcf2b

open P2MAux_aa0dcf2b

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω)
    (r : LinearOrder D.Possibility) (hr : D.IsNaturalOrder r) :
    (∀ x₁ : D.Possibility, D.beforeStmt r x₁ ∈ D.stmts) ∧
      ∀ x₁ x₂ : D.Possibility, r.le x₁ x₂ ↔ D.beforeStmt r x₁ ⊆ D.beforeStmt r x₂ := by
  obtain ⟨B, hBc, hB⟩ := D.exists_countable_basis
  letI := r
  constructor
  · intro x₁
    have hopen : IsOpen {x : D.Possibility | x < x₁} := by
      have h : @IsOpen _ (Preorder.topology D.Possibility) {x : D.Possibility | x < x₁} :=
        TopologicalSpace.isOpen_generateFrom_of_mem ⟨x₁, Or.inr rfl⟩
      have hr' : Preorder.topology D.Possibility = D.naturalTopology := hr
      rw [hr'] at h
      exact h
    let T := {c ∈ finInters B | D.verifiableSet c ⊆ {x | x < x₁}}
    have hTc : T.Countable := (finInters_countable hBc).mono (fun c hc => hc.1)
    have heq : D.beforeStmt r x₁ = ⋃₀ T := by
      ext ω
      constructor
      · intro hω
        obtain ⟨x, hx, hωx⟩ := Set.mem_iUnion₂.mp hω
        obtain ⟨c, hc, hxc, hcU⟩ := nbhd D hB _ hopen x hx
        have hsub := sub_of_meet D x (finInters_subset_stmts D hB.1 hc) hxc
        exact ⟨c, ⟨hc, hcU⟩, hsub hωx⟩
      · rintro ⟨c, ⟨hc, hcU⟩, hωc⟩
        obtain ⟨x, hωx⟩ := exists_possibility D ω
        have hx : x ∈ D.verifiableSet c := ⟨ω, hωx, hωc⟩
        exact Set.mem_iUnion₂.mpr ⟨x, hcU hx, hωx⟩
    rw [heq]
    exact countable_sUnion_mem D hTc (fun c hc => finInters_subset_stmts D hB.1 hc.1)
  · intro x₁ x₂
    constructor
    · intro hle ω hω
      obtain ⟨x, hx, hωx⟩ := Set.mem_iUnion₂.mp hω
      exact Set.mem_iUnion₂.mpr ⟨x, lt_of_lt_of_le (show x < x₁ from hx) hle, hωx⟩
    · intro hsub
      by_contra hnot
      have hlt : x₂ < x₁ := not_le.mp hnot
      obtain ⟨ω, hω⟩ := x₂.isPossibility.2.1
      have h1 : ω ∈ D.beforeStmt r x₁ := Set.mem_iUnion₂.mpr ⟨x₂, hlt, hω⟩
      obtain ⟨x, hx, hωx⟩ := Set.mem_iUnion₂.mp (hsub h1)
      have hxe : x = x₂ := poss_eq_of_meet D ⟨ω, hωx, hω⟩
      subst hxe
      exact lt_irrefl x (show x < x from hx)
