-- Prove2me | solution 1 for AssumptionsOfPhysics.isDecidable_iff_discrete_quantity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:53:25.563407+00:00
-- url     : https://prove2.me/submissions/322263d0-b2b5-4d71-9572-35a5f7e49d9f

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

set_option autoImplicit false

namespace AoP029

open AssumptionsOfPhysics

universe u

variable {Ω : Type u}

lemma theo_iInter (D : ExperimentalDomain Ω) (f : ℕ → Set Ω)
    (hf : ∀ n, f n ∈ D.theoretical) : (⋂ n, f n) ∈ D.theoretical := by
  have h : (⋂ n, f n) = (⋃ n, (f n)ᶜ)ᶜ := by rw [Set.compl_iUnion]; simp
  rw [h]
  exact NegFinConjCountDisj.compl
    (NegFinConjCountDisj.iUnion _ fun n => NegFinConjCountDisj.compl (hf n))

lemma theo_sInter (D : ExperimentalDomain Ω) {S : Set (Set Ω)} (hS : S.Countable)
    (h : ∀ s ∈ S, s ∈ D.theoretical) : ⋂₀ S ∈ D.theoretical := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Set.sInter_empty]; exact NegFinConjCountDisj.univ
  · obtain ⟨f, rfl⟩ := hS.exists_eq_range hne
    rw [Set.sInter_range]
    exact theo_iInter D f (fun n => h _ ⟨n, rfl⟩)

lemma stmts_sUnion (D : ExperimentalDomain Ω) {S : Set (Set Ω)} (hS : S.Countable)
    (h : ∀ s ∈ S, s ∈ D.stmts) : ⋃₀ S ∈ D.stmts := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Set.sUnion_empty]; exact D.empty_mem
  · obtain ⟨f, rfl⟩ := hS.exists_eq_range hne
    rw [Set.sUnion_range]
    exact D.iUnion_mem f (fun n => h _ ⟨n, rfl⟩)

lemma fccd_sUnion {B S : Set (Set Ω)} (hS : S.Countable)
    (h : ∀ s ∈ S, FinConjCountDisj B s) : FinConjCountDisj B (⋃₀ S) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [Set.sUnion_empty]; exact FinConjCountDisj.empty
  · obtain ⟨f, rfl⟩ := hS.exists_eq_range hne
    rw [Set.sUnion_range]
    exact FinConjCountDisj.iUnion f (fun n => h _ ⟨n, rfl⟩)

lemma fccd_resp {B : Set (Set Ω)} {ω ω' : Ω} (hB : ∀ b ∈ B, (ω' ∈ b ↔ ω ∈ b))
    {s : Set Ω} (hs : FinConjCountDisj B s) : (ω' ∈ s ↔ ω ∈ s) := by
  induction hs with
  | basic hb => exact hB _ hb
  | univ => simp
  | empty => simp
  | inter _ _ ih1 ih2 => simp only [Set.mem_inter_iff, ih1, ih2]
  | iUnion f _ ih => simp only [Set.mem_iUnion]; exact exists_congr ih

lemma theo_resp (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hBas : IsBasis D.stmts B)
    {ω ω' : Ω} (hB : ∀ b ∈ B, (ω' ∈ b ↔ ω ∈ b))
    {s : Set Ω} (hs : s ∈ D.theoretical) : (ω' ∈ s ↔ ω ∈ s) := by
  change NegFinConjCountDisj D.stmts s at hs
  induction hs with
  | basic h => exact fccd_resp hB (hBas.2 _ h)
  | univ => simp
  | compl _ ih => simp only [Set.mem_compl_iff, ih]
  | inter _ _ ih1 ih2 => simp only [Set.mem_inter_iff, ih1, ih2]
  | iUnion f _ ih => simp only [Set.mem_iUnion]; exact exists_congr ih

def atom (B : Set (Set Ω)) (ω : Ω) : Set Ω := {ω' | ∀ b ∈ B, (ω' ∈ b ↔ ω ∈ b)}

lemma mem_atom {B : Set (Set Ω)} {ω ω' : Ω} :
    ω' ∈ atom B ω ↔ ∀ b ∈ B, (ω' ∈ b ↔ ω ∈ b) := Iff.rfl

lemma mem_atom_self (B : Set (Set Ω)) (ω : Ω) : ω ∈ atom B ω :=
  mem_atom.2 (fun _ _ => Iff.rfl)

open Classical in
lemma atom_eq (B : Set (Set Ω)) (ω : Ω) :
    atom B ω = ⋂₀ ((fun b => if ω ∈ b then b else bᶜ) '' B) := by
  ext ω'
  rw [mem_atom, Set.mem_sInter, Set.forall_mem_image]
  apply forall₂_congr
  intro b _
  by_cases h : ω ∈ b
  · simp [h]
  · simp [h]

open Classical in
lemma atom_theo (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hc : B.Countable)
    (hBas : IsBasis D.stmts B) (ω : Ω) : atom B ω ∈ D.theoretical := by
  rw [atom_eq]
  apply theo_sInter D (hc.image _)
  rintro _ ⟨b, hb, rfl⟩
  have hbt : b ∈ D.theoretical := NegFinConjCountDisj.basic (hBas.1 hb)
  by_cases h : ω ∈ b
  · simp only [h, if_true]; exact hbt
  · simp only [h, if_false]; exact NegFinConjCountDisj.compl hbt

lemma atom_poss (D : ExperimentalDomain Ω) {B : Set (Set Ω)} (hc : B.Countable)
    (hBas : IsBasis D.stmts B) (ω : Ω) : D.IsPossibility (atom B ω) := by
  refine ⟨atom_theo D hc hBas ω, ⟨ω, mem_atom_self B ω⟩, fun s hs => ?_⟩
  by_cases h : ω ∈ s
  · left
    intro ω' hω'
    exact (theo_resp D hBas (mem_atom.1 hω') hs).2 h
  · right
    rw [Set.disjoint_left]
    intro ω' hω' h'
    exact h ((theo_resp D hBas (mem_atom.1 hω') hs).1 h')

lemma poss_eq_of_inter (D : ExperimentalDomain Ω) {x y : Set Ω} (hx : D.IsPossibility x)
    (hy : D.IsPossibility y) (h : (x ∩ y).Nonempty) : x = y := by
  rcases hx.2.2 y hy.1 with h1 | h1
  · rcases hy.2.2 x hx.1 with h2 | h2
    · exact le_antisymm h1 h2
    · exact absurd h2 (Set.not_disjoint_iff_nonempty_inter.2 (by rwa [Set.inter_comm]))
  · exact absurd h1 (Set.not_disjoint_iff_nonempty_inter.2 h)

lemma theo_eq_sUnion_poss (D : ExperimentalDomain Ω) {s : Set Ω} (hs : s ∈ D.theoretical) :
    s = ⋃₀ {x | x ∈ D.possibilities ∧ x ⊆ s} := by
  obtain ⟨B, hc, hBas⟩ := D.exists_countable_basis
  apply le_antisymm
  · intro ω hω
    have hp := atom_poss D hc hBas ω
    refine Set.mem_sUnion.2 ⟨atom B ω, ⟨hp, ?_⟩, mem_atom_self B ω⟩
    rcases hp.2.2 s hs with h | h
    · exact h
    · exact absurd hω (Set.disjoint_left.1 h (mem_atom_self B ω))
  · exact Set.sUnion_subset (fun x hx => hx.2)

lemma fccd_local {B : Set (Set Ω)} {s : Set Ω} (hs : FinConjCountDisj B s) :
    ∀ ω ∈ s, ∃ t : Set (Set Ω), t.Finite ∧ t ⊆ B ∧ ω ∈ ⋂₀ t ∧ ⋂₀ t ⊆ s := by
  induction hs with
  | @basic s hb =>
      intro ω hω
      refine ⟨{s}, Set.finite_singleton _, Set.singleton_subset_iff.2 hb, ?_, ?_⟩
      · rw [Set.sInter_singleton]; exact hω
      · rw [Set.sInter_singleton]
  | univ =>
      intro ω _
      exact ⟨∅, Set.finite_empty, Set.empty_subset _, by simp, by simp⟩
  | empty =>
      intro ω h
      simp at h
  | inter _ _ ih1 ih2 =>
      intro ω hω
      obtain ⟨t1, f1, s1, m1, k1⟩ := ih1 ω hω.1
      obtain ⟨t2, f2, s2, m2, k2⟩ := ih2 ω hω.2
      refine ⟨t1 ∪ t2, f1.union f2, Set.union_subset s1 s2, ?_, ?_⟩
      · rw [Set.sInter_union]; exact ⟨m1, m2⟩
      · rw [Set.sInter_union]; exact Set.inter_subset_inter k1 k2
  | iUnion f _ ih =>
      intro ω hω
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hω
      obtain ⟨t, ft, st, mt, kt⟩ := ih n ω hn
      exact ⟨t, ft, st, mt, kt.trans (Set.subset_iUnion f n)⟩

lemma poss_countable (D : ExperimentalDomain Ω)
    (h3 : ∀ x ∈ D.possibilities, x ∈ D.stmts) : D.possibilities.Countable := by
  classical
  obtain ⟨B, hc, hBas⟩ := D.exists_countable_basis
  have hT : {t : Set (Set Ω) | t.Finite ∧ t ⊆ B}.Countable :=
    Set.countable_ofPred_finite_subset hc
  let g : Set (Set Ω) → Set Ω := fun t =>
    if h : ∃ x ∈ D.possibilities, (⋂₀ t ∩ x).Nonempty then h.choose else ∅
  refine (hT.image g).mono ?_
  intro x hx
  have hx' : D.IsPossibility x := hx
  obtain ⟨ω, hω⟩ := hx'.2.1
  obtain ⟨t, ft, st, mt, kt⟩ := fccd_local (hBas.2 x (h3 x hx)) ω hω
  refine ⟨t, ⟨ft, st⟩, ?_⟩
  have hex : ∃ y ∈ D.possibilities, (⋂₀ t ∩ y).Nonempty := ⟨x, hx, ω, mt, hω⟩
  have hg : g t = hex.choose := dif_pos hex
  rw [hg]
  obtain ⟨hy, ω', h1, h2⟩ := hex.choose_spec
  exact poss_eq_of_inter D hy hx' ⟨ω', h2, kt h1⟩


lemma nonempty_iff_subset (D : ExperimentalDomain Ω) (x : D.Possibility) {t : Set Ω}
    (ht : t ∈ D.theoretical) : (x.val ∩ t).Nonempty ↔ x.val ⊆ t := by
  obtain ⟨_, hne, hx⟩ := x.isPossibility
  constructor
  · intro h
    rcases hx t ht with h1 | h1
    · exact h1
    · exact absurd h1 (Set.not_disjoint_iff_nonempty_inter.mpr h)
  · intro h
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, h ha⟩

lemma vs_univ (D : ExperimentalDomain Ω) : D.verifiableSet Set.univ = Set.univ := by
  ext x
  simp only [ExperimentalDomain.verifiableSet, Set.mem_setOf_eq, Set.inter_univ,
    Set.mem_univ, iff_true]
  exact x.isPossibility.2.1

lemma vs_inter (D : ExperimentalDomain Ω) {s t : Set Ω} (hs : s ∈ D.theoretical)
    (ht : t ∈ D.theoretical) :
    D.verifiableSet (s ∩ t) = D.verifiableSet s ∩ D.verifiableSet t := by
  ext x
  simp only [ExperimentalDomain.verifiableSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [nonempty_iff_subset D x hs, nonempty_iff_subset D x ht,
    nonempty_iff_subset D x (NegFinConjCountDisj.inter hs ht), Set.subset_inter_iff]

lemma poss_val_inj (D : ExperimentalDomain Ω) {x y : D.Possibility} (h : x.val = y.val) :
    x = y := by
  cases x; cases y; cases h; rfl

/-- In the decidable case the natural topology is discrete. -/
lemma isOpen_singleton_of_mem (D : ExperimentalDomain Ω)
    (h3 : ∀ x : D.Possibility, x.val ∈ D.stmts) (x : D.Possibility) :
    IsOpen ({x} : Set D.Possibility) := by
  have hU : D.verifiableSet x.val = {x} := by
    ext y
    simp only [ExperimentalDomain.verifiableSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact poss_val_inj D (poss_eq_of_inter D y.isPossibility x.isPossibility h)
    · rintro rfl
      obtain ⟨a, ha⟩ := y.isPossibility.2.1
      exact ⟨a, ha, ha⟩
  rw [← hU]
  exact TopologicalSpace.GenerateOpen.basic _ ⟨x.val, h3 x, rfl⟩

lemma val_mem_of_isOpen (D : ExperimentalDomain Ω) (x : D.Possibility)
    (ho : IsOpen ({x} : Set D.Possibility)) : x.val ∈ D.stmts := by
  have hfi : FiniteInter (D.verifiableSet '' D.stmts) :=
    ⟨⟨Set.univ, D.univ_mem, vs_univ D⟩, by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      exact ⟨s ∩ t, D.inter_mem s t hs ht,
        vs_inter D (NegFinConjCountDisj.basic hs) (NegFinConjCountDisj.basic ht)⟩⟩
  have hb : TopologicalSpace.IsTopologicalBasis (D.verifiableSet '' D.stmts) :=
    TopologicalSpace.isTopologicalBasis_of_subbasis_of_finiteInter rfl hfi
  obtain ⟨_, ⟨t, ht, rfl⟩, hxt, hsub⟩ := hb.isOpen_iff.1 ho x rfl
  have htt : t ∈ D.theoretical := NegFinConjCountDisj.basic ht
  have h1 : x.val ⊆ t := (nonempty_iff_subset D x htt).1 hxt
  have h2 : t ⊆ x.val := by
    obtain ⟨B, hc, hBas⟩ := D.exists_countable_basis
    intro ω hω
    let y : D.Possibility := ⟨atom B ω, atom_poss D hc hBas ω⟩
    have hy : y ∈ D.verifiableSet t := ⟨ω, mem_atom_self B ω, hω⟩
    have hyx : y = x := hsub hy
    have : ω ∈ y.val := mem_atom_self B ω
    rw [hyx] at this
    exact this
  rw [Set.Subset.antisymm h1 h2]
  exact ht

/-- A sparse linear order with its order topology is discrete. -/
lemma sparse_isOpen_singleton {Q : Type} [LinearOrder Q] [TopologicalSpace Q] [OrderTopology Q]
    (hs : IsSparseOrder Q) (q : Q) : IsOpen ({q} : Set Q) := by
  have hlow : ∃ A : Set Q, IsOpen A ∧ q ∈ A ∧ ∀ r ∈ A, q ≤ r := by
    by_cases h : ∃ a, a < q
    · obtain ⟨a, ha⟩ := h
      have hfin : (Set.Ico a q).Finite := (hs a q).subset Set.Ico_subset_Icc_self
      obtain ⟨p, hp, hmax⟩ := Set.exists_max_image (Set.Ico a q) id hfin ⟨a, le_refl a, ha⟩
      refine ⟨Set.Ioi p, isOpen_Ioi, hp.2, fun r hr => ?_⟩
      by_contra hrq
      push_neg at hrq
      have := hmax r ⟨le_of_lt (lt_of_le_of_lt hp.1 hr), hrq⟩
      exact absurd hr (not_lt.2 this)
    · push_neg at h
      exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun r _ => h r⟩
  have hup : ∃ A : Set Q, IsOpen A ∧ q ∈ A ∧ ∀ r ∈ A, r ≤ q := by
    by_cases h : ∃ a, q < a
    · obtain ⟨a, ha⟩ := h
      have hfin : (Set.Ioc q a).Finite := (hs q a).subset Set.Ioc_subset_Icc_self
      obtain ⟨p, hp, hmin⟩ := Set.exists_min_image (Set.Ioc q a) id hfin ⟨a, ha, le_refl a⟩
      refine ⟨Set.Iio p, isOpen_Iio, hp.1, fun r hr => ?_⟩
      by_contra hrq
      push_neg at hrq
      have := hmin r ⟨hrq, le_of_lt (lt_of_lt_of_le hr hp.2)⟩
      exact absurd hr (not_lt.2 this)
    · push_neg at h
      exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun r _ => h r⟩
  obtain ⟨A, hA, hqA, hA'⟩ := hlow
  obtain ⟨C, hC, hqC, hC'⟩ := hup
  have : ({q} : Set Q) = A ∩ C := by
    ext r
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff]
    constructor
    · rintro rfl; exact ⟨hqA, hqC⟩
    · rintro ⟨h1, h2⟩; exact le_antisymm (hC' r h2) (hA' r h1)
  rw [this]
  exact hA.inter hC

theorem dec_tfae (D : ExperimentalDomain Ω) :
    List.TFAE [D.IsDecidable, D.theoretical = D.stmts,
      ∀ x : D.Possibility, x.val ∈ D.stmts,
      D.possibilities.Countable ∧ IsBasis D.stmts D.possibilities] := by
  tfae_have 1 → 2 := by
    intro hdec
    ext s
    constructor
    · intro hs
      change NegFinConjCountDisj D.stmts s at hs
      induction hs with
      | basic h => exact h
      | univ => exact D.univ_mem
      | compl _ ih => exact hdec _ ih
      | inter _ _ ih1 ih2 => exact D.inter_mem _ _ ih1 ih2
      | iUnion f _ ih => exact D.iUnion_mem f ih
    · intro hs
      exact NegFinConjCountDisj.basic hs
  tfae_have 2 → 3 := by
    intro h x
    rw [← h]
    exact x.isPossibility.1
  tfae_have 3 → 4 := by
    intro h3
    have h3' : ∀ x ∈ D.possibilities, x ∈ D.stmts := fun x hx => h3 ⟨x, hx⟩
    have hcount := poss_countable D h3'
    refine ⟨hcount, h3', fun s hs => ?_⟩
    rw [theo_eq_sUnion_poss D (NegFinConjCountDisj.basic hs)]
    exact fccd_sUnion (hcount.mono fun x hx => hx.1)
      (fun x hx => FinConjCountDisj.basic hx.1)
  tfae_have 4 → 1 := by
    rintro ⟨hc, hsub, _⟩ s hs
    have hsc : sᶜ ∈ D.theoretical :=
      NegFinConjCountDisj.compl (NegFinConjCountDisj.basic hs)
    rw [theo_eq_sUnion_poss D hsc]
    exact stmts_sUnion D (hc.mono fun x hx => hx.1) (fun x hx => hsub hx.1)
  tfae_finish
end AoP029

open AssumptionsOfPhysics in
theorem solution {Ω : Type*} (D : ExperimentalDomain Ω) :
    D.IsDecidable ↔
      ∃ (Q : Type) (_ : LinearOrder Q) (_ : TopologicalSpace Q) (_ : OrderTopology Q),
        IsSparseOrder Q ∧ D.IsFullyCharacterizedBy Q := by
  have hT := AoP029.dec_tfae D
  constructor
  · intro hdec
    have h3 : ∀ x : D.Possibility, x.val ∈ D.stmts := (hT.out 0 2).1 hdec
    have hc : D.possibilities.Countable := AoP029.poss_countable D (fun x hx => h3 ⟨x, hx⟩)
    have : Countable D.possibilities := hc.to_subtype
    have : Countable D.Possibility :=
      Function.Injective.countable
        (f := fun x : D.Possibility => (⟨x.val, x.isPossibility⟩ : D.possibilities))
        (fun x y h => AoP029.poss_val_inj D (congrArg Subtype.val h))
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat D.Possibility
    let tQ : TopologicalSpace (Set.range f) := Preorder.topology _
    have hoQ : @OrderTopology (Set.range f) tQ _ := @OrderTopology.mk _ tQ _ rfl
    have hsp : IsSparseOrder (Set.range f) := fun a b =>
      ((Set.finite_Icc (a : ℕ) b).preimage Subtype.val_injective.injOn).subset (fun x hx => hx)
    have hdX : DiscreteTopology D.Possibility :=
      discreteTopology_iff_isOpen_singleton.2 (AoP029.isOpen_singleton_of_mem D h3)
    have hdQ : @DiscreteTopology (Set.range f) tQ :=
      (@discreteTopology_iff_isOpen_singleton (Set.range f) tQ).2
        (@AoP029.sparse_isOpen_singleton _ _ tQ hoQ hsp)
    refine ⟨Set.range f, inferInstance, tQ, hoQ, hsp,
      ⟨@Homeomorph.mk _ _ _ tQ (Equiv.ofInjective f hf) ?_ ?_⟩⟩
    · letI := tQ
      exact continuous_of_discreteTopology
    · letI := tQ
      haveI := hdQ
      exact continuous_of_discreteTopology
  · rintro ⟨Q, _, _, _, hsp, ⟨h⟩⟩
    apply (hT.out 0 2).2
    intro x
    apply AoP029.val_mem_of_isOpen D x
    have : ({x} : Set D.Possibility) = h ⁻¹' {h x} := by
      ext y
      simp [h.injective.eq_iff]
    rw [this]
    exact (AoP029.sparse_isOpen_singleton hsp (h x)).preimage h.continuous
