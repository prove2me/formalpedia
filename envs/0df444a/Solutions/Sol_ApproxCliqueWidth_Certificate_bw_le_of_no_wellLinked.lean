-- Prove2me | solution 1 for ApproxCliqueWidth.Certificate.bw_le_of_no_wellLinked
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T20:59:54.808304+00:00
-- url     : https://prove2.me/submissions/a1e9b960-15fc-47e4-bf6f-d7174f8d8dc2

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_BranchDecomp
set_option autoImplicit false
open ApproxCliqueWidth.Certificate
theorem isTree_of_parent {N : Type*} [Fintype N] [DecidableEq N] (T : SimpleGraph N) (r : N)
    (par : N → N) (ρ : N → ℕ)
    (hadj : ∀ x y, T.Adj x y ↔ ((x ≠ r ∧ par x = y) ∨ (y ≠ r ∧ par y = x)))
    (hρ : ∀ x, x ≠ r → ρ (par x) < ρ x) : T.IsTree := by
  classical
  have hconn : T.Connected := by
    have hr : ∀ x, T.Reachable x r := by
      intro x
      induction' h : ρ x using Nat.strong_induction_on with n ih generalizing x
      by_cases hx : x = r
      · subst hx; exact SimpleGraph.Reachable.refl _
      · have h1 : T.Adj x (par x) := (hadj _ _).2 (Or.inl ⟨hx, rfl⟩)
        have := ih (ρ (par x)) (h ▸ hρ x hx) (par x) rfl
        exact h1.reachable.trans this
    have : Nonempty N := ⟨r⟩
    exact ⟨fun a b => (hr a).trans (hr b).symm⟩
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  let f : {x : N // x ≠ r} → T.edgeSet := fun x =>
    ⟨s(x.1, par x.1), (hadj _ _).2 (Or.inl ⟨x.2, rfl⟩)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      have h' : s(x, par x) = s(y, par y) := congrArg Subtype.val h
      rw [Sym2.eq_iff] at h'
      rcases h' with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact Subtype.ext h1
      · exfalso
        have a1 := hρ x hx
        have a2 := hρ y hy
        rw [h2] at a1
        rw [← h1] at a2
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | _ a b =>
        rw [SimpleGraph.mem_edgeSet, hadj] at he
        rcases he with ⟨ha, hab⟩ | ⟨hb, hba⟩
        · exact ⟨⟨a, ha⟩, Subtype.ext (by simp [f, hab])⟩
        · exact ⟨⟨b, hb⟩, Subtype.ext (by simp [f, hba, Sym2.eq_swap])⟩
  have := Nat.card_congr (Equiv.ofBijective f hf)
  rw [← this, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp
  have : 0 < Fintype.card N := Fintype.card_pos_iff.2 ⟨r⟩
  omega

structure Hier {V : Type*} [Fintype V] [DecidableEq V] (F : Finset (Finset V)) : Prop where
  univ_mem : Finset.univ ∈ F
  single_mem : ∀ v : V, ({v} : Finset V) ∈ F
  nonempty : ∀ X ∈ F, X.Nonempty
  laminar : ∀ X ∈ F, ∀ Y ∈ F, Disjoint X Y ∨ X ⊆ Y ∨ Y ⊆ X
  split : ∀ X ∈ F, 2 ≤ X.card → ∃ Y ∈ F, ∃ Z ∈ F, Disjoint Y Z ∧ Y ∪ Z = X

namespace Hier
variable {V : Type*} [Fintype V] [DecidableEq V] {F : Finset (Finset V)}

open Classical in
noncomputable def parF (F : Finset (Finset V)) (X : Finset V) : Finset V :=
  if h : (F.filter (fun Z => X ⊂ Z)).Nonempty then
    (Finset.exists_min_image _ Finset.card h).choose else X

theorem parF_mem (hF : Hier F) {X : Finset V} (hX : X ∈ F) : parF F X ∈ F := by
  classical
  unfold parF
  split_ifs with h
  · exact (Finset.mem_filter.1 (Finset.exists_min_image _ Finset.card h).choose_spec.1).1
  · exact hX

theorem parF_spec (hF : Hier F) {X : Finset V} (hX : X ∈ F) (hne : X ≠ Finset.univ) :
    X ⊂ parF F X ∧ ∀ Z ∈ F, X ⊂ Z → parF F X ⊆ Z := by
  classical
  have hnon : (F.filter (fun Z => X ⊂ Z)).Nonempty :=
    ⟨Finset.univ, Finset.mem_filter.2 ⟨hF.univ_mem, Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, hne⟩⟩⟩
  have hdef : parF F X = (Finset.exists_min_image _ Finset.card hnon).choose := by
    unfold parF; rw [dif_pos hnon]
  have hs := (Finset.exists_min_image _ Finset.card hnon).choose_spec
  rw [hdef]
  obtain ⟨hP, hmin⟩ := hs
  have hP' := Finset.mem_filter.1 hP
  refine ⟨hP'.2, fun Z hZ hXZ => ?_⟩
  have hc := hmin Z (Finset.mem_filter.2 ⟨hZ, hXZ⟩)
  obtain ⟨x, hx⟩ := hF.nonempty X hX
  rcases hF.laminar _ hP'.1 Z hZ with hd | h1 | h2
  · exact absurd hd (Finset.not_disjoint_iff.2 ⟨x, hP'.2.1 hx, hXZ.1 hx⟩)
  · exact h1
  · exact (Finset.eq_of_subset_of_card_le h2 hc) ▸ Finset.Subset.refl _


theorem parF_ne (hF : Hier F) {X : Finset V} (hX : X ∈ F) (hne : X ≠ Finset.univ) :
    parF F X ≠ X := fun h => by
  have := (hF.parF_spec hX hne).1
  rw [h] at this
  exact lt_irrefl _ this

theorem child_of_split (hF : Hier F) {X Y Z M : Finset V} (hY : Y ∈ F) (hZ : Z ∈ F)
    (hd : Disjoint Y Z) (hU : Y ∪ Z = X) (hM : M ∈ F) (hMu : M ≠ Finset.univ)
    (hp : parF F M = X) : M = Y ∨ M = Z := by
  have hYne := hF.nonempty Y hY
  have hZne := hF.nonempty Z hZ
  have hMX : M ⊂ X := hp ▸ (hF.parF_spec hM hMu).1
  have hmin := (hF.parF_spec hM hMu).2
  rw [hp] at hmin
  obtain ⟨m, hm⟩ := hF.nonempty M hM
  have hmX : m ∈ Y ∪ Z := hU ▸ hMX.1 hm
  -- a symmetric core
  have core : ∀ (A B : Finset V), A ∈ F → B ∈ F → Disjoint A B → A ∪ B = X → A.Nonempty → B.Nonempty →
      m ∈ A → M = A := by
    intro A B hA hB hAB hU' hAn hBn hmA
    rcases hF.laminar M hM A hA with hd' | h1 | h2
    · exact absurd hd' (Finset.not_disjoint_iff.2 ⟨m, hm, hmA⟩)
    · rcases h1.eq_or_ssubset with h | h
      · exact h
      · exfalso
        have := hmin A hA h
        have hBsub : B ⊆ A := fun b hb => this (hU' ▸ Finset.mem_union_right _ hb)
        obtain ⟨b, hb⟩ := hBn
        exact Finset.disjoint_left.1 hAB (hBsub hb) hb
    · rcases hF.laminar M hM B hB with hd' | h3 | h4
      · -- M disjoint from B, so M ⊆ A
        apply Finset.Subset.antisymm _ h2
        intro y hy
        have hyX : y ∈ A ∪ B := hU' ▸ hMX.1 hy
        rcases Finset.mem_union.1 hyX with h | h
        · exact h
        · exact absurd h (Finset.disjoint_left.1 hd' hy)
      · exfalso
        obtain ⟨a, ha⟩ := hAn
        exact Finset.disjoint_left.1 hAB ha (h3 (h2 ha))
      · exfalso
        have : X ⊆ M := by rw [← hU']; exact Finset.union_subset h2 h4
        exact absurd hMX.2 (not_not.2 this)
  rcases Finset.mem_union.1 hmX with h | h
  · exact Or.inl (core Y Z hY hZ hd hU hYne hZne h)
  · refine Or.inr (core Z Y hZ hY hd.symm (by rw [Finset.union_comm]; exact hU) hZne hYne h)


theorem ssub_of_split {X Y Z : Finset V} (hF : Hier F) (hZ : Z ∈ F)
    (hd : Disjoint Y Z) (hU : Y ∪ Z = X) : Y ⊂ X := by
  refine ⟨hU ▸ Finset.subset_union_left, fun h => ?_⟩
  obtain ⟨z, hz⟩ := hF.nonempty Z hZ
  exact Finset.disjoint_left.1 hd (h (hU ▸ Finset.mem_union_right _ hz)) hz

theorem parF_split (hF : Hier F) {X Y Z : Finset V} (hX : X ∈ F) (hY : Y ∈ F) (hZ : Z ∈ F)
    (hd : Disjoint Y Z) (hU : Y ∪ Z = X) : parF F Y = X := by
  have hYX := ssub_of_split hF hZ hd hU
  have hYne : Y ≠ Finset.univ := fun h => by
    have := hYX.2; exact this (h ▸ Finset.subset_univ _)
  obtain ⟨hs1, hs2⟩ := hF.parF_spec hY hYne
  have hPX : parF F Y ⊆ X := hs2 X hX hYX
  have hP := hF.parF_mem hY
  apply Finset.Subset.antisymm hPX
  have hYne' := hF.nonempty Y hY
  rcases hF.laminar _ hP Z hZ with hd' | h1 | h2
  · exfalso
    have : parF F Y ⊆ Y := by
      intro p hp
      have := hU ▸ hPX hp
      rcases Finset.mem_union.1 this with h | h
      · exact h
      · exact absurd h (Finset.disjoint_left.1 hd' hp)
    exact hs1.2 this
  · exfalso
    obtain ⟨y, hy⟩ := hYne'
    exact Finset.disjoint_left.1 hd hy (h1 (hs1.1 hy))
  · rw [← hU]
    exact Finset.union_subset hs1.1 h2

end Hier

theorem reach_iso_aux {A B : Type*} (φ : A ≃ B) (G : SimpleGraph A) (H : SimpleGraph B)
    (hφ : ∀ a b, G.Adj a b ↔ H.Adj (φ a) (φ b)) (u w x y : A)
    (h : (G.deleteEdges {s(u, w)}).Reachable x y) :
    (H.deleteEdges {s(φ u, φ w)}).Reachable (φ x) (φ y) := by
  let f : (G.deleteEdges {s(u, w)}) →g (H.deleteEdges {s(φ u, φ w)}) :=
    ⟨φ, by
      intro a b hab
      rw [SimpleGraph.deleteEdges_adj] at hab ⊢
      refine ⟨(hφ _ _).1 hab.1, fun hm => hab.2 ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hm ⊢
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨φ.injective h1, φ.injective h2⟩
      · exact Or.inr ⟨φ.injective h1, φ.injective h2⟩⟩
  exact h.map f

theorem reach_iso {A B : Type*} (φ : A ≃ B) (G : SimpleGraph A) (H : SimpleGraph B)
    (hφ : ∀ a b, G.Adj a b ↔ H.Adj (φ a) (φ b)) (u w x y : A) :
    (G.deleteEdges {s(u, w)}).Reachable x y ↔
      (H.deleteEdges {s(φ u, φ w)}).Reachable (φ x) (φ y) := by
  refine ⟨reach_iso_aux φ G H hφ u w x y, fun h => ?_⟩
  have := reach_iso_aux φ.symm H G (fun a b => by simpa using (hφ (φ.symm a) (φ.symm b)).symm)
    (φ u) (φ w) (φ x) (φ y) h
  simpa using this

open Classical in
theorem exists_bd_tree {V N : Type*} [Fintype V] [Fintype N] [DecidableEq N] (T : SimpleGraph N)
    (hT : T.IsTree) (hn : 2 ≤ Fintype.card N) (hsub : ∀ t, (T.neighborSet t).ncard ≤ 3)
    (L : V → N) (hleaf : ∀ v, (T.neighborSet (L v)).ncard = 1) (hinj : Function.Injective L)
    (hsurj : ∀ t, (T.neighborSet t).ncard = 1 → ∃ v, L v = t) :
    ∃ D : BranchDecomp V, ∀ u w, D.T.Adj u w → ∃ a b, T.Adj a b ∧
      D.side u w = Finset.univ.filter
        (fun x : V => (T.deleteEdges {s(a, b)}).Reachable a (L x)) := by
  classical
  let e : N ≃ Fin (Fintype.card N) := Fintype.equivFin N
  let T' : SimpleGraph (Fin (Fintype.card N)) := T.comap e.symm
  have hiso : T' ≃g T := SimpleGraph.Iso.comap e.symm T
  have hnb : ∀ t, (T'.neighborSet t).ncard = (T.neighborSet (e.symm t)).ncard := by
    intro t
    have : T'.neighborSet t = e.symm ⁻¹' T.neighborSet (e.symm t) := by
      ext s; simp [T']
    rw [this]
    exact Set.ncard_preimage_of_injective_subset_range e.symm.injective (by simp)
  refine ⟨⟨Fintype.card N, T', (hiso.isTree_iff).2 hT, hn, fun t => ?_, fun v => e (L v), ?_, ?_, ?_⟩, ?_⟩
  · rw [hnb]; exact hsub _
  · intro v; rw [hnb]; simpa using hleaf v
  · intro v w h; exact hinj (e.injective h)
  · intro t ht
    rw [hnb] at ht
    obtain ⟨v, hv⟩ := hsurj _ ht
    exact ⟨v, by simp [hv]⟩
  · intro u w huw
    refine ⟨e.symm u, e.symm w, huw, ?_⟩
    ext x
    simp only [BranchDecomp.side, Finset.mem_filter, Finset.mem_univ, true_and]
    have := reach_iso e.symm T' T (fun a b => Iff.rfl) u w u (e (L x))
    simpa using this


theorem closed_reach {N : Type*} (G : SimpleGraph N) (S : Set N)
    (hS : ∀ a b, G.Adj a b → a ∈ S → b ∈ S) {a b : N} (h : G.Reachable a b) (ha : a ∈ S) :
    b ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons hadj p ih => exact ih (hS _ _ hadj ha)

namespace Hier
variable {V : Type*} [Fintype V] [DecidableEq V] {F : Finset (Finset V)}

abbrev Node (F : Finset (Finset V)) := {X : Finset V // X ∈ F}

noncomputable def rootN (hF : Hier F) : Node F := ⟨Finset.univ, hF.univ_mem⟩
noncomputable def parN (hF : Hier F) (x : Node F) : Node F := ⟨parF F x.1, hF.parF_mem x.2⟩
def Lnode (hF : Hier F) (x : V) : Node F := ⟨{x}, hF.single_mem x⟩

theorem ne_root_iff (hF : Hier F) (x : Node F) : x ≠ rootN hF ↔ x.1 ≠ Finset.univ := by
  simp [rootN, Subtype.ext_iff]

theorem parN_ssub (hF : Hier F) (x : Node F) (hx : x ≠ rootN hF) : x.1 ⊂ (parN hF x).1 :=
  (hF.parF_spec x.2 ((ne_root_iff hF x).1 hx)).1

theorem parN_min (hF : Hier F) (a : Node F) (ha : a ≠ rootN hF) {M : Node F}
    (hs : a.1 ⊂ M.1) : (parN hF a).1 ⊆ M.1 :=
  (hF.parF_spec a.2 ((ne_root_iff hF a).1 ha)).2 M.1 M.2 hs

noncomputable def graphN (hF : Hier F) : SimpleGraph (Node F) where
  Adj x y := (x ≠ rootN hF ∧ parN hF x = y) ∨ (y ≠ rootN hF ∧ parN hF y = x)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun x h => by
    rcases h with ⟨hx, h⟩ | ⟨hx, h⟩
    · have := parN_ssub hF x hx
      rw [h] at this
      exact lt_irrefl _ this
    · have := parN_ssub hF x hx
      rw [h] at this
      exact lt_irrefl _ this⟩

theorem isTree_graphN (hF : Hier F) : (graphN hF).IsTree := by
  refine isTree_of_parent (graphN hF) (rootN hF) (parN hF) (fun x => Fintype.card V - x.1.card)
    (fun _ _ => Iff.rfl) ?_
  intro x hx
  have h1 := Finset.card_lt_card (parN_ssub hF x hx)
  have h2 := Finset.card_le_univ (parN hF x).1
  show Fintype.card V - (parN hF x).1.card < Fintype.card V - x.1.card
  omega

end Hier


namespace Hier
variable {V : Type*} [Fintype V] [DecidableEq V] {F : Finset (Finset V)}

theorem Lnode_ne_root (hF : Hier F) (hV : 2 ≤ Fintype.card V) (v : V) :
    Lnode hF v ≠ rootN hF := by
  rw [ne_root_iff]
  intro h
  change ({v} : Finset V) = Finset.univ at h
  have : Fintype.card V = 1 := by rw [← Finset.card_univ, ← h]; exact Finset.card_singleton v
  omega

theorem nbr_single (hF : Hier F) (hV : 2 ≤ Fintype.card V) (v : V) :
    (graphN hF).neighborSet (Lnode hF v) = {parN hF (Lnode hF v)} := by
  ext y
  simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨hy, h⟩)
    · exact h.symm
    · exfalso
      have := parN_ssub hF y hy
      rw [h] at this
      have h2 : y.1 = ∅ := Finset.ssubset_singleton_iff.1 this
      exact Finset.not_nonempty_empty (h2 ▸ hF.nonempty y.1 y.2)
  · intro h
    exact Or.inl ⟨Lnode_ne_root hF hV v, h.symm⟩

theorem nbr_card_ge2 (hF : Hier F) (x : Node F) (hx : 2 ≤ x.1.card) :
    2 ≤ ((graphN hF).neighborSet x).ncard ∧ ((graphN hF).neighborSet x).ncard ≤ 3 := by
  obtain ⟨Y, hY, Z, hZ, hd, hU⟩ := hF.split x.1 x.2 hx
  let yN : Node F := ⟨Y, hY⟩
  let zN : Node F := ⟨Z, hZ⟩
  have hYX := ssub_of_split hF hZ hd hU
  have hZX : Z ⊂ x.1 :=
    ssub_of_split hF hY hd.symm (by rw [Finset.union_comm]; exact hU)
  have hYne : yN ≠ rootN hF := by
    rw [ne_root_iff]; intro h
    exact hYX.2 (by rw [show Y = Finset.univ from h]; exact Finset.subset_univ _)
  have hZne : zN ≠ rootN hF := by
    rw [ne_root_iff]; intro h
    exact hZX.2 (by rw [show Z = Finset.univ from h]; exact Finset.subset_univ _)
  have hyx : parN hF yN = x := Subtype.ext (parF_split hF x.2 hY hZ hd hU)
  have hzx : parN hF zN = x :=
    Subtype.ext (parF_split hF x.2 hZ hY hd.symm (by rw [Finset.union_comm]; exact hU))
  have hyz : yN ≠ zN := by
    intro h
    have h' : Y = Z := congrArg Subtype.val h
    rw [h'] at hd
    obtain ⟨z, hz⟩ := hF.nonempty Z hZ
    exact Finset.disjoint_left.1 hd hz hz
  constructor
  · calc 2 = ({yN, zN} : Set (Node F)).ncard := (Set.ncard_pair hyz).symm
      _ ≤ _ := by
        apply Set.ncard_le_ncard _ (Set.toFinite _)
        intro t ht
        rcases ht with rfl | rfl
        · exact Or.inr ⟨hYne, hyx⟩
        · exact Or.inr ⟨hZne, hzx⟩
  · calc _ ≤ ({parN hF x, yN, zN} : Set (Node F)).ncard := by
          apply Set.ncard_le_ncard _ (Set.toFinite _)
          intro t ht
          rcases ht with ⟨_, h⟩ | ⟨ht, h⟩
          · exact Or.inl h.symm
          · have := child_of_split hF hY hZ hd hU t.2 ((ne_root_iff hF t).1 ht)
              (congrArg Subtype.val h)
            rcases this with h1 | h1
            · exact Or.inr (Or.inl (Subtype.ext h1))
            · exact Or.inr (Or.inr (Subtype.ext h1))
      _ ≤ 3 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        have := Set.ncard_insert_le yN ({zN} : Set (Node F))
        rw [Set.ncard_singleton] at this
        omega

end Hier


namespace Hier
variable {V : Type*} [Fintype V] [DecidableEq V] {F : Finset (Finset V)}

theorem card_lt_of_par (hF : Hier F) (Y : Node F) (hY : Y ≠ rootN hF) :
    Y.1.card < (parN hF Y).1.card := Finset.card_lt_card (parN_ssub hF Y hY)

theorem reach_child (hF : Hier F) (M : Node F) (hM : M ≠ rootN hF) (x : V) :
    ((graphN hF).deleteEdges {s(M, parN hF M)}).Reachable M (Lnode hF x) ↔ x ∈ M.1 := by
  constructor
  · intro h
    have := closed_reach ((graphN hF).deleteEdges {s(M, parN hF M)})
      {Y : Node F | Y.1 ⊆ M.1} ?_ h (Finset.Subset.refl _)
    · exact this (Finset.mem_singleton_self x)
    · intro a b hab ha
      rw [SimpleGraph.deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      change a.1 ⊆ M.1 at ha
      change b.1 ⊆ M.1
      rcases hadj with ⟨hane, hpar⟩ | ⟨hbne, hpar⟩
      · by_cases haM : a = M
        · subst haM
          exfalso
          apply hne
          rw [hpar]
          simp
        · have : a.1 ⊂ M.1 := ⟨ha, fun h => haM (Subtype.ext (Finset.Subset.antisymm ha h))⟩
          rw [← hpar]
          exact parN_min hF a hane this
      · have := parN_ssub hF b hbne
        rw [hpar] at this
        exact this.1.trans ha
  · intro hx
    have key : ∀ n : ℕ, ∀ Y : Node F, Fintype.card V - Y.1.card = n → x ∈ Y.1 → Y.1 ⊆ M.1 →
        ((graphN hF).deleteEdges {s(M, parN hF M)}).Reachable M Y := by
      intro n
      induction' n using Nat.strong_induction_on with n ih
      intro Y hn hxY hYM
      by_cases hYeq : Y = M
      · subst hYeq; exact SimpleGraph.Reachable.refl _
      · have hlt : Y.1 ⊂ M.1 := ⟨hYM, fun h => hYeq (Subtype.ext (Finset.Subset.antisymm hYM h))⟩
        have hYne : Y ≠ rootN hF := by
          rw [ne_root_iff]; intro h
          exact hlt.2 (by rw [h]; exact Finset.subset_univ _)
        have hP1 : (parN hF Y).1 ⊆ M.1 := parN_min hF Y hYne hlt
        have hxP : x ∈ (parN hF Y).1 := (parN_ssub hF Y hYne).1 hxY
        have hc := card_lt_of_par hF Y hYne
        have hcV := Finset.card_le_univ (parN hF Y).1
        have := ih (Fintype.card V - (parN hF Y).1.card) (by omega) (parN hF Y) rfl hxP hP1
        refine this.trans (SimpleGraph.Adj.reachable ?_)
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨Or.inr ⟨hYne, rfl⟩, ?_⟩
        intro hmem
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- parN Y = M ∧ Y = parN M
          have c1 := card_lt_of_par hF M hM
          have c2 : Y.1.card = (parN hF M).1.card := by rw [h2]
          have c3 : (parN hF Y).1.card = M.1.card := by rw [h1]
          omega
        · exact hYeq h2
    exact key _ (Lnode hF x) rfl (Finset.mem_singleton_self x) (Finset.singleton_subset_iff.2 hx)

theorem reach_up (hF : Hier F) (M : Node F) (hM : M ≠ rootN hF) :
    ∀ n : ℕ, ∀ Y : Node F, Fintype.card V - Y.1.card = n → ¬ Y.1 ⊆ M.1 →
      ((graphN hF).deleteEdges {s(parN hF M, M)}).Reachable Y (rootN hF) := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro Y hn hQ
  by_cases hY : Y = rootN hF
  · subst hY; exact SimpleGraph.Reachable.refl _
  · have hc := card_lt_of_par hF Y hY
    have hcV := Finset.card_le_univ (parN hF Y).1
    have hQ' : ¬ (parN hF Y).1 ⊆ M.1 := fun h => hQ ((parN_ssub hF Y hY).1.trans h)
    have := ih (Fintype.card V - (parN hF Y).1.card) (by omega) (parN hF Y) rfl hQ'
    refine SimpleGraph.Adj.reachable ?_ |>.trans this
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨Or.inl ⟨hY, rfl⟩, ?_⟩
    intro hmem
    rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have c1 := card_lt_of_par hF M hM
      have c2 : Y.1.card = (parN hF M).1.card := by rw [h1]
      have c3 : (parN hF Y).1.card = M.1.card := by rw [h2]
      omega
    · exact hQ (by rw [h1])

theorem reach_parent (hF : Hier F) (M : Node F) (hM : M ≠ rootN hF) (x : V) :
    ((graphN hF).deleteEdges {s(parN hF M, M)}).Reachable (parN hF M) (Lnode hF x) ↔
      x ∉ M.1 := by
  constructor
  · intro h hx
    have := closed_reach ((graphN hF).deleteEdges {s(parN hF M, M)})
      {Y : Node F | ¬ Y.1 ⊆ M.1} ?_ h ?_
    · exact this (Finset.singleton_subset_iff.2 hx)
    · intro a b hab ha
      rw [SimpleGraph.deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      change ¬ a.1 ⊆ M.1 at ha
      change ¬ b.1 ⊆ M.1
      rcases hadj with ⟨hane, hpar⟩ | ⟨hbne, hpar⟩
      · intro hb
        apply ha
        rw [← hpar] at hb
        exact (parN_ssub hF a hane).1.trans hb
      · intro hb
        by_cases hbM : b = M
        · subst hbM
          apply hne
          rw [← hpar]
          simp
        · have : b.1 ⊂ M.1 := ⟨hb, fun h => hbM (Subtype.ext (Finset.Subset.antisymm hb h))⟩
          rw [← hpar] at ha
          exact ha (parN_min hF b hbne this)
    · change ¬ (parN hF M).1 ⊆ M.1
      intro h
      exact lt_irrefl _ (lt_of_lt_of_le (card_lt_of_par hF M hM) (Finset.card_le_card h))
  · intro hx
    have h1 := reach_up hF M hM _ (parN hF M) rfl (by
      intro h
      exact lt_irrefl _ (lt_of_lt_of_le (card_lt_of_par hF M hM) (Finset.card_le_card h)))
    have h2 := reach_up hF M hM _ (Lnode hF x) rfl (by
      intro h
      exact hx (h (Finset.mem_singleton_self x)))
    exact h1.trans h2.symm

end Hier


namespace Hier
variable {V : Type*} [Fintype V] [DecidableEq V] {F : Finset (Finset V)}

theorem card_cases (hF : Hier F) (t : Node F) :
    (∃ v : V, t = Lnode hF v) ∨ 2 ≤ t.1.card := by
  have h1 : 0 < t.1.card := Finset.card_pos.2 (hF.nonempty t.1 t.2)
  by_cases h2 : t.1.card = 1
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.1 h2
    exact Or.inl ⟨v, Subtype.ext hv⟩
  · exact Or.inr (by omega)

open Classical in
theorem bwLE_of_hier (f : Finset V → ℤ) (hsym : IsSymmetric f) (hF : Hier F)
    (hV : 2 ≤ Fintype.card V) (k : ℤ) (hk : ∀ X ∈ F, f X ≤ k) : BwLE f k := by
  right
  have hnode : 2 ≤ Fintype.card (Node F) := by
    have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨v⟩ := this
    exact Fintype.one_lt_card_iff.2 ⟨Lnode hF v, rootN hF, Lnode_ne_root hF hV v⟩
  have hsub : ∀ t : Node F, ((graphN hF).neighborSet t).ncard ≤ 3 := by
    intro t
    rcases card_cases hF t with ⟨v, rfl⟩ | h
    · simp [nbr_single hF hV]
    · exact (nbr_card_ge2 hF t h).2
  have hleaf : ∀ v : V, ((graphN hF).neighborSet (Lnode hF v)).ncard = 1 := by
    intro v
    rw [nbr_single hF hV, Set.ncard_singleton]
  have hinj : Function.Injective (Lnode hF) := by
    intro v w h
    exact Finset.singleton_injective (congrArg Subtype.val h)
  have hsurj : ∀ t : Node F, ((graphN hF).neighborSet t).ncard = 1 → ∃ v, Lnode hF v = t := by
    intro t ht
    rcases card_cases hF t with ⟨v, rfl⟩ | h
    · exact ⟨v, rfl⟩
    · have := (nbr_card_ge2 hF t h).1
      omega
  obtain ⟨D, hD⟩ := exists_bd_tree (graphN hF) (isTree_graphN hF) hnode hsub (Lnode hF) hleaf hinj hsurj
  refine ⟨D, ?_⟩
  intro u w huw
  obtain ⟨a, b, hab, hside⟩ := hD u w huw
  rw [hside]
  rcases hab with ⟨ha, hpar⟩ | ⟨hb, hpar⟩
  · subst hpar
    have : Finset.univ.filter (fun x : V =>
        ((graphN hF).deleteEdges {s(a, parN hF a)}).Reachable a (Lnode hF x)) = a.1 := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact reach_child hF a ha x
    rw [this]
    exact hk _ a.2
  · subst hpar
    have : Finset.univ.filter (fun x : V =>
        ((graphN hF).deleteEdges {s(parN hF b, b)}).Reachable (parN hF b) (Lnode hF x)) =
        b.1ᶜ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      exact reach_parent hF b hb x
    rw [this, ← hsym]
    exact hk _ b.2

end Hier

namespace C3
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- rooted hierarchy of a set `A` -/
structure RH (A : Finset V) (F : Finset (Finset V)) : Prop where
  top : A ∈ F
  sub : ∀ X ∈ F, X ⊆ A
  single : ∀ v ∈ A, ({v} : Finset V) ∈ F
  nonempty : ∀ X ∈ F, X.Nonempty
  laminar : ∀ X ∈ F, ∀ Y ∈ F, Disjoint X Y ∨ X ⊆ Y ∨ Y ⊆ X
  split : ∀ X ∈ F, 2 ≤ X.card → ∃ Y ∈ F, ∃ Z ∈ F, Disjoint Y Z ∧ Y ∪ Z = X

theorem RH.single' (v : V) : RH ({v} : Finset V) {{v}} where
  top := Finset.mem_singleton_self _
  sub := by intro X hX; rw [Finset.mem_singleton.1 hX]
  single := by intro w hw; rw [Finset.mem_singleton.1 hw]; exact Finset.mem_singleton_self _
  nonempty := by intro X hX; rw [Finset.mem_singleton.1 hX]; exact Finset.singleton_nonempty v
  laminar := by
    intro X hX Y hY
    rw [Finset.mem_singleton.1 hX, Finset.mem_singleton.1 hY]
    right; left; exact le_rfl
  split := by
    intro X hX h2
    rw [Finset.mem_singleton.1 hX, Finset.card_singleton] at h2
    omega

theorem RH.join {A1 A2 : Finset V} {F1 F2 : Finset (Finset V)} (h1 : RH A1 F1) (h2 : RH A2 F2)
    (hd : Disjoint A1 A2) : RH (A1 ∪ A2) (insert (A1 ∪ A2) (F1 ∪ F2)) := by
  have key : ∀ X ∈ F1 ∪ F2, X ⊆ A1 ∪ A2 := by
    intro X hX
    rcases Finset.mem_union.1 hX with hX | hX
    · exact (h1.sub X hX).trans Finset.subset_union_left
    · exact (h2.sub X hX).trans Finset.subset_union_right
  refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX
    rcases Finset.mem_insert.1 hX with rfl | hX
    · exact le_rfl
    · exact key X hX
  · intro v hv
    apply Finset.mem_insert_of_mem
    rcases Finset.mem_union.1 hv with hv | hv
    · exact Finset.mem_union_left _ (h1.single v hv)
    · exact Finset.mem_union_right _ (h2.single v hv)
  · intro X hX
    rcases Finset.mem_insert.1 hX with rfl | hX
    · exact (h1.nonempty A1 h1.top).mono Finset.subset_union_left
    rcases Finset.mem_union.1 hX with hX | hX
    · exact h1.nonempty X hX
    · exact h2.nonempty X hX
  · intro X hX Y hY
    rcases Finset.mem_insert.1 hX with rfl | hX
    · rcases Finset.mem_insert.1 hY with rfl | hY
      · right; left; exact le_rfl
      · right; right; exact key Y hY
    rcases Finset.mem_insert.1 hY with rfl | hY
    · right; left; exact key X hX
    rcases Finset.mem_union.1 hX with hX | hX <;> rcases Finset.mem_union.1 hY with hY | hY
    · exact h1.laminar X hX Y hY
    · left; exact hd.mono (h1.sub X hX) (h2.sub Y hY)
    · left; exact (hd.mono (h1.sub Y hY) (h2.sub X hX)).symm
    · exact h2.laminar X hX Y hY
  · intro X hX hc
    rcases Finset.mem_insert.1 hX with rfl | hX
    · exact ⟨A1, Finset.mem_insert_of_mem (Finset.mem_union_left _ h1.top), A2,
        Finset.mem_insert_of_mem (Finset.mem_union_right _ h2.top), hd, rfl⟩
    rcases Finset.mem_union.1 hX with hX | hX
    · obtain ⟨Y, hY, Z, hZ, hYZ, hU⟩ := h1.split X hX hc
      exact ⟨Y, Finset.mem_insert_of_mem (Finset.mem_union_left _ hY), Z,
        Finset.mem_insert_of_mem (Finset.mem_union_left _ hZ), hYZ, hU⟩
    · obtain ⟨Y, hY, Z, hZ, hYZ, hU⟩ := h2.split X hX hc
      exact ⟨Y, Finset.mem_insert_of_mem (Finset.mem_union_right _ hY), Z,
        Finset.mem_insert_of_mem (Finset.mem_union_right _ hZ), hYZ, hU⟩

theorem exists_RH : ∀ n : ℕ, ∀ A : Finset V, A.card = n → A.Nonempty → ∃ F, RH A F := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hA hne
    obtain ⟨a, ha⟩ := hne
    have hpos := Finset.card_pos.2 ⟨a, ha⟩
    by_cases h1 : A.card = 1
    · obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 h1
      exact ⟨_, RH.single' b⟩
    · have hne2 : (A.erase a).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ha]; omega
      obtain ⟨F2, hF2⟩ := ih _ (by rw [← hA, Finset.card_erase_of_mem ha]; omega) (A.erase a) rfl hne2
      have hd : Disjoint ({a} : Finset V) (A.erase a) := by simp
      have hj := (RH.single' a).join hF2 hd
      have e : ({a} : Finset V) ∪ A.erase a = A := by
        rw [← Finset.insert_eq, Finset.insert_erase ha]
      rw [e] at hj
      exact ⟨_, hj⟩

theorem RH.hier {F : Finset (Finset V)} (h : RH (Finset.univ : Finset V) F) : Hier F where
  univ_mem := h.top
  single_mem := fun v => h.single v (Finset.mem_univ v)
  nonempty := h.nonempty
  laminar := h.laminar
  split := h.split

theorem f_nonneg {f : Finset V → ℤ} (hsym : IsSymmetric f) (hsub : IsSubmodular f) (h0 : f ∅ = 0)
    (X : Finset V) : 0 ≤ f X := by
  have h1 := hsub X Xᶜ
  have h2 := hsym X
  have h3 : f Finset.univ = 0 := by
    have := hsym ∅
    rw [Finset.compl_empty] at this
    rw [← this, h0]
  rw [Finset.inter_compl, Finset.union_compl, h0, h3] at h1
  linarith

theorem f_insert_le {f : Finset V → ℤ} (hsub : IsSubmodular f) (hnn : ∀ X, 0 ≤ f X)
    (hsingle : ∀ v : V, f {v} ≤ 1) (S : Finset V) (a : V) : f (insert a S) ≤ f S + 1 := by
  have h := hsub S {a}
  have e : S ∪ {a} = insert a S := by ext; simp [or_comm]
  rw [e] at h
  have := hnn (S ∩ {a})
  have := hsingle a
  linarith

theorem f_le_card {f : Finset V → ℤ} (hsub : IsSubmodular f) (hnn : ∀ X, 0 ≤ f X)
    (hsingle : ∀ v : V, f {v} ≤ 1) (h0 : f ∅ = 0) (T : Finset V) : f T ≤ T.card := by
  refine Finset.induction_on T ?_ ?_
  · simp [h0]
  · intro a T ha ih
    rw [Finset.card_insert_of_notMem ha]
    have := f_insert_le hsub hnn hsingle T a
    push_cast
    linarith

theorem f_union_le {f : Finset V → ℤ} (hsub : IsSubmodular f) (hnn : ∀ X, 0 ≤ f X)
    (hsingle : ∀ v : V, f {v} ≤ 1) (h0 : f ∅ = 0) (S T : Finset V) :
    f (S ∪ T) ≤ f S + ((T \ S).card : ℤ) := by
  have e : S ∪ T = S ∪ (T \ S) := by
    ext; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  have h1 := hsub S (T \ S)
  have h2 := hnn (S ∩ (T \ S))
  have h3 := f_le_card hsub hnn hsingle h0 (T \ S)
  rw [e]
  linarith

/-- Menger-type lemma: a minimum separator of `X` from `Y` has a linked subset of `X`. -/
theorem ml {f : Finset V → ℤ} (hsub : IsSubmodular f) (hnn : ∀ X, 0 ≤ f X)
    (hle : ∀ S T : Finset V, f (S ∪ T) ≤ f S + ((T \ S).card : ℤ)) {X Y Z : Finset V}
    (hXZ : X ⊆ Z) (hZY : Disjoint Z Y) (hmin : ∀ S, X ⊆ S → Disjoint S Y → f Z ≤ f S) :
    ∃ X' ⊆ X, (X'.card : ℤ) ≤ f Z ∧ ∀ S, Disjoint S Y → f Z ≤ f S + ((X' \ S).card : ℤ) := by
  classical
  have hPX : ∀ S, Disjoint S Y → f Z ≤ f S + ((X \ S).card : ℤ) := by
    intro S hS
    have h1 := hmin (S ∪ X) Finset.subset_union_right
      (Finset.disjoint_union_left.2 ⟨hS, Finset.disjoint_of_subset_left hXZ hZY⟩)
    have h2 := hle S X
    linarith
  obtain ⟨X', hX'm, hX'min⟩ := (X.powerset.filter (fun X' => ∀ S, Disjoint S Y →
      f Z ≤ f S + ((X' \ S).card : ℤ))).exists_min_image Finset.card
      ⟨X, Finset.mem_filter.2 ⟨Finset.mem_powerset_self X, hPX⟩⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hX'm
  obtain ⟨hX'X, hP⟩ := hX'm
  have hZt : Z ∈ Finset.univ.filter
      (fun S => Disjoint S Y ∧ f S + ((X' \ S).card : ℤ) = f Z) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hZY, ?_⟩
    rw [Finset.sdiff_eq_empty_iff_subset.2 (hX'X.trans hXZ)]
    simp
  obtain ⟨S0, hS0m, hS0min⟩ := (Finset.univ.filter
      (fun S => Disjoint S Y ∧ f S + ((X' \ S).card : ℤ) = f Z)).exists_min_image
      Finset.card ⟨Z, hZt⟩
  rw [Finset.mem_filter] at hS0m
  obtain ⟨-, hS0Y, hS0t⟩ := hS0m
  have hdis : Disjoint X' S0 := by
    rw [Finset.disjoint_left]
    intro x hxX hxS
    have hnP : ¬ ∀ S, Disjoint S Y → f Z ≤ f S + (((X'.erase x) \ S).card : ℤ) := by
      intro hPe
      have := hX'min (X'.erase x) (Finset.mem_filter.2
        ⟨Finset.mem_powerset.2 ((Finset.erase_subset x X').trans hX'X), hPe⟩)
      rw [Finset.card_erase_of_mem hxX] at this
      have := Finset.card_pos.2 ⟨x, hxX⟩
      omega
    push_neg at hnP
    obtain ⟨S, hSY, hSlt⟩ := hnP
    have hPS := hP S hSY
    have hxS' : x ∉ S := by
      intro hxS'
      have e : (X'.erase x) \ S = X' \ S := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
        · rintro ⟨h, h'⟩; exact ⟨⟨fun e => h' (e ▸ hxS'), h⟩, h'⟩
      rw [e] at hSlt
      linarith
    have hcard : (X' \ S).card = ((X'.erase x) \ S).card + 1 := by
      have e : X' \ S = insert x ((X'.erase x) \ S) := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨h, h'⟩
          by_cases e : y = x
          · left; exact e
          · right; exact ⟨⟨e, h⟩, h'⟩
        · rintro (rfl | ⟨⟨_, h⟩, h'⟩)
          · exact ⟨hxX, hxS'⟩
          · exact ⟨h, h'⟩
      rw [e, Finset.card_insert_of_notMem]
      simp
    have hSt : f S + ((X' \ S).card : ℤ) = f Z := by
      rw [hcard]; push_cast at hSlt ⊢; linarith
    have hi := hP (S ∩ S0) (Finset.disjoint_of_subset_left Finset.inter_subset_left hSY)
    have hu := hP (S ∪ S0) (Finset.disjoint_union_left.2 ⟨hSY, hS0Y⟩)
    have hs := hsub S S0
    have hc : ((X' \ (S ∩ S0)).card : ℤ) + ((X' \ (S ∪ S0)).card : ℤ) =
        ((X' \ S).card : ℤ) + ((X' \ S0).card : ℤ) := by
      have e1 : X' \ (S ∩ S0) = (X' \ S) ∪ (X' \ S0) := by ext; simp; tauto
      have e2 : X' \ (S ∪ S0) = (X' \ S) ∩ (X' \ S0) := by ext; simp; tauto
      rw [e1, e2]
      exact_mod_cast Finset.card_union_add_card_inter _ _
    have htight : f (S ∩ S0) + ((X' \ (S ∩ S0)).card : ℤ) = f Z := by linarith
    have hle2 := hS0min (S ∩ S0) (Finset.mem_filter.2 ⟨Finset.mem_univ _,
      Finset.disjoint_of_subset_left Finset.inter_subset_left hSY, htight⟩)
    have hlt : (S ∩ S0).card < S0.card := Finset.card_lt_card
      ⟨Finset.inter_subset_right, fun h => hxS' (Finset.mem_of_mem_inter_left (h hxS))⟩
    omega
  refine ⟨X', hX'X, ?_, hP⟩
  have e : X' \ S0 = X' := Finset.sdiff_eq_self_of_disjoint hdis
  rw [e] at hS0t
  have := hnn S0
  linarith

/-- `B` (outside `A`) carries the boundary of `A`. -/
def Link (f : Finset V → ℤ) (A B : Finset V) : Prop :=
  ∀ U, A ⊆ U → f A ≤ f U + ((U ∩ B).card : ℤ)

theorem child_link {f : Finset V → ℤ} (hsym : IsSymmetric f) (hsub : IsSubmodular f)
    {A B X Y' Z : Finset V} (hA : Link f A B) (hAB : Disjoint A B) (hXZ : X ⊆ Z)
    (hY'Z : Disjoint Y' Z) (hP : ∀ S, Disjoint S X → f Z ≤ f S + ((Y' \ S).card : ℤ)) :
    Link f (A ∩ Z) (B ∩ Z ∪ Y') := by
  intro U hU
  have h1 := hP (Zᶜ \ U) (by
    rw [Finset.disjoint_left]; intro x hx hxX
    exact (Finset.mem_compl.1 (Finset.mem_sdiff.1 hx).1) (hXZ hxX))
  have h2 : (Y' \ (Zᶜ \ U)).card ≤ (U ∩ Y').card := by
    apply Finset.card_le_card
    intro y hy
    have hyZ : y ∉ Z := Finset.disjoint_left.1 hY'Z (Finset.mem_sdiff.1 hy).1
    simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_inter] at hy ⊢
    tauto
  have h3 : f (U ∪ Z) = f (Zᶜ \ U) := by
    rw [hsym (U ∪ Z)]; congr 1; ext x; simp; tauto
  have h4 := hsub U Z
  have h5 := hsub (U ∩ Z) A
  have h6 : U ∩ Z ∩ A = A ∩ Z := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨⟨_, hz⟩, ha⟩; exact ⟨ha, hz⟩
    · rintro ⟨ha, hz⟩; exact ⟨⟨hU (Finset.mem_inter.2 ⟨ha, hz⟩), hz⟩, ha⟩
  have h7 := hA (U ∩ Z ∪ A) Finset.subset_union_right
  have h8 : (U ∩ Z ∪ A) ∩ B = U ∩ (B ∩ Z) := by
    ext x
    have := fun ha : x ∈ A => Finset.disjoint_left.1 hAB ha
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have h9 : (U ∩ (B ∩ Z ∪ Y')).card = (U ∩ (B ∩ Z)).card + (U ∩ Y').card := by
    rw [Finset.inter_union_distrib_left]
    apply Finset.card_union_of_disjoint
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_inter] at hx hx'
    exact Finset.disjoint_left.1 hY'Z hx'.2 hx.2.2
  rw [h6] at h5
  rw [h8] at h7
  rw [h9]
  push_cast
  have h2' : ((Y' \ (Zᶜ \ U)).card : ℤ) ≤ ((U ∩ Y').card : ℤ) := by exact_mod_cast h2
  linarith

end C3

namespace C3
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem main {f : Finset V → ℤ} (hsym : IsSymmetric f) (hsub : IsSubmodular f)
    (hsingle : ∀ v : V, f {v} ≤ 1) (h0 : f ∅ = 0) (k : ℕ)
    (hno : ¬ ∃ W : Finset V, W.card = k ∧ IsWellLinked f W) :
    ∀ a : ℕ, ∀ A : Finset V, A.card = a → ∀ b : ℕ, ∀ B : Finset V, B.card = b →
      A.Nonempty → Disjoint A B → b ≤ k → Link f A B →
      ∃ F, RH A F ∧ ∀ T ∈ F, f T ≤ k := by
  have hnn := f_nonneg hsym hsub h0
  have hle := f_union_le hsub hnn hsingle h0
  have hcard := f_le_card hsub hnn hsingle h0
  have huniv : f Finset.univ = 0 := by
    have := hsym ∅
    rw [Finset.compl_empty] at this
    rw [← this, h0]
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ihA =>
  intro A hAa b
  induction b using Nat.strong_induction_on with
  | _ b ihB =>
  intro B hBb hne hAB hbk hL
  have hBk : (B.card : ℤ) ≤ k := by exact_mod_cast (hBb ▸ hbk)
  have hAk : f A ≤ k := by
    have := hL Finset.univ (Finset.subset_univ _)
    rw [huniv, Finset.univ_inter] at this
    linarith
  by_cases hsmall : A.card ≤ k
  · obtain ⟨F, hF⟩ := exists_RH _ A rfl hne
    refine ⟨F, hF, fun T hT => ?_⟩
    have h1 := hcard T
    have h2 : T.card ≤ k := (Finset.card_le_card (hF.sub T hT)).trans hsmall
    have h3 : (T.card : ℤ) ≤ k := by exact_mod_cast h2
    linarith
  push_neg at hsmall
  obtain ⟨Win, hWinA, hWinc⟩ := Finset.exists_subset_card_eq (show k - b ≤ A.card by omega)
  have hWB : Disjoint Win B := Finset.disjoint_of_subset_left hWinA hAB
  have hWc : (Win ∪ B).card = k := by
    rw [Finset.card_union_of_disjoint hWB, hWinc, hBb]; omega
  have hnw : ¬ IsWellLinked f (Win ∪ B) := fun h => hno ⟨_, hWc, h⟩
  unfold IsWellLinked at hnw
  push_neg at hnw
  obtain ⟨X, Y, hXY, hdXY, Z0, hXZ0, hZ0Y, hlt⟩ := hnw
  obtain ⟨Z, hZm, hZmin⟩ := (Finset.univ.filter (fun Z => X ⊆ Z ∧ Disjoint Z Y)).exists_min_image
    f ⟨Z0, by simp [hXZ0, hZ0Y]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hZm
  obtain ⟨hXZ, hZY⟩ := hZm
  have hZmin' : ∀ S, X ⊆ S → Disjoint S Y → f Z ≤ f S :=
    fun S h1 h2 => hZmin S (by simp [h1, h2])
  have hfZ0 := hZmin' Z0 hXZ0 hZ0Y
  have hm : f Z0 < X.card ∧ f Z0 < Y.card := by simpa [lt_min_iff] using hlt
  have hZX : f Z < X.card := by linarith [hm.1]
  have hZYc : f Z < Y.card := by linarith [hm.2]
  have hsZ : f Zᶜ = f Z := (hsym Z).symm
  obtain ⟨X', hX'X, hX'c, hX'P⟩ := ml hsub hnn hle hXZ hZY hZmin'
  have hYZc : Y ⊆ Zᶜ := fun y hy => Finset.mem_compl.2 (fun hz => Finset.disjoint_left.1 hZY hz hy)
  have hZcX : Disjoint Zᶜ X := by
    rw [Finset.disjoint_left]; intro x hx hxX; exact (Finset.mem_compl.1 hx) (hXZ hxX)
  have hZcmin : ∀ S, Y ⊆ S → Disjoint S X → f Zᶜ ≤ f S := by
    intro S h1 h2
    rw [hsZ, hsym S]
    apply hZmin'
    · intro x hx; exact Finset.mem_compl.2 (fun hs => Finset.disjoint_left.1 h2 hs hx)
    · rw [Finset.disjoint_left]; intro y hy hyY; exact (Finset.mem_compl.1 hy) (h1 hyY)
  obtain ⟨Y', hY'Y, hY'c, hY'P⟩ := ml hsub hnn hle hYZc hZcX hZcmin
  have hY'Z : Disjoint Y' Z := Finset.disjoint_of_subset_left hY'Y hZY.symm
  have hX'Zc : Disjoint X' Zᶜ := by
    rw [Finset.disjoint_left]; intro x hx hxc; exact (Finset.mem_compl.1 hxc) (hXZ (hX'X hx))
  have L1 : Link f (A ∩ Z) (B ∩ Z ∪ Y') :=
    child_link hsym hsub hL hAB hXZ hY'Z (fun S hS => by rw [← hsZ]; exact hY'P S hS)
  have L2 : Link f (A ∩ Zᶜ) (B ∩ Zᶜ ∪ X') :=
    child_link hsym hsub hL hAB hYZc hX'Zc (fun S hS => by rw [hsZ]; exact hX'P S hS)
  have hD1 : Disjoint (A ∩ Z) (B ∩ Z ∪ Y') := by
    rw [Finset.disjoint_union_right]
    exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hAB),
      Finset.disjoint_of_subset_left Finset.inter_subset_right hY'Z.symm⟩
  have hD2 : Disjoint (A ∩ Zᶜ) (B ∩ Zᶜ ∪ X') := by
    rw [Finset.disjoint_union_right]
    exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hAB),
      Finset.disjoint_of_subset_left Finset.inter_subset_right hX'Zc.symm⟩
  have hXYc : X.card + Y.card = k := by
    rw [← Finset.card_union_of_disjoint hdXY, hXY, hWc]
  have hBZX : B ∩ Z ⊆ X := by
    intro x hx
    rw [Finset.mem_inter] at hx
    have : x ∈ X ∪ Y := hXY ▸ Finset.mem_union_right _ hx.1
    rcases Finset.mem_union.1 this with h | h
    · exact h
    · exact absurd h (Finset.disjoint_left.1 hZY hx.2)
  have hBZcY : B ∩ Zᶜ ⊆ Y := by
    intro x hx
    rw [Finset.mem_inter] at hx
    have : x ∈ X ∪ Y := hXY ▸ Finset.mem_union_right _ hx.1
    rcases Finset.mem_union.1 this with h | h
    · exact absurd (hXZ h) (Finset.mem_compl.1 hx.2)
    · exact h
  have hB1 : (B ∩ Z ∪ Y').card ≤ (B ∩ Z).card + Y'.card := Finset.card_union_le _ _
  have hB2 : (B ∩ Zᶜ ∪ X').card ≤ (B ∩ Zᶜ).card + X'.card := Finset.card_union_le _ _
  have hBZc : (B ∩ Z).card ≤ X.card := Finset.card_le_card hBZX
  have hBZcc : (B ∩ Zᶜ).card ≤ Y.card := Finset.card_le_card hBZcY
  have hBs : (B ∩ Z).card + (B ∩ Zᶜ).card = B.card := by
    rw [← Finset.sdiff_eq_inter_compl, add_comm]
    exact Finset.card_sdiff_add_card_inter B Z
  have hY'lt : Y'.card < Y.card := by
    have : (Y'.card : ℤ) < Y.card := by rw [hsZ] at hY'c; linarith
    exact_mod_cast this
  have hX'lt : X'.card < X.card := by
    have : (X'.card : ℤ) < X.card := by linarith
    exact_mod_cast this
  by_cases h1 : (A ∩ Z).Nonempty
  · by_cases h2 : (A ∩ Zᶜ).Nonempty
    · -- genuine split
      have hc1 : (A ∩ Z).card < a := by
        rw [← hAa]
        obtain ⟨x, hx⟩ := h2
        refine Finset.card_lt_card ⟨Finset.inter_subset_left, fun h => ?_⟩
        have := h (Finset.mem_inter.1 hx).1
        exact (Finset.mem_compl.1 (Finset.mem_inter.1 hx).2) (Finset.mem_inter.1 this).2
      have hc2 : (A ∩ Zᶜ).card < a := by
        rw [← hAa]
        obtain ⟨x, hx⟩ := h1
        refine Finset.card_lt_card ⟨Finset.inter_subset_left, fun h => ?_⟩
        have := h (Finset.mem_inter.1 hx).1
        exact (Finset.mem_compl.1 (Finset.mem_inter.1 this).2) (Finset.mem_inter.1 hx).2
      obtain ⟨F1, hF1, hF1k⟩ := ihA _ hc1 (A ∩ Z) rfl _ (B ∩ Z ∪ Y') rfl h1 hD1 (by omega) L1
      obtain ⟨F2, hF2, hF2k⟩ := ihA _ hc2 (A ∩ Zᶜ) rfl _ (B ∩ Zᶜ ∪ X') rfl h2 hD2 (by omega) L2
      have hd : Disjoint (A ∩ Z) (A ∩ Zᶜ) :=
        Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right disjoint_compl_right)
      have hj := hF1.join hF2 hd
      have hAeq : A ∩ Z ∪ A ∩ Zᶜ = A := by ext x; simp; tauto
      rw [hAeq] at hj
      refine ⟨_, hj, ?_⟩
      intro T hT
      rcases Finset.mem_insert.1 hT with rfl | hT
      · exact hAk
      rcases Finset.mem_union.1 hT with hT | hT
      · exact hF1k T hT
      · exact hF2k T hT
    · -- A ⊆ Z : shrink B
      have hAZ : A ∩ Z = A := by
        ext x
        simp only [Finset.mem_inter, and_iff_left_iff_imp]
        intro hx
        by_contra hz
        exact h2 ⟨x, Finset.mem_inter.2 ⟨hx, Finset.mem_compl.2 hz⟩⟩
      have hYB : Y ⊆ B ∩ Zᶜ := by
        intro y hy
        have hyc := hYZc hy
        have : y ∈ Win ∪ B := hXY ▸ Finset.mem_union_right _ hy
        rcases Finset.mem_union.1 this with h | h
        · exfalso
          have : y ∈ A ∩ Z := by rw [hAZ]; exact hWinA h
          exact (Finset.mem_compl.1 hyc) (Finset.mem_inter.1 this).2
        · exact Finset.mem_inter.2 ⟨h, hyc⟩
      have := Finset.card_le_card hYB
      rw [hAZ] at L1 hD1
      exact ihB _ (by omega) _ rfl hne hD1 (by omega) L1
  · -- A ∩ Z = ∅ : shrink B
    have hAZ : A ∩ Zᶜ = A := by
      ext x
      simp only [Finset.mem_inter, and_iff_left_iff_imp]
      intro hx
      exact Finset.mem_compl.2 (fun hz => h1 ⟨x, Finset.mem_inter.2 ⟨hx, hz⟩⟩)
    have hXB : X ⊆ B ∩ Z := by
      intro x hx
      have hxz := hXZ hx
      have : x ∈ Win ∪ B := hXY ▸ Finset.mem_union_left _ hx
      rcases Finset.mem_union.1 this with h | h
      · exfalso
        exact h1 ⟨x, Finset.mem_inter.2 ⟨hWinA h, hxz⟩⟩
      · exact Finset.mem_inter.2 ⟨h, hxz⟩
    have := Finset.card_le_card hXB
    rw [hAZ] at L2 hD2
    exact ihB _ (by omega) _ rfl hne hD2 (by omega) L2

end C3

open ApproxCliqueWidth.Certificate in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (hsym : IsSymmetric f) (hsub : IsSubmodular f)
    (hsingle : ∀ v : V, f {v} ≤ 1) (h0 : f ∅ = 0) (k : ℕ)
    (hno : ¬ ∃ W : Finset V, W.card = k ∧ IsWellLinked f W) :
    BwLE f k := by
  by_cases hV : Fintype.card V ≤ 1
  · left
    refine ⟨hV, ?_⟩
    rw [h0]
    exact_mod_cast Nat.zero_le k
  · push_neg at hV
    have hne : (Finset.univ : Finset V).Nonempty :=
      Finset.univ_nonempty_iff.2 (Fintype.card_pos_iff.1 (by omega))
    obtain ⟨F, hF, hFk⟩ := C3.main hsym hsub hsingle h0 k hno _ Finset.univ rfl _ ∅ rfl hne
      (Finset.disjoint_empty_right _) (Nat.zero_le _)
      (by intro U hU; rw [Finset.univ_subset_iff.1 hU]; simp)
    exact Hier.bwLE_of_hier f hsym hF.hier hV k hFk

