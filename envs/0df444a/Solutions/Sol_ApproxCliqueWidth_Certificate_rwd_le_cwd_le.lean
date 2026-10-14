-- Prove2me | solution 1 for ApproxCliqueWidth.Certificate.rwd_le_cwd_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T12:41:36.526955+00:00
-- url     : https://prove2.me/submissions/5b678c19-f55b-4d63-ab72-eec948bf53fc

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_BranchDecomp
import Definitions.Def_ApproxCliqueWidth_Certificate_KExpr
import Definitions.Def_ApproxCliqueWidth_Certificate_CutRank
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


theorem cutrk_le_of_rows {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Y : Finset V) (k : ℕ) (lam : V → Fin k)
    (h : ∀ a ∈ Y, ∀ b ∈ Y, lam a = lam b → ∀ c, c ∉ Y → (G.Adj a c ↔ G.Adj b c)) :
    cutrk G Y ≤ k := by
  classical
  unfold cutrk cutrkStar
  let P : Matrix Y (Fin k) (ZMod 2) := Matrix.of fun a i => if lam a = i then 1 else 0
  let Q : Matrix (Fin k) (Yᶜ : Finset V) (ZMod 2) :=
    Matrix.of fun i c => if ∃ a ∈ Y, lam a = i ∧ G.Adj a c then 1 else 0
  have hM : (G.adjMatrix (ZMod 2)).submatrix (fun x : Y => (x : V))
      (fun y : (Yᶜ : Finset V) => (y : V)) = P * Q := by
    ext a c
    have hc : (c : V) ∉ Y := Finset.mem_compl.1 c.2
    rw [Matrix.mul_apply]
    simp only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, P, Q, Matrix.of_apply]
    rw [Finset.sum_eq_single (lam a.1)]
    · simp only [if_true, one_mul]
      have : (∃ a' ∈ Y, lam a' = lam a.1 ∧ G.Adj a' c) ↔ G.Adj a.1 c := by
        constructor
        · rintro ⟨a', ha', hl, hadj⟩
          exact (h a' ha' a.1 a.2 hl c hc).1 hadj
        · intro hadj; exact ⟨a.1, a.2, rfl, hadj⟩
      by_cases hh : G.Adj a.1 c
      · simp [hh, this.2 hh]
      · simp [hh, mt this.1 hh]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [hM]
  have h1 := (Matrix.rank_mul_le_left P Q).trans (Matrix.rank_le_card_width P)
  have h2 : (Matrix.rank (P * Q) : ℤ) ≤ (Fintype.card (Fin k) : ℤ) := by exact_mod_cast h1
  simpa using h2


structure HierS {α : Type*} (S : Set (Set α)) : Prop where
  univ_mem : Set.univ ∈ S
  single_mem : ∀ a : α, ({a} : Set α) ∈ S
  nonempty : ∀ X ∈ S, X.Nonempty
  laminar : ∀ X ∈ S, ∀ Y ∈ S, Disjoint X Y ∨ X ⊆ Y ∨ Y ⊆ X
  split : ∀ X ∈ S, (∃ a, X = {a}) ∨ ∃ Y ∈ S, ∃ Z ∈ S, Disjoint Y Z ∧ Y ∪ Z = X

theorem HierS.unit : HierS ({Set.univ} : Set (Set Unit)) where
  univ_mem := rfl
  single_mem a := by
    rw [Set.mem_singleton_iff]
    ext x; simp
  nonempty X hX := by
    rw [Set.mem_singleton_iff] at hX; subst hX; exact Set.univ_nonempty
  laminar X hX Y hY := by
    rw [Set.mem_singleton_iff] at hX hY; subst hX; subst hY; exact Or.inr (Or.inl le_rfl)
  split X hX := by
    rw [Set.mem_singleton_iff] at hX; subst hX
    left
    exact ⟨(), by ext x; simp⟩

theorem HierS.union {α β : Type*} {S : Set (Set α)} {T : Set (Set β)} (hS : HierS S)
    (hT : HierS T) :
    HierS ({Set.univ} ∪ Set.image (Set.image (Sum.inl : α → α ⊕ β)) S ∪
      Set.image (Set.image (Sum.inr : β → α ⊕ β)) T) where
  univ_mem := Or.inl (Or.inl rfl)
  single_mem a := by
    rcases a with a | b
    · refine Or.inl (Or.inr ⟨{a}, hS.single_mem a, ?_⟩)
      simp
    · refine Or.inr ⟨{b}, hT.single_mem b, ?_⟩
      simp
  nonempty X hX := by
    rcases hX with (hX | ⟨X1, hX1, rfl⟩) | ⟨X1, hX1, rfl⟩
    · rw [Set.mem_singleton_iff] at hX; subst hX
      obtain ⟨a, _⟩ := hS.nonempty _ hS.univ_mem
      exact ⟨Sum.inl a, trivial⟩
    · exact (hS.nonempty _ hX1).image _
    · exact (hT.nonempty _ hX1).image _
  laminar X hX Y hY := by
    have hinl : ∀ X1 : Set α, ∀ Y1 : Set β, Disjoint (Sum.inl '' X1) (Sum.inr '' Y1 : Set (α ⊕ β)) := by
      intro X1 Y1
      rw [Set.disjoint_left]
      rintro _ ⟨a, _, rfl⟩ ⟨b, _, h⟩
      cases h
    rcases hX with (rfl | ⟨X1, hX1, rfl⟩) | ⟨X1, hX1, rfl⟩ <;>
    rcases hY with (rfl | ⟨Y1, hY1, rfl⟩) | ⟨Y1, hY1, rfl⟩
    · exact Or.inr (Or.inl (Set.Subset.refl _))
    · exact Or.inr (Or.inr (Set.subset_univ _))
    · exact Or.inr (Or.inr (Set.subset_univ _))
    · exact Or.inr (Or.inl (Set.subset_univ _))
    · rcases hS.laminar _ hX1 _ hY1 with h | h | h
      · exact Or.inl ((Set.disjoint_image_iff Sum.inl_injective).2 h)
      · exact Or.inr (Or.inl (Set.image_mono h))
      · exact Or.inr (Or.inr (Set.image_mono h))
    · exact Or.inl (hinl _ _)
    · exact Or.inr (Or.inl (Set.subset_univ _))
    · exact Or.inl (hinl _ _).symm
    · rcases hT.laminar _ hX1 _ hY1 with h | h | h
      · exact Or.inl ((Set.disjoint_image_iff Sum.inr_injective).2 h)
      · exact Or.inr (Or.inl (Set.image_mono h))
      · exact Or.inr (Or.inr (Set.image_mono h))
  split X hX := by
    rcases hX with (hX | ⟨X1, hX1, rfl⟩) | ⟨X1, hX1, rfl⟩
    · rw [Set.mem_singleton_iff] at hX; subst hX
      right
      refine ⟨Sum.inl '' Set.univ, Or.inl (Or.inr ⟨_, hS.univ_mem, rfl⟩),
        Sum.inr '' Set.univ, Or.inr ⟨_, hT.univ_mem, rfl⟩, ?_, ?_⟩
      · rw [Set.disjoint_left]
        rintro _ ⟨a, _, rfl⟩ ⟨b, _, h⟩
        cases h
      · ext x; rcases x with a | b <;> simp
    · rcases hS.split _ hX1 with ⟨a, rfl⟩ | ⟨Y, hY, Z, hZ, hd, hU⟩
      · left; exact ⟨Sum.inl a, by simp⟩
      · right
        refine ⟨Sum.inl '' Y, Or.inl (Or.inr ⟨_, hY, rfl⟩), Sum.inl '' Z,
          Or.inl (Or.inr ⟨_, hZ, rfl⟩), (Set.disjoint_image_iff Sum.inl_injective).2 hd, ?_⟩
        rw [← Set.image_union, hU]
    · rcases hT.split _ hX1 with ⟨a, rfl⟩ | ⟨Y, hY, Z, hZ, hd, hU⟩
      · left; exact ⟨Sum.inr a, by simp⟩
      · right
        refine ⟨Sum.inr '' Y, Or.inr ⟨_, hY, rfl⟩, Sum.inr '' Z,
          Or.inr ⟨_, hZ, rfl⟩, (Set.disjoint_image_iff Sum.inr_injective).2 hd, ?_⟩
        rw [← Set.image_union, hU]


namespace ApproxCliqueWidth.Certificate.KExpr
variable {k : ℕ}

def fam : (t : KExpr k) → Set (Set t.Vtx)
  | const _ => {Set.univ}
  | eta _ _ _ t => fam t
  | rho _ _ t => fam t
  | union t₁ t₂ => {Set.univ} ∪ Set.image (Set.image Sum.inl) (fam t₁) ∪
      Set.image (Set.image Sum.inr) (fam t₂)

theorem eta_adj (i j : Fin k) (h : i ≠ j) (t : KExpr k) (a c : t.Vtx) :
    (eta i j h t).graph.Adj a c ↔ t.graph.Adj a c ∨
      (a ≠ c ∧ ((t.lab a = i ∧ t.lab c = j) ∨ (t.lab c = i ∧ t.lab a = j))) := by
  show (t.graph ⊔ SimpleGraph.fromRel (fun v w => t.lab v = i ∧ t.lab w = j)).Adj a c ↔ _
  simp only [SimpleGraph.sup_adj, SimpleGraph.fromRel_adj]

theorem fam_hier : ∀ t : KExpr k, HierS (fam t)
  | const _ => HierS.unit
  | eta _ _ _ t => fam_hier t
  | rho _ _ t => fam_hier t
  | union t₁ t₂ => HierS.union (fam_hier t₁) (fam_hier t₂)

/-- Row property of a subterm vertex set. -/
def RP (t : KExpr k) (X : Set t.Vtx) : Prop :=
  ∃ ℓ : t.Vtx → Fin k, ∀ a ∈ X, ∀ b ∈ X, ℓ a = ℓ b →
    t.lab a = t.lab b ∧ ∀ c, c ∉ X → (t.graph.Adj a c ↔ t.graph.Adj b c)

theorem fam_rp : ∀ (t : KExpr k), ∀ X ∈ fam t, RP t X
  | const i, X, hX => by
    rw [fam, Set.mem_singleton_iff] at hX; subst hX
    refine ⟨fun _ => i, fun a _ b _ _ => ⟨rfl, fun c hc => absurd (Set.mem_univ c) hc⟩⟩
  | eta i j h t, X, hX => by
    obtain ⟨ℓ, hℓ⟩ := fam_rp t X hX
    refine ⟨ℓ, fun a ha b hb hab => ?_⟩
    obtain ⟨h1, h2⟩ := hℓ a ha b hb hab
    refine ⟨h1, fun c hc => ?_⟩
    have hac : a ≠ c := fun e => hc (e ▸ ha)
    have hbc : b ≠ c := fun e => hc (e ▸ hb)
    rw [eta_adj i j h t a c, eta_adj i j h t b c, h2 c hc]
    have e1 : (t.lab a = i ∧ t.lab c = j) ↔ (t.lab b = i ∧ t.lab c = j) := by rw [h1]
    have e2 : (t.lab c = i ∧ t.lab a = j) ↔ (t.lab c = i ∧ t.lab b = j) := by rw [h1]
    constructor
    · rintro (hh | ⟨_, hh⟩)
      · exact Or.inl hh
      · exact Or.inr ⟨hbc, hh.imp e1.1 e2.1⟩
    · rintro (hh | ⟨_, hh⟩)
      · exact Or.inl hh
      · exact Or.inr ⟨hac, hh.imp e1.2 e2.2⟩
  | rho i j t, X, hX => by
    obtain ⟨ℓ, hℓ⟩ := fam_rp t X hX
    refine ⟨ℓ, fun a ha b hb hab => ?_⟩
    obtain ⟨h1, h2⟩ := hℓ a ha b hb hab
    refine ⟨?_, h2⟩
    show (if t.lab a = i then j else t.lab a) = (if t.lab b = i then j else t.lab b)
    rw [h1]
  | union t₁ t₂, X, hX => by
    rcases hX with (hX | ⟨X1, hX1, rfl⟩) | ⟨X1, hX1, rfl⟩
    · rw [Set.mem_singleton_iff] at hX; subst hX
      refine ⟨(union t₁ t₂).lab, fun a _ b _ h => ⟨h, fun c hc => absurd (Set.mem_univ c) hc⟩⟩
    · obtain ⟨ℓ, hℓ⟩ := fam_rp t₁ X1 hX1
      refine ⟨Sum.elim ℓ (t₂.lab), ?_⟩
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      obtain ⟨h1, h2⟩ := hℓ a ha b hb hab
      refine ⟨by simp [lab, h1], ?_⟩
      intro c hc
      rcases c with c | c
      · have : c ∉ X1 := fun hh => hc ⟨c, hh, rfl⟩
        show (t₁.graph ⊕g t₂.graph).Adj (Sum.inl a) (Sum.inl c) ↔
          (t₁.graph ⊕g t₂.graph).Adj (Sum.inl b) (Sum.inl c)
        rw [SimpleGraph.sum_adj_inl, SimpleGraph.sum_adj_inl]
        exact h2 c this
      · show (t₁.graph ⊕g t₂.graph).Adj (Sum.inl a) (Sum.inr c) ↔
          (t₁.graph ⊕g t₂.graph).Adj (Sum.inl b) (Sum.inr c)
        simp
    · obtain ⟨ℓ, hℓ⟩ := fam_rp t₂ X1 hX1
      refine ⟨Sum.elim t₁.lab ℓ, ?_⟩
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
      obtain ⟨h1, h2⟩ := hℓ a ha b hb hab
      refine ⟨by simp [lab, h1], ?_⟩
      intro c hc
      rcases c with c | c
      · show (t₁.graph ⊕g t₂.graph).Adj (Sum.inr a) (Sum.inl c) ↔
          (t₁.graph ⊕g t₂.graph).Adj (Sum.inr b) (Sum.inl c)
        simp
      · have : c ∉ X1 := fun hh => hc ⟨c, hh, rfl⟩
        show (t₁.graph ⊕g t₂.graph).Adj (Sum.inr a) (Sum.inr c) ↔
          (t₁.graph ⊕g t₂.graph).Adj (Sum.inr b) (Sum.inr c)
        rw [SimpleGraph.sum_adj_inr, SimpleGraph.sum_adj_inr]
        exact h2 c this

end ApproxCliqueWidth.Certificate.KExpr


theorem cutrkStar_comm {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Y Z : Finset V) : cutrkStar G Y Z = cutrkStar G Z Y := by
  unfold cutrkStar
  congr 1
  have h1 := Matrix.rank_transpose
    ((G.adjMatrix (ZMod 2)).submatrix (fun x : Y => (x : V)) (fun y : Z => (y : V)))
  rw [Matrix.transpose_submatrix, SimpleGraph.transpose_adjMatrix] at h1
  exact h1.symm

theorem cutrk_isSymmetric {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : IsSymmetric (cutrk G) := by
  intro X
  unfold cutrk
  rw [cutrkStar_comm G Xᶜ Xᶜᶜ, compl_compl]
  
theorem cutrk_empty_eq_zero' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : cutrk G ∅ = 0 := by
  unfold cutrk cutrkStar
  have h := Matrix.rank_le_card_height
    ((G.adjMatrix (ZMod 2)).submatrix (fun x : (∅ : Finset V) => (x : V))
      (fun y : (((∅ : Finset V))ᶜ : Finset V) => (y : V)))
  have h1 : Fintype.card (∅ : Finset V) = 0 := by simp
  rw [h1] at h
  have : (Matrix.rank ((G.adjMatrix (ZMod 2)).submatrix (fun x : (∅ : Finset V) => (x : V))
      (fun y : (((∅ : Finset V))ᶜ : Finset V) => (y : V)))) = 0 := Nat.le_zero.mp h
  exact_mod_cast this

noncomputable def toF {V : Type*} [Fintype V] (A : Set V) : Finset V := by
  classical exact Finset.univ.filter (· ∈ A)

theorem coe_toF {V : Type*} [Fintype V] (A : Set V) : (toF A : Set V) = A := by
  classical
  ext x; simp [toF]

theorem hier_of_hierS {α V : Type*} [Fintype V] [DecidableEq V] {S : Set (Set α)} (hS : HierS S)
    (e : α ≃ V) :
    ∃ F : Finset (Finset V), Hier F ∧ ∀ Y ∈ F, ∃ X ∈ S, (Y : Set V) = e '' X := by
  classical
  have hfin : Set.Finite {Y : Finset V | ∃ X ∈ S, Y = toF (e '' X)} := Set.toFinite _
  refine ⟨hfin.toFinset, ?_, ?_⟩
  swap
  · intro Y hY
    obtain ⟨X, hX, rfl⟩ := hfin.mem_toFinset.1 hY
    exact ⟨X, hX, coe_toF _⟩
  have mem : ∀ Y : Finset V, Y ∈ hfin.toFinset ↔ ∃ X ∈ S, (Y : Set V) = e '' X := by
    intro Y
    rw [hfin.mem_toFinset]
    constructor
    · rintro ⟨X, hX, rfl⟩; exact ⟨X, hX, coe_toF _⟩
    · rintro ⟨X, hX, h⟩; exact ⟨X, hX, Finset.coe_injective (by rw [h, coe_toF])⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mem]; exact ⟨Set.univ, hS.univ_mem, by simp⟩
  · intro v; rw [mem]; exact ⟨{e.symm v}, hS.single_mem _, by simp⟩
  · intro Y hY
    obtain ⟨X, hX, h⟩ := (mem Y).1 hY
    rw [← Finset.coe_nonempty, h]
    exact (hS.nonempty X hX).image _
  · intro Y1 h1 Y2 h2
    obtain ⟨X1, hX1, e1⟩ := (mem _).1 h1
    obtain ⟨X2, hX2, e2⟩ := (mem _).1 h2
    rcases hS.laminar X1 hX1 X2 hX2 with h | h | h
    · left
      rw [← Finset.disjoint_coe, e1, e2]
      exact (Set.disjoint_image_iff e.injective).2 h
    · right; left
      rw [← Finset.coe_subset, e1, e2]
      exact Set.image_mono h
    · right; right
      rw [← Finset.coe_subset, e1, e2]
      exact Set.image_mono h
  · intro Y hY hc
    obtain ⟨X, hX, h⟩ := (mem Y).1 hY
    rcases hS.split X hX with ⟨a, rfl⟩ | ⟨X1, hX1, X2, hX2, hd, hU⟩
    · exfalso
      have : (Y : Set V) = {e a} := by rw [h]; simp
      have h2 : Y = {e a} := Finset.coe_injective (by rw [this]; simp)
      rw [h2] at hc; simp at hc
    · refine ⟨toF (e '' X1), (mem _).2 ⟨X1, hX1, by rw [coe_toF]⟩, toF (e '' X2),
        (mem _).2 ⟨X2, hX2, by rw [coe_toF]⟩, ?_, ?_⟩
      · rw [← Finset.disjoint_coe, coe_toF, coe_toF]
        exact (Set.disjoint_image_iff e.injective).2 hd
      · apply Finset.coe_injective
        rw [Finset.coe_union, coe_toF, coe_toF, h, ← Set.image_union, hU]

theorem cwd_bound_rwd {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hG : HasKExpr G k) : BwLE (cutrk G) k := by
  classical
  obtain ⟨t, ⟨e⟩⟩ := hG
  by_cases hV : Fintype.card V ≤ 1
  · left
    refine ⟨hV, ?_⟩
    rw [cutrk_empty_eq_zero']
    exact_mod_cast Nat.zero_le k
  · have hV2 : 2 ≤ Fintype.card V := by omega
    obtain ⟨F, hF, hFm⟩ := hier_of_hierS (KExpr.fam_hier t) e.toEquiv
    refine Hier.bwLE_of_hier (cutrk G) (cutrk_isSymmetric G) hF hV2 k ?_
    intro Y hY
    obtain ⟨X, hX, hXY⟩ := hFm Y hY
    obtain ⟨ℓ, hℓ⟩ := KExpr.fam_rp t X hX
    have := cutrk_le_of_rows G Y k (fun a => ℓ (e.symm a)) ?_
    · exact this
    · intro a ha b hb hab c hc
      have ha' : e.symm a ∈ X := by
        have : a ∈ (Y : Set V) := ha
        rw [hXY] at this
        obtain ⟨x, hx, rfl⟩ := this
        simpa using hx
      have hb' : e.symm b ∈ X := by
        have : b ∈ (Y : Set V) := hb
        rw [hXY] at this
        obtain ⟨x, hx, rfl⟩ := this
        simpa using hx
      have hc' : e.symm c ∉ X := by
        intro hcx
        apply hc
        have : c ∈ e.toEquiv '' X := ⟨e.symm c, hcx, by simp⟩
        rw [← hXY] at this
        exact this
      have := (hℓ _ ha' _ hb' hab).2 _ hc'
      have e1 : G.Adj a c ↔ t.graph.Adj (e.symm a) (e.symm c) := by
        simpa using e.map_adj_iff (v := e.symm a) (w := e.symm c)
      have e2 : G.Adj b c ↔ t.graph.Adj (e.symm b) (e.symm c) := by
        simpa using e.map_adj_iff (v := e.symm b) (w := e.symm c)
      rw [e1, e2]
      exact this


namespace ApproxCliqueWidth.Certificate

/-- Realization of the vertex set `X`, with adjacency `A` and labelling `lam`, by an expression. -/
def Rl {V : Type*} {m : ℕ} (t : KExpr m) (A : V → V → Prop) (X : Finset V) (lam : V → Fin m) :
    Prop :=
  ∃ e : t.Vtx ≃ ↥X, (∀ a b, t.graph.Adj a b ↔ A (e a) (e b)) ∧ ∀ a, t.lab a = lam (e a)

theorem Rl.congr {V : Type*} {m : ℕ} {t : KExpr m} {A A' : V → V → Prop} {X : Finset V}
    {lam lam' : V → Fin m} (h : Rl t A X lam) (hA : ∀ v ∈ X, ∀ w ∈ X, A v w ↔ A' v w)
    (hl : ∀ v ∈ X, lam v = lam' v) : Rl t A' X lam' := by
  obtain ⟨e, h1, h2⟩ := h
  refine ⟨e, fun a b => (h1 a b).trans (hA _ (e a).2 _ (e b).2), fun a => ?_⟩
  rw [h2 a]; exact hl _ (e a).2

theorem Rl.const {V : Type*} {m : ℕ} (v : V) (i : Fin m) :
    Rl (KExpr.const i) (fun _ _ => False) ({v} : Finset V) (fun _ => i) := by
  refine ⟨⟨fun _ => ⟨v, Finset.mem_singleton_self v⟩, fun _ => (), fun _ => rfl, fun x => ?_⟩,
    ?_, fun _ => rfl⟩
  · obtain ⟨x, hx⟩ := x
    exact Subtype.ext (Finset.mem_singleton.1 hx).symm
  · intro a b
    exact Iff.rfl

theorem Rl.union {V : Type*} [DecidableEq V] {m : ℕ} {t₁ t₂ : KExpr m} {A₁ A₂ : V → V → Prop}
    {X₁ X₂ : Finset V} {lam₁ lam₂ : V → Fin m} (h₁ : Rl t₁ A₁ X₁ lam₁) (h₂ : Rl t₂ A₂ X₂ lam₂)
    (hd : Disjoint X₁ X₂) :
    Rl (KExpr.union t₁ t₂)
      (fun v w => (v ∈ X₁ ∧ w ∈ X₁ ∧ A₁ v w) ∨ (v ∈ X₂ ∧ w ∈ X₂ ∧ A₂ v w)) (X₁ ∪ X₂)
      (fun v => if v ∈ X₁ then lam₁ v else lam₂ v) := by
  classical
  obtain ⟨e₁, a₁, l₁⟩ := h₁
  obtain ⟨e₂, a₂, l₂⟩ := h₂
  let e : (KExpr.union t₁ t₂).Vtx ≃ ↥(X₁ ∪ X₂) :=
    (Equiv.sumCongr e₁ e₂).trans (Equiv.Finset.union X₁ X₂ hd)
  have h1 : ∀ a, ((e (Sum.inl a) : ↥(X₁ ∪ X₂)) : V) = (e₁ a : V) := fun a => rfl
  have h2 : ∀ b, ((e (Sum.inr b) : ↥(X₁ ∪ X₂)) : V) = (e₂ b : V) := fun b => rfl
  have n2 : ∀ a, (e₁ a : V) ∉ X₂ := fun a hx => Finset.disjoint_left.1 hd (e₁ a).2 hx
  have n1 : ∀ b, (e₂ b : V) ∉ X₁ := fun b hx => Finset.disjoint_left.1 hd hx (e₂ b).2
  refine ⟨e, ?_, ?_⟩
  · intro a b
    rcases a with a | a <;> rcases b with b | b
    · show (t₁.graph ⊕g t₂.graph).Adj (Sum.inl a) (Sum.inl b) ↔ _
      rw [SimpleGraph.sum_adj_inl, a₁, h1, h1]
      constructor
      · intro h; exact Or.inl ⟨(e₁ a).2, (e₁ b).2, h⟩
      · rintro (⟨_, _, h⟩ | ⟨h, _, _⟩)
        · exact h
        · exact absurd h (n2 a)
    · show (t₁.graph ⊕g t₂.graph).Adj (Sum.inl a) (Sum.inr b) ↔ _
      rw [h1, h2]
      constructor
      · intro h; exact absurd h (SimpleGraph.not_adj_sum_inl_inr _ _)
      · rintro (⟨_, h, _⟩ | ⟨h, _, _⟩)
        · exact absurd h (n1 b)
        · exact absurd h (n2 a)
    · show (t₁.graph ⊕g t₂.graph).Adj (Sum.inr a) (Sum.inl b) ↔ _
      rw [h1, h2]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro (⟨h, _, _⟩ | ⟨_, h, _⟩)
        · exact absurd h (n1 a)
        · exact absurd h (n2 b)
    · show (t₁.graph ⊕g t₂.graph).Adj (Sum.inr a) (Sum.inr b) ↔ _
      rw [SimpleGraph.sum_adj_inr, a₂, h2, h2]
      constructor
      · intro h; exact Or.inr ⟨(e₂ a).2, (e₂ b).2, h⟩
      · rintro (⟨h, _, _⟩ | ⟨_, _, h⟩)
        · exact absurd h (n1 a)
        · exact h
  · intro a
    rcases a with a | a
    · show t₁.lab a = _
      rw [h1]; show _ = (if (e₁ a : V) ∈ X₁ then _ else _); rw [if_pos (e₁ a).2]; exact l₁ a
    · show t₂.lab a = _
      rw [h2]; show _ = (if (e₂ a : V) ∈ X₁ then _ else _); rw [if_neg (n1 a)]; exact l₂ a

end ApproxCliqueWidth.Certificate


namespace ApproxCliqueWidth.Certificate

theorem Rl.rho_aux {V : Type*} {m : ℕ} :
    ∀ (N : ℕ) (F : Fin m → Fin m) (r : Fin m → ℕ), (∀ x, F x ≠ x → r (F x) < r x) →
      (Finset.univ.filter (fun x => F x ≠ x)).card = N →
      ∀ {t : KExpr m} {A : V → V → Prop} {X : Finset V} {lam : V → Fin m}, Rl t A X lam →
        ∃ t' : KExpr m, Rl t' A X (fun v => F (lam v)) := by
  classical
  intro N
  induction N with
  | zero =>
    intro F r hr hN t A X lam h
    have hfix : ∀ x, F x = x := by
      intro x
      by_contra hx
      have : x ∈ Finset.univ.filter (fun x => F x ≠ x) := by simp [hx]
      rw [Finset.card_eq_zero] at hN
      rw [hN] at this
      simp at this
    exact ⟨t, h.congr (fun _ _ _ _ => Iff.rfl) (fun v _ => (hfix _).symm)⟩
  | succ N ih =>
    intro F r hr hN t A X lam h
    set S := Finset.univ.filter (fun x => F x ≠ x) with hS
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨a, haS, hmax⟩ := Finset.exists_max_image S r hne
    have haF : F a ≠ a := (Finset.mem_filter.1 haS).2
    have leaf : ∀ x, x ≠ a → F x ≠ a := by
      intro x hxa hFx
      have hx : F x ≠ x := by rw [hFx]; exact Ne.symm hxa
      have h1 := hr x hx
      rw [hFx] at h1
      have := hmax x (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩)
      omega
    let F' : Fin m → Fin m := Function.update F a a
    have hF'a : F' a = a := by simp [F']
    have hF'x : ∀ x, x ≠ a → F' x = F x := fun x hx => by simp [F', hx]
    have hS' : Finset.univ.filter (fun x => F' x ≠ x) = S.erase a := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, hS]
      by_cases hx : x = a
      · subst hx; simp [hF'a]
      · rw [hF'x x hx]; simp [hx]
    have hcard : (Finset.univ.filter (fun x => F' x ≠ x)).card = N := by
      rw [hS', Finset.card_erase_of_mem haS]; omega
    have hr' : ∀ x, F' x ≠ x → r (F' x) < r x := by
      intro x hx
      by_cases hxa : x = a
      · subst hxa; exact absurd hF'a hx
      · rw [hF'x x hxa] at hx ⊢; exact hr x hx
    obtain ⟨t1, h1⟩ := ih F' r hr' hcard h
    refine ⟨KExpr.rho a (F a) t1, ?_⟩
    obtain ⟨e, a1, l1⟩ := h1
    refine ⟨e, a1, fun v => ?_⟩
    show (if t1.lab v = a then F a else t1.lab v) = F (lam (e v))
    rw [l1 v]
    beta_reduce
    by_cases hl : lam (e v) = a
    · rw [hl, hF'a]; simp
    · have := hF'x _ hl
      rw [this, if_neg (leaf _ hl)]

theorem Rl.rho {V : Type*} {m : ℕ} {t : KExpr m} {A : V → V → Prop} {X : Finset V}
    {lam : V → Fin m} (h : Rl t A X lam) (F : Fin m → Fin m) (r : Fin m → ℕ)
    (hr : ∀ x, F x ≠ x → r (F x) < r x) :
    ∃ t' : KExpr m, Rl t' A X (fun v => F (lam v)) :=
  Rl.rho_aux _ F r hr rfl h

theorem Rl.eta_aux {V : Type*} {m : ℕ} (S : Finset (Fin m × Fin m)) (hS : ∀ p ∈ S, p.1 ≠ p.2) :
    ∀ {t : KExpr m} {A : V → V → Prop} {X : Finset V} {lam : V → Fin m}, Rl t A X lam →
      ∃ t' : KExpr m, Rl t' (fun v w => A v w ∨ (v ≠ w ∧ ((lam v, lam w) ∈ S ∨ (lam w, lam v) ∈ S)))
        X lam := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro t A X lam h
    refine ⟨t, h.congr (fun v _ w _ => ?_) (fun _ _ => rfl)⟩
    simp
  | insert p S hp ih =>
    intro t A X lam h
    obtain ⟨t1, h1⟩ := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq)) h
    have hpne : p.1 ≠ p.2 := hS p (Finset.mem_insert_self _ _)
    refine ⟨KExpr.eta p.1 p.2 hpne t1, ?_⟩
    obtain ⟨e, a1, l1⟩ := h1
    refine ⟨e, fun (a b : t1.Vtx) => ?_, l1⟩
    rw [KExpr.eta_adj p.1 p.2 hpne t1 a b, a1]
    beta_reduce
    have hab : a ≠ b ↔ (e a : V) ≠ (e b : V) := by
      constructor
      · intro h h'; exact h (e.injective (Subtype.ext h'))
      · intro h h'; exact h (by rw [h'])
    have key : ∀ x y : Fin m, ((x, y) = p) ↔ (x = p.1 ∧ y = p.2) := fun x y => Prod.ext_iff
    rw [hab, l1 a, l1 b]
    simp only [Finset.mem_insert, key]
    tauto

end ApproxCliqueWidth.Certificate


theorem rows_card_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (X : Finset V) (k : ℕ) (hk : cutrk G X ≤ k) :
    (insert (0 : (Xᶜ : Finset V) → ZMod 2)
      (Finset.univ.image (fun x : X =>
        (fun c : (Xᶜ : Finset V) => if G.Adj (x : V) (c : V) then (1 : ZMod 2) else 0)))).card
      ≤ 2 ^ k := by
  classical
  set M : Matrix X (Xᶜ : Finset V) (ZMod 2) :=
    (G.adjMatrix (ZMod 2)).submatrix (fun x : X => (x : V)) (fun y : (Xᶜ : Finset V) => (y : V))
    with hM
  have hrank : M.rank ≤ k := by
    have : (M.rank : ℤ) ≤ k := hk
    exact_mod_cast this
  let S : Submodule (ZMod 2) ((Xᶜ : Finset V) → ZMod 2) := LinearMap.range M.transpose.mulVecLin
  have hS : Module.finrank (ZMod 2) S ≤ k := by
    have : Module.finrank (ZMod 2) S = M.transpose.rank := rfl
    rw [this, Matrix.rank_transpose]; exact hrank
  have hsub : ((insert (0 : (Xᶜ : Finset V) → ZMod 2)
      (Finset.univ.image (fun x : X =>
        (fun c : (Xᶜ : Finset V) => if G.Adj (x : V) (c : V) then (1 : ZMod 2) else 0))) :
        Finset _) : Set ((Xᶜ : Finset V) → ZMod 2)) ⊆
      (S : Set ((Xᶜ : Finset V) → ZMod 2)) := by
    intro f hf
    simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_insert_iff, Set.mem_range] at hf
    rcases hf with rfl | ⟨x, rfl⟩
    · exact S.zero_mem
    · refine ⟨Pi.single x 1, ?_⟩
      ext c
      simp [hM, SimpleGraph.adjMatrix_apply]
      simp only [SimpleGraph.adj_comm G (c : V) (x : V)]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at h1
  have h2 : (S : Set ((Xᶜ : Finset V) → ZMod 2)).ncard = 2 ^ Module.finrank (ZMod 2) S := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card S = _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := S)]
    simp [ZMod.card]
  calc _ ≤ _ := h1
    _ = 2 ^ Module.finrank (ZMod 2) S := h2
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hS


theorem exists_numbering {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (X : Finset V) (k : ℕ) (hk : cutrk G X ≤ k) :
    ∃ ν : V → Fin (2 ^ k),
      (∀ x ∈ X, ∀ y ∈ X, ν x = ν y ↔ ∀ c, c ∉ X → (G.Adj x c ↔ G.Adj y c)) ∧
      (∀ x ∈ X, ν x = ⟨0, by positivity⟩ ↔ ∀ c, c ∉ X → ¬ G.Adj x c) := by
  classical
  have hcard := rows_card_le G X k hk
  let rowf : V → ((Xᶜ : Finset V) → ZMod 2) :=
    fun x c => if G.Adj x (c : V) then (1 : ZMod 2) else 0
  let T : Finset ((Xᶜ : Finset V) → ZMod 2) :=
    insert 0 (Finset.univ.image (fun x : X => rowf (x : V)))
  have hcard' : T.card ≤ 2 ^ k := hcard
  have pos : 0 < T.card := Finset.card_pos.2 ⟨0, Finset.mem_insert_self _ _⟩
  let e : T ≃ Fin T.card := T.equivFin
  let z : T := ⟨0, Finset.mem_insert_self _ _⟩
  let sw := Equiv.swap (e z) ⟨0, pos⟩
  let ν0 : T → Fin (2 ^ k) := fun t => Fin.castLE hcard' (sw (e t))
  have ν0inj : Function.Injective ν0 := by
    intro a b h
    exact e.injective (sw.injective (Fin.castLE_injective hcard' h))
  have ν0z : ν0 z = ⟨0, by positivity⟩ := by
    simp [ν0, sw, Fin.castLE]
  have hmem : ∀ x ∈ X, rowf x ∈ T := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩)
  refine ⟨fun x => if hx : x ∈ X then ν0 ⟨rowf x, hmem x hx⟩ else ⟨0, by positivity⟩, ?_, ?_⟩
  · intro x hx y hy
    simp only [hx, hy, dite_true]
    have : (ν0 ⟨rowf x, hmem x hx⟩ = ν0 ⟨rowf y, hmem y hy⟩) ↔ rowf x = rowf y := by
      constructor
      · intro h; exact congrArg Subtype.val (ν0inj h)
      · intro h; congr 1; exact Subtype.ext h
    rw [this]
    constructor
    · intro h c hc
      have := congrFun h ⟨c, Finset.mem_compl.2 hc⟩
      simp only [rowf] at this
      by_cases h1 : G.Adj x c <;> by_cases h2 : G.Adj y c <;> simp_all
    · intro h
      funext c
      have := h c (Finset.mem_compl.1 c.2)
      simp only [rowf]
      by_cases h1 : G.Adj x c <;> by_cases h2 : G.Adj y c <;> simp_all
  · intro x hx
    simp only [hx, dite_true]
    have : (ν0 ⟨rowf x, hmem x hx⟩ = ⟨0, by positivity⟩) ↔ rowf x = 0 := by
      rw [← ν0z]
      constructor
      · intro h; exact congrArg Subtype.val (ν0inj h)
      · intro h; congr 1; exact Subtype.ext h
    rw [this]
    constructor
    · intro h c hc
      have := congrFun h ⟨c, Finset.mem_compl.2 hc⟩
      simp only [rowf] at this
      by_cases h1 : G.Adj x c <;> simp_all
    · intro h
      funext c
      have := h c (Finset.mem_compl.1 c.2)
      simp only [rowf]
      simp [this]


theorem exists_compress (m K : ℕ) (hm : 0 < m) (g : Fin m → Fin K) (U : Finset (Fin m)) :
    ∃ F : Fin m → Fin m, (∀ l, F l ≤ l) ∧
      (∀ l ∈ insert (⟨0, hm⟩ : Fin m) U, (F l).val < K) ∧
      (∀ l ∈ insert (⟨0, hm⟩ : Fin m) U, ∀ l' ∈ insert (⟨0, hm⟩ : Fin m) U,
        F l = F l' → g l = g l') ∧ F ⟨0, hm⟩ = ⟨0, hm⟩ := by
  classical
  let z : Fin m := ⟨0, hm⟩
  let V0 : Finset (Fin m) := insert z U
  let rep : Fin m → Fin m := fun l =>
    (insert l (V0.filter (fun l' => g l' = g l))).min' (Finset.insert_nonempty _ _)
  have P1 : ∀ l ∈ V0, rep l ∈ V0 ∧ g (rep l) = g l ∧ rep l ≤ l ∧
      ∀ x ∈ V0, g x = g l → rep l ≤ x := by
    intro l hl
    have hmem := Finset.min'_mem (insert l (V0.filter (fun l' => g l' = g l)))
      (Finset.insert_nonempty _ _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases Finset.mem_insert.1 hmem with h | h
      · show rep l ∈ V0
        rw [show rep l = l from h]; exact hl
      · exact (Finset.mem_filter.1 h).1
    · rcases Finset.mem_insert.1 hmem with h | h
      · rw [show rep l = l from h]
      · exact (Finset.mem_filter.1 h).2
    · exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    · intro x hx hgx
      exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, hgx⟩))
  have P2 : ∀ l ∈ V0, ∀ l' ∈ V0, g l = g l' → rep l = rep l' := by
    intro l hl l' hl' h
    obtain ⟨a1, a2, a3, a4⟩ := P1 l hl
    obtain ⟨b1, b2, b3, b4⟩ := P1 l' hl'
    exact le_antisymm (a4 _ b1 (by rw [b2, h])) (b4 _ a1 (by rw [a2, h]))
  let C : Finset (Fin m) := V0.image rep
  have hCK : C.card ≤ K := by
    have : C.card ≤ (Finset.univ : Finset (Fin K)).card := by
      apply Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_univ _)
      intro a ha b hb hab
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hb
      have e1 := (P1 a' ha').2.1
      have e2 := (P1 b' hb').2.1
      exact P2 a' ha' b' hb' (by rw [← e1, ← e2]; exact hab)
    simpa using this
  let cnt : Fin m → ℕ := fun l => (C.filter (fun c => c < rep l)).card
  have cnt_le : ∀ l, cnt l ≤ (rep l).val := by
    intro l
    calc cnt l ≤ (Finset.Iio (rep l)).card := by
          apply Finset.card_le_card
          intro c hc
          exact Finset.mem_Iio.2 (Finset.mem_filter.1 hc).2
      _ = (rep l).val := Fin.card_Iio _
  have cnt_lt : ∀ l ∈ V0, cnt l < C.card := by
    intro l hl
    apply Finset.card_lt_card
    rw [Finset.filter_ssubset]
    exact ⟨rep l, Finset.mem_image.2 ⟨l, hl, rfl⟩, lt_irrefl _⟩
  have cnt_mono : ∀ l ∈ V0, ∀ l' ∈ V0, rep l < rep l' → cnt l < cnt l' := by
    intro l hl l' hl' h
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨rep l, Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨l, hl, rfl⟩, h⟩,
        fun hh => lt_irrefl _ (Finset.mem_filter.1 hh).2⟩
    · intro c hc
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hc).1,
        lt_trans (Finset.mem_filter.1 hc).2 h⟩
  let F : Fin m → Fin m := fun l =>
    if h : l ∈ V0 then ⟨cnt l, lt_of_le_of_lt (cnt_le l) (rep l).2⟩ else l
  have hF : ∀ l ∈ V0, (F l).val = cnt l := by
    intro l hl
    simp [F, hl]
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro l
    by_cases hl : l ∈ V0
    · show (F l).val ≤ l.val
      rw [hF l hl]
      exact (cnt_le l).trans (P1 l hl).2.2.1
    · simp [F, hl]
  · intro l hl
    rw [hF l hl]
    exact lt_of_lt_of_le (cnt_lt l hl) hCK
  · intro l hl l' hl' h
    have hc : cnt l = cnt l' := by
      have := congrArg Fin.val h
      rwa [hF l hl, hF l' hl'] at this
    have hr : rep l = rep l' := by
      rcases lt_trichotomy (rep l) (rep l') with h1 | h1 | h1
      · exact absurd hc (ne_of_lt (cnt_mono l hl l' hl' h1))
      · exact h1
      · exact absurd hc (ne_of_gt (cnt_mono l' hl' l hl h1))
    rw [← (P1 l hl).2.1, ← (P1 l' hl').2.1, hr]
  · have hz : z ∈ V0 := Finset.mem_insert_self _ _
    apply Fin.ext
    rw [hF z hz]
    have := (cnt_le z).trans (P1 z hz).2.2.1
    exact Nat.le_zero.1 this


def shiftF (k m : ℕ) : Fin m → Fin m := fun l =>
  if h : 0 < l.val ∧ l.val < 2 ^ k ∧ l.val + 2 ^ k - 1 < m then ⟨l.val + 2 ^ k - 1, h.2.2⟩ else l

theorem shiftF_mid (k m : ℕ) (hm : m = 2 ^ (k + 1) - 1) (l : Fin m) (h0 : 0 < l.val)
    (h1 : l.val < 2 ^ k) : (shiftF k m l).val = l.val + 2 ^ k - 1 := by
  have hp : 0 < 2 ^ k := by positivity
  have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  have : l.val + 2 ^ k - 1 < m := by omega
  simp [shiftF, h0, h1, this]

theorem shiftF_fix (k m : ℕ) (l : Fin m) (h : l.val = 0 ∨ 2 ^ k ≤ l.val) : shiftF k m l = l := by
  have : ¬ (0 < l.val ∧ l.val < 2 ^ k ∧ l.val + 2 ^ k - 1 < m) := by omega
  simp [shiftF, this]

theorem shiftF_rank (k m : ℕ) (hm : m = 2 ^ (k + 1) - 1) (l : Fin m) (h : shiftF k m l ≠ l) :
    (if 0 < (shiftF k m l).val ∧ (shiftF k m l).val < 2 ^ k then 1 else 0) <
      (if 0 < l.val ∧ l.val < 2 ^ k then 1 else 0) := by
  have hp : 0 < 2 ^ k := by positivity
  by_cases h0 : l.val = 0 ∨ 2 ^ k ≤ l.val
  · exact absurd (shiftF_fix k m l h0) h
  · have h1 : 0 < l.val := by omega
    have h2 : l.val < 2 ^ k := by omega
    have hv := shiftF_mid k m hm l h1 h2
    have hn : ¬ (0 < (shiftF k m l).val ∧ (shiftF k m l).val < 2 ^ k) := by
      rw [hv]; omega
    rw [if_neg hn, if_pos ⟨h1, h2⟩]
    omega


def InvL {V : Type*} (G : SimpleGraph V) (k m : ℕ) (hm0 : 0 < m) (X : Finset V)
    (lam : V → Fin m) : Prop :=
  (∀ x ∈ X, (lam x).val < 2 ^ k) ∧
  (∀ x ∈ X, ∀ y ∈ X, lam x = lam y → ∀ c, c ∉ X → (G.Adj x c ↔ G.Adj y c)) ∧
  (∀ x ∈ X, lam x = ⟨0, hm0⟩ → ∀ c, c ∉ X → ¬ G.Adj x c)

section Merge
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k m : ℕ)
  (hm : m = 2 ^ (k + 1) - 1) (hm0 : 0 < m)
include hm

/-- facts about the shifted labelling -/
theorem shift_facts (X : Finset V) (l : V → Fin m) (hi : InvL G k m hm0 X l) :
    (∀ x ∈ X, (shiftF k m (l x)).val = 0 ∨ 2 ^ k ≤ (shiftF k m (l x)).val) ∧
    (∀ x ∈ X, ∀ y ∈ X, shiftF k m (l x) = shiftF k m (l y) → l x = l y) ∧
    (∀ x ∈ X, shiftF k m (l x) = ⟨0, hm0⟩ → l x = ⟨0, hm0⟩) ∧
    (∀ x ∈ X, l x = ⟨0, hm0⟩ → shiftF k m (l x) = ⟨0, hm0⟩) := by
  have hp : 0 < 2 ^ k := by positivity
  have key : ∀ x ∈ X, (l x).val = 0 ∧ (shiftF k m (l x)).val = 0 ∨
      0 < (l x).val ∧ (shiftF k m (l x)).val = (l x).val + 2 ^ k - 1 := by
    intro x hx
    by_cases h0 : (l x).val = 0
    · left; exact ⟨h0, by rw [shiftF_fix k m _ (Or.inl h0)]; exact h0⟩
    · right
      have h1 : 0 < (l x).val := by omega
      exact ⟨h1, shiftF_mid k m hm _ h1 (hi.1 x hx)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases key x hx with ⟨_, h⟩ | ⟨h1, h⟩
    · exact Or.inl h
    · right; omega
  · intro x hx y hy h
    have hv := congrArg Fin.val h
    rcases key x hx with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases key y hy with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact Fin.ext (by omega)
    · exfalso; omega
    · exfalso; omega
    · exact Fin.ext (by omega)
  · intro x hx h
    have hv := congrArg Fin.val h
    rcases key x hx with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Fin.ext a1
    · exfalso; simp at hv; omega
  · intro x hx h
    have hv := congrArg Fin.val h
    rcases key x hx with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · exact Fin.ext a2
    · exfalso; simp at hv; omega


omit [Fintype V] in
def mergeLab (X1 : Finset V) (l1 l2 : V → Fin m) : V → Fin m :=
  fun v => if v ∈ X1 then l1 v else shiftF k m (l2 v)

theorem merged_consistency (X1 X2 : Finset V) (hd : Disjoint X1 X2) (l1 l2 : V → Fin m)
    (i1 : InvL G k m hm0 X1 l1) (i2 : InvL G k m hm0 X2 l2) :
    (∀ x ∈ X1 ∪ X2, ∀ y ∈ X1 ∪ X2, mergeLab k m X1 l1 l2 x = mergeLab k m X1 l1 l2 y →
      ∀ c, c ∉ X1 ∪ X2 → (G.Adj x c ↔ G.Adj y c)) ∧
    (∀ x ∈ X1 ∪ X2, mergeLab k m X1 l1 l2 x = ⟨0, hm0⟩ → ∀ c, c ∉ X1 ∪ X2 → ¬ G.Adj x c) := by
  obtain ⟨s1, s2, s3, s4⟩ := shift_facts G k m hm hm0 X2 l2 i2
  have hn1 : ∀ x ∈ X2, x ∉ X1 := fun x hx h => Finset.disjoint_left.1 hd h hx
  have hp : 0 < 2 ^ k := by positivity
  have e1 : ∀ x ∈ X1, mergeLab k m X1 l1 l2 x = l1 x := fun x hx => by simp [mergeLab, hx]
  have e2 : ∀ x ∈ X2, mergeLab k m X1 l1 l2 x = shiftF k m (l2 x) := fun x hx => by
    simp [mergeLab, hn1 x hx]
  refine ⟨?_, ?_⟩
  · intro x hx y hy h c hc
    have hc1 : c ∉ X1 := fun h' => hc (Finset.mem_union_left _ h')
    have hc2 : c ∉ X2 := fun h' => hc (Finset.mem_union_right _ h')
    rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hy with hy | hy
    · rw [e1 x hx, e1 y hy] at h
      exact i1.2.1 x hx y hy h c hc1
    · rw [e1 x hx, e2 y hy] at h
      have hv := congrArg Fin.val h
      have a1 := i1.1 x hx
      rcases s1 y hy with a2 | a2
      · have z1 : l1 x = ⟨0, hm0⟩ := Fin.ext (by show (l1 x).val = 0; omega)
        have z2 : l2 y = ⟨0, hm0⟩ := s3 y hy (Fin.ext a2)
        exact iff_of_false (i1.2.2 x hx z1 c hc1) (i2.2.2 y hy z2 c hc2)
      · omega
    · rw [e2 x hx, e1 y hy] at h
      have hv := congrArg Fin.val h
      have a1 := i1.1 y hy
      rcases s1 x hx with a2 | a2
      · have z1 : l1 y = ⟨0, hm0⟩ := Fin.ext (by show (l1 y).val = 0; omega)
        have z2 : l2 x = ⟨0, hm0⟩ := s3 x hx (Fin.ext a2)
        exact iff_of_false (i2.2.2 x hx z2 c hc2) (i1.2.2 y hy z1 c hc1)
      · omega
    · rw [e2 x hx, e2 y hy] at h
      exact i2.2.1 x hx y hy (s2 x hx y hy h) c hc2
  · intro x hx h c hc
    have hc1 : c ∉ X1 := fun h' => hc (Finset.mem_union_left _ h')
    have hc2 : c ∉ X2 := fun h' => hc (Finset.mem_union_right _ h')
    rcases Finset.mem_union.1 hx with hx | hx
    · rw [e1 x hx] at h
      exact i1.2.2 x hx h c hc1
    · rw [e2 x hx] at h
      exact i2.2.2 x hx (s3 x hx h) c hc2

end Merge


section Merge2
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k m : ℕ)

noncomputable def crossPairs (X1 X2 : Finset V) (lm : V → Fin m) : Finset (Fin m × Fin m) := by
  classical
  exact Finset.univ.filter (fun p => ∃ x ∈ X1, ∃ y ∈ X2, lm x = p.1 ∧ lm y = p.2 ∧ G.Adj x y)

theorem mem_crossPairs (X1 X2 : Finset V) (lm : V → Fin m) (p : Fin m × Fin m) :
    p ∈ crossPairs G m X1 X2 lm ↔ ∃ x ∈ X1, ∃ y ∈ X2, lm x = p.1 ∧ lm y = p.2 ∧ G.Adj x y := by
  classical
  simp [crossPairs]

/-- label facts for pairs in `crossPairs`. -/
theorem crossPairs_range (hm : m = 2 ^ (k + 1) - 1) (hm0 : 0 < m) (X1 X2 : Finset V) (hd : Disjoint X1 X2) (l1 l2 : V → Fin m)
    (i1 : InvL G k m hm0 X1 l1) (i2 : InvL G k m hm0 X2 l2) (p : Fin m × Fin m)
    (hp : p ∈ crossPairs G m X1 X2 (mergeLab k m X1 l1 l2)) :
    1 ≤ p.1.val ∧ p.1.val < 2 ^ k ∧ 2 ^ k ≤ p.2.val := by
  obtain ⟨s1, s2, s3, s4⟩ := shift_facts G k m hm hm0 X2 l2 i2
  have hn1 : ∀ x ∈ X2, x ∉ X1 := fun x hx h => Finset.disjoint_left.1 hd h hx
  obtain ⟨x, hx, y, hy, h1, h2, hadj⟩ := (mem_crossPairs G m X1 X2 _ p).1 hp
  have e1 : mergeLab k m X1 l1 l2 x = l1 x := by simp [mergeLab, hx]
  have e2 : mergeLab k m X1 l1 l2 y = shiftF k m (l2 y) := by simp [mergeLab, hn1 y hy]
  rw [e1] at h1
  rw [e2] at h2
  have hx0 : l1 x ≠ ⟨0, hm0⟩ := fun h => i1.2.2 x hx h y (hn1 y hy) hadj
  have hy0 : l2 y ≠ ⟨0, hm0⟩ := fun h =>
    i2.2.2 y hy h x (fun h' => Finset.disjoint_left.1 hd hx h') (hadj.symm)
  have hx0' : (l1 x).val ≠ 0 := fun h => hx0 (Fin.ext h)
  have hy1 : shiftF k m (l2 y) ≠ ⟨0, hm0⟩ := fun h => hy0 (s3 y hy h)
  have hy2 : (shiftF k m (l2 y)).val ≠ 0 := fun h => hy1 (Fin.ext h)
  have := i1.1 x hx
  rcases s1 y hy with a | a
  · exact absurd a hy2
  · rw [← h1, ← h2]; omega


theorem cross_iff (hm : m = 2 ^ (k + 1) - 1) (hm0 : 0 < m) (X1 X2 : Finset V)
    (hd : Disjoint X1 X2) (l1 l2 : V → Fin m)
    (i1 : InvL G k m hm0 X1 l1) (i2 : InvL G k m hm0 X2 l2) (v w : V) (hv : v ∈ X1)
    (hw : w ∈ X2) :
    ((mergeLab k m X1 l1 l2 v, mergeLab k m X1 l1 l2 w) ∈
        crossPairs G m X1 X2 (mergeLab k m X1 l1 l2)) ↔ G.Adj v w := by
  obtain ⟨s1, s2, s3, s4⟩ := shift_facts G k m hm hm0 X2 l2 i2
  have hn1 : ∀ x ∈ X2, x ∉ X1 := fun x hx h => Finset.disjoint_left.1 hd h hx
  have e1 : ∀ x ∈ X1, mergeLab k m X1 l1 l2 x = l1 x := fun x hx => by simp [mergeLab, hx]
  have e2 : ∀ x ∈ X2, mergeLab k m X1 l1 l2 x = shiftF k m (l2 x) := fun x hx => by
    simp [mergeLab, hn1 x hx]
  constructor
  · intro h
    obtain ⟨x, hx, y, hy, h1, h2, hadj⟩ := (mem_crossPairs G m X1 X2 _ _).1 h
    simp only at h1 h2
    rw [e1 x hx, e1 v hv] at h1
    rw [e2 y hy, e2 w hw] at h2
    have c1 := i1.2.1 x hx v hv h1 y (hn1 y hy)
    have c2 := i2.2.1 y hy w hw (s2 y hy w hw h2) v (fun h' => Finset.disjoint_left.1 hd hv h')
    exact (c2.1 (c1.1 hadj).symm).symm
  · intro h
    exact (mem_crossPairs G m X1 X2 _ _).2 ⟨v, hv, w, hw, rfl, rfl, h⟩

theorem merge_adj (hm : m = 2 ^ (k + 1) - 1) (hm0 : 0 < m) (X1 X2 : Finset V)
    (hd : Disjoint X1 X2) (l1 l2 : V → Fin m)
    (i1 : InvL G k m hm0 X1 l1) (i2 : InvL G k m hm0 X2 l2) (v w : V)
    (hv : v ∈ X1 ∪ X2) (hw : w ∈ X1 ∪ X2) :
    (((v ∈ X1 ∧ w ∈ X1 ∧ G.Adj v w) ∨ (v ∈ X2 ∧ w ∈ X2 ∧ G.Adj v w)) ∨
      (v ≠ w ∧ ((mergeLab k m X1 l1 l2 v, mergeLab k m X1 l1 l2 w) ∈
          crossPairs G m X1 X2 (mergeLab k m X1 l1 l2) ∨
        (mergeLab k m X1 l1 l2 w, mergeLab k m X1 l1 l2 v) ∈
          crossPairs G m X1 X2 (mergeLab k m X1 l1 l2)))) ↔ G.Adj v w := by
  obtain ⟨s1, s2, s3, s4⟩ := shift_facts G k m hm hm0 X2 l2 i2
  have hn1 : ∀ x ∈ X2, x ∉ X1 := fun x hx h => Finset.disjoint_left.1 hd h hx
  have hn2 : ∀ x ∈ X1, x ∉ X2 := fun x hx h => Finset.disjoint_left.1 hd hx h
  have e1 : ∀ x ∈ X1, mergeLab k m X1 l1 l2 x = l1 x := fun x hx => by simp [mergeLab, hx]
  have e2 : ∀ x ∈ X2, mergeLab k m X1 l1 l2 x = shiftF k m (l2 x) := fun x hx => by
    simp [mergeLab, hn1 x hx]
  have R := crossPairs_range G k m hm hm0 X1 X2 hd l1 l2 i1 i2
  have r1 : ∀ x ∈ X1, (mergeLab k m X1 l1 l2 x).val < 2 ^ k := fun x hx => by
    rw [e1 x hx]; exact i1.1 x hx
  have r2 : ∀ x ∈ X2, (mergeLab k m X1 l1 l2 x).val = 0 ∨ 2 ^ k ≤ (mergeLab k m X1 l1 l2 x).val :=
    fun x hx => by rw [e2 x hx]; exact s1 x hx
  rcases Finset.mem_union.1 hv with hv | hv <;> rcases Finset.mem_union.1 hw with hw | hw
  · -- both in X1
    have a1 : ¬ (mergeLab k m X1 l1 l2 v, mergeLab k m X1 l1 l2 w) ∈
        crossPairs G m X1 X2 (mergeLab k m X1 l1 l2) := fun h => by
      have := (R _ h).2.2; have := r1 w hw; simp only at *; omega
    have a2 : ¬ (mergeLab k m X1 l1 l2 w, mergeLab k m X1 l1 l2 v) ∈
        crossPairs G m X1 X2 (mergeLab k m X1 l1 l2) := fun h => by
      have := (R _ h).2.2; have := r1 v hv; simp only at *; omega
    constructor
    · rintro ((⟨_, _, h⟩ | ⟨h, _, _⟩) | ⟨_, h | h⟩)
      · exact h
      · exact absurd h (hn2 v hv)
      · exact absurd h a1
      · exact absurd h a2
    · intro h; exact Or.inl (Or.inl ⟨hv, hw, h⟩)
  · -- v ∈ X1, w ∈ X2
    have a2 : ¬ (mergeLab k m X1 l1 l2 w, mergeLab k m X1 l1 l2 v) ∈
        crossPairs G m X1 X2 (mergeLab k m X1 l1 l2) := fun h => by
      have h3 := (R _ h).1; have h4 := (R _ h).2.1
      simp only at h3 h4
      rcases r2 w hw with h5 | h5 <;> omega
    have hne : v ≠ w := fun h => hn2 v hv (h ▸ hw)
    constructor
    · rintro ((⟨_, h, _⟩ | ⟨h, _, _⟩) | ⟨_, h | h⟩)
      · exact absurd h (hn1 w hw)
      · exact absurd h (hn2 v hv)
      · exact (cross_iff G k m hm hm0 X1 X2 hd l1 l2 i1 i2 v w hv hw).1 h
      · exact absurd h a2
    · intro h
      exact Or.inr ⟨hne, Or.inl ((cross_iff G k m hm hm0 X1 X2 hd l1 l2 i1 i2 v w hv hw).2 h)⟩
  · -- v ∈ X2, w ∈ X1
    have a1 : ¬ (mergeLab k m X1 l1 l2 v, mergeLab k m X1 l1 l2 w) ∈
        crossPairs G m X1 X2 (mergeLab k m X1 l1 l2) := fun h => by
      have h3 := (R _ h).1; have h4 := (R _ h).2.1
      simp only at h3 h4
      rcases r2 v hv with h5 | h5 <;> omega
    have hne : v ≠ w := fun h => hn2 w hw (h ▸ hv)
    constructor
    · rintro ((⟨h, _, _⟩ | ⟨_, h, _⟩) | ⟨_, h | h⟩)
      · exact absurd h (hn1 v hv)
      · exact absurd h (hn2 w hw)
      · exact absurd h a1
      · exact ((cross_iff G k m hm hm0 X1 X2 hd l1 l2 i1 i2 w v hw hv).1 h).symm
    · intro h
      exact Or.inr ⟨hne, Or.inr ((cross_iff G k m hm hm0 X1 X2 hd l1 l2 i1 i2 w v hw hv).2 h.symm)⟩
  · -- both in X2
    have a1 : ¬ (mergeLab k m X1 l1 l2 v, mergeLab k m X1 l1 l2 w) ∈
        crossPairs G m X1 X2 (mergeLab k m X1 l1 l2) := fun h => by
      have h3 := (R _ h).1; have h4 := (R _ h).2.1
      simp only at h3 h4
      rcases r2 v hv with h5 | h5 <;> omega
    have a2 : ¬ (mergeLab k m X1 l1 l2 w, mergeLab k m X1 l1 l2 v) ∈
        crossPairs G m X1 X2 (mergeLab k m X1 l1 l2) := fun h => by
      have h3 := (R _ h).1; have h4 := (R _ h).2.1
      simp only at h3 h4
      rcases r2 w hw with h5 | h5 <;> omega
    constructor
    · rintro ((⟨h, _, _⟩ | ⟨_, _, h⟩) | ⟨_, h | h⟩)
      · exact absurd h (hn1 v hv)
      · exact h
      · exact absurd h a1
      · exact absurd h a2
    · intro h; exact Or.inl (Or.inr ⟨hv, hw, h⟩)

end Merge2


theorem merge_step {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k m : ℕ) (hm : m = 2 ^ (k + 1) - 1) (hm0 : 0 < m)
    (X1 X2 : Finset V) (hd : Disjoint X1 X2) (hk : cutrk G (X1 ∪ X2) ≤ k)
    {t1 t2 : KExpr m} {l1 l2 : V → Fin m} (h1 : Rl t1 G.Adj X1 l1) (h2 : Rl t2 G.Adj X2 l2)
    (i1 : InvL G k m hm0 X1 l1) (i2 : InvL G k m hm0 X2 l2) :
    ∃ (t : KExpr m) (l : V → Fin m), Rl t G.Adj (X1 ∪ X2) l ∧ InvL G k m hm0 (X1 ∪ X2) l := by
  classical
  obtain ⟨t2s, h2s⟩ := Rl.rho h2 (shiftF k m)
    (fun l => if 0 < l.val ∧ l.val < 2 ^ k then 1 else 0) (shiftF_rank k m hm)
  have hu := Rl.union h1 h2s hd
  have hR := crossPairs_range G k m hm hm0 X1 X2 hd l1 l2 i1 i2
  obtain ⟨t3, h3⟩ := Rl.eta_aux (crossPairs G m X1 X2 (mergeLab k m X1 l1 l2))
    (fun p hp => by have := hR p hp; intro h; rw [h] at this; omega) hu
  have h3' : Rl t3 G.Adj (X1 ∪ X2) (mergeLab k m X1 l1 l2) := by
    refine h3.congr (fun v hv w hw => ?_) (fun v _ => rfl)
    exact merge_adj G k m hm hm0 X1 X2 hd l1 l2 i1 i2 v w hv hw
  -- compress
  obtain ⟨hcons1, hcons2⟩ := merged_consistency G k m hm hm0 X1 X2 hd l1 l2 i1 i2
  set X := X1 ∪ X2 with hX
  set lm := mergeLab k m X1 l1 l2 with hlm
  obtain ⟨ν, hν1, hν2⟩ := exists_numbering G X k hk
  let g : Fin m → Fin (2 ^ k) := fun l =>
    if h : ∃ x, x ∈ X ∧ lm x = l then ν h.choose else ⟨0, by positivity⟩
  have gval : ∀ x ∈ X, g (lm x) = ν x := by
    intro x hx
    have h : ∃ x', x' ∈ X ∧ lm x' = lm x := ⟨x, hx, rfl⟩
    simp only [g, dif_pos h]
    obtain ⟨hc1, hc2⟩ := h.choose_spec
    exact (hν1 _ hc1 x hx).2 (hcons1 _ hc1 x hx hc2)
  have gz : g ⟨0, hm0⟩ = ⟨0, by positivity⟩ := by
    by_cases h : ∃ x, x ∈ X ∧ lm x = ⟨0, hm0⟩
    · simp only [g, dif_pos h]
      obtain ⟨hc1, hc2⟩ := h.choose_spec
      exact (hν2 _ hc1).2 (hcons2 _ hc1 hc2)
    · simp only [g, dif_neg h]
  obtain ⟨F, hF1, hF2, hF3, hF4⟩ := exists_compress m (2 ^ k) hm0 g (X.image lm)
  obtain ⟨t4, h4⟩ := Rl.rho h3' F (fun l => l.val) (fun l hl => by
    have := hF1 l
    have h' : (F l).val ≤ l.val := this
    have : (F l).val ≠ l.val := fun h => hl (Fin.ext h)
    show (F l).val < l.val
    omega)
  refine ⟨t4, fun v => F (lm v), h4, ?_, ?_, ?_⟩
  · intro x hx
    exact hF2 _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem lm hx))
  · intro x hx y hy h c hc
    have h' := hF3 _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem lm hx)) _
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem lm hy)) h
    rw [gval x hx, gval y hy] at h'
    exact (hν1 x hx y hy).1 h' c hc
  · intro x hx h c hc
    have h' := hF3 _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem lm hx)) ⟨0, hm0⟩
      (Finset.mem_insert_self _ _) (h.trans hF4.symm)
    rw [gval x hx, gz] at h'
    exact (hν2 x hx).1 h' c hc


theorem single_step {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k m : ℕ) (hm : m = 2 ^ (k + 1) - 1) (hm0 : 0 < m) (v : V)
    (hk : cutrk G {v} ≤ k) :
    ∃ (t : KExpr m) (l : V → Fin m), Rl t G.Adj {v} l ∧ InvL G k m hm0 {v} l := by
  have hp : 0 < 2 ^ k := by positivity
  have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  have hle : 2 ^ k ≤ m := by omega
  obtain ⟨ν, hν1, hν2⟩ := exists_numbering G {v} k hk
  let i : Fin m := ⟨(ν v).val, lt_of_lt_of_le (ν v).2 hle⟩
  refine ⟨KExpr.const i, fun _ => i, ?_, ?_, ?_, ?_⟩
  · refine (Rl.const v i).congr (fun a ha b hb => ?_) (fun _ _ => rfl)
    rw [Finset.mem_singleton] at ha hb
    subst ha; subst hb
    exact ⟨fun h => h.elim, fun h => absurd h (G.loopless.irrefl _)⟩
  · intro x hx
    exact (ν v).2
  · intro x hx y hy _ c hc
    rw [Finset.mem_singleton] at hx hy
    rw [hx, hy]
  · intro x hx h c hc
    rw [Finset.mem_singleton] at hx
    subst hx
    refine (hν2 x (Finset.mem_singleton_self x)).1 (Fin.ext ?_) c hc
    have := congrArg Fin.val h
    simpa [i] using this

theorem build_all {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k m : ℕ) (hm : m = 2 ^ (k + 1) - 1) (hm0 : 0 < m)
    (P : Finset V → Prop) (hw : ∀ X, P X → cutrk G X ≤ k)
    (hs : ∀ X, P X → X.Nonempty ∧ ((∃ v, X = {v}) ∨ ∃ X1 X2, P X1 ∧ P X2 ∧ Disjoint X1 X2 ∧
      X1 ∪ X2 = X ∧ X1.Nonempty ∧ X2.Nonempty)) :
    ∀ X, P X → ∃ (t : KExpr m) (l : V → Fin m), Rl t G.Adj X l ∧ InvL G k m hm0 X l := by
  intro X
  induction' hc : X.card using Nat.strong_induction_on with n ih generalizing X
  intro hX
  obtain ⟨hne, hcase⟩ := hs X hX
  rcases hcase with ⟨v, rfl⟩ | ⟨X1, X2, p1, p2, hd, hU, n1, n2⟩
  · exact single_step G k m hm hm0 v (hw _ hX)
  · have c1 : X1.card < n := by
      rw [← hc, ← hU, Finset.card_union_of_disjoint hd]
      have := Finset.card_pos.2 n2; omega
    have c2 : X2.card < n := by
      rw [← hc, ← hU, Finset.card_union_of_disjoint hd]
      have := Finset.card_pos.2 n1; omega
    obtain ⟨t1, l1, h1, i1⟩ := ih _ c1 X1 rfl p1
    obtain ⟨t2, l2, h2, i2⟩ := ih _ c2 X2 rfl p2
    rw [← hU] at hX ⊢
    exact merge_step G k m hm hm0 X1 X2 hd (hw _ hX) h1 h2 i1 i2


section TreeFacts
variable {N : Type*} [DecidableEq N] {T : SimpleGraph N}

theorem tree_bridge (hT : T.IsTree) {u p : N} (h : T.Adj u p) :
    ¬ (T.deleteEdges {s(u, p)}).Reachable u p :=
  SimpleGraph.isBridge_iff.1 (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hT.IsAcyclic h)

theorem avoid_edge {a b : N} (q : T.Walk a b) (u p : N) (hq : u ∉ q.support) :
    s(u, p) ∉ q.edges := fun h => hq (q.fst_mem_support_of_mem_edges h)

theorem comp_iff_avoid (hT : T.IsTree) {u p : N} (h : T.Adj u p) (x : N) :
    (T.deleteEdges {s(u, p)}).Reachable p x ↔ ∃ q : T.Walk p x, u ∉ q.support := by
  constructor
  · rintro ⟨q'⟩
    by_cases hu : u ∈ q'.support
    · exfalso
      exact tree_bridge hT h (SimpleGraph.Reachable.symm ⟨q'.takeUntil u hu⟩)
    · exact ⟨q'.mapLe (SimpleGraph.deleteEdges_le _), by
        rwa [SimpleGraph.Walk.support_mapLe_eq_support]⟩
  · rintro ⟨q, hq⟩
    exact ⟨q.toDeleteEdge _ (avoid_edge q u p hq)⟩

theorem comp_iff_nbr (hT : T.IsTree) {u w : N} (h : T.Adj u w) (x : N) (hx : x ≠ u) :
    (T.deleteEdges {s(u, w)}).Reachable u x ↔
      ∃ p, T.Adj u p ∧ p ≠ w ∧ ∃ q : T.Walk p x, u ∉ q.support := by
  constructor
  · rintro hr
    obtain ⟨r, hr⟩ := hr.exists_isPath
    cases r with
    | nil => exact absurd rfl hx
    | cons hadj q =>
      rw [SimpleGraph.Walk.cons_isPath_iff] at hr
      rw [SimpleGraph.deleteEdges_adj] at hadj
      refine ⟨_, hadj.1, ?_, q.mapLe (SimpleGraph.deleteEdges_le _), ?_⟩
      · intro hpw
        apply hadj.2
        rw [hpw]; exact Set.mem_singleton _
      · rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hr.2
  · rintro ⟨p, hp, hpw, q, hq⟩
    have hadj : (T.deleteEdges {s(u, w)}).Adj u p := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hp, ?_⟩
      intro hm
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hm
      rcases hm with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact hpw h2
      · exact T.loopless.irrefl _ (h1 ▸ h)
    exact hadj.reachable.trans ⟨q.toDeleteEdge _ (avoid_edge q u w hq)⟩

theorem comp_disjoint (hT : T.IsTree) {u p q : N} (hp : T.Adj u p) (hq : T.Adj u q) (hpq : p ≠ q)
    (x : N) : ¬ ((∃ r : T.Walk p x, u ∉ r.support) ∧ (∃ r : T.Walk q x, u ∉ r.support)) := by
  rintro ⟨⟨r1, h1⟩, ⟨r2, h2⟩⟩
  have hr : u ∉ (r1.append r2.reverse).support := by
    rw [SimpleGraph.Walk.mem_support_append_iff]
    simp only [SimpleGraph.Walk.support_reverse, List.mem_reverse]
    tauto
  have hreach : (T.deleteEdges {s(u, p)}).Reachable p q :=
    ⟨(r1.append r2.reverse).toDeleteEdge _ (avoid_edge _ u p hr)⟩
  have hadj : (T.deleteEdges {s(u, p)}).Adj q u := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hq.symm, ?_⟩
    intro hm
    rw [Set.mem_singleton_iff, Sym2.eq_iff] at hm
    rcases hm with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact T.loopless.irrefl _ (h1 ▸ hq)
    · exact hpq h1.symm
  exact tree_bridge hT hp (hreach.trans hadj.reachable).symm

theorem comp_partition (hT : T.IsTree) {u w : N} (h : T.Adj u w) (y : N) :
    (T.deleteEdges {s(u, w)}).Reachable u y ∨ (T.deleteEdges {s(u, w)}).Reachable w y := by
  obtain ⟨r, hr⟩ := hT.connected.exists_isPath u y
  cases r with
  | nil => exact Or.inl (SimpleGraph.Reachable.refl u)
  | @cons _ a _ hadj q =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hr
    by_cases hpw : a = w
    · right
      subst hpw
      exact (comp_iff_avoid hT h y).2 ⟨q, hr.2⟩
    · left
      have hy : y ≠ u := fun e => hr.2 (e ▸ q.end_mem_support)
      exact (comp_iff_nbr hT h y hy).2 ⟨_, hadj, hpw, q, hr.2⟩

end TreeFacts


namespace ApproxCliqueWidth.Certificate.BranchDecomp
variable {V : Type*} [Fintype V] (D : BranchDecomp V)

theorem mem_side_iff (u w : Fin D.n) (x : V) :
    x ∈ D.side u w ↔ (D.T.deleteEdges {s(u, w)}).Reachable u (D.L x) := by
  classical
  simp [BranchDecomp.side]

theorem mem_side_decomp (u w : Fin D.n) (h : D.T.Adj u w) (x : V) :
    x ∈ D.side u w ↔ D.L x = u ∨ ∃ p, D.T.Adj u p ∧ p ≠ w ∧ x ∈ D.side p u := by
  rw [mem_side_iff]
  by_cases hx : D.L x = u
  · simp only [hx, true_or, iff_true]
    exact SimpleGraph.Reachable.refl u
  · rw [comp_iff_nbr D.isTree h _ hx]
    simp only [hx, false_or]
    constructor
    · rintro ⟨p, hp, hpw, hq⟩
      refine ⟨p, hp, hpw, ?_⟩
      rw [mem_side_iff, Sym2.eq_swap, comp_iff_avoid D.isTree hp]
      exact hq
    · rintro ⟨p, hp, hpw, hq⟩
      refine ⟨p, hp, hpw, ?_⟩
      rw [mem_side_iff, Sym2.eq_swap, comp_iff_avoid D.isTree hp] at hq
      exact hq

theorem side_disj (u p q : Fin D.n) (hp : D.T.Adj u p) (hq : D.T.Adj u q) (hpq : p ≠ q) :
    Disjoint (D.side p u) (D.side q u) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  rw [mem_side_iff, Sym2.eq_swap, comp_iff_avoid D.isTree hp] at hx1
  rw [mem_side_iff, Sym2.eq_swap, comp_iff_avoid D.isTree hq] at hx2
  exact comp_disjoint D.isTree hp hq hpq _ ⟨hx1, hx2⟩

end ApproxCliqueWidth.Certificate.BranchDecomp


namespace ApproxCliqueWidth.Certificate.BranchDecomp
variable {V : Type*} [Fintype V] (D : BranchDecomp V)

noncomputable def compSz (u w : Fin D.n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun y => (D.T.deleteEdges {s(u, w)}).Reachable u y)).card

def Pt (X : Finset V) : Prop := ∃ a b, D.T.Adj a b ∧ X = D.side a b

theorem compSz_lt (u w p : Fin D.n) (h : D.T.Adj u w) (hp : D.T.Adj u p) (hpw : p ≠ w) :
    D.compSz p u < D.compSz u w := by
  classical
  unfold compSz
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨u, ?_, ?_⟩
    · simp [SimpleGraph.Reachable.refl u]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Sym2.eq_swap, comp_iff_avoid D.isTree hp]
      rintro ⟨q, hq⟩
      exact hq q.end_mem_support
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [Sym2.eq_swap, comp_iff_avoid D.isTree hp] at hy
    obtain ⟨q, hq⟩ := hy
    have hyu : y ≠ u := fun e => hq (e ▸ q.end_mem_support)
    exact (comp_iff_nbr D.isTree h y hyu).2 ⟨p, hp, hpw, q, hq⟩

theorem nbr_two (u w p : Fin D.n) (hw : D.T.Adj u w) (hp : D.T.Adj u p) (hpw : p ≠ w) :
    2 ≤ (D.T.neighborSet u).ncard := by
  have : ({w, p} : Set (Fin D.n)) ⊆ D.T.neighborSet u := by
    intro y hy
    rcases hy with rfl | rfl
    · exact hw
    · exact hp
  calc 2 = ({w, p} : Set (Fin D.n)).ncard := (Set.ncard_pair (Ne.symm hpw)).symm
    _ ≤ _ := Set.ncard_le_ncard this (Set.toFinite _)

theorem no_third (u w p1 p2 p : Fin D.n) (hw : D.T.Adj u w) (h1 : D.T.Adj u p1)
    (h2 : D.T.Adj u p2) (h3 : D.T.Adj u p) (a1 : p1 ≠ w) (a2 : p2 ≠ w) (a3 : p ≠ w)
    (b1 : p2 ≠ p1) (b2 : p ≠ p1) (b3 : p ≠ p2) : False := by
  classical
  have hsub : (({w, p1, p2, p} : Finset (Fin D.n)) : Set (Fin D.n)) ⊆ D.T.neighborSet u := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hw
    · exact h1
    · exact h2
    · exact h3
  have hc : ({w, p1, p2, p} : Finset (Fin D.n)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm a1, Ne.symm a2, Ne.symm a3]),
      Finset.card_insert_of_notMem (by simp [Ne.symm b1, Ne.symm b2]),
      Finset.card_pair b3.symm]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hc] at this
  have := D.subcubic u
  omega

end ApproxCliqueWidth.Certificate.BranchDecomp


namespace ApproxCliqueWidth.Certificate.BranchDecomp
variable {V : Type*} [Fintype V] [DecidableEq V] (D : BranchDecomp V)

theorem side_struct : ∀ (n : ℕ) (u w : Fin D.n), D.compSz u w = n → D.T.Adj u w →
    (D.side u w).Nonempty ∧ ((∃ v, D.side u w = {v}) ∨
      ∃ X1 X2, D.Pt X1 ∧ D.Pt X2 ∧ Disjoint X1 X2 ∧ X1 ∪ X2 = D.side u w ∧ X1.Nonempty ∧
        X2.Nonempty) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u w hn h
  by_cases hex : ∃ p, D.T.Adj u p ∧ p ≠ w
  · obtain ⟨p1, hp1, hp1w⟩ := hex
    have hnotleaf : ∀ x, D.L x ≠ u := by
      intro x hx
      have h2 := nbr_two D u w p1 h hp1 hp1w
      have h1 := D.L_leaf x
      rw [hx] at h1
      omega
    have decomp : ∀ x, x ∈ D.side u w ↔ ∃ p, D.T.Adj u p ∧ p ≠ w ∧ x ∈ D.side p u := by
      intro x
      rw [mem_side_decomp D u w h x]
      simp [hnotleaf x]
    have ih1 := ih _ (hn ▸ compSz_lt D u w p1 h hp1 hp1w) p1 u rfl hp1.symm
    by_cases hex2 : ∃ p2, D.T.Adj u p2 ∧ p2 ≠ w ∧ p2 ≠ p1
    · obtain ⟨p2, hp2, hp2w, hp21⟩ := hex2
      have ih2 := ih _ (hn ▸ compSz_lt D u w p2 h hp2 hp2w) p2 u rfl hp2.symm
      have hU : D.side p1 u ∪ D.side p2 u = D.side u w := by
        ext x
        rw [Finset.mem_union, decomp x]
        constructor
        · rintro (hx | hx)
          · exact ⟨p1, hp1, hp1w, hx⟩
          · exact ⟨p2, hp2, hp2w, hx⟩
        · rintro ⟨p, hp, hpw, hx⟩
          by_cases a : p = p1
          · subst a; exact Or.inl hx
          · by_cases b : p = p2
            · subst b; exact Or.inr hx
            · exact (no_third D u w p1 p2 p h hp1 hp2 hp hp1w hp2w hpw hp21 a b).elim
      refine ⟨?_, Or.inr ⟨D.side p1 u, D.side p2 u, ⟨p1, u, hp1.symm, rfl⟩,
        ⟨p2, u, hp2.symm, rfl⟩, side_disj D u p1 p2 hp1 hp2 (Ne.symm hp21), hU, ih1.1, ih2.1⟩⟩
      rw [← hU]
      exact ih1.1.mono Finset.subset_union_left
    · have heq : D.side u w = D.side p1 u := by
        ext x
        rw [decomp x]
        constructor
        · rintro ⟨p, hp, hpw, hx⟩
          have : p = p1 := by
            by_contra hne
            exact hex2 ⟨p, hp, hpw, hne⟩
          rwa [this] at hx
        · intro hx
          exact ⟨p1, hp1, hp1w, hx⟩
      rw [heq]
      exact ih1
  · push Not at hex
    have hnb : D.T.neighborSet u = {w} := by
      ext y
      simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
      constructor
      · exact hex y
      · rintro rfl; exact h
    obtain ⟨v, hv⟩ := D.L_surjective u (by rw [hnb, Set.ncard_singleton])
    have heq : D.side u w = {v} := by
      ext x
      rw [mem_side_decomp D u w h x, Finset.mem_singleton]
      constructor
      · rintro (hx | ⟨p, hp, hpw, _⟩)
        · exact D.L_injective (hx.trans hv.symm)
        · exact absurd (hex p hp) hpw
      · rintro rfl; exact Or.inl hv
    rw [heq]
    exact ⟨Finset.singleton_nonempty v, Or.inl ⟨v, rfl⟩⟩

end ApproxCliqueWidth.Certificate.BranchDecomp


theorem hasKExpr_of_rl {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (m : ℕ)
    {t : KExpr m} {l : V → Fin m} (h : Rl t G.Adj Finset.univ l) : HasKExpr G m := by
  obtain ⟨e, h1, _⟩ := h
  refine ⟨t, ⟨⟨e.trans (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)), ?_⟩⟩⟩
  intro a b
  simp only [Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply]
  exact (h1 a b).symm

theorem cutrk_univ_eq_zero {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : cutrk G Finset.univ = 0 := by
  have := cutrk_isSymmetric G ∅
  rw [Finset.compl_empty] at this
  rw [← this]
  exact cutrk_empty_eq_zero' G

theorem rwd_bound_cwd {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hG : BwLE (cutrk G) k) :
    HasKExpr G (2 ^ (k + 1) - 1) := by
  classical
  have hp : 0 < 2 ^ (k + 1) := by positivity
  have hm0 : 0 < 2 ^ (k + 1) - 1 := by
    have : 2 ≤ 2 ^ (k + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hV : Fintype.card V ≤ 1
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.1 (by
      have : 0 < Fintype.card V := Fintype.card_pos
      rw [Finset.card_univ]; omega : (Finset.univ : Finset V).card = 1)
    have hk : cutrk G {v} ≤ k := by
      rw [← hv, cutrk_univ_eq_zero]; exact_mod_cast Nat.zero_le k
    obtain ⟨t, l, h1, _⟩ := single_step G k _ rfl hm0 v hk
    rw [← hv] at h1
    exact hasKExpr_of_rl G _ h1
  · have hV2 : 2 ≤ Fintype.card V := by omega
    rcases hG with ⟨h, _⟩ | ⟨D, hD⟩
    · exact absurd h hV
    -- pick an edge
    obtain ⟨v0⟩ := ‹Nonempty V›
    have hne : (D.T.neighborSet (D.L v0)).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by rw [D.L_leaf v0]; norm_num)
    obtain ⟨w, hw⟩ := hne
    have huw : D.T.Adj (D.L v0) w := hw
    set u := D.L v0 with hu
    have hP : ∀ X, D.Pt X → cutrk G X ≤ k := by
      rintro X ⟨a, b, hab, rfl⟩
      exact hD a b hab
    have hS : ∀ X, D.Pt X → X.Nonempty ∧ ((∃ v, X = {v}) ∨ ∃ X1 X2, D.Pt X1 ∧ D.Pt X2 ∧
        Disjoint X1 X2 ∧ X1 ∪ X2 = X ∧ X1.Nonempty ∧ X2.Nonempty) := by
      rintro X ⟨a, b, hab, rfl⟩
      exact BranchDecomp.side_struct D _ a b rfl hab
    have hb := build_all G k _ rfl hm0 D.Pt hP hS
    obtain ⟨t1, l1, h1, i1⟩ := hb (D.side u w) ⟨u, w, huw, rfl⟩
    obtain ⟨t2, l2, h2, i2⟩ := hb (D.side w u) ⟨w, u, huw.symm, rfl⟩
    have hdisj : Disjoint (D.side u w) (D.side w u) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [BranchDecomp.mem_side_iff] at hx1 hx2
      rw [Sym2.eq_swap] at hx2
      exact tree_bridge D.isTree huw (hx1.trans hx2.symm)
    have hunion : D.side u w ∪ D.side w u = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      rw [BranchDecomp.mem_side_iff, BranchDecomp.mem_side_iff, Sym2.eq_swap (a := w) (b := u)]
      exact comp_partition D.isTree huw (D.L x)
    have hk : cutrk G (D.side u w ∪ D.side w u) ≤ k := by
      rw [hunion, cutrk_univ_eq_zero]; exact_mod_cast Nat.zero_le k
    obtain ⟨t, l, h, _⟩ := merge_step G k _ rfl hm0 _ _ hdisj hk h1 h2 i1 i2
    rw [hunion] at h
    exact hasKExpr_of_rl G _ h


open ApproxCliqueWidth.Certificate in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ k : ℕ, HasKExpr G k → BwLE (cutrk G) k) ∧
    (Nonempty V → ∀ k : ℕ, BwLE (cutrk G) k → HasKExpr G (2 ^ (k + 1) - 1)) := by
  refine ⟨fun k h => cwd_bound_rwd G k h, fun hne k h => ?_⟩
  haveI := hne
  exact rwd_bound_cwd G k h
