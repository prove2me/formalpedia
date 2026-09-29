-- Prove2me | solution 1 for ApproxCliqueWidth.Certificate.bw_ge_of_wellLinked
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:51:46.666764+00:00
-- url     : https://prove2.me/submissions/543689fb-1d4e-495a-958c-cbd11a6315db

import Mathlib
import Definitions.Def_ApproxCliqueWidth_Certificate_SetFunction
import Definitions.Def_ApproxCliqueWidth_Certificate_BranchDecomp

namespace ApproxCliqueWidth.Certificate

open SimpleGraph

theorem aux_bwwl_bridge {n : ℕ} {T : SimpleGraph (Fin n)} (hT : T.IsTree) {u w : Fin n}
    (h : T.Adj u w) : ¬ (T.deleteEdges {s(u, w)}).Reachable u w :=
  isBridge_iff.mp (isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic h)

theorem aux_bwwl_reach_of_walk {n : ℕ} {T G : SimpleGraph (Fin n)} (hGT : G ≤ T)
    {a b c d : Fin n} (p : G.Walk a b) (hc : c ∉ p.support) :
    (T.deleteEdges {s(c, d)}).Reachable a b := by
  refine ⟨p.transfer _ ?_⟩
  intro e he
  rw [edgeSet_deleteEdges]
  refine ⟨edgeSet_subset_edgeSet.mpr hGT (p.edges_subset_edgeSet he), ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hed
  subst hed
  exact hc (p.fst_mem_support_of_mem_edges he)

theorem aux_bwwl_first_step {n : ℕ} {T : SimpleGraph (Fin n)} {a b : Fin n} (hab : a ≠ b)
    (hr : T.Reachable a b) : ∃ c, T.Adj a c ∧ (T.deleteEdges {s(c, a)}).Reachable c b := by
  classical
  obtain ⟨p0⟩ := hr
  have hp := p0.bypass_isPath
  generalize p0.bypass = p at hp
  cases p with
  | nil => exact absurd rfl hab
  | cons h q =>
    rw [Walk.cons_isPath_iff] at hp
    refine ⟨_, h, ?_⟩
    rw [Sym2.eq_swap]
    exact aux_bwwl_reach_of_walk le_rfl q hp.2

theorem aux_bwwl_mem_side {V : Type*} [Fintype V] (D : BranchDecomp V) (u w : Fin D.n) (x : V) :
    x ∈ D.side u w ↔ (D.T.deleteEdges {s(u, w)}).Reachable u (D.L x) := by
  unfold BranchDecomp.side
  simp

theorem aux_bwwl_main {V : Type*} [Fintype V] [DecidableEq V]
    (f : Finset V → ℤ) (k : ℕ) (hk : k ≠ 1) (W : Finset V) (hWcard : W.card = k)
    (hW : IsWellLinked f W) (D : BranchDecomp V)
    (hcon : ∀ u w : Fin D.n, D.T.Adj u w → 3 * f (D.side u w) < k) : False := by
  classical
  have hT := D.isTree
  -- the two sides of an edge are disjoint
  have hdisj : ∀ u w : Fin D.n, D.T.Adj u w → Disjoint (D.side u w) (D.side w u) := by
    intro u w huw
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [aux_bwwl_mem_side] at hx1 hx2
    rw [Sym2.eq_swap] at hx2
    exact aux_bwwl_bridge hT huw (hx1.trans hx2.symm)
  -- each edge has a small side
  have hA : ∀ u w, D.T.Adj u w →
      3 * (W ∩ D.side u w).card < k ∨ 3 * (W ∩ D.side w u).card < k := by
    intro u w huw
    have hU : W ∩ D.side u w ∪ W \ D.side u w = W := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    have hDj : Disjoint (W ∩ D.side u w) (W \ D.side u w) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hx1 hx2
      exact hx2.2 hx1.2
    have h1 := hW (W ∩ D.side u w) (W \ D.side u w) hU hDj (D.side u w)
      Finset.inter_subset_right Finset.disjoint_sdiff
    have h2 := hcon u w huw
    have h3 : (W ∩ D.side w u).card ≤ (W \ D.side u w).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_sdiff]
      exact ⟨hx.1, fun h => Finset.disjoint_left.mp (hdisj u w huw) h hx.2⟩
    omega
  -- an edge exists
  have hn := D.two_le
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin D.n, D.T.Adj a b := by
    have hne : (⟨0, by omega⟩ : Fin D.n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    obtain ⟨c, hc, -⟩ := aux_bwwl_first_step hne (hT.connected.preconnected _ _)
    exact ⟨_, _, hc⟩
  -- maximal oriented edge
  let comp : Fin D.n × Fin D.n → ℕ := fun e =>
    (Finset.univ.filter (fun y => (D.T.deleteEdges {s(e.1, e.2)}).Reachable e.1 y)).card
  let P := Finset.univ.filter (fun e : Fin D.n × Fin D.n =>
    D.T.Adj e.1 e.2 ∧ 3 * (W ∩ D.side e.1 e.2).card < k)
  have hPne : P.Nonempty := by
    rcases hA a b hab with h | h
    · exact ⟨(a, b), by simp [P, hab, h]⟩
    · exact ⟨(b, a), by simp [P, hab.symm, h]⟩
  obtain ⟨⟨t, s⟩, htsP, hmax⟩ := Finset.exists_max_image P comp hPne
  simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at htsP
  obtain ⟨hts, hsmall⟩ := htsP
  -- strict monotonicity of components
  have hE : ∀ r, D.T.Adj s r → r ≠ t → comp (t, s) < comp (s, r) := by
    intro r hsr hrt
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨s, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Reachable.refl _
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact aux_bwwl_bridge hT hts
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      obtain ⟨p⟩ := hy
      have hsp : s ∉ p.support := fun hs => aux_bwwl_bridge hT hts ⟨p.takeUntil s hs⟩
      have h1 : (D.T.deleteEdges {s(s, r)}).Reachable t y :=
        aux_bwwl_reach_of_walk (deleteEdges_le _) p hsp
      have h2 : (D.T.deleteEdges {s(s, r)}).Adj s t := by
        rw [deleteEdges_adj]
        refine ⟨hts.symm, ?_⟩
        simp only [Set.mem_singleton_iff, Sym2.congr_right]
        exact fun h => hrt h.symm
      exact h2.reachable.trans h1
  -- s is a sink
  have hD : ∀ r, D.T.Adj s r → 3 * (W ∩ D.side r s).card < k := by
    intro r hsr
    by_cases hrt : r = t
    · subst hrt; exact hsmall
    · rcases hA s r hsr with h | h
      · exfalso
        have h4 := hmax (s, r) (by simp [P, hsr, h])
        have h5 := hE r hsr hrt
        omega
      · exact h
  -- covering
  have hF : ∀ x, D.L x ≠ s → ∃ r, D.T.Adj s r ∧ x ∈ D.side r s := by
    intro x hx
    obtain ⟨r, hr, hreach⟩ := aux_bwwl_first_step (Ne.symm hx) (hT.connected.preconnected _ _)
    exact ⟨r, hr, (aux_bwwl_mem_side D r s x).mpr hreach⟩
  -- counting
  let N := Finset.univ.filter (fun r => D.T.Adj s r)
  have hNcard : (D.T.neighborSet s).ncard = N.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext r
    simp [N]
  have hN3 : N.card ≤ 3 := hNcard ▸ D.subcubic s
  have hcover : W ⊆ N.biUnion (fun r => W ∩ D.side r s) ∪ W.filter (fun x => D.L x = s) := by
    intro x hx
    by_cases hxs : D.L x = s
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxs⟩)
    · obtain ⟨r, hr, hxr⟩ := hF x hxs
      refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r, ?_, ?_⟩)
      · simp [N, hr]
      · exact Finset.mem_inter.mpr ⟨hx, hxr⟩
  have hcard1 := Finset.card_le_card hcover
  have hcard2 := Finset.card_union_le (N.biUnion (fun r => W ∩ D.side r s))
    (W.filter (fun x => D.L x = s))
  have hcard3 := Finset.card_biUnion_le (s := N) (t := fun r => W ∩ D.side r s)
  have hk1 : 1 ≤ k := by omega
  by_cases hleaf : ∃ x0, D.L x0 = s
  · obtain ⟨x0, hx0⟩ := hleaf
    have hN1 : N.card = 1 := by
      rw [← hNcard, ← hx0]; exact D.L_leaf x0
    obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp hN1
    have hr0N : r0 ∈ N := by rw [hr0]; exact Finset.mem_singleton_self _
    have hsr0 : D.T.Adj s r0 := by simpa [N] using hr0N
    have hsum : ∑ r ∈ N, (W ∩ D.side r s).card = (W ∩ D.side r0 s).card := by
      rw [hr0, Finset.sum_singleton]
    have hfil : (W.filter (fun x => D.L x = s)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      simp only [Finset.mem_filter] at hx hy
      exact D.L_injective (hx.2.trans hy.2.symm)
    have := hD r0 hsr0
    omega
  · push_neg at hleaf
    have hfil : (W.filter (fun x => D.L x = s)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _
      exact hleaf x
    have hsum : ∑ r ∈ N, (3 * (W ∩ D.side r s).card + 1) ≤ N.card • k := by
      apply Finset.sum_le_card_nsmul
      intro r hr
      have hsr : D.T.Adj s r := by simpa [N] using hr
      have := hD r hsr
      omega
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul, smul_eq_mul,
      mul_one] at hsum
    interval_cases h : N.card <;> omega

end ApproxCliqueWidth.Certificate

open ApproxCliqueWidth.Certificate

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (f : Finset V → ℤ) (hsym : IsSymmetric f) (hsub : IsSubmodular f)
    (h0 : f ∅ = 0) (k : ℕ) (hk : k ≠ 1) (W : Finset V) (hWcard : W.card = k)
    (hW : IsWellLinked f W) :
    ∀ D : BranchDecomp V, ∃ u w : Fin D.n, D.T.Adj u w ∧ (k : ℤ) ≤ 3 * f (D.side u w) := by
  intro D
  by_contra hcon
  push_neg at hcon
  exact aux_bwwl_main f k hk W hWcard hW D hcon
