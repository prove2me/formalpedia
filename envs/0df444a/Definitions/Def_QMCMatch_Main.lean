-- Prove2me | Definitions.Def_QMCMatch_Main
-- name    : QMCMatch_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T15:34:37.190197+00:00
-- url     : https://prove2.me/theorems/005c1b45-bfa1-4633-8077-7f6a5c090613
-- title:
--   Edmonds' matching polytope theorem, weighted form
-- statement:
--   Let $x\ge 0$ be an edge vector on the complete graph on $n$ vertices with $x(\delta(v))\le 1$ for every vertex $v$ and $x(E[S])\le(|S|-1)/2$ for every odd vertex set $S$. Then for all nonnegative integer weights (`edmonds_nat`) and all nonnegative rational weights (`edmonds_rat`) there is a matching $M$ with $\sum_e w_ex_e\le w(M)$. The proof is by induction on the total integer weight, following Schrijver's proof of the Cunningham-Marsh formula with the primal point in place of a dual solution: split along components of the positive-weight graph; if some vertex is covered by every maximum-weight matching, lower the weights at that vertex by one and use its degree constraint; otherwise lower all positive weights by one and use the odd-set constraint of the whole component together with the weighted Gallai lemma.
-- source:
--   Supporting library for QuantumMaxCutEnergy.matching_polytope_integral_rounding (Prove2me Quantum Max-Cut campaign). Edmonds, Maximum matching and a polyhedron with 0,1-vertices, J. Res. Nat. Bur. Standards 69B, 1965; proof after Schrijver, Short proofs on the matching polyhedron, J. Combin. Theory Ser. B 34, 1983, and Combinatorial Optimization, Section 25.4 (Cunningham-Marsh formula).

import Definitions.Def_QMCMatch_Claims

/-!
Edmonds' matching polytope theorem in weighted form: a nonnegative edge vector that
satisfies the degree constraints and all odd-set constraints is dominated, for every
nonnegative weight, by an integral matching.
-/

noncomputable section
open scoped BigOperators
open Classical
open QuantumMaxCutEnergy

namespace QMCMatch

variable {n : ℕ}

/-- The linear objective of an integer weight at the fractional point `x`. -/
def Lx (x : Edge n → ℝ) (w : Edge n → ℕ) : ℝ := ∑ e, (w e : ℝ) * x e

theorem mem_supp_iff (w : Edge n → ℕ) (e : Edge n) : e ∈ supp w ↔ 0 < w e := by
  simp [supp]

theorem eq_zero_of_not_mem_supp {w : Edge n → ℕ} {e : Edge n} (h : e ∉ supp w) :
    w e = 0 := by
  rw [mem_supp_iff] at h
  omega

theorem wt_cast (w : Edge n → ℕ) (M : Finset (Edge n)) :
    (∑ e ∈ M, (w e : ℝ)) = ((wt w M : ℕ) : ℝ) := by
  simp [wt]

theorem Lx_add (x : Edge n → ℝ) (w w1 w2 : Edge n → ℕ) (h : ∀ e, w e = w1 e + w2 e) :
    Lx x w = Lx x w1 + Lx x w2 := by
  unfold Lx
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [h e]
  push_cast
  ring

theorem Lx_ind (x : Edge n → ℝ) (D : Finset (Edge n)) (ind : Edge n → ℕ)
    (hind : ∀ e, ind e = if e ∈ D then 1 else 0) :
    Lx x ind = ∑ e ∈ D, x e := by
  unfold Lx
  rw [← Finset.sum_subset (Finset.subset_univ D) (fun e _ he => by simp [hind e, he])]
  exact Finset.sum_congr rfl fun e he => by simp [hind e, he]

/-- Lowering the weight by one on a set `D` of positive edges. -/
theorem dec_step (x : Edge n → ℝ) (w : Edge n → ℕ) (D : Finset (Edge n))
    (hD : D ⊆ supp w) (hDne : D.Nonempty) (c : ℝ) (hc : ∑ e ∈ D, x e ≤ c) (ν : ℕ)
    (ih : ∀ w' : Edge n → ℕ, ∑ e, w' e < ∑ e, w e →
      ∃ M, IsM M ∧ Lx x w' ≤ ((wt w' M : ℕ) : ℝ))
    (hbound : ∀ N, IsM N → N ⊆ supp w →
      ((wt w N : ℕ) : ℝ) - ((N ∩ D).card : ℝ) + c ≤ (ν : ℝ)) :
    Lx x w ≤ (ν : ℝ) := by
  obtain ⟨ind, hind⟩ : ∃ ind : Edge n → ℕ, ∀ e, ind e = if e ∈ D then 1 else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨w', hw'⟩ : ∃ w' : Edge n → ℕ, ∀ e, w' e = w e - ind e := ⟨_, fun _ => rfl⟩
  have hpos : ∀ e ∈ D, 1 ≤ w e := fun e he => (mem_supp_iff w e).1 (hD he)
  have hsplit : ∀ e, w e = w' e + ind e := by
    intro e
    rw [hw' e, hind e]
    split_ifs with he
    · have := hpos e he
      omega
    · omega
  have hlt : ∑ e, w' e < ∑ e, w e := by
    obtain ⟨d, hd⟩ := hDne
    refine Finset.sum_lt_sum (fun e _ => by have := hsplit e; omega)
      ⟨d, Finset.mem_univ _, ?_⟩
    have h1 := hsplit d
    have h2 : ind d = 1 := by rw [hind d, if_pos hd]
    omega
  obtain ⟨M', hM', hle⟩ := ih w' hlt
  have hN := isM_subset hM' (Finset.inter_subset_left : M' ∩ supp w ⊆ M')
  have hwt1 : wt w' (M' ∩ supp w) = wt w' M' := by
    unfold wt
    refine Finset.sum_subset Finset.inter_subset_left fun e he hne => ?_
    have h0 : w e = 0 :=
      eq_zero_of_not_mem_supp fun h => hne (Finset.mem_inter.2 ⟨he, h⟩)
    have := hsplit e
    omega
  have hcard : ((M' ∩ supp w) ∩ D).card = ∑ e ∈ M' ∩ supp w, ind e := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_ite_mem]
    exact Finset.sum_congr rfl fun e _ => (hind e).symm
  have hwt2 : wt w' (M' ∩ supp w) + ((M' ∩ supp w) ∩ D).card = wt w (M' ∩ supp w) := by
    rw [hcard]
    unfold wt
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => (hsplit e).symm
  have hb := hbound _ hN Finset.inter_subset_right
  have hL : Lx x w = Lx x w' + ∑ e ∈ D, x e := by
    rw [Lx_add x w w' ind hsplit, Lx_ind x D ind hind]
  have h2 : ((wt w' M' : ℕ) : ℝ) + (((M' ∩ supp w) ∩ D).card : ℝ) =
      ((wt w (M' ∩ supp w) : ℕ) : ℝ) := by
    rw [← hwt1]
    exact_mod_cast hwt2
  linarith

/-- Some vertex is covered by every maximum-weight matching. -/
theorem case_cov (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (w : Edge n → ℕ) (M0 : Finset (Edge n)) (hM0 : IsMax w M0) (u : Fin n)
    (hu : ∀ M, IsMax w M → cov M u)
    (ih : ∀ w' : Edge n → ℕ, ∑ e, w' e < ∑ e, w e →
      ∃ M, IsM M ∧ Lx x w' ≤ ((wt w' M : ℕ) : ℝ)) :
    Lx x w ≤ ((wt w M0 : ℕ) : ℝ) := by
  have hD : (supp w).filter (fun e => u = e.val.1 ∨ u = e.val.2) ⊆ supp w :=
    Finset.filter_subset _ _
  have hDne : ((supp w).filter (fun e => u = e.val.1 ∨ u = e.val.2)).Nonempty := by
    obtain ⟨e, he, heu⟩ := hu M0 hM0
    exact ⟨e, Finset.mem_filter.2 ⟨hM0.2.1 he, heu⟩⟩
  have hc : ∑ e ∈ (supp w).filter (fun e => u = e.val.1 ∨ u = e.val.2), x e ≤ 1 := by
    refine le_trans ?_ (hload u)
    rw [← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun e he => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 he).2⟩)
      (fun e _ _ => hx e)
  refine dec_step x w _ hD hDne 1 hc (wt w M0) ih ?_
  intro N hN hNs
  by_cases hcov : cov N u
  · obtain ⟨e, he, heu⟩ := hcov
    have h1 : 1 ≤ (N ∩ (supp w).filter (fun e => u = e.val.1 ∨ u = e.val.2)).card :=
      Finset.card_pos.2
        ⟨e, Finset.mem_inter.2 ⟨he, Finset.mem_filter.2 ⟨hNs he, heu⟩⟩⟩
    have h2 : wt w N ≤ wt w M0 := hM0.2.2 N hN hNs
    have h1' : (1 : ℝ) ≤
        ((N ∩ (supp w).filter (fun e => u = e.val.1 ∨ u = e.val.2)).card : ℝ) := by
      exact_mod_cast h1
    have h2' : ((wt w N : ℕ) : ℝ) ≤ ((wt w M0 : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  · have h2 : wt w N < wt w M0 := by
      by_contra hlt
      push Not at hlt
      exact hcov (hu N ⟨hN, hNs, fun M' hM' hM's => le_trans (hM0.2.2 M' hM' hM's) hlt⟩)
    have h2' : ((wt w N : ℕ) : ℝ) + 1 ≤ ((wt w M0 : ℕ) : ℝ) := by exact_mod_cast h2
    have h3 : (0 : ℝ) ≤
        ((N ∩ (supp w).filter (fun e => u = e.val.1 ∨ u = e.val.2)).card : ℝ) :=
      Nat.cast_nonneg _
    linarith

/-- Connected, and every vertex is missed by some maximum-weight matching. -/
theorem case_gallai (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hodd : ∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤
        ((S.card : ℝ) - 1) / 2)
    (w : Edge n → ℕ) (hne : (supp w).Nonempty) (hconn : Conn w)
    (hmiss : ∀ v : Fin n, ∃ M, IsMax w M ∧ ¬ cov M v)
    (M0 : Finset (Edge n)) (hM0 : IsMax w M0)
    (ih : ∀ w' : Edge n → ℕ, ∑ e, w' e < ∑ e, w e →
      ∃ M, IsM M ∧ Lx x w' ≤ ((wt w' M : ℕ) : ℝ)) :
    Lx x w ≤ ((wt w M0 : ℕ) : ℝ) := by
  obtain ⟨hoddS, -⟩ := claimA w hne hconn hmiss
  have hB := claimB w hne hconn hmiss
  obtain ⟨k, hk⟩ := hoddS
  have hc : ∑ e ∈ supp w, x e ≤ (k : ℝ) := by
    have h1 := hodd (Sv w) ⟨k, hk⟩
    have h2 : ((Sv w).card : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
    have h3 : (((Sv w).card : ℝ) - 1) / 2 = (k : ℝ) := by rw [h2]; ring
    rw [h3] at h1
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => hx e)) h1
    intro e he
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, he, Or.inl rfl⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, he, Or.inr rfl⟩
  refine dec_step x w (supp w) (Finset.Subset.refl _) hne k hc (wt w M0) ih ?_
  intro N hN hNs
  have h1 := hB M0 N hM0 hN hNs
  have h2 : ((Sv w).card - 1) / 2 = k := by omega
  rw [h2] at h1
  rw [Finset.inter_eq_left.2 hNs]
  have h1' : ((wt w N : ℕ) : ℝ) + (k : ℝ) ≤ ((wt w M0 : ℕ) : ℝ) + (N.card : ℝ) := by
    exact_mod_cast h1
  linarith

/-- The positive-weight graph is disconnected: split along a component. -/
theorem case_disconn (x : Edge n → ℝ) (w : Edge n → ℕ) (hconn : ¬ Conn w)
    (ih : ∀ w' : Edge n → ℕ, ∑ e, w' e < ∑ e, w e →
      ∃ M, IsM M ∧ Lx x w' ≤ ((wt w' M : ℕ) : ℝ)) :
    ∃ M, IsM M ∧ Lx x w ≤ ((wt w M : ℕ) : ℝ) := by
  unfold Conn at hconn
  push Not at hconn
  obtain ⟨u, hu, v, hv, huv⟩ := hconn
  obtain ⟨C, hC⟩ : ∃ C : Finset (Fin n), C = comp (supp w) u := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Finset (Edge n), A = inside (supp w) C := ⟨_, rfl⟩
  have hcl : ∀ e ∈ supp w, (e.val.1 ∈ C ↔ e.val.2 ∈ C) := by
    rw [hC]
    exact comp_closed (supp w) u
  have huC : u ∈ C := by
    rw [hC]
    exact mem_comp_self (supp w) u
  have hvC : v ∉ C := by
    rw [hC]
    exact fun h => huv (Finset.mem_filter.1 h).2
  have hin : ∀ a ∈ A, a.val.1 ∈ C ∧ a.val.2 ∈ C := by
    intro a ha
    rw [hA] at ha
    exact (Finset.mem_filter.1 ha).2
  have hmemA : ∀ a ∈ supp w, a.val.1 ∈ C → a.val.2 ∈ C → a ∈ A := by
    intro a ha h1 h2
    rw [hA]
    exact Finset.mem_filter.2 ⟨ha, h1, h2⟩
  obtain ⟨e, he, heu⟩ := (Finset.mem_filter.1 hu).2
  obtain ⟨f, hf, hfv⟩ := (Finset.mem_filter.1 hv).2
  have heA : e ∈ A := by
    rcases heu with h | h
    · have h1 : e.val.1 ∈ C := h ▸ huC
      exact hmemA e he h1 ((hcl e he).1 h1)
    · have h2 : e.val.2 ∈ C := h ▸ huC
      exact hmemA e he ((hcl e he).2 h2) h2
  have hfA : f ∉ A := by
    intro h
    have h' := hin f h
    rcases hfv with h'' | h''
    · exact hvC (h'' ▸ h'.1)
    · exact hvC (h'' ▸ h'.2)
  obtain ⟨wA, hwA⟩ : ∃ wA : Edge n → ℕ, ∀ e, wA e = if e ∈ A then w e else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨wB, hwB⟩ : ∃ wB : Edge n → ℕ, ∀ e, wB e = if e ∈ A then 0 else w e :=
    ⟨_, fun _ => rfl⟩
  have hsplit : ∀ e, w e = wA e + wB e := by
    intro e
    rw [hwA e, hwB e]
    split_ifs <;> simp
  have hltA : ∑ e, wA e < ∑ e, w e := by
    refine Finset.sum_lt_sum (fun e _ => by have := hsplit e; omega)
      ⟨f, Finset.mem_univ _, ?_⟩
    have h0 : wA f = 0 := by rw [hwA f, if_neg hfA]
    rw [h0]
    exact (mem_supp_iff w f).1 hf
  have hltB : ∑ e, wB e < ∑ e, w e := by
    refine Finset.sum_lt_sum (fun e _ => by have := hsplit e; omega)
      ⟨e, Finset.mem_univ _, ?_⟩
    have h0 : wB e = 0 := by rw [hwB e, if_pos heA]
    rw [h0]
    exact (mem_supp_iff w e).1 he
  obtain ⟨MA, hMA, hleA⟩ := ih wA hltA
  obtain ⟨MB, hMB, hleB⟩ := ih wB hltB
  have hout : ∀ b ∈ supp w \ A, b.val.1 ∉ C ∧ b.val.2 ∉ C := by
    intro b hb
    obtain ⟨hbs, hbA⟩ := Finset.mem_sdiff.1 hb
    have hiff := hcl b hbs
    exact ⟨fun h => hbA (hmemA b hbs h (hiff.1 h)), fun h => hbA (hmemA b hbs (hiff.2 h) h)⟩
  refine ⟨(MA ∩ A) ∪ (MB ∩ (supp w \ A)), ?_, ?_⟩
  · intro a ha b hb hab
    rcases Finset.mem_union.1 ha with ha | ha <;> rcases Finset.mem_union.1 hb with hb | hb
    · exact hMA a (Finset.mem_inter.1 ha).1 b (Finset.mem_inter.1 hb).1 hab
    · have h1 := hin a (Finset.mem_inter.1 ha).2
      have h2 := hout b (Finset.mem_inter.1 hb).2
      exact ⟨fun h => h2.1 (h ▸ h1.1), fun h => h2.2 (h ▸ h1.1),
        fun h => h2.1 (h ▸ h1.2), fun h => h2.2 (h ▸ h1.2)⟩
    · have h1 := hout a (Finset.mem_inter.1 ha).2
      have h2 := hin b (Finset.mem_inter.1 hb).2
      exact ⟨fun h => h1.1 (h ▸ h2.1), fun h => h1.1 (h ▸ h2.2),
        fun h => h1.2 (h ▸ h2.1), fun h => h1.2 (h ▸ h2.2)⟩
    · exact hMB a (Finset.mem_inter.1 ha).1 b (Finset.mem_inter.1 hb).1 hab
  · have hdisj : Disjoint (MA ∩ A) (MB ∩ (supp w \ A)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 hb).2).2 (Finset.mem_inter.1 ha).2
    have hwtA : wt w (MA ∩ A) = wt wA MA := by
      unfold wt
      rw [← Finset.sum_ite_mem]
      exact Finset.sum_congr rfl fun a _ => (hwA a).symm
    have hwtB : wt w (MB ∩ (supp w \ A)) = wt wB MB := by
      unfold wt
      refine (Finset.sum_congr rfl fun b hb => ?_).trans
        (Finset.sum_subset (Finset.inter_subset_left : MB ∩ (supp w \ A) ⊆ MB) ?_)
      · have hbA : b ∉ A := (Finset.mem_sdiff.1 (Finset.mem_inter.1 hb).2).2
        rw [hwB b, if_neg hbA]
      · intro b hb hnb
        by_cases hbA : b ∈ A
        · rw [hwB b, if_pos hbA]
        · have h0 : w b = 0 := eq_zero_of_not_mem_supp fun h =>
            hnb (Finset.mem_inter.2 ⟨hb, Finset.mem_sdiff.2 ⟨h, hbA⟩⟩)
          rw [hwB b, if_neg hbA, h0]
    have hwt : wt w ((MA ∩ A) ∪ (MB ∩ (supp w \ A))) = wt wA MA + wt wB MB := by
      rw [← hwtA, ← hwtB]
      unfold wt
      exact Finset.sum_union hdisj
    rw [hwt, Lx_add x w wA wB hsplit]
    push_cast
    linarith

theorem edmonds_aux (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (hodd : ∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤
        ((S.card : ℝ) - 1) / 2) :
    ∀ W : ℕ, ∀ w : Edge n → ℕ, ∑ e, w e = W →
      ∃ M, IsM M ∧ Lx x w ≤ ((wt w M : ℕ) : ℝ) := by
  intro W
  induction W using Nat.strong_induction_on with
  | _ W IH =>
    intro w hW
    have ih : ∀ w' : Edge n → ℕ, ∑ e, w' e < ∑ e, w e →
        ∃ M, IsM M ∧ Lx x w' ≤ ((wt w' M : ℕ) : ℝ) :=
      fun w' h => IH _ (hW ▸ h) w' rfl
    by_cases h0 : supp w = ∅
    · refine ⟨∅, isM_empty, ?_⟩
      have hz : ∀ e, w e = 0 := fun e =>
        eq_zero_of_not_mem_supp (by rw [h0]; exact Finset.notMem_empty e)
      simp [Lx, wt, hz]
    · have hne : (supp w).Nonempty := Finset.nonempty_iff_ne_empty.2 h0
      by_cases hconn : Conn w
      · obtain ⟨M0, hM0⟩ := exists_isMax w
        refine ⟨M0, hM0.1, ?_⟩
        by_cases hmiss : ∀ v : Fin n, ∃ M, IsMax w M ∧ ¬ cov M v
        · exact case_gallai x hx hodd w hne hconn hmiss M0 hM0 ih
        · push Not at hmiss
          obtain ⟨u, hu⟩ := hmiss
          exact case_cov x hx hload w M0 hM0 u hu ih
      · exact case_disconn x w hconn ih

theorem edmonds_nat (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (hodd : ∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤
        ((S.card : ℝ) - 1) / 2)
    (w : Edge n → ℕ) :
    ∃ M : Finset (Edge n), IsM M ∧ (∑ e, (w e : ℝ) * x e) ≤ ∑ e ∈ M, (w e : ℝ) := by
  obtain ⟨M, hM, h⟩ := edmonds_aux x hx hload hodd _ w rfl
  exact ⟨M, hM, by rw [wt_cast]; exact h⟩

theorem edmonds_rat (w : Weights n) (x : Edge n → ℝ)
    (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (hodd : ∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤
        ((S.card : ℝ) - 1) / 2) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      (∑ e, (w e : ℝ) * x e) ≤ ∑ e ∈ M, (w e : ℝ) := by
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = ∏ e, (w e).den := ⟨_, rfl⟩
  have hDpos : 0 < D := by
    rw [hD]
    exact Finset.prod_pos fun e _ => (w e).den_pos
  have hwn : ∀ e, ∃ m : ℕ, (m : ℝ) = (w e : ℝ) * D := by
    intro e
    obtain ⟨q, hq⟩ : (w e).den ∣ D := by
      rw [hD]
      exact Finset.dvd_prod_of_mem (fun e => (w e).den) (Finset.mem_univ e)
    refine ⟨(w e).num * q, ?_⟩
    have hden : ((w e).den : ℝ) ≠ 0 := by exact_mod_cast (w e).den_pos.ne'
    rw [hq, NNRat.cast_def]
    push_cast
    field_simp
  choose wn hwn using hwn
  obtain ⟨M, hM, h⟩ := edmonds_nat x hx hload hodd wn
  refine ⟨M, hM, ?_⟩
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  have h1 : ∑ e, (wn e : ℝ) * x e = (∑ e, (w e : ℝ) * x e) * D := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by rw [hwn e]; ring
  have h2 : ∑ e ∈ M, (wn e : ℝ) = (∑ e ∈ M, (w e : ℝ)) * D := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => hwn e
  rw [h1, h2] at h
  exact le_of_mul_le_mul_right h hDR

end QMCMatch


