-- Prove2me | Definitions.Def_QMCMatch_Claims
-- name    : QMCMatch_Claims
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T15:33:43.453981+00:00
-- url     : https://prove2.me/theorems/6337408b-6dbe-4807-8392-927b6a905f03
-- title:
--   A weighted Gallai lemma for maximum-weight matchings
-- statement:
--   Let $w$ be nonnegative integer edge weights whose positive-weight graph is connected on its vertex set $S$, and suppose every vertex is missed by some maximum-weight matching of positive edges. Then (`claimA`) $|S|$ is odd and every maximum-weight matching of positive edges misses exactly one vertex of $S$; and (`claimB`) for every matching $N$ of positive edges, $w(N)+(|S|-1)/2\le\nu_w+|N|$, where $\nu_w$ is the maximum weight. Equivalently, lowering every positive weight by one lowers the maximum by at least $(|S|-1)/2$. Both are proved by exchanging two matchings along a component of their union. The file also proves that a maximum-weight matching exists (`exists_isMax`).
-- source:
--   Supporting library for QuantumMaxCutEnergy.matching_polytope_integral_rounding (Prove2me Quantum Max-Cut campaign). Edmonds, Maximum matching and a polyhedron with 0,1-vertices, J. Res. Nat. Bur. Standards 69B, 1965; proof after Schrijver, Short proofs on the matching polyhedron, J. Combin. Theory Ser. B 34, 1983, and Combinatorial Optimization, Section 25.4 (Cunningham-Marsh formula).

import Definitions.Def_QMCMatch_Graph

/-!
Weighted Gallai lemma: if the positive-weight graph is connected and every vertex is
missed by some maximum-weight matching, then maximum-weight matchings are near-perfect
and lowering every positive weight by one lowers the optimum by the matching size.
-/

noncomputable section
open scoped BigOperators
open Classical
open QuantumMaxCutEnergy

namespace QMCMatch

variable {n : ℕ}

theorem exists_isMax (w : Edge n → ℕ) : ∃ M, IsMax w M := by
  have hne : ((supp w).powerset.filter IsM).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.empty_subset _), isM_empty⟩⟩
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image _ (wt w) hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hM
  exact ⟨M, hM.2, hM.1, fun M' h1 h2 =>
    hmax M' (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 h2, h1⟩)⟩

/-- The positive part of a matching is a matching of positive edges with the same weight. -/
theorem wt_inter_supp (w : Edge n → ℕ) (M : Finset (Edge n)) :
    wt w (M ∩ supp w) = wt w M := by
  unfold wt
  apply Finset.sum_subset Finset.inter_subset_left
  intro e he hne
  by_contra h0
  apply hne
  rw [Finset.mem_inter]
  refine ⟨he, ?_⟩
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Nat.pos_of_ne_zero h0

/-! ### Helper facts -/

theorem gl_cov_supp_mem_Sv {w : Edge n → ℕ} {M : Finset (Edge n)} (hM : M ⊆ supp w)
    {v : Fin n} (hv : cov M v) : v ∈ Sv w := by
  simp only [Sv, Finset.mem_filter, Finset.mem_univ, true_and]
  exact cov_mono hM hv

theorem gl_two_mul_card_Sv {w : Edge n → ℕ} {M : Finset (Edge n)} (hM : IsM M)
    (hMs : M ⊆ supp w) :
    2 * M.card + ((Sv w).filter (fun v => ¬ cov M v)).card = (Sv w).card := by
  rw [two_mul_card M hM]
  have h : Finset.univ.filter (fun v : Fin n => cov M v)
      = (Sv w).filter (fun v => cov M v) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨gl_cov_supp_mem_Sv hMs h, h⟩, fun h => h.2⟩
  rw [h]
  exact Finset.card_filter_add_card_filter_not _

theorem gl_two_mul_inside_add (X : Finset (Edge n)) (C : Finset (Fin n)) (hX : IsM X)
    (hC : ∀ e ∈ X, (e.val.1 ∈ C ↔ e.val.2 ∈ C)) :
    2 * (inside X C).card + (C.filter (fun v => ¬ cov X v)).card = C.card := by
  rw [two_mul_card_inside X C hX hC]
  exact Finset.card_filter_add_card_filter_not _

theorem gl_comp_closed_left (M N : Finset (Edge n)) (t : Fin n) :
    ∀ e ∈ M, (e.val.1 ∈ comp (M ∪ N) t ↔ e.val.2 ∈ comp (M ∪ N) t) :=
  fun e he => comp_closed (M ∪ N) t e (Finset.mem_union_left _ he)

theorem gl_comp_closed_right (M N : Finset (Edge n)) (t : Fin n) :
    ∀ e ∈ N, (e.val.1 ∈ comp (M ∪ N) t ↔ e.val.2 ∈ comp (M ∪ N) t) :=
  fun e he => comp_closed (M ∪ N) t e (Finset.mem_union_right _ he)

theorem gl_cov_union {M N : Finset (Edge n)} {v : Fin n} (h : cov (M ∪ N) v) :
    cov M v ∨ cov N v := by
  obtain ⟨e, he, hv⟩ := h
  rcases Finset.mem_union.1 he with h | h
  · exact Or.inl ⟨e, h, hv⟩
  · exact Or.inr ⟨e, h, hv⟩

theorem gl_adj_ne {F : Finset (Edge n)} {a b : Fin n} (h : adj F a b) : a ≠ b := by
  obtain ⟨e, _, h | h⟩ := h
  · rw [h.1, h.2]; exact ne_of_lt e.property
  · rw [h.1, h.2]; exact ne_of_gt e.property

theorem gl_swp_wt (w : Edge n → ℕ) (M N : Finset (Edge n)) (t : Fin n) :
    wt w (swp M N (comp (M ∪ N) t)) + wt w (swp N M (comp (M ∪ N) t))
      = wt w M + wt w N :=
  swp_sum M N _ (gl_comp_closed_left M N t) (gl_comp_closed_right M N t) w

theorem gl_swp_isMax (w : Edge n → ℕ) {M N : Finset (Edge n)} (hM : IsMax w M)
    (hN : IsMax w N) (t : Fin n) : IsMax w (swp M N (comp (M ∪ N) t)) := by
  have hsum := gl_swp_wt w M N t
  have h1 : IsM (swp M N (comp (M ∪ N) t)) := swp_isM M N _ hM.1 hN.1
  have h2 : swp M N (comp (M ∪ N) t) ⊆ supp w := swp_subset M N _ _ hM.2.1 hN.2.1
  have h3 : IsM (swp N M (comp (M ∪ N) t)) := swp_isM N M _ hN.1 hM.1
  have h4 : swp N M (comp (M ∪ N) t) ⊆ supp w := swp_subset N M _ _ hN.2.1 hM.2.1
  have h5 := hN.2.2 _ h3 h4
  refine ⟨h1, h2, fun X hX hXs => ?_⟩
  have h6 := hM.2.2 X hX hXs
  omega

/-! ### Claim A -/

theorem gl_adj_not_both_missed (w : Edge n → ℕ) {M : Finset (Edge n)} (hM : IsMax w M)
    {u v : Fin n} (h : adj (supp w) u v) : ¬ (¬ cov M u ∧ ¬ cov M v) := by
  rintro ⟨hu, hv⟩
  obtain ⟨e, he, hee⟩ := h
  have h12 : ¬ cov M e.val.1 ∧ ¬ cov M e.val.2 := by
    rcases hee with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact ⟨hu, hv⟩
    · rw [← h1, ← h2]; exact ⟨hv, hu⟩
  have heM : e ∉ M := fun h => h12.1 ⟨e, h, Or.inl rfl⟩
  have hins := isM_insert hM.1 e h12.1 h12.2
  have hsub : insert e M ⊆ supp w := Finset.insert_subset he hM.2.1
  have hle := hM.2.2 _ hins hsub
  have hw : 0 < w e := by
    simpa only [supp, Finset.mem_filter, Finset.mem_univ, true_and] using he
  unfold wt at hle
  rw [Finset.sum_insert heM] at hle
  omega

theorem gl_no_two_missed (w : Edge n → ℕ)
    (hmiss : ∀ v : Fin n, ∃ M, IsMax w M ∧ ¬ cov M v) {u v : Fin n}
    (h : Relation.ReflTransGen (adj (supp w)) u v) :
    u ≠ v → ∀ M, IsMax w M → ¬ (¬ cov M u ∧ ¬ cov M v) := by
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => a ≠ v → ∀ M, IsMax w M → ¬ (¬ cov M a ∧ ¬ cov M v)) h ?_ ?_
  · intro h; exact absurd rfl h
  · intro u t hut _ ih huv M hM hmv
    obtain ⟨hu, hv⟩ := hmv
    by_cases htv : t = v
    · rw [htv] at hut
      exact gl_adj_not_both_missed w hM hut ⟨hu, hv⟩
    have hut' : u ≠ t := gl_adj_ne hut
    obtain ⟨N, hN, hNt⟩ := hmiss t
    have hM'max : IsMax w (swp M N (comp (M ∪ N) t)) := gl_swp_isMax w hM hN t
    have hM't : ¬ cov (swp M N (comp (M ∪ N) t)) t :=
      (swp_cov_in M N _ (gl_comp_closed_right M N t) (mem_comp_self _ t)).not.2 hNt
    by_cases huC : u ∈ comp (M ∪ N) t
    · by_cases hvC : v ∈ comp (M ∪ N) t
      · have hdef := comp_deficient_le_two M N hM.1 hN.1 t
        have h3 : 2 < ((comp (M ∪ N) t).filter (fun v => ¬ cov M v ∨ ¬ cov N v)).card := by
          rw [Finset.two_lt_card]
          exact ⟨t, Finset.mem_filter.2 ⟨mem_comp_self _ t, Or.inr hNt⟩,
            u, Finset.mem_filter.2 ⟨huC, Or.inl hu⟩,
            v, Finset.mem_filter.2 ⟨hvC, Or.inl hv⟩, hut'.symm, htv, huv⟩
        omega
      · have hM'v : ¬ cov (swp M N (comp (M ∪ N) t)) v :=
          (swp_cov_out M N _ (gl_comp_closed_left M N t) hvC).not.2 hv
        exact ih htv _ hM'max ⟨hM't, hM'v⟩
    · have hM'u : ¬ cov (swp M N (comp (M ∪ N) t)) u :=
        (swp_cov_out M N _ (gl_comp_closed_left M N t) huC).not.2 hu
      exact gl_adj_not_both_missed w hM'max hut ⟨hM'u, hM't⟩

theorem gl_missed_le_one (w : Edge n → ℕ) (hconn : Conn w)
    (hmiss : ∀ v : Fin n, ∃ M, IsMax w M ∧ ¬ cov M v) {M : Finset (Edge n)}
    (hM : IsMax w M) : ((Sv w).filter (fun v => ¬ cov M v)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  by_contra hab
  exact gl_no_two_missed w hmiss (hconn a ha.1 b hb.1) hab M hM ⟨ha.2, hb.2⟩

theorem claimA (w : Edge n → ℕ) (hne : (supp w).Nonempty) (hconn : Conn w)
    (hmiss : ∀ v : Fin n, ∃ M, IsMax w M ∧ ¬ cov M v) :
    Odd (Sv w).card ∧
      ∀ M, IsMax w M → ((Sv w).filter (fun v => ¬ cov M v)).card = 1 := by
  obtain ⟨e, he⟩ := hne
  have hv0 : e.val.1 ∈ Sv w := by
    simp only [Sv, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, he, Or.inl rfl⟩
  obtain ⟨M0, hM0, hM0v⟩ := hmiss e.val.1
  have h0le := gl_missed_le_one w hconn hmiss hM0
  have h0pos : 0 < ((Sv w).filter (fun v => ¬ cov M0 v)).card :=
    Finset.card_pos.2 ⟨e.val.1, Finset.mem_filter.2 ⟨hv0, hM0v⟩⟩
  have h0 := gl_two_mul_card_Sv hM0.1 hM0.2.1
  refine ⟨⟨M0.card, by omega⟩, fun M hM => ?_⟩
  have hle := gl_missed_le_one w hconn hmiss hM
  have h1 := gl_two_mul_card_Sv hM.1 hM.2.1
  omega

/-! ### Claim B -/

theorem gl_comp_cov_M (w : Edge n → ℕ) {M N : Finset (Edge n)} (hMs : M ⊆ supp w)
    (hNs : N ⊆ supp w) {t u : Fin n} (hcovM : ∀ v ∈ Sv w, v ≠ t → cov M v)
    (huS : u ∈ Sv w) {v : Fin n} (hv : v ∈ comp (M ∪ N) u) (hvt : v ≠ t) : cov M v := by
  apply hcovM v _ hvt
  by_cases hvu : v = u
  · rw [hvu]; exact huS
  · exact gl_cov_supp_mem_Sv (Finset.union_subset hMs hNs) (comp_cov _ _ hv hvu)

/-- Sub-lemma (K): augmenting along a component that avoids the vertex missed by `M`. -/
theorem gl_claimB_K (w : Edge n → ℕ) (h : ℕ)
    (hmaxcard : ∀ M, IsMax w M → M.card = h)
    {M : Finset (Edge n)} (hM : IsMax w M) {t : Fin n}
    (hcovM : ∀ v ∈ Sv w, v ≠ t → cov M v)
    {N : Finset (Edge n)} (hN : IsM N) (hNs : N ⊆ supp w)
    (ih : ∀ N' : Finset (Edge n), IsM N' → N' ⊆ supp w → N'.card = N.card + 1 →
      wt w N' + h ≤ wt w M + N'.card)
    {u : Fin n} (huS : u ∈ Sv w) (huN : ¬ cov N u) (htC : t ∉ comp (M ∪ N) u) :
    wt w N + h ≤ wt w M + N.card := by
  have hcM := gl_comp_closed_left M N u
  have hcN := gl_comp_closed_right M N u
  have hallM : ∀ v ∈ comp (M ∪ N) u, cov M v := fun v hv =>
    gl_comp_cov_M w hM.2.1 hNs hcovM huS hv (fun hvt => htC (hvt ▸ hv))
  have hiM := two_mul_card_inside M _ hM.1 hcM
  rw [Finset.filter_true_of_mem hallM] at hiM
  have hiN := gl_two_mul_inside_add N _ hN hcN
  have hdef := comp_deficient_le_two M N hM.1 hN u
  have hk2 : ((comp (M ∪ N) u).filter (fun v => ¬ cov N v)).card ≤ 2 := by
    refine le_trans (Finset.card_le_card ?_) hdef
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, Or.inr hv.2⟩
  have hk1 : 0 < ((comp (M ∪ N) u).filter (fun v => ¬ cov N v)).card :=
    Finset.card_pos.2 ⟨u, Finset.mem_filter.2 ⟨mem_comp_self _ u, huN⟩⟩
  have hcN' := swp_card N M _ hcN hcM
  have hcM' := swp_card M N _ hcM hcN
  have hMh := hmaxcard M hM
  have hM'm : IsM (swp M N (comp (M ∪ N) u)) := swp_isM M N _ hM.1 hN
  have hM's : swp M N (comp (M ∪ N) u) ⊆ supp w := swp_subset M N _ _ hM.2.1 hNs
  have hN'm : IsM (swp N M (comp (M ∪ N) u)) := swp_isM N M _ hN hM.1
  have hN's : swp N M (comp (M ∪ N) u) ⊆ supp w := swp_subset N M _ _ hNs hM.2.1
  have hlt : wt w (swp M N (comp (M ∪ N) u)) < wt w M := by
    by_contra hge
    have hmax : IsMax w (swp M N (comp (M ∪ N) u)) :=
      ⟨hM'm, hM's, fun X hX hXs => le_trans (hM.2.2 X hX hXs) (not_lt.1 hge)⟩
    have := hmaxcard _ hmax
    omega
  have hsum := gl_swp_wt w M N u
  have hih := ih _ hN'm hN's (by omega)
  omega

/-- Case (a): the vertex missed by `M` is also missed by `N`. -/
theorem gl_claimB_a (w : Edge n → ℕ) (h : ℕ) (hS : (Sv w).card = 2 * h + 1)
    (hmaxcard : ∀ M, IsMax w M → M.card = h)
    {M : Finset (Edge n)} (hM : IsMax w M) {t : Fin n} (htM : ¬ cov M t)
    (hcovM : ∀ v ∈ Sv w, v ≠ t → cov M v)
    {N : Finset (Edge n)} (hN : IsM N) (hNs : N ⊆ supp w)
    (ih : ∀ N' : Finset (Edge n), IsM N' → N' ⊆ supp w → N'.card = N.card + 1 →
      wt w N' + h ≤ wt w M + N'.card)
    (hlt : N.card < h) (htN : ¬ cov N t) :
    wt w N + h ≤ wt w M + N.card := by
  have hcnt := gl_two_mul_card_Sv hN hNs
  obtain ⟨u, hu, hut⟩ :=
    Finset.exists_mem_ne (s := (Sv w).filter (fun v => ¬ cov N v)) (by omega) t
  rw [Finset.mem_filter] at hu
  refine gl_claimB_K w h hmaxcard hM hcovM hN hNs ih hu.1 hu.2 ?_
  intro htC
  rcases gl_cov_union (comp_cov _ _ htC (Ne.symm hut)) with h1 | h1
  · exact htM h1
  · exact htN h1

/-- Case (b): the vertex missed by `M` is covered by `N`. -/
theorem gl_claimB_b (w : Edge n → ℕ) (h : ℕ) (hS : (Sv w).card = 2 * h + 1)
    (hmaxcard : ∀ M, IsMax w M → M.card = h)
    {M : Finset (Edge n)} (hM : IsMax w M) {t : Fin n} (htM : ¬ cov M t)
    (hcovM : ∀ v ∈ Sv w, v ≠ t → cov M v)
    {N : Finset (Edge n)} (hN : IsM N) (hNs : N ⊆ supp w)
    (ih : ∀ N' : Finset (Edge n), IsM N' → N' ⊆ supp w → N'.card = N.card + 1 →
      wt w N' + h ≤ wt w M + N'.card)
    (hlt : N.card < h) (htN : cov N t) :
    wt w N + h ≤ wt w M + N.card := by
  have hcnt := gl_two_mul_card_Sv hN hNs
  obtain ⟨u, hu⟩ := Finset.card_pos.1
    (show 0 < ((Sv w).filter (fun v => ¬ cov N v)).card by omega)
  rw [Finset.mem_filter] at hu
  have hut : u ≠ t := fun hut => hu.2 (hut ▸ htN)
  by_cases htC : t ∈ comp (M ∪ N) u
  · have hcM := gl_comp_closed_left M N u
    have hcN := gl_comp_closed_right M N u
    have huM : cov M u := hcovM u hu.1 hut
    -- `t` is the only vertex of the component missed by `M`
    have hkM : ((comp (M ∪ N) u).filter (fun v => ¬ cov M v)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨t, ?_⟩
      ext v
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hv, hvM⟩
        by_contra hvt
        exact hvM (gl_comp_cov_M w hM.2.1 hNs hcovM hu.1 hv hvt)
      · intro hvt
        rw [hvt]
        exact ⟨htC, htM⟩
    -- `u` is the only vertex of the component missed by `N`
    have hdef := comp_deficient_le_two M N hM.1 hN u
    have hkN1 : 0 < ((comp (M ∪ N) u).filter (fun v => ¬ cov N v)).card :=
      Finset.card_pos.2 ⟨u, Finset.mem_filter.2 ⟨mem_comp_self _ u, hu.2⟩⟩
    have hkN2 : ((comp (M ∪ N) u).filter (fun v => ¬ cov N v)).card + 1 ≤ 2 := by
      have hnot : t ∉ (comp (M ∪ N) u).filter (fun v => ¬ cov N v) := by
        rw [Finset.mem_filter]
        exact fun hh => hh.2 htN
      rw [← Finset.card_insert_of_notMem hnot]
      refine le_trans (Finset.card_le_card ?_) hdef
      intro v hv
      rw [Finset.mem_insert] at hv
      rw [Finset.mem_filter]
      rcases hv with hv | hv
      · rw [hv]; exact ⟨htC, Or.inl htM⟩
      · rw [Finset.mem_filter] at hv
        exact ⟨hv.1, Or.inr hv.2⟩
    have hiM := gl_two_mul_inside_add M _ hM.1 hcM
    have hiN := gl_two_mul_inside_add N _ hN hcN
    have hcN' := swp_card N M _ hcN hcM
    have hM'm : IsM (swp M N (comp (M ∪ N) u)) := swp_isM M N _ hM.1 hN
    have hM's : swp M N (comp (M ∪ N) u) ⊆ supp w := swp_subset M N _ _ hM.2.1 hNs
    have hN'm : IsM (swp N M (comp (M ∪ N) u)) := swp_isM N M _ hN hM.1
    have hN's : swp N M (comp (M ∪ N) u) ⊆ supp w := swp_subset N M _ _ hNs hM.2.1
    have hle := hM.2.2 _ hM'm hM's
    have hsum := gl_swp_wt w M N u
    have hN't : ¬ cov (swp N M (comp (M ∪ N) u)) t :=
      (swp_cov_in N M _ hcM htC).not.2 htM
    have hcard : (swp N M (comp (M ∪ N) u)).card = N.card := by omega
    have ha := gl_claimB_a w h hS hmaxcard hM htM hcovM hN'm hN's
      (fun N'' h1 h2 h3 => ih N'' h1 h2 (by omega)) (by omega) hN't
    omega
  · exact gl_claimB_K w h hmaxcard hM hcovM hN hNs ih hu.1 hu.2 htC

theorem claimB (w : Edge n → ℕ) (hne : (supp w).Nonempty) (hconn : Conn w)
    (hmiss : ∀ v : Fin n, ∃ M, IsMax w M ∧ ¬ cov M v) :
    ∀ M N : Finset (Edge n), IsMax w M → IsM N → N ⊆ supp w →
      wt w N + ((Sv w).card - 1) / 2 ≤ wt w M + N.card := by
  intro M N hM hN hNs
  obtain ⟨hodd, hone⟩ := claimA w hne hconn hmiss
  obtain ⟨h, hS⟩ := hodd
  have hh : ((Sv w).card - 1) / 2 = h := by omega
  rw [hh]
  have hmaxcard : ∀ M, IsMax w M → M.card = h := by
    intro X hX
    have h1 := gl_two_mul_card_Sv hX.1 hX.2.1
    have h2 := hone X hX
    omega
  -- the unique vertex missed by `M`
  obtain ⟨t, ht⟩ := Finset.card_eq_one.1 (hone M hM)
  have htmem : t ∈ (Sv w).filter (fun v => ¬ cov M v) := by
    rw [ht]; exact Finset.mem_singleton_self t
  rw [Finset.mem_filter] at htmem
  have htM : ¬ cov M t := htmem.2
  have hcovM : ∀ v ∈ Sv w, v ≠ t → cov M v := by
    intro v hv hvt
    by_contra hc
    have : v ∈ (Sv w).filter (fun v => ¬ cov M v) := Finset.mem_filter.2 ⟨hv, hc⟩
    rw [ht, Finset.mem_singleton] at this
    exact hvt this
  have key : ∀ d : ℕ, ∀ N : Finset (Edge n), IsM N → N ⊆ supp w → N.card + d = h →
      wt w N + h ≤ wt w M + N.card := by
    intro d
    induction d with
    | zero =>
      intro N hN hNs hd
      have := hM.2.2 N hN hNs
      omega
    | succ d ihd =>
      intro N hN hNs hd
      have ih : ∀ N' : Finset (Edge n), IsM N' → N' ⊆ supp w → N'.card = N.card + 1 →
          wt w N' + h ≤ wt w M + N'.card :=
        fun N' h1 h2 h3 => ihd N' h1 h2 (by omega)
      by_cases htN : cov N t
      · exact gl_claimB_b w h hS hmaxcard hM htM hcovM hN hNs ih (by omega) htN
      · exact gl_claimB_a w h hS hmaxcard hM htM hcovM hN hNs ih (by omega) htN
  have hcnt := gl_two_mul_card_Sv hN hNs
  exact key (h - N.card) N hN hNs (by omega)

end QMCMatch


