-- Prove2me | solution 1 for AllocationIndices.search_index_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T07:40:41.529237+00:00
-- url     : https://prove2.me/submissions/b5e170f2-e190-40a2-b2b6-705e7a41eb70

import Mathlib
import Definitions.Def_AllocationIndices_Jobs

open AllocationIndices in
private lemma p2m7d_sc_eq {n : ℕ} (σ : ℕ → Fin n) (k : ℕ) (i : Fin n) :
    searchCount σ k i = ∑ t ∈ Finset.range k, if σ t = i then 1 else 0 := by
  unfold searchCount
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun t => if σ t = i then 1 else 0) k

open AllocationIndices in
private lemma p2m7d_sc_succ {n : ℕ} (σ : ℕ → Fin n) (k : ℕ) (i : Fin n) :
    searchCount σ (k + 1) i = searchCount σ k i + if σ k = i then 1 else 0 := by
  rw [p2m7d_sc_eq, p2m7d_sc_eq, Finset.sum_range_succ]

open AllocationIndices in
private lemma p2m7d_sc_congr {n : ℕ} (σ τ : ℕ → Fin n) (k : ℕ) (i : Fin n)
    (h : ∀ t < k, σ t = τ t) : searchCount σ k i = searchCount τ k i := by
  rw [p2m7d_sc_eq, p2m7d_sc_eq]
  exact Finset.sum_congr rfl (fun t ht => by rw [h t (Finset.mem_range.1 ht)])

open AllocationIndices in
private lemma p2m7d_sc_mono {n : ℕ} (σ : ℕ → Fin n) (i : Fin n) {k k' : ℕ} (h : k ≤ k') :
    searchCount σ k i ≤ searchCount σ k' i := by
  rw [p2m7d_sc_eq, p2m7d_sc_eq]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

open AllocationIndices in
private lemma p2m7d_sc_const {n : ℕ} (σ : ℕ → Fin n) (i : Fin n) (m d : ℕ)
    (h : ∀ e < d, σ (m + e) ≠ i) : searchCount σ (m + d) i = searchCount σ m i := by
  induction d with
  | zero => rfl
  | succ d ih =>
    show searchCount σ (m + d + 1) i = _
    rw [p2m7d_sc_succ, ih (fun e he => h e (by omega)), if_neg (h d (by omega)), add_zero]

open AllocationIndices in
private lemma p2m7d_nf_nonneg {n : ℕ} (p q : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq1 : ∀ i, q i ≤ 1) (σ : ℕ → Fin n) (k : ℕ) : 0 ≤ notFoundProb p q σ k :=
  Finset.sum_nonneg (fun l _ => mul_nonneg (hp l) (pow_nonneg (sub_nonneg.2 (hq1 l)) _))

open AllocationIndices in
private lemma p2m7d_nf_succ {n : ℕ} (p q : Fin n → ℝ) (σ : ℕ → Fin n) (k : ℕ) :
    notFoundProb p q σ (k + 1) = notFoundProb p q σ k -
      p (σ k) * (1 - q (σ k)) ^ searchCount σ k (σ k) * q (σ k) := by
  unfold notFoundProb
  have h : ∀ l, p l * (1 - q l) ^ searchCount σ (k + 1) l =
      p l * (1 - q l) ^ searchCount σ k l -
        (if σ k = l then p l * (1 - q l) ^ searchCount σ k l * q l else 0) := by
    intro l
    rw [p2m7d_sc_succ]
    split_ifs with hl
    · rw [pow_succ]; ring
    · simp
  rw [Finset.sum_congr rfl (fun l _ => h l), Finset.sum_sub_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

open AllocationIndices in
private lemma p2m7d_nf_congr {n : ℕ} (p q : Fin n → ℝ) (σ τ : ℕ → Fin n) (k : ℕ)
    (h : ∀ t < k, σ t = τ t) : notFoundProb p q σ k = notFoundProb p q τ k := by
  unfold notFoundProb
  exact Finset.sum_congr rfl (fun l _ => by rw [p2m7d_sc_congr σ τ k l h])

open AllocationIndices in
private lemma p2m7d_term_congr {n : ℕ} (p q c : Fin n → ℝ) (σ τ : ℕ → Fin n) (k : ℕ)
    (h : ∀ t ≤ k, σ t = τ t) :
    ENNReal.ofReal (c (σ k) * notFoundProb p q σ k) =
      ENNReal.ofReal (c (τ k) * notFoundProb p q τ k) := by
  rw [h k le_rfl, p2m7d_nf_congr p q σ τ k (fun t ht => h t ht.le)]

open AllocationIndices in
private lemma p2m7d_idx_anti {n : ℕ} (p q c : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1) (hc : ∀ i, 0 < c i) (σ : ℕ → Fin n) (i : Fin n)
    {k k' : ℕ} (h : k ≤ k') : searchIndex p q c σ k' i ≤ searchIndex p q c σ k i := by
  unfold searchIndex
  apply div_le_div_of_nonneg_right _ (hc i).le
  apply mul_le_mul_of_nonneg_right _ (hq0 i).le
  apply mul_le_mul_of_nonneg_left _ (hp i)
  exact pow_le_pow_of_le_one (sub_nonneg.2 (hq1 i)) (by linarith [hq0 i]) (p2m7d_sc_mono σ i h)

open AllocationIndices in
private lemma p2m7d_idx_nonneg {n : ℕ} (p q c : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1) (hc : ∀ i, 0 < c i) (σ : ℕ → Fin n) (k : ℕ)
    (i : Fin n) : 0 ≤ searchIndex p q c σ k i :=
  div_nonneg (mul_nonneg (mul_nonneg (hp i) (pow_nonneg (sub_nonneg.2 (hq1 i)) _)) (hq0 i).le)
    (hc i).le

open AllocationIndices in
private lemma p2m7d_cost_split {n : ℕ} (p q c : Fin n → ℝ) (σ : ℕ → Fin n) (s : ℕ) :
    searchCost p q c σ =
      ∑ k ∈ Finset.range s, ENNReal.ofReal (c (σ k) * notFoundProb p q σ k) +
      (ENNReal.ofReal (c (σ s) * notFoundProb p q σ s) +
        ENNReal.ofReal (c (σ (s + 1)) * notFoundProb p q σ (s + 1))) +
      ∑' k, ENNReal.ofReal (c (σ (k + (s + 2))) * notFoundProb p q σ (k + (s + 2))) := by
  unfold searchCost
  have h := Summable.sum_add_tsum_nat_add'
    (f := fun k => ENNReal.ofReal (c (σ k) * notFoundProb p q σ k)) (k := s + 2) ENNReal.summable
  rw [← h, show s + 2 = s + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    add_assoc (∑ k ∈ Finset.range s, _)]

open AllocationIndices in
private lemma p2m7d_two_step {n : ℕ} (p q c : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq1 : ∀ i, q i ≤ 1) (hc : ∀ i, 0 < c i) (σ : ℕ → Fin n) (s : ℕ) :
    ENNReal.ofReal (c (σ s) * notFoundProb p q σ s) +
        ENNReal.ofReal (c (σ (s + 1)) * notFoundProb p q σ (s + 1)) =
      ENNReal.ofReal (c (σ s) * notFoundProb p q σ s + c (σ (s + 1)) *
        (notFoundProb p q σ s - p (σ s) * (1 - q (σ s)) ^ searchCount σ s (σ s) * q (σ s))) := by
  rw [← p2m7d_nf_succ, ENNReal.ofReal_add (mul_nonneg (hc _).le (p2m7d_nf_nonneg p q hp hq1 σ s))
    (mul_nonneg (hc _).le (p2m7d_nf_nonneg p q hp hq1 σ (s + 1)))]

private lemma p2m7d_real_le (R Wi Wj qi qj ci cj : ℝ) (hci : 0 < ci) (hcj : 0 < cj)
    (h : Wj * qj / cj ≤ Wi * qi / ci) :
    ci * R + cj * (R - Wi * qi) ≤ cj * R + ci * (R - Wj * qj) := by
  rw [div_le_div_iff₀ hcj hci] at h
  nlinarith [h]

private lemma p2m7d_real_lt (R Wi Wj qi qj ci cj : ℝ) (hci : 0 < ci) (hcj : 0 < cj)
    (h : Wj * qj / cj < Wi * qi / ci) :
    ci * R + cj * (R - Wi * qi) < cj * R + ci * (R - Wj * qj) := by
  rw [div_lt_div_iff₀ hcj hci] at h
  nlinarith [h]

open AllocationIndices in
private lemma p2m7d_swap {n : ℕ} (p q c : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1) (hc : ∀ i, 0 < c i) (τ : ℕ → Fin n) (s : ℕ) :
    (searchIndex p q c τ s (τ s) ≤ searchIndex p q c τ s (τ (s + 1)) →
      searchCost p q c (fun t => τ (Equiv.swap s (s + 1) t)) ≤ searchCost p q c τ) ∧
    (searchIndex p q c τ s (τ s) < searchIndex p q c τ s (τ (s + 1)) →
      searchCost p q c τ ≠ ⊤ →
      searchCost p q c (fun t => τ (Equiv.swap s (s + 1) t)) < searchCost p q c τ) := by
  set τ' : ℕ → Fin n := fun t => τ (Equiv.swap s (s + 1) t) with hτ'
  have hs : τ' s = τ (s + 1) := by
    show τ (Equiv.swap s (s + 1) s) = τ (s + 1)
    rw [Equiv.swap_apply_left]
  have hs1 : τ' (s + 1) = τ s := by
    show τ (Equiv.swap s (s + 1) (s + 1)) = τ s
    rw [Equiv.swap_apply_right]
  have hne : ∀ t, t ≠ s → t ≠ s + 1 → τ' t = τ t := fun t h1 h2 => by
    show τ (Equiv.swap s (s + 1) t) = τ t
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hlow : ∀ t < s, τ' t = τ t := fun t ht => hne t (by omega) (by omega)
  have hcs : ∀ l, searchCount τ' s l = searchCount τ s l := fun l => p2m7d_sc_congr τ' τ s l hlow
  have hnfs : notFoundProb p q τ' s = notFoundProb p q τ s := p2m7d_nf_congr p q τ' τ s hlow
  have hchigh : ∀ r l, searchCount τ' (s + 2 + r) l = searchCount τ (s + 2 + r) l := by
    intro r l
    induction r with
    | zero =>
      show searchCount τ' (s + 1 + 1) l = searchCount τ (s + 1 + 1) l
      rw [p2m7d_sc_succ τ' (s + 1) l, p2m7d_sc_succ τ' s l, p2m7d_sc_succ τ (s + 1) l,
        p2m7d_sc_succ τ s l, hcs, hs, hs1]
      ring
    | succ r ih =>
      show searchCount τ' (s + 2 + r + 1) l = searchCount τ (s + 2 + r + 1) l
      rw [p2m7d_sc_succ τ' (s + 2 + r) l, p2m7d_sc_succ τ (s + 2 + r) l, ih,
        hne (s + 2 + r) (by omega) (by omega)]
  have htail : ∀ k, ENNReal.ofReal (c (τ' (k + (s + 2))) * notFoundProb p q τ' (k + (s + 2))) =
      ENNReal.ofReal (c (τ (k + (s + 2))) * notFoundProb p q τ (k + (s + 2))) := by
    intro k
    have h1 : k + (s + 2) = s + 2 + k := by ring
    have hnf : notFoundProb p q τ' (k + (s + 2)) = notFoundProb p q τ (k + (s + 2)) := by
      unfold notFoundProb
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [h1, hchigh k l]
    rw [hne (k + (s + 2)) (by omega) (by omega), hnf]
  have hhead : ∑ k ∈ Finset.range s, ENNReal.ofReal (c (τ' k) * notFoundProb p q τ' k) =
      ∑ k ∈ Finset.range s, ENNReal.ofReal (c (τ k) * notFoundProb p q τ k) :=
    Finset.sum_congr rfl (fun k hk => p2m7d_term_congr p q c τ' τ k
      (fun t ht => hlow t (by have := Finset.mem_range.1 hk; omega)))
  have hmidτ := p2m7d_two_step p q c hp hq1 hc τ s
  have hmidτ' : ENNReal.ofReal (c (τ' s) * notFoundProb p q τ' s) +
        ENNReal.ofReal (c (τ' (s + 1)) * notFoundProb p q τ' (s + 1)) =
      ENNReal.ofReal (c (τ (s + 1)) * notFoundProb p q τ s + c (τ s) *
        (notFoundProb p q τ s - p (τ (s + 1)) * (1 - q (τ (s + 1))) ^
          searchCount τ s (τ (s + 1)) * q (τ (s + 1)))) := by
    rw [p2m7d_two_step p q c hp hq1 hc τ' s, hs, hs1, hnfs, hcs]
  have hRi : 0 ≤ notFoundProb p q τ s - p (τ (s + 1)) * (1 - q (τ (s + 1))) ^
      searchCount τ s (τ (s + 1)) * q (τ (s + 1)) := by
    have h := p2m7d_nf_nonneg p q hp hq1 τ' (s + 1)
    rw [p2m7d_nf_succ, hs, hcs, hnfs] at h
    exact h
  have hR := p2m7d_nf_nonneg p q hp hq1 τ s
  rw [p2m7d_cost_split p q c τ' s, p2m7d_cost_split p q c τ s, hhead, hmidτ', hmidτ,
    tsum_congr htail]
  refine ⟨fun hidx => ?_, fun hidx htop => ?_⟩
  · exact add_le_add (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (p2m7d_real_le (notFoundProb p q τ s)
        (p (τ (s + 1)) * (1 - q (τ (s + 1))) ^ searchCount τ s (τ (s + 1)))
        (p (τ s) * (1 - q (τ s)) ^ searchCount τ s (τ s)) (q (τ (s + 1))) (q (τ s))
        (c (τ (s + 1))) (c (τ s)) (hc _) (hc _) hidx))) le_rfl
  · have hT := (ENNReal.add_ne_top.1 htop).2
    have hH := (ENNReal.add_ne_top.1 (ENNReal.add_ne_top.1 htop).1).1
    refine ENNReal.add_lt_add_right hT (ENNReal.add_lt_add_left hH ?_)
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (add_nonneg (mul_nonneg (hc _).le hR) (mul_nonneg (hc _).le hRi))]
    exact p2m7d_real_lt (notFoundProb p q τ s)
        (p (τ (s + 1)) * (1 - q (τ (s + 1))) ^ searchCount τ s (τ (s + 1)))
        (p (τ s) * (1 - q (τ s)) ^ searchCount τ s (τ s)) (q (τ (s + 1))) (q (τ s))
        (c (τ (s + 1))) (c (τ s)) (hc _) (hc _) hidx

open AllocationIndices in
private lemma p2m7d_top {n : ℕ} (p q c : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hq1 : ∀ i, q i ≤ 1)
    (hc : ∀ i, 0 < c i) (τ : ℕ → Fin n) (m : ℕ) (i : Fin n)
    (hw : 0 < p i * (1 - q i) ^ searchCount τ m i) (hnever : ∀ e, τ (m + e) ≠ i) :
    searchCost p q c τ = ⊤ := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨l0, hl0⟩ := Finite.exists_min c
  have hδ : (0 : ENNReal) < ENNReal.ofReal (c l0 * (p i * (1 - q i) ^ searchCount τ m i)) :=
    ENNReal.ofReal_pos.2 (mul_pos (hc l0) hw)
  have hge : ∀ e, ENNReal.ofReal (c l0 * (p i * (1 - q i) ^ searchCount τ m i)) ≤
      ENNReal.ofReal (c (τ (m + e)) * notFoundProb p q τ (m + e)) := by
    intro e
    apply ENNReal.ofReal_le_ofReal
    have h1 : searchCount τ (m + e) i = searchCount τ m i :=
      p2m7d_sc_const τ i m e (fun e' _ => hnever e')
    have h2 : p i * (1 - q i) ^ searchCount τ m i ≤ notFoundProb p q τ (m + e) := by
      unfold notFoundProb
      have := Finset.single_le_sum (f := fun l => p l * (1 - q l) ^ searchCount τ (m + e) l)
        (fun l _ => mul_nonneg (hp l) (pow_nonneg (sub_nonneg.2 (hq1 l)) _)) (Finset.mem_univ i)
      rw [h1] at this
      exact this
    exact mul_le_mul (hl0 _) h2 hw.le (hc _).le
  by_contra hne
  unfold searchCost at hne
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hne
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds hδ))
  have := hN (m + N) (by omega)
  exact absurd (hge N) (not_le.2 this)

open AllocationIndices in
private lemma p2m7d_bubble {n : ℕ} (p q c : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1) (hc : ∀ i, 0 < c i) (σ : ℕ → Fin n) (m : ℕ)
    (hconf : ∀ l, searchIndex p q c σ m l ≤ searchIndex p q c σ m (σ m)) :
    ∀ d (τ : ℕ → Fin n), (∀ k < m, τ k = σ k) → τ (m + d) = σ m →
      (∀ e < d, τ (m + e) ≠ σ m) →
      ∃ τ' : ℕ → Fin n, (∀ k < m + 1, τ' k = σ k) ∧
        searchCost p q c τ' ≤ searchCost p q c τ := by
  intro d
  induction d with
  | zero =>
    intro τ h1 h2 _
    refine ⟨τ, fun k hk => ?_, le_rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact h1 k hk
    · rw [hk]; exact h2
  | succ d ih =>
    intro τ h1 h2 h3
    have hcnt_m : ∀ l, searchCount τ m l = searchCount σ m l :=
      fun l => p2m7d_sc_congr τ σ m l h1
    have hidx : searchIndex p q c τ (m + d) (τ (m + d)) ≤
        searchIndex p q c τ (m + d) (τ (m + d + 1)) := by
      have e2 : τ (m + d + 1) = σ m := h2
      rw [e2]
      calc searchIndex p q c τ (m + d) (τ (m + d)) ≤ searchIndex p q c τ m (τ (m + d)) :=
            p2m7d_idx_anti p q c hp hq0 hq1 hc τ _ (by omega)
        _ = searchIndex p q c σ m (τ (m + d)) := by unfold searchIndex; rw [hcnt_m]
        _ ≤ searchIndex p q c σ m (σ m) := hconf _
        _ = searchIndex p q c τ m (σ m) := by unfold searchIndex; rw [hcnt_m]
        _ = searchIndex p q c τ (m + d) (σ m) := by
            unfold searchIndex
            rw [p2m7d_sc_const τ (σ m) m d (fun e he => h3 e (by omega))]
    have hsw := (p2m7d_swap p q c hp hq0 hq1 hc τ (m + d)).1 hidx
    have g1 : ∀ k < m, τ (Equiv.swap (m + d) (m + d + 1) k) = σ k := fun k hk => by
      rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]; exact h1 k hk
    have g2 : τ (Equiv.swap (m + d) (m + d + 1) (m + d)) = σ m := by
      rw [Equiv.swap_apply_left]; exact h2
    have g3 : ∀ e < d, τ (Equiv.swap (m + d) (m + d + 1) (m + e)) ≠ σ m := fun e he => by
      rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]; exact h3 e (by omega)
    obtain ⟨τ', k1, k2⟩ := ih (fun t => τ (Equiv.swap (m + d) (m + d + 1) t)) g1 g2 g3
    exact ⟨τ', k1, k2.trans hsw⟩

open AllocationIndices in
private lemma p2m7d_stepA {n : ℕ} (p q c : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1) (hc : ∀ i, 0 < c i) (σ : ℕ → Fin n)
    (hconf : ∀ k l, searchIndex p q c σ k l ≤ searchIndex p q c σ k (σ k)) (m : ℕ)
    (τ : ℕ → Fin n) (h1 : ∀ k < m, τ k = σ k) (hfin : searchCost p q c τ ≠ ⊤) :
    ∃ τ' : ℕ → Fin n, (∀ k < m + 1, τ' k = σ k) ∧
      searchCost p q c τ' ≤ searchCost p q c τ := by
  have hcnt_m : ∀ l, searchCount τ m l = searchCount σ m l := fun l => p2m7d_sc_congr τ σ m l h1
  by_cases hw : 0 < p (σ m) * (1 - q (σ m)) ^ searchCount σ m (σ m)
  · have hex : ∃ d, τ (m + d) = σ m := by
      by_contra hno
      push Not at hno
      exact hfin (p2m7d_top p q c hp hq1 hc τ m (σ m) (by rw [hcnt_m]; exact hw) hno)
    classical
    exact p2m7d_bubble p q c hp hq0 hq1 hc σ m (fun l => hconf m l) (Nat.find hex) τ h1
      (Nat.find_spec hex) (fun e he => Nat.find_min hex he)
  · have hw0 : p (σ m) * (1 - q (σ m)) ^ searchCount σ m (σ m) = 0 :=
      le_antisymm (not_lt.1 hw) (mul_nonneg (hp _) (pow_nonneg (sub_nonneg.2 (hq1 _)) _))
    have hall : ∀ l, p l * (1 - q l) ^ searchCount σ m l = 0 := by
      intro l
      have h := hconf m l
      have hi0 : searchIndex p q c σ m (σ m) = 0 := by unfold searchIndex; rw [hw0]; simp
      rw [hi0] at h
      have hl0 : 0 ≤ searchIndex p q c σ m l := p2m7d_idx_nonneg p q c hp hq0 hq1 hc σ m l
      have hz : searchIndex p q c σ m l = 0 := le_antisymm h hl0
      unfold searchIndex at hz
      rcases div_eq_zero_iff.1 hz with h' | h'
      · rcases mul_eq_zero.1 h' with h'' | h''
        · exact h''
        · exact absurd h'' (hq0 l).ne'
      · exact absurd h' (hc l).ne'
    refine ⟨Function.update τ m (σ m), fun k hk => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · rw [Function.update_of_ne (by omega)]; exact h1 k hk
      · rw [hk]; exact Function.update_self _ _ _
    · unfold searchCost
      refine ENNReal.tsum_le_tsum (fun k => ?_)
      by_cases hk : k < m
      · exact le_of_eq (p2m7d_term_congr p q c _ τ k
          (fun t ht => Function.update_of_ne (by omega) _ _))
      · have hz : notFoundProb p q (Function.update τ m (σ m)) k = 0 := by
          apply le_antisymm _ (p2m7d_nf_nonneg p q hp hq1 _ k)
          unfold notFoundProb
          apply Finset.sum_nonpos
          intro l _
          have hc1 : searchCount (Function.update τ m (σ m)) m l = searchCount σ m l :=
            p2m7d_sc_congr _ σ m l
              (fun t ht => by rw [Function.update_of_ne (by omega)]; exact h1 t ht)
          calc p l * (1 - q l) ^ searchCount (Function.update τ m (σ m)) k l
              ≤ p l * (1 - q l) ^ searchCount (Function.update τ m (σ m)) m l :=
                mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (sub_nonneg.2 (hq1 l))
                  (by linarith [hq0 l]) (p2m7d_sc_mono _ l (by omega))) (hp l)
            _ = 0 := by rw [hc1, hall l]
        rw [hz, mul_zero, ENNReal.ofReal_zero]
        exact zero_le

open AllocationIndices in
private lemma p2m7d_rr {n : ℕ} (p q c : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1) (hc : ∀ i, 0 < c i) :
    ∃ τ : ℕ → Fin n, searchCost p q c τ ≠ ⊤ := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hp1
    · exact h
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let rr : ℕ → Fin n := fun k => ⟨k % n, Nat.mod_lt _ hn⟩
  have hcount : ∀ a l, searchCount rr (n * a) l = a := by
    intro a l
    induction a with
    | zero => simp [p2m7d_sc_eq]
    | succ a ih =>
      rw [p2m7d_sc_eq] at ih ⊢
      rw [show n * (a + 1) = n * a + n by ring, Finset.sum_range_add, ih]
      congr 1
      rw [Finset.sum_congr rfl (g := fun x => if x = l.val then 1 else 0)]
      · rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.2 l.isLt)]
      · intro x hx
        have hx' := Finset.mem_range.1 hx
        have hiff : rr (n * a + x) = l ↔ x = l.val := by
          rw [Fin.ext_iff]
          show (n * a + x) % n = l.val ↔ x = l.val
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hx']
        simp only [hiff]
  have hge : ∀ k l, k / n ≤ searchCount rr k l := by
    intro k l
    rw [← hcount (k / n) l]
    exact p2m7d_sc_mono rr l (Nat.mul_div_le k n)
  obtain ⟨l0, hl0⟩ := Finite.exists_min q
  obtain ⟨l1, hl1⟩ := Finite.exists_max c
  have hρ0 : 0 ≤ 1 - q l0 := sub_nonneg.2 (hq1 l0)
  have hρ1 : 1 - q l0 < 1 := by linarith [hq0 l0]
  have hbound : ∀ k, ENNReal.ofReal (c (rr k) * notFoundProb p q rr k) ≤
      ENNReal.ofReal (c l1 * (1 - q l0) ^ (k / n)) := by
    intro k
    apply ENNReal.ofReal_le_ofReal
    have hnf : notFoundProb p q rr k ≤ (1 - q l0) ^ (k / n) := by
      unfold notFoundProb
      calc ∑ l, p l * (1 - q l) ^ searchCount rr k l ≤ ∑ l, p l * (1 - q l0) ^ (k / n) := by
            apply Finset.sum_le_sum
            intro l _
            apply mul_le_mul_of_nonneg_left _ (hp l)
            calc (1 - q l) ^ searchCount rr k l ≤ (1 - q l) ^ (k / n) :=
                  pow_le_pow_of_le_one (sub_nonneg.2 (hq1 l)) (by linarith [hq0 l]) (hge k l)
              _ ≤ (1 - q l0) ^ (k / n) :=
                  pow_le_pow_left₀ (sub_nonneg.2 (hq1 l)) (by linarith [hl0 l]) _
        _ = (1 - q l0) ^ (k / n) := by rw [← Finset.sum_mul, hp1, one_mul]
    exact mul_le_mul (hl1 _) hnf (p2m7d_nf_nonneg p q hp hq1 rr k) (hc l1).le
  refine ⟨rr, ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)⟩
  have h1 : ∑' k : ℕ, ENNReal.ofReal (c l1 * (1 - q l0) ^ (k / n)) =
      ∑' x : ℕ × Fin n, ENNReal.ofReal (c l1 * (1 - q l0) ^ x.1) :=
    (Nat.divModEquiv n).tsum_eq (fun x : ℕ × Fin n => ENNReal.ofReal (c l1 * (1 - q l0) ^ x.1))
  have h2 : ∑' x : ℕ × Fin n, ENNReal.ofReal (c l1 * (1 - q l0) ^ x.1) =
      ∑' a : ℕ, (n : ENNReal) * ENNReal.ofReal (c l1 * (1 - q l0) ^ a) := by
    rw [ENNReal.tsum_prod (f := fun a _ => ENNReal.ofReal (c l1 * (1 - q l0) ^ a))]
    congr 1
    ext a
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h1, h2, ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg
    (fun a => mul_nonneg (hc l1).le (pow_nonneg hρ0 a))
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left _)]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) ENNReal.ofReal_ne_top

open MeasureTheory ProbabilityTheory BanditAlgorithm AllocationIndices in
theorem solution {n : ℕ} (p q c : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i ≤ 1) (hc : ∀ i, 0 < c i) (σ : ℕ → Fin n) :
    IsOptimalSearch p q c σ ↔ ConformsToSearchIndex p q c σ := by
  constructor
  · intro hopt
    have hopt' : ∀ σ' : ℕ → Fin n, searchCost p q c σ ≤ searchCost p q c σ' := hopt
    obtain ⟨τ0, hτ0⟩ := p2m7d_rr p q c hp hp1 hq0 hq1 hc
    have hfin : searchCost p q c σ ≠ ⊤ := ne_top_of_le_ne_top hτ0 (hopt' τ0)
    by_contra hnc
    unfold ConformsToSearchIndex at hnc
    push Not at hnc
    obtain ⟨k, i, hki⟩ := hnc
    have hasc : ∃ s, searchIndex p q c σ s (σ s) < searchIndex p q c σ (s + 1) (σ (s + 1)) := by
      by_contra hno
      push Not at hno
      have hstay : ∀ d, searchCount σ (k + d) i = searchCount σ k i ∧
          searchIndex p q c σ (k + d) (σ (k + d)) ≤ searchIndex p q c σ k (σ k) := by
        intro d
        induction d with
        | zero => exact ⟨rfl, le_rfl⟩
        | succ d ih =>
          have hne : σ (k + d) ≠ i := by
            intro heq
            have e1 : searchIndex p q c σ (k + d) (σ (k + d)) = searchIndex p q c σ k i := by
              rw [heq]; unfold searchIndex; rw [ih.1]
            linarith [ih.2]
          refine ⟨?_, (hno (k + d)).trans ih.2⟩
          show searchCount σ (k + d + 1) i = _
          rw [p2m7d_sc_succ, if_neg hne, add_zero, ih.1]
      have hnever : ∀ e, σ (k + e) ≠ i := by
        intro e heq
        have e1 : searchIndex p q c σ (k + e) (σ (k + e)) = searchIndex p q c σ k i := by
          rw [heq]; unfold searchIndex; rw [(hstay e).1]
        linarith [(hstay e).2]
      have hw : 0 < p i * (1 - q i) ^ searchCount σ k i := by
        rcases (mul_nonneg (hp i) (pow_nonneg (sub_nonneg.2 (hq1 i))
          (searchCount σ k i))).lt_or_eq with h | h
        · exact h
        · exfalso
          have h0 : searchIndex p q c σ k i = 0 := by unfold searchIndex; rw [← h]; simp
          have := p2m7d_idx_nonneg p q c hp hq0 hq1 hc σ k (σ k)
          linarith
      exact hfin (p2m7d_top p q c hp hq1 hc σ k i hw hnever)
    obtain ⟨s, hs⟩ := hasc
    have hlt : searchIndex p q c σ s (σ s) < searchIndex p q c σ s (σ (s + 1)) :=
      lt_of_lt_of_le hs (p2m7d_idx_anti p q c hp hq0 hq1 hc σ _ (Nat.le_succ s))
    have hlt2 := (p2m7d_swap p q c hp hq0 hq1 hc σ s).2 hlt hfin
    exact absurd (hopt' _) (not_le.2 hlt2)
  · intro hconf
    have hconf' : ∀ k l, searchIndex p q c σ k l ≤ searchIndex p q c σ k (σ k) := hconf
    show ∀ σ' : ℕ → Fin n, searchCost p q c σ ≤ searchCost p q c σ'
    intro σ'
    by_cases hfin' : searchCost p q c σ' = ⊤
    · rw [hfin']; exact le_top
    have key : ∀ K, ∃ τ : ℕ → Fin n, (∀ k < K, τ k = σ k) ∧
        searchCost p q c τ ≤ searchCost p q c σ' := by
      intro K
      induction K with
      | zero => exact ⟨σ', fun k hk => absurd hk (Nat.not_lt_zero k), le_rfl⟩
      | succ K ih =>
        obtain ⟨τ, h1, h2⟩ := ih
        obtain ⟨τ', h1', h2'⟩ := p2m7d_stepA p q c hp hq0 hq1 hc σ hconf' K τ h1
          (ne_top_of_le_ne_top hfin' h2)
        exact ⟨τ', h1', h2'.trans h2⟩
    unfold searchCost
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le (fun K => ?_)
    obtain ⟨τ, h1, h2⟩ := key K
    calc ∑ k ∈ Finset.range K, ENNReal.ofReal (c (σ k) * notFoundProb p q σ k)
        = ∑ k ∈ Finset.range K, ENNReal.ofReal (c (τ k) * notFoundProb p q τ k) :=
          Finset.sum_congr rfl (fun k hk => p2m7d_term_congr p q c σ τ k
            (fun t ht => (h1 t (by have := Finset.mem_range.1 hk; omega)).symm))
      _ ≤ ∑' k, ENNReal.ofReal (c (τ k) * notFoundProb p q τ k) := ENNReal.sum_le_tsum _
      _ ≤ ∑' k, ENNReal.ofReal (c (σ' k) * notFoundProb p q σ' k) := h2
