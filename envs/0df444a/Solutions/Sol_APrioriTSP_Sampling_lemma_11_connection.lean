-- Prove2me | solution 1 for APrioriTSP.Sampling.lemma_11_connection
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:54:03.687845+00:00
-- url     : https://prove2.me/submissions/20c8cc80-f400-46f4-8639-4b0047daf67d

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

open APrioriTSP.Sampling Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace APTSPConn

variable {V : Type} [Fintype V] [DecidableEq V]

/-- probability of a pattern: all of `S` active, none of `U` active. -/
theorem pattern (q : V → ℝ) (S U : Finset V) (hSU : Disjoint S U) :
    ∑ A : Finset V, subsetProb q A * (if S ⊆ A ∧ Disjoint U A then 1 else 0) =
      (∏ v ∈ S, q v) * ∏ v ∈ U, (1 - q v) := by
  set f : V → ℝ := fun v => if v ∈ U then 0 else q v with hf
  set g : V → ℝ := fun v => if v ∈ S then 0 else 1 - q v with hg
  have key : ∀ A : Finset V, subsetProb q A * (if S ⊆ A ∧ Disjoint U A then 1 else 0) =
      (∏ v ∈ A, f v) * ∏ v ∈ univ \ A, g v := by
    intro A
    unfold subsetProb
    by_cases hc : S ⊆ A ∧ Disjoint U A
    · rw [if_pos hc, mul_one]
      congr 1
      · apply Finset.prod_congr rfl; intro v hv
        simp only [hf]; rw [if_neg]; intro hvU
        exact Finset.disjoint_left.1 hc.2 hvU hv
      · apply Finset.prod_congr rfl; intro v hv
        simp only [hg]; rw [if_neg]; intro hvS
        simp at hv; exact hv (hc.1 hvS)
    · rw [if_neg hc, mul_zero]
      rw [not_and_or] at hc
      rcases hc with h1 | h1
      · rw [Finset.not_subset] at h1
        obtain ⟨s, hsS, hsA⟩ := h1
        have : ∏ v ∈ univ \ A, g v = 0 := by
          apply Finset.prod_eq_zero (i := s) (by simp [hsA])
          simp [hg, hsS]
        rw [this, mul_zero]
      · rw [Finset.not_disjoint_iff] at h1
        obtain ⟨u, huU, huA⟩ := h1
        have : ∏ v ∈ A, f v = 0 := by
          apply Finset.prod_eq_zero huA
          simp [hf, huU]
        rw [this, zero_mul]
  rw [Finset.sum_congr rfl (fun A _ => key A)]
  have h2 := (Finset.prod_add f g (univ : Finset V)).symm
  rw [Finset.powerset_univ] at h2
  rw [h2]
  have h3 : ∀ v, f v + g v = (if v ∈ S then q v else 1) * (if v ∈ U then 1 - q v else 1) := by
    intro v
    simp only [hf, hg]
    by_cases hS : v ∈ S
    · have hU : v ∉ U := Finset.disjoint_left.1 hSU hS
      simp [hS, hU]
    · by_cases hU : v ∈ U
      · simp [hS, hU]
      · simp [hS, hU]
  rw [Finset.prod_congr rfl (fun v _ => h3 v), Finset.prod_mul_distrib,
    Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter, Finset.univ_inter]


theorem geom_tail (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (m : ℕ) :
    ∑' i : ℕ, (if m ≤ i then (1 - p) ^ i * p ^ 2 else 0) = p * (1 - p) ^ m := by
  have hr0 : 0 ≤ 1 - p := by linarith
  have hr1 : 1 - p < 1 := by linarith
  have hgs : Summable (fun i : ℕ => (1 - p) ^ i * p ^ 2) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_right _
  have hs : Summable (fun i : ℕ => if m ≤ i then (1 - p) ^ i * p ^ 2 else 0) := by
    apply Summable.of_nonneg_of_le _ _ hgs
    · intro i; split_ifs <;> positivity
    · intro i; split_ifs
      · exact le_rfl
      · positivity
  rw [← hs.sum_add_tsum_nat_add m]
  have h1 : ∑ i ∈ range m, (if m ≤ i then (1 - p) ^ i * p ^ 2 else 0) = 0 := by
    apply Finset.sum_eq_zero; intro i hi; simp at hi; rw [if_neg (by omega)]
  have h2 : ∀ i : ℕ, (if m ≤ i + m then (1 - p) ^ (i + m) * p ^ 2 else 0) =
      ((1 - p) ^ m * p ^ 2) * (1 - p) ^ i := by
    intro i; rw [if_pos (by omega)]; ring
  rw [h1, zero_add, tsum_congr h2, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1,
    sub_sub_cancel]
  field_simp

theorem tourVertex_eq (d : V) (T : List V) (hd : T.head? = some d) (j : ℤ) :
    tourVertex d T j = T.getD j.toNat d := by
  unfold tourVertex
  split_ifs with h
  · rfl
  · rw [Int.toNat_of_nonpos (by omega)]
    cases T with
    | nil => simp at hd
    | cons x R => simp at hd; simp [hd]


theorem kappaX (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (n a b : ℕ) :
    ∑' i : ℕ, (1 - p) ^ i * p ^ 2 * (if a < n ∧ b = min (a + (i + 1)) n then 1 else 0) =
      if a < b ∧ b < n then p ^ 2 * (1 - p) ^ (b - a - 1)
      else if a < n ∧ b = n then p * (1 - p) ^ (n - a - 1) else 0 := by
  by_cases h1 : a < b ∧ b < n
  · rw [if_pos h1]
    have : ∀ i : ℕ, (1 - p) ^ i * p ^ 2 * (if a < n ∧ b = min (a + (i + 1)) n then 1 else 0) =
        if i = b - a - 1 then (1 - p) ^ i * p ^ 2 else 0 := by
      intro i
      by_cases hi : i = b - a - 1
      · rw [if_pos hi, if_pos (by omega), mul_one]
      · rw [if_neg hi, if_neg (by omega), mul_zero]
    rw [tsum_congr this, tsum_ite_eq]; ring
  · rw [if_neg h1]
    by_cases h2 : a < n ∧ b = n
    · rw [if_pos h2, ← geom_tail p hp0 hp1 (n - a - 1)]
      apply tsum_congr; intro i
      by_cases hi : n - a - 1 ≤ i
      · rw [if_pos hi, if_pos (by omega), mul_one]
      · rw [if_neg hi, if_neg (by omega), mul_zero]
    · rw [if_neg h2]
      have : ∀ i : ℕ, (1 - p) ^ i * p ^ 2 * (if a < n ∧ b = min (a + (i + 1)) n then 1 else 0) =
          0 := by
        intro i; rw [if_neg (by omega), mul_zero]
      rw [tsum_congr this, tsum_zero]


theorem c_nonneg {c : V → V → ℝ} {p : V → ℝ} {d : V} (hI : IsDepotInstance c p d) (u v : V) :
    0 ≤ c u v := by
  have h1 := hI.c_triangle u v u
  rw [hI.c_self u, hI.c_symm v u] at h1
  linarith

theorem subsetProb_nonneg (q : V → ℝ) (hq : ∀ v, 0 ≤ q v ∧ q v ≤ 1) (A : Finset V) :
    0 ≤ subsetProb q A := by
  unfold subsetProb
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun v _ => (hq v).1)
  · exact Finset.prod_nonneg (fun v _ => by linarith [(hq v).2])


theorem tourVertex_out (d : V) (T : List V) (hd : T.head? = some d) (j : ℤ)
    (hj : j < 0 ∨ (T.length : ℤ) ≤ j) : tourVertex d T j = d := by
  unfold tourVertex
  split_ifs with h
  · apply List.getD_eq_default
    omega
  · rfl

theorem hopC_window (c : V → V → ℝ) (p : ℝ) (d : V) (T : List V) (hd : T.head? = some d)
    (hcdd : c d d = 0) (k K : ℕ) (M : ℤ) (hK : k ≤ K) (hM : (T.length : ℤ) - 1 ≤ M) :
    hopC c p d T k = p ^ 2 * ∑ j ∈ Finset.Icc (-(K : ℤ)) M,
      c (tourVertex d T j) (tourVertex d T (j + k)) := by
  unfold hopC
  congr 1
  apply Finset.sum_subset
  · intro j hj; simp at hj ⊢; omega
  · intro j hj hnj
    simp at hj hnj
    rcases lt_or_ge j (-(k : ℤ)) with h | h
    · rw [tourVertex_out d T hd j (Or.inl (by omega)),
        tourVertex_out d T hd (j + k) (Or.inl (by omega)), hcdd]
    · have := hnj h
      rw [tourVertex_out d T hd j (Or.inr (by omega)),
        tourVertex_out d T hd (j + k) (Or.inr (by omega)), hcdd]

theorem hopC_nonneg (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v) (p : ℝ) (d : V) (T : List V)
    (k : ℕ) : 0 ≤ hopC c p d T k := by
  unfold hopC
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => hc _ _))

theorem hopC_triangle {pf : V → ℝ} (c : V → V → ℝ) (p : ℝ) (d : V)
    (hI : IsDepotInstance c pf d) (T : List V) (hd : T.head? = some d) (i j : ℕ) :
    hopC c p d T (i + j) ≤ hopC c p d T i + hopC c p d T j := by
  have hcdd : c d d = 0 := hI.c_self d
  rw [hopC_window c p d T hd hcdd i (i + j) ((T.length : ℤ) - 1) (by omega) le_rfl,
    hopC_window c p d T hd hcdd j j ((T.length : ℤ) - 1 + i) le_rfl (by omega)]
  unfold hopC
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg p)
  have hshift : ∑ l ∈ Finset.Icc (-((i + j : ℕ) : ℤ)) ((T.length : ℤ) - 1),
      c (tourVertex d T (l + i)) (tourVertex d T (l + i + j)) =
      ∑ l ∈ Finset.Icc (-(j : ℤ)) ((T.length : ℤ) - 1 + i),
        c (tourVertex d T l) (tourVertex d T (l + j)) := by
    apply Finset.sum_nbij' (fun l : ℤ => l + (i : ℤ)) (fun l : ℤ => l - (i : ℤ))
    · intro l hl; simp at hl ⊢; omega
    · intro l hl; simp at hl ⊢; omega
    · intro l _; simp
    · intro l _; simp
    · intro l _; rfl
  rw [← hshift, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l _
  have := hI.c_triangle (tourVertex d T l) (tourVertex d T (l + i)) (tourVertex d T (l + i + j))
  have e : l + ((i + j : ℕ) : ℤ) = l + i + j := by push_cast; ring
  rw [e]; exact this


theorem tsum_count_tail (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (n : ℕ) :
    ∑' k : ℕ, (1 - x) ^ k * x ^ 2 * ((k + 1 - n : ℕ) : ℝ) = (1 - x) ^ n := by
  have hy0 : 0 ≤ 1 - x := by linarith
  have hy1 : 1 - x < 1 := by linarith
  have hny : ‖1 - x‖ < 1 := by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have hs1 : Summable (fun k : ℕ => (k : ℝ) * (1 - x) ^ k) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 hny
    simpa using this
  have hs0 : Summable (fun k : ℕ => (1 - x) ^ k) := summable_geometric_of_lt_one hy0 hy1
  have hsum : Summable (fun k : ℕ => (1 - x) ^ k * x ^ 2 * ((k + 1 - n : ℕ) : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun k => by positivity) _
      (((hs1.add hs0).mul_right (x ^ 2)))
    intro k
    have : ((k + 1 - n : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
      have : k + 1 - n ≤ k + 1 := Nat.sub_le _ _
      exact_mod_cast this
    have hpos : 0 ≤ (1 - x) ^ k * x ^ 2 := by positivity
    calc (1 - x) ^ k * x ^ 2 * ((k + 1 - n : ℕ) : ℝ) ≤ (1 - x) ^ k * x ^ 2 * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left this hpos
      _ = ((k : ℝ) * (1 - x) ^ k + (1 - x) ^ k) * x ^ 2 := by ring
  rw [← hsum.sum_add_tsum_nat_add n]
  have h1 : ∑ k ∈ range n, (1 - x) ^ k * x ^ 2 * ((k + 1 - n : ℕ) : ℝ) = 0 := by
    apply Finset.sum_eq_zero; intro k hk; simp at hk
    rw [show k + 1 - n = 0 by omega]; simp
  have h2 : ∀ k : ℕ, (1 - x) ^ (k + n) * x ^ 2 * ((k + n + 1 - n : ℕ) : ℝ) =
      ((1 - x) ^ n * x ^ 2) * ((k : ℝ) * (1 - x) ^ k + (1 - x) ^ k) := by
    intro k
    rw [show k + n + 1 - n = k + 1 by omega]
    push_cast; ring
  rw [h1, zero_add, tsum_congr h2, tsum_mul_left, Summable.tsum_add hs1 hs0,
    tsum_coe_mul_geometric_of_norm_lt_one hny, tsum_geometric_of_lt_one hy0 hy1, sub_sub_cancel]
  field_simp
  ring

/-- the `Y`-coefficient for the connection bound -/
theorem kappaYc (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (n b : ℕ) (hb : b ≤ n) :
    ∑' k : ℕ, (1 - x) ^ k * x ^ 2 *
      (∑ t ∈ range (k + 1), if min t n = b then (1 : ℝ) else 0) =
      if b < n then x * (1 - x) ^ b else (1 - x) ^ n := by
  by_cases hbn : b < n
  · rw [if_pos hbn, ← geom_tail x hx0 hx1 b]
    apply tsum_congr; intro k
    have : (∑ t ∈ range (k + 1), if min t n = b then (1 : ℝ) else 0) =
        if b ≤ k then 1 else 0 := by
      by_cases hbk : b ≤ k
      · rw [if_pos hbk, Finset.sum_eq_single b]
        · rw [if_pos (min_eq_left hbn.le)]
        · intro t _ htb
          rw [if_neg]; intro h
          apply htb
          rcases le_total t n with h' | h'
          · rw [min_eq_left h'] at h; exact h
          · rw [min_eq_right h'] at h; omega
        · intro hb'
          simp at hb'
          omega
      · rw [if_neg hbk]
        apply Finset.sum_eq_zero
        intro t ht
        simp at ht
        rw [if_neg]; intro h
        have : min t n ≤ t := min_le_left _ _
        omega
    rw [this]; split_ifs <;> ring
  · rw [if_neg hbn]
    have hbn' : b = n := by omega
    subst hbn'
    rw [← tsum_count_tail x hx0 hx1 b]
    apply tsum_congr; intro k
    congr 1
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    rw [show (range (k + 1)).filter (fun t => min t b = b) = Finset.Ico b (k + 1) by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, min_eq_right_iff]
      omega]
    simp

end APTSPConn

open APTSPConn in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (pf : V → ℝ) (d : V) (σ p : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hp0 : 0 < p) (hp1 : p < 1) (hnorm : IsNormalized c pf d p)
    (T : List V) (hT : IsTour T) (hd : T.head? = some d) :
    ∑ S : Finset V, subsetProb (fun v => linSampling σ (pf v)) S *
        ∑ v, pf v * distToSet c v S ≤
      σ ^ 2 * p * ∑' k : ℕ, (1 - σ * p) ^ k *
        ∑ i ∈ Finset.Icc 1 k, min (hopC c p d T i) (hopC c p d T (k + 1 - i)) := by
  obtain ⟨hI, hnp⟩ := hnorm
  have hc := c_nonneg hI
  have hcdd : c d d = 0 := hI.c_self d
  have hpd : pf d = 1 := hI.p_depot
  obtain ⟨hnd, hall⟩ := hT
  have hTour : IsTour T := ⟨hnd, hall⟩
  obtain ⟨R, rfl⟩ : ∃ R, T = d :: R := by
    cases T with
    | nil => simp at hd
    | cons x R => simp at hd; exact ⟨R, by rw [hd]⟩
  set n := (d :: R).length with hn
  set w : ℕ → V := fun a => (d :: R).getD a d with hw
  have hw0 : w 0 = d := by simp [hw]
  have hwn : ∀ m, n ≤ m → w m = d := fun m hm => List.getD_eq_default _ _ hm
  have hwinj : ∀ s t, s < n → t < n → w s = w t → s = t := by
    intro s t hs ht heq
    simp only [hw] at heq
    rw [List.getD_eq_getElem _ _ hs, List.getD_eq_getElem _ _ ht] at heq
    exact (List.Nodup.getElem_inj_iff hnd).1 heq
  have hwne : ∀ s, 1 ≤ s → s < n → w s ≠ d := by
    intro s h1 h2 heq
    have := hwinj s 0 h2 (by simp [hn]) (by rw [heq, hw0])
    omega
  have hn1 : 1 ≤ n := by simp [hn]
  have hv : ∀ j : ℤ, tourVertex d (d :: R) j = w j.toNat := fun j => tourVertex_eq d _ hd j
  set x : ℝ := σ * p with hx
  have hx0 : 0 < x := mul_pos hσ0 hp0
  have hx1 : x < 1 := by rw [hx]; nlinarith
  set q : V → ℝ := fun v => linSampling σ (pf v) with hq
  have hqd : q d = 1 := by simp [hq, linSampling, hpd]
  have hqv : ∀ v, v ≠ d → q v = x := by
    intro v hv'
    simp only [hq, linSampling, hnp v hv']
    rw [if_neg (by linarith)]
  have hqw : ∀ s, 1 ≤ s → s < n → q (w s) = x := fun s h1 h2 => hqv _ (hwne s h1 h2)
  have hq01 : ∀ v, 0 ≤ q v ∧ q v ≤ 1 := by
    intro v
    by_cases hvd : v = d
    · rw [hvd, hqd]; norm_num
    · rw [hqv v hvd]; exact ⟨hx0.le, hx1.le⟩
  set g : ℕ → ℕ → ℝ := fun a b =>
    ∑ s ∈ Finset.Ioo a b, min (c (w a) (w s)) (c (w s) (w b)) with hg
  have hg0 : ∀ a b, 0 ≤ g a b := fun a b =>
    Finset.sum_nonneg (fun s _ => le_min (hc _ _) (hc _ _))
  set gap : Finset V → ℕ → ℕ → Prop := fun S a b =>
    d ∈ S ∧ (a < b ∧ w a ∈ S ∧ w b ∈ S ∧ ∀ s ∈ Finset.Ioo a b, w s ∉ S) with hgap
  have hdist : ∀ (v : V) (S : Finset V) (u : V), u ∈ S → distToSet c v S ≤ c v u := by
    intro v S u hu
    unfold distToSet
    apply csInf_le
    · exact ⟨0, by rintro _ ⟨u', _, rfl⟩; exact hc _ _⟩
    · exact Set.mem_image_of_mem _ (by simpa using hu)
  -- Step A: deterministic bound for a sample containing the depot
  have hA : ∀ S : Finset V, d ∈ S → ∑ v, pf v * distToSet c v S ≤
      p * ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), (if gap S a b then 1 else 0) * g a b := by
    intro S hdS
    have e1 : ∑ v, pf v * distToSet c v S = ∑ s ∈ range n, pf (w s) * distToSet c (w s) S := by
      apply Finset.sum_nbij' (fun v => (d :: R).idxOf v) w
      · intro v _; simp only [Finset.mem_range, hn]; exact List.idxOf_lt_length_iff.2 (hall v)
      · intro s _; exact Finset.mem_univ _
      · intro v _
        simp only [hw]
        rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.2 (hall v)), List.getElem_idxOf]
      · intro s hs
        simp only [Finset.mem_range] at hs
        simp only [hw]
        rw [List.getD_eq_getElem _ _ hs, List.Nodup.idxOf_getElem hnd]
      · intro v _
        simp only [hw]
        rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.2 (hall v)), List.getElem_idxOf]
    set D : ℕ → ℝ := fun s => ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
      if gap S a b ∧ s ∈ Finset.Ioo a b then min (c (w a) (w s)) (c (w s) (w b)) else 0 with hD
    have hD0 : ∀ s, 0 ≤ D s := fun s => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg
      (fun b _ => by split_ifs; exact le_min (hc _ _) (hc _ _); exact le_rfl))
    have e2 : ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), (if gap S a b then 1 else 0) * g a b =
        ∑ s ∈ range n, D s := by
      have e3 : ∑ s ∈ range n, D s = ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
          ∑ s ∈ range n, (if gap S a b ∧ s ∈ Finset.Ioo a b then
            min (c (w a) (w s)) (c (w s) (w b)) else 0) := by
        simp only [hD]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_comm]
      rw [e3]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b hb
      simp only [Finset.mem_range] at hb
      by_cases hgp : gap S a b
      · rw [if_pos hgp, one_mul]
        simp only [hg]
        rw [← Finset.sum_subset (s₁ := Finset.Ioo a b) (s₂ := range n)]
        · apply Finset.sum_congr rfl; intro s hs; rw [if_pos ⟨hgp, hs⟩]
        · intro s hs; simp at hs ⊢; omega
        · intro s _ hs; rw [if_neg (fun h => hs h.2)]
      · rw [if_neg hgp, zero_mul]; symm
        apply Finset.sum_eq_zero; intro s _; rw [if_neg (fun h => hgp h.1)]
    rw [e1, e2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    simp only [Finset.mem_range] at hs
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · subst hs0
      rw [hw0, hpd, one_mul]
      have := hdist d S d hdS
      rw [hcdd] at this
      have := hD0 0
      nlinarith
    · rw [hnp _ (hwne s hs0 hs)]
      apply mul_le_mul_of_nonneg_left _ hp0.le
      by_cases hsS : w s ∈ S
      · have := hdist (w s) S (w s) hsS
        rw [hI.c_self] at this
        linarith [hD0 s]
      · -- the gap containing s
        set a0 := Nat.findGreatest (fun a => w a ∈ S) s with ha0
        have ha0S : w a0 ∈ S := Nat.findGreatest_spec (P := fun a => w a ∈ S) (Nat.zero_le s)
          (by show w 0 ∈ S; rw [hw0]; exact hdS)
        have ha0le : a0 ≤ s := Nat.findGreatest_le s
        have ha0lt : a0 < s := by
          rcases lt_or_eq_of_le ha0le with h | h
          · exact h
          · exfalso; rw [h] at ha0S; exact hsS ha0S
        have ha0g : ∀ t, a0 < t → t ≤ s → w t ∉ S := fun t h1 h2 =>
          Nat.findGreatest_is_greatest (P := fun a => w a ∈ S) h1 h2
        have hex : ∃ b, s ≤ b ∧ w b ∈ S := ⟨n, by omega, by rw [hwn n le_rfl]; exact hdS⟩
        set b0 := Nat.find hex with hb0
        have hb0spec := Nat.find_spec hex
        have hb0le : b0 ≤ n := Nat.find_min' hex ⟨by omega, by rw [hwn n le_rfl]; exact hdS⟩
        have hb0lt : s < b0 := by
          rcases lt_or_eq_of_le hb0spec.1 with h | h
          · exact h
          · exfalso; rw [← h] at hb0spec; exact hsS hb0spec.2
        have hb0g : ∀ t, s ≤ t → t < b0 → w t ∉ S := by
          intro t h1 h2 h3
          have := Nat.find_min hex h2
          exact this ⟨h1, h3⟩
        have hgap0 : gap S a0 b0 := by
          refine ⟨hdS, by omega, ha0S, hb0spec.2, fun t ht => ?_⟩
          simp only [Finset.mem_Ioo] at ht
          rcases le_total t s with h | h
          · exact ha0g t ht.1 h
          · exact hb0g t h ht.2
        have hterm : min (c (w a0) (w s)) (c (w s) (w b0)) ≤ D s := by
          simp only [hD]
          have h1 : (if gap S a0 b0 ∧ s ∈ Finset.Ioo a0 b0 then
              min (c (w a0) (w s)) (c (w s) (w b0)) else 0) = min (c (w a0) (w s)) (c (w s) (w b0)) :=
            if_pos ⟨hgap0, by simp; omega⟩
          rw [← h1]
          have hin : ∀ a b, 0 ≤ (if gap S a b ∧ s ∈ Finset.Ioo a b then
              min (c (w a) (w s)) (c (w s) (w b)) else 0) := by
            intro a b; split_ifs; exact le_min (hc _ _) (hc _ _); exact le_rfl
          calc _ ≤ ∑ b ∈ range (n + 1), (if gap S a0 b ∧ s ∈ Finset.Ioo a0 b then
                min (c (w a0) (w s)) (c (w s) (w b)) else 0) :=
                Finset.single_le_sum (f := fun b => if gap S a0 b ∧ s ∈ Finset.Ioo a0 b then
                  min (c (w a0) (w s)) (c (w s) (w b)) else 0) (fun b _ => hin a0 b)
                  (by simp; omega)
            _ ≤ _ := Finset.single_le_sum (f := fun a => ∑ b ∈ range (n + 1),
                  (if gap S a b ∧ s ∈ Finset.Ioo a b then
                  min (c (w a) (w s)) (c (w s) (w b)) else 0))
                  (fun a _ => Finset.sum_nonneg (fun b _ => hin a b)) (by simp; omega)
        have hd1 := hdist (w s) S (w a0) ha0S
        have hd2 := hdist (w s) S (w b0) hb0spec.2
        rw [hI.c_symm (w s) (w a0)] at hd1
        have : distToSet c (w s) S ≤ min (c (w a0) (w s)) (c (w s) (w b0)) := le_min hd1 hd2
        linarith
  -- Step B: expectation over the sample
  set ρ : ℕ → ℝ := fun s => if s = 0 ∨ s = n then 1 else x with hρ
  set coefL : ℕ → ℕ → ℝ := fun a b => if a < b then ρ a * ρ b * (1 - x) ^ (b - a - 1) else 0
    with hcoefL
  have hL3 : ∀ a ∈ range (n + 1), ∀ b ∈ range (n + 1),
      ∑ S : Finset V, subsetProb q S * (if gap S a b then 1 else 0) = coefL a b := by
    intro a ha b hb
    simp only [Finset.mem_range] at ha hb
    by_cases hab : a < b
    · set S0 : Finset V := insert d (insert (w a) {w b}) with hS
      set U : Finset V := (Finset.Ioo a b).image w with hU
      have hmid : ∀ s ∈ Finset.Ioo a b, 1 ≤ s ∧ s < n := by
        intro s hs; simp at hs; omega
      have hdisj : Disjoint S0 U := by
        rw [Finset.disjoint_left]
        intro v hvS hvU
        simp only [hU, Finset.mem_image] at hvU
        obtain ⟨s, hs, rfl⟩ := hvU
        obtain ⟨hs1, hs2⟩ := hmid s hs
        have hs' := Finset.mem_Ioo.1 hs
        simp only [hS, Finset.mem_insert, Finset.mem_singleton] at hvS
        rcases hvS with h | h | h
        · exact hwne s hs1 hs2 h
        · by_cases ha0 : a = 0
          · rw [ha0, hw0] at h; exact hwne s hs1 hs2 h
          · have := hwinj s a hs2 (by omega) h; omega
        · by_cases hbn : b = n
          · rw [hbn, hwn n le_rfl] at h; exact hwne s hs1 hs2 h
          · have := hwinj s b hs2 (by omega) h; omega
      have hiff : ∀ A : Finset V, (if gap A a b then (1 : ℝ) else 0) =
          if S0 ⊆ A ∧ Disjoint U A then 1 else 0 := by
        intro A
        congr 1
        apply propext
        simp only [hgap, hS, hU, Finset.insert_subset_iff, Finset.singleton_subset_iff,
          Finset.disjoint_left, Finset.mem_image]
        constructor
        · rintro ⟨h1, _, h2, h3, h4⟩
          refine ⟨⟨h1, h2, h3⟩, ?_⟩
          rintro v ⟨s, hs, rfl⟩; exact h4 s hs
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          exact ⟨h1, hab, h2, h3, fun s hs => h4 ⟨s, hs, rfl⟩⟩
      simp_rw [hiff]
      rw [pattern q S0 U hdisj]
      have hprodU : ∏ v ∈ U, (1 - q v) = (1 - x) ^ (b - a - 1) := by
        rw [hU, Finset.prod_image]
        · rw [Finset.prod_congr rfl (fun s hs => by
            rw [hqw s (hmid s hs).1 (hmid s hs).2])]
          rw [Finset.prod_const, Nat.card_Ioo]
        · intro s hs t ht hst
          exact hwinj s t (hmid s hs).2 (hmid t ht).2 hst
      have hprodS : ∏ v ∈ S0, q v = ρ a * ρ b := by
        simp only [hρ]
        by_cases ha0 : a = 0
        · subst ha0
          rw [hS, hw0]
          by_cases hbn : b = n
          · subst hbn
            rw [hwn _ le_rfl]
            simp [hqd]
          · have hb1 : 1 ≤ b := by omega
            have hwb : w b ≠ d := hwne b hb1 (by omega)
            rw [Finset.insert_eq_of_mem (by simp), Finset.prod_insert (by simp; exact hwb.symm),
              Finset.prod_singleton, hqd, hqw b hb1 (by omega)]
            rw [if_pos (Or.inl rfl), if_neg (by omega)]; try ring
        · have ha1 : 1 ≤ a := by omega
          have hwa : w a ≠ d := hwne a ha1 (by omega)
          by_cases hbn : b = n
          · subst hbn
            rw [hS, hwn _ le_rfl]
            rw [Finset.pair_comm, Finset.insert_eq_of_mem (by simp),
              Finset.prod_insert (by simp; exact hwa.symm), Finset.prod_singleton, hqd,
              hqw a ha1 (by omega)]
            rw [if_neg (by omega), if_pos (Or.inr rfl)]; try ring
          · have hb1 : 1 ≤ b := by omega
            have hwb : w b ≠ d := hwne b hb1 (by omega)
            have hab' : w a ≠ w b := fun h => by have := hwinj a b (by omega) (by omega) h; omega
            rw [hS, Finset.prod_insert (by simp; exact ⟨hwa.symm, hwb.symm⟩),
              Finset.prod_insert (by simp; exact hab'), Finset.prod_singleton, hqd,
              hqw a ha1 (by omega), hqw b hb1 (by omega)]
            rw [if_neg (by omega), if_neg (by omega)]; try ring
      rw [hprodU, hprodS]
      simp only [hcoefL, if_pos hab]
    · simp only [hcoefL, if_neg hab]
      apply Finset.sum_eq_zero; intro A _
      rw [if_neg (fun h => hab h.2.1), mul_zero]
  have hB : ∑ S : Finset V, subsetProb q S * ∑ v, pf v * distToSet c v S ≤
      p * ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), g a b * coefL a b := by
    calc ∑ S : Finset V, subsetProb q S * ∑ v, pf v * distToSet c v S
        ≤ ∑ S : Finset V, subsetProb q S * (p * ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
            (if gap S a b then 1 else 0) * g a b) := by
          apply Finset.sum_le_sum; intro S _
          by_cases hdS : d ∈ S
          · exact mul_le_mul_of_nonneg_left (hA S hdS) (subsetProb_nonneg q hq01 S)
          · have hP : subsetProb q S = 0 := by
              unfold subsetProb
              have : ∏ v ∈ univ \ S, (1 - q v) = 0 :=
                Finset.prod_eq_zero (i := d) (by simp [hdS]) (by rw [hqd]; ring)
              rw [this, mul_zero]
            rw [hP, zero_mul, zero_mul]
      _ = p * ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), g a b * coefL a b := by
          have e : ∀ S : Finset V, subsetProb q S * (p * ∑ a ∈ range (n + 1),
              ∑ b ∈ range (n + 1), (if gap S a b then 1 else 0) * g a b) =
              p * ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1),
              g a b * (subsetProb q S * (if gap S a b then 1 else 0)) := by
            intro S
            rw [← mul_assoc, mul_comm (subsetProb q S) p, mul_assoc, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl; intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro b _
            ring
          rw [Finset.sum_congr rfl (fun S _ => e S), ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro a ha
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro b hb
          rw [← Finset.mul_sum, hL3 a ha b hb]
  -- Step C1: comparison with the hop sums, for each k
  set C : ℕ → ℝ := fun k => hopC c p d (d :: R) k with hC
  set Gs : ℕ → ℝ := fun k => ∑ a ∈ range n, g a (min (a + (k + 1)) n) +
    ∑ t ∈ range (k + 1), g 0 (min t n) with hGs
  have hC1 : ∀ k : ℕ, x ^ 2 * Gs k ≤
      σ ^ 2 * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)) := by
    intro k
    set K : ℕ := k + 1 with hK
    set W : Finset ℤ := Finset.Icc (-(K : ℤ)) ((n : ℤ) - 1) with hW
    set v : ℤ → V := fun j => tourVertex d (d :: R) j with hvdef
    have hCi : ∀ i ∈ Finset.Icc 1 k, C i = p ^ 2 * ∑ j ∈ W, c (v j) (v (j + i)) := by
      intro i hi
      simp at hi
      exact hopC_window c p d (d :: R) hd hcdd i K ((n : ℤ) - 1) (by omega) le_rfl
    have hCKi : ∀ i ∈ Finset.Icc 1 k, C (k + 1 - i) =
        p ^ 2 * ∑ j ∈ W, c (v (j + i)) (v (j + K)) := by
      intro i hi
      simp at hi
      rw [hC]
      simp only
      rw [hopC_window c p d (d :: R) hd hcdd (k + 1 - i) (k + 1 - i) ((n : ℤ) - 1 + i) le_rfl
        (by omega)]
      congr 1
      apply Finset.sum_nbij' (fun l : ℤ => l - (i : ℤ)) (fun l : ℤ => l + (i : ℤ))
      · intro l hl; simp [hW] at hl ⊢; omega
      · intro l hl; simp [hW] at hl ⊢; omega
      · intro l _; simp
      · intro l _; simp
      · intro l _
        simp only [hvdef]
        congr 2
        · ring
        · rw [hK]; push_cast [Nat.cast_sub (by omega : i ≤ k + 1)]; ring
    -- per-j bound
    have hj : ∀ j ∈ W, g j.toNat (min (j + K).toNat n) ≤
        ∑ i ∈ Finset.Icc 1 k, min (c (v j) (v (j + i))) (c (v (j + i)) (v (j + K))) := by
      intro j hjW
      simp [hW] at hjW
      set a := j.toNat with ha
      set b := min (j + K).toNat n with hb
      set φ : ℕ → ℕ := fun s => ((s : ℤ) - j).toNat with hφ
      set H : ℕ → ℝ := fun i => min (c (v j) (v (j + i))) (c (v (j + i)) (v (j + K))) with hH
      have hva : v j = w a := hv j
      have hvb : v (j + K) = w b := by
        simp only [hvdef]
        rw [hv]
        by_cases hle : (j + K).toNat ≤ n
        · rw [hb, min_eq_left hle]
        · rw [hb, min_eq_right (by omega), hwn n le_rfl, hwn _ (by omega)]
      have himg : (Finset.Ioo a b).image φ ⊆ Finset.Icc 1 k := by
        intro i hi
        simp only [Finset.mem_image, Finset.mem_Ioo] at hi
        obtain ⟨s, ⟨hs1, hs2⟩, rfl⟩ := hi
        simp only [Finset.mem_Icc, hφ]
        omega
      have hinj : Set.InjOn φ (Finset.Ioo a b : Set ℕ) := by
        intro s hs t ht hst
        simp only [Finset.coe_Ioo, Set.mem_Ioo] at hs ht
        simp only [hφ] at hst
        omega
      calc g a b = ∑ s ∈ Finset.Ioo a b, H (φ s) := by
            simp only [hg]
            apply Finset.sum_congr rfl
            intro s hs
            simp only [Finset.mem_Ioo] at hs
            have hjs : j + ((φ s : ℕ) : ℤ) = (s : ℤ) := by simp only [hφ]; omega
            simp only [hH]
            rw [hjs, hva, hvb]
            simp only [hvdef]
            rw [hv (s : ℤ)]
            simp
        _ = ∑ i ∈ (Finset.Ioo a b).image φ, H i := (Finset.sum_image hinj).symm
        _ ≤ ∑ i ∈ Finset.Icc 1 k, H i :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => le_min (hc _ _) (hc _ _))
    -- reindex Gs
    have hGsW : Gs k = ∑ j ∈ W, g j.toNat (min (j + K).toNat n) := by
      have hb : ∑ m ∈ range (K + n), g (m - K) (min m n) =
          ∑ j ∈ W, g j.toNat (min (j + K).toNat n) := by
        apply Finset.sum_nbij' (fun m : ℕ => (m : ℤ) - K) (fun j : ℤ => (j + K).toNat)
        · intro m hm; simp [hW] at hm ⊢; omega
        · intro j hj; simp [hW] at hj ⊢; omega
        · intro m _; simp
        · intro j hj; simp [hW] at hj ⊢; omega
        · intro m _
          congr 2
          · omega
          · omega
      rw [← hb, Finset.sum_range_add, add_comm]
      simp only [hGs]
      congr 1
      · apply Finset.sum_congr rfl; intro a _
        congr 2
        · omega
        · omega
      · apply Finset.sum_congr rfl; intro t ht
        simp at ht
        congr 1
        omega
    -- assemble
    have hmin : ∀ i ∈ Finset.Icc 1 k, p ^ 2 * ∑ j ∈ W,
        min (c (v j) (v (j + i))) (c (v (j + i)) (v (j + K))) ≤ min (C i) (C (k + 1 - i)) := by
      intro i hi
      rw [hCi i hi, hCKi i hi, ← mul_min_of_nonneg _ _ (sq_nonneg p)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg p)
      exact le_min (Finset.sum_le_sum (fun j _ => min_le_left _ _))
        (Finset.sum_le_sum (fun j _ => min_le_right _ _))
    calc x ^ 2 * Gs k = σ ^ 2 * (p ^ 2 * ∑ j ∈ W, g j.toNat (min (j + K).toNat n)) := by
          rw [hGsW, hx]; ring
      _ ≤ σ ^ 2 * (p ^ 2 * ∑ j ∈ W, ∑ i ∈ Finset.Icc 1 k,
            min (c (v j) (v (j + i))) (c (v (j + i)) (v (j + K)))) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg σ)
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg p)
          exact Finset.sum_le_sum hj
      _ = σ ^ 2 * ∑ i ∈ Finset.Icc 1 k, p ^ 2 * ∑ j ∈ W,
            min (c (v j) (v (j + i))) (c (v (j + i)) (v (j + K))) := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ σ ^ 2 * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmin) (sq_nonneg σ)
  -- Step C2: the weights
  set φX : ℕ → ℕ → ℕ → ℝ := fun k a b =>
    (1 - x) ^ k * x ^ 2 * (if a < n ∧ b = min (a + (k + 1)) n then 1 else 0) with hφX
  set φY : ℕ → ℕ → ℕ → ℝ := fun k a b =>
    (1 - x) ^ k * x ^ 2 * (if a = 0 then
      ∑ t ∈ range (k + 1), (if min t n = b then (1 : ℝ) else 0) else 0) with hφY
  have hR1 : ∀ k : ℕ, (1 - x) ^ k * x ^ 2 * Gs k =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), g a b * (φX k a b + φY k a b) := by
    intro k
    have hX : ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), g a b * φX k a b =
        (1 - x) ^ k * x ^ 2 * ∑ a ∈ range n, g a (min (a + (k + 1)) n) := by
      rw [Finset.sum_range_succ]
      have hlast : ∑ b ∈ range (n + 1), g n b * φX k n b = 0 := by
        apply Finset.sum_eq_zero; intro b _
        simp only [hφX]; rw [if_neg (by omega)]; ring
      rw [hlast, add_zero, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a ha
      simp only [Finset.mem_range] at ha
      have : ∀ b, g a b * φX k a b =
          if b = min (a + (k + 1)) n then (1 - x) ^ k * x ^ 2 * g a b else 0 := by
        intro b
        simp only [hφX]
        by_cases hb : b = min (a + (k + 1)) n
        · rw [if_pos ⟨ha, hb⟩, if_pos hb]; ring
        · rw [if_neg (fun h => hb h.2), if_neg hb]; ring
      rw [Finset.sum_congr rfl (fun b _ => this b), Finset.sum_ite_eq']
      rw [if_pos (by simp only [Finset.mem_range]; omega)]
    have hY : ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), g a b * φY k a b =
        (1 - x) ^ k * x ^ 2 * ∑ t ∈ range (k + 1), g 0 (min t n) := by
      rw [Finset.sum_eq_single 0]
      · simp only [hφY, if_true]
        have : ∀ b, g 0 b * ((1 - x) ^ k * x ^ 2 *
            ∑ t ∈ range (k + 1), (if min t n = b then (1 : ℝ) else 0)) =
            (1 - x) ^ k * x ^ 2 * ∑ t ∈ range (k + 1), (if min t n = b then g 0 b else 0) := by
          intro b
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro t _
          split_ifs <;> ring
        rw [Finset.sum_congr rfl (fun b _ => this b), ← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl; intro t _
        rw [Finset.sum_ite_eq]
        rw [if_pos (by simp only [Finset.mem_range]; omega)]
      · intro a _ ha0
        apply Finset.sum_eq_zero; intro b _
        simp only [hφY]; rw [if_neg ha0]; ring
      · intro h; simp at h
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hX, hY, hGs]
    ring
  have hx1' : x ≤ 1 := hx1.le
  have hsX : ∀ a b, Summable (fun k => φX k a b) := by
    intro a b
    have hr0 : 0 ≤ 1 - x := by linarith
    apply Summable.of_nonneg_of_le _ _
      ((summable_geometric_of_lt_one hr0 (by linarith)).mul_right (x ^ 2))
    · intro k; simp only [hφX]; split_ifs <;> positivity
    · intro k; simp only [hφX]; split_ifs <;> simp; positivity
  have hsY : ∀ a b, Summable (fun k => φY k a b) := by
    intro a b
    have hr0 : 0 ≤ 1 - x := by linarith
    have hny : ‖1 - x‖ < 1 := by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
    have hs1 : Summable (fun k : ℕ => (k : ℝ) * (1 - x) ^ k) := by
      have := summable_pow_mul_geometric_of_norm_lt_one 1 hny
      simpa using this
    have hs0 : Summable (fun k : ℕ => (1 - x) ^ k) := summable_geometric_of_lt_one hr0 (by linarith)
    apply Summable.of_nonneg_of_le _ _ ((hs1.add hs0).mul_right (x ^ 2))
    · intro k; simp only [hφY]
      apply mul_nonneg (by positivity)
      split_ifs
      · exact Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num)
      · exact le_rfl
    · intro k; simp only [hφY]
      have hcnt : (if a = 0 then ∑ t ∈ range (k + 1), (if min t n = b then (1 : ℝ) else 0)
          else 0) ≤ (k : ℝ) + 1 := by
        split_ifs
        · calc ∑ t ∈ range (k + 1), (if min t n = b then (1 : ℝ) else 0)
              ≤ ∑ t ∈ range (k + 1), (1 : ℝ) :=
                Finset.sum_le_sum (fun t _ => by split_ifs <;> norm_num)
            _ = (k : ℝ) + 1 := by simp
        · positivity
      have hpos : 0 ≤ (1 - x) ^ k * x ^ 2 := by positivity
      calc (1 - x) ^ k * x ^ 2 * (if a = 0 then
            ∑ t ∈ range (k + 1), (if min t n = b then (1 : ℝ) else 0) else 0)
          ≤ (1 - x) ^ k * x ^ 2 * ((k : ℝ) + 1) := mul_le_mul_of_nonneg_left hcnt hpos
        _ = ((k : ℝ) * (1 - x) ^ k + (1 - x) ^ k) * x ^ 2 := by ring
  have hC2 : ∑' k : ℕ, (1 - x) ^ k * x ^ 2 * Gs k =
      ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), g a b * coefL a b := by
    rw [tsum_congr hR1]
    rw [Summable.tsum_finsetSum (fun a _ => by
      apply summable_sum; intro b _; exact ((hsX a b).add (hsY a b)).mul_left _)]
    apply Finset.sum_congr rfl; intro a ha
    rw [Summable.tsum_finsetSum (fun b _ => ((hsX a b).add (hsY a b)).mul_left _)]
    apply Finset.sum_congr rfl; intro b hb
    simp only [Finset.mem_range] at ha hb
    rw [tsum_mul_left, Summable.tsum_add (hsX a b) (hsY a b)]
    have eX : ∑' k : ℕ, φX k a b = if a < b ∧ b < n then x ^ 2 * (1 - x) ^ (b - a - 1)
        else if a < n ∧ b = n then x * (1 - x) ^ (n - a - 1) else 0 :=
      kappaX x hx0 hx1' n a b
    have eY : ∑' k : ℕ, φY k a b = if a = 0 then
        (if b < n then x * (1 - x) ^ b else (1 - x) ^ n) else 0 := by
      by_cases ha0 : a = 0
      · rw [if_pos ha0, ← kappaYc x hx0 hx1' n b (by omega)]
        apply tsum_congr; intro k; simp only [hφY, if_pos ha0]
      · rw [if_neg ha0]
        have : ∀ k, φY k a b = 0 := by intro k; simp only [hφY, if_neg ha0]; ring
        rw [tsum_congr this, tsum_zero]
    rw [eX, eY]
    by_cases hab : a < b
    · congr 1
      simp only [hcoefL, hρ, if_pos hab]
      have hpow : ∀ m : ℕ, 1 ≤ m → (1 - x) ^ m = (1 - x) ^ (m - 1) * (1 - x) := by
        intro m hm; rw [← pow_succ]; congr 1; omega
      rcases Nat.eq_zero_or_pos a with ha0 | ha0
      · subst ha0
        by_cases hbn : b < n
        · rw [if_pos (show 0 = 0 ∨ 0 = n from Or.inl rfl),
            if_neg (show ¬(b = 0 ∨ b = n) by omega), if_pos (show 0 < b ∧ b < n from ⟨hab, hbn⟩),
            if_pos (show (0 : ℕ) = 0 from rfl), if_pos hbn]
          rw [hpow b (by omega)]; simp only [Nat.sub_zero]; ring
        · have hb' : b = n := by omega
          rw [if_pos (show 0 = 0 ∨ 0 = n from Or.inl rfl),
            if_pos (show b = 0 ∨ b = n from Or.inr hb'), if_neg (show ¬(0 < b ∧ b < n) by omega),
            if_pos (show 0 < n ∧ b = n from ⟨by omega, hb'⟩),
            if_pos (show (0 : ℕ) = 0 from rfl), if_neg hbn, hb']
          rw [hpow n (by omega)]; simp only [Nat.sub_zero]; ring
      · by_cases hbn : b < n
        · rw [if_neg (show ¬(a = 0 ∨ a = n) by omega), if_neg (show ¬(b = 0 ∨ b = n) by omega),
            if_pos (show a < b ∧ b < n from ⟨hab, hbn⟩), if_neg (show ¬(a = 0) by omega)]
          ring
        · have hb' : b = n := by omega
          rw [if_neg (show ¬(a = 0 ∨ a = n) by omega), if_pos (show b = 0 ∨ b = n by omega),
            if_neg (show ¬(a < b ∧ b < n) by omega), if_pos (show a < n ∧ b = n by omega),
            if_neg (show ¬(a = 0) by omega), hb']
          ring
    · have : g a b = 0 := by
        simp only [hg]
        rw [Finset.Ioo_eq_empty (by omega), Finset.sum_empty]
      rw [this, zero_mul, zero_mul]
  -- summability of the right-hand side
  have hC0 : ∀ k, 0 ≤ C k := fun k => hopC_nonneg c hc p d (d :: R) k
  have hCt : ∀ i j, C (i + j) ≤ C i + C j := fun i j => hopC_triangle c p d hI (d :: R) hd i j
  have hClin : ∀ k : ℕ, C (k + 1) ≤ ((k : ℝ) + 1) * C 1 := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      have := hCt (m + 1) 1
      push_cast
      linarith
  have hr0 : 0 ≤ 1 - x := by linarith
  have hnorm_r : ‖1 - x‖ < 1 := by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have hminle : ∀ k, ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)) ≤
      ((k : ℝ) + 1) ^ 2 * C 1 := by
    intro k
    have hb : ∀ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)) ≤ ((k : ℝ) + 1) * C 1 := by
      intro i hi
      simp at hi
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have := hClin i'
      have hle : ((i' : ℝ) + 1) ≤ (k : ℝ) + 1 := by
        have : (i' : ℝ) + 1 ≤ k := by exact_mod_cast hi.2
        linarith
      calc min (C (i' + 1)) (C (k + 1 - (i' + 1))) ≤ C (i' + 1) := min_le_left _ _
        _ ≤ ((i' : ℝ) + 1) * C 1 := this
        _ ≤ ((k : ℝ) + 1) * C 1 := mul_le_mul_of_nonneg_right hle (hC0 1)
    calc ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))
        ≤ ∑ i ∈ Finset.Icc 1 k, ((k : ℝ) + 1) * C 1 := Finset.sum_le_sum hb
      _ = (k : ℝ) * (((k : ℝ) + 1) * C 1) := by simp
      _ ≤ ((k : ℝ) + 1) ^ 2 * C 1 := by nlinarith [hC0 1]
  have hmaj : Summable (fun k : ℕ => (1 - x) ^ k * (((k : ℝ) + 1) ^ 2 * C 1)) := by
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hnorm_r
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm_r
    have h0 := summable_geometric_of_lt_one hr0 (by linarith : 1 - x < 1)
    have := ((h2.add (h1.mul_left 2)).add h0).mul_right (C 1)
    refine this.congr (fun k => ?_)
    ring
  have hsumN : Summable (fun k : ℕ => (1 - x) ^ k *
      ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))) := by
    apply Summable.of_nonneg_of_le _ _ hmaj
    · intro k
      exact mul_nonneg (pow_nonneg hr0 _)
        (Finset.sum_nonneg (fun i _ => le_min (hC0 _) (hC0 _)))
    · intro k
      exact mul_le_mul_of_nonneg_left (hminle k) (pow_nonneg hr0 _)
  have hGs0 : ∀ k, 0 ≤ Gs k := fun k => add_nonneg (Finset.sum_nonneg (fun a _ => hg0 _ _))
    (Finset.sum_nonneg (fun t _ => hg0 _ _))
  have hsumG : Summable (fun k : ℕ => (1 - x) ^ k * x ^ 2 * Gs k) := by
    apply Summable.of_nonneg_of_le (fun k => by have := hGs0 k; positivity) _
      (hsumN.mul_left (σ ^ 2))
    intro k
    have := mul_le_mul_of_nonneg_left (hC1 k) (pow_nonneg hr0 k)
    calc (1 - x) ^ k * x ^ 2 * Gs k = (1 - x) ^ k * (x ^ 2 * Gs k) := by ring
      _ ≤ (1 - x) ^ k * (σ ^ 2 * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))) := this
      _ = σ ^ 2 * ((1 - x) ^ k * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))) := by ring
  -- conclusion
  calc ∑ S : Finset V, subsetProb (fun v => linSampling σ (pf v)) S *
        ∑ v, pf v * distToSet c v S
      ≤ p * ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), g a b * coefL a b := hB
    _ = p * ∑' k : ℕ, (1 - x) ^ k * x ^ 2 * Gs k := by rw [hC2]
    _ ≤ p * ∑' k : ℕ, σ ^ 2 * ((1 - x) ^ k * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))) := by
        apply mul_le_mul_of_nonneg_left _ hp0.le
        apply Summable.tsum_le_tsum _ hsumG (hsumN.mul_left _)
        intro k
        have := mul_le_mul_of_nonneg_left (hC1 k) (pow_nonneg hr0 k)
        calc (1 - x) ^ k * x ^ 2 * Gs k = (1 - x) ^ k * (x ^ 2 * Gs k) := by ring
          _ ≤ (1 - x) ^ k * (σ ^ 2 * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))) := this
          _ = σ ^ 2 * ((1 - x) ^ k * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))) := by ring
    _ = σ ^ 2 * p * ∑' k : ℕ, (1 - σ * p) ^ k *
        ∑ i ∈ Finset.Icc 1 k, min (hopC c p d (d :: R) i) (hopC c p d (d :: R) (k + 1 - i)) := by
        rw [tsum_mul_left]; ring
