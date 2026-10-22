-- Prove2me | solution 1 for AKS.r_exists
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:15:52.015502+00:00
-- url     : https://prove2.me/submissions/d2cad390-921b-4083-a478-652042d11a66

import Mathlib
import Definitions.Def_AKS_poly
import Definitions.Def_AKS_alg
open AKS

theorem g71a_lcmFirst_succ (m : ℕ) : lcmFirst (m + 1) = Nat.lcm (lcmFirst m) (m + 1) := by
  unfold lcmFirst
  rw [List.range_succ, List.foldl_append]
  rfl

theorem g71a_lcmFirst_pos (m : ℕ) : 0 < lcmFirst m := by
  induction m with
  | zero => decide
  | succ m ih => rw [g71a_lcmFirst_succ]; exact Nat.lcm_pos ih (by omega)

theorem g71a_dvd_lcmFirst {j m : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) : j ∣ lcmFirst m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [g71a_lcmFirst_succ]
    rcases Nat.lt_or_ge j (m + 1) with h | h
    · exact dvd_trans (ih (by omega)) (Nat.dvd_lcm_left _ _)
    · have : j = m + 1 := by omega
      subst this; exact Nat.dvd_lcm_right _ _

theorem g71a_lcmFirst_dvd {m Q : ℕ} (h : ∀ j, 1 ≤ j → j ≤ m → j ∣ Q) : lcmFirst m ∣ Q := by
  induction m with
  | zero => exact one_dvd _
  | succ m ih =>
    rw [g71a_lcmFirst_succ]
    exact Nat.lcm_dvd (ih fun j h1 h2 => h j h1 (by omega)) (h _ (by omega) le_rfl)

theorem g71a_lcmFirst_mono {m m' : ℕ} (h : m ≤ m') : lcmFirst m ∣ lcmFirst m' :=
  g71a_lcmFirst_dvd fun _ h1 h2 => g71a_dvd_lcmFirst h1 (le_trans h2 h)

/-- closed form step -/
theorem g71a_step (N k : ℕ) (hk : 1 ≤ k) :
    (1 : ℚ) / (k * (N + 1 + k).choose k) =
      1 / (k * (N + k).choose k) - 1 / ((k + 1 : ℕ) * (N + k + 1).choose (k + 1)) := by
  have hB := Nat.choose_mul_succ_eq (N + k) k
  have hC := Nat.add_one_mul_choose_eq (N + k) k
  have e1 : N + k + 1 - k = N + 1 := by omega
  rw [e1] at hB
  have e2 : N + 1 + k = N + k + 1 := by omega
  rw [e2]
  have hA0 : ((N + k).choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hB0 : ((N + k + 1).choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hC0 : ((N + k + 1).choose (k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hBq : ((N + k).choose k : ℚ) * (N + k + 1) = ((N + k + 1).choose k) * (N + 1) := by
    exact_mod_cast hB
  have hCq : ((N + k + 1 : ℕ) : ℚ) * ((N + k).choose k) = ((N + k + 1).choose (k + 1)) * (k + 1) := by
    exact_mod_cast hC
  push_cast at hCq ⊢
  have hN1 : (N : ℚ) + 1 ≠ 0 := by positivity
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have hB' : ((N + k + 1).choose k : ℚ) = ((N + k).choose k) * (N + k + 1) / (N + 1) := by
    rw [hBq]; field_simp
  have hC' : ((N + k + 1).choose (k + 1) : ℚ) = (N + k + 1) * ((N + k).choose k) / (k + 1) := by
    rw [hCq]; field_simp
  rw [hB', hC']
  field_simp
  ring

theorem g71a_sum_identity (N : ℕ) : ∀ k : ℕ, 1 ≤ k →
    (∑ i ∈ Finset.range (N + 1), (-1 : ℚ) ^ i * (N.choose i) / ((k + i : ℕ) : ℚ)) =
      1 / (k * (N + k).choose k) := by
  induction N with
  | zero => intro k hk; simp
  | succ N ih =>
    intro k hk
    have ih2 := ih (k + 1) (by omega)
    rw [show N + (k + 1) = N + k + 1 by omega] at ih2
    rw [g71a_step N k hk, ← ih k hk, ← ih2]
    rw [Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range (N + 1),
        (-1 : ℚ) ^ (i + 1) * ((N + 1).choose (i + 1) : ℕ) / ((k + (i + 1) : ℕ) : ℚ)
        = -((-1 : ℚ) ^ i * (N.choose i) / ((k + 1 + i : ℕ) : ℚ)) +
          (-1 : ℚ) ^ (i + 1) * (N.choose (i + 1)) / ((k + (i + 1) : ℕ) : ℚ) := by
      intro i _
      rw [Nat.choose_succ_succ', show k + (i + 1) = k + 1 + i by omega]
      push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have h2 : (∑ i ∈ Finset.range (N + 1), (-1 : ℚ) ^ i * (N.choose i) / ((k + i : ℕ) : ℚ)) =
        (∑ i ∈ Finset.range (N + 1 + 1), (-1 : ℚ) ^ i * (N.choose i) / ((k + i : ℕ) : ℚ)) := by
      rw [Finset.sum_range_succ _ (N + 1)]; simp
    rw [h2, Finset.sum_range_succ' _ (N + 1)]
    simp
    ring

theorem g71a_kchoose_dvd (N k : ℕ) (hk : 1 ≤ k) :
    k * (N + k).choose k ∣ lcmFirst (N + k) := by
  set L := lcmFirst (N + k) with hL
  have hdv : ∀ i ∈ Finset.range (N + 1), (k + i) ∣ L := fun i hi =>
    g71a_dvd_lcmFirst (by omega) (by simp at hi; omega)
  set z : ℤ := ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (N.choose i) * ((L / (k + i) : ℕ) : ℤ)
  have hz : (L : ℚ) * (1 / (k * (N + k).choose k)) = z := by
    rw [← g71a_sum_identity N k hk, Finset.mul_sum]
    simp only [z]; rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : ((k + i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : k + i ≠ 0)
    have hq : ((L / (k + i) : ℕ) : ℚ) = (L : ℚ) / ((k + i : ℕ) : ℚ) := Nat.cast_div (hdv i hi) hne
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [hq]; field_simp
  have hA0 : ((N + k).choose k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hz2 : (L : ℚ) = (z : ℚ) * (k * (N + k).choose k) := by
    rw [← hz]; field_simp
  have hz3 : (L : ℤ) = z * ((k * (N + k).choose k : ℕ) : ℤ) := by
    push_cast; exact_mod_cast hz2
  have : ((k * (N + k).choose k : ℕ) : ℤ) ∣ (L : ℤ) := ⟨z, by rw [hz3]; ring⟩
  exact_mod_cast this

theorem g71a_lcm_lower (m : ℕ) (hm : 7 ≤ m) : 2 ^ m ≤ lcmFirst m := by
  have odd_case : ∀ t, 2 ≤ t → t * 4 ^ t ≤ lcmFirst (2 * t + 1) := by
    intro t ht
    have h1 : t * (2 * t).choose t ∣ lcmFirst (2 * t + 1) := by
      have := g71a_kchoose_dvd t t (by omega)
      rw [show t + t = 2 * t by ring] at this
      exact dvd_trans this (g71a_lcmFirst_mono (by omega))
    have h2 : (2 * t + 1) * (2 * t).choose t ∣ lcmFirst (2 * t + 1) := by
      have := g71a_kchoose_dvd t (t + 1) (by omega)
      rw [show t + (t + 1) = 2 * t + 1 by ring] at this
      have e := Nat.add_one_mul_choose_eq (2 * t) t
      rw [show (2 * t + 1).choose (t + 1) * (t + 1) = (t + 1) * (2 * t + 1).choose (t + 1) by ring] at e
      rw [e]; exact this
    have hcop : Nat.Coprime t (2 * t + 1) := by
      simp
    have h3 : t * (2 * t + 1) * (2 * t).choose t ∣ lcmFirst (2 * t + 1) := by
      have := Nat.lcm_dvd h1 h2
      rwa [Nat.lcm_mul_right, hcop.lcm_eq_mul] at this
    have h4 := Nat.le_of_dvd (g71a_lcmFirst_pos _) h3
    have h5 := Nat.four_pow_le_two_mul_add_one_mul_central_binom t
    calc t * 4 ^ t ≤ t * ((2 * t + 1) * (2 * t).choose t) := Nat.mul_le_mul_left _ h5
      _ = t * (2 * t + 1) * (2 * t).choose t := by ring
      _ ≤ _ := h4
  obtain ⟨t, rfl | rfl⟩ : ∃ t, m = 2 * t + 1 ∨ m = 2 * t + 2 := ⟨(m - 1) / 2, by omega⟩
  · have := odd_case t (by omega)
    calc 2 ^ (2 * t + 1) = 2 * 4 ^ t := by rw [pow_succ, pow_mul]; norm_num; ring
      _ ≤ t * 4 ^ t := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := this
  · rcases Nat.lt_or_ge t 4 with h | h
    · have : t = 3 := by omega
      subst this; decide
    have := odd_case t (by omega)
    have hd := Nat.le_of_dvd (g71a_lcmFirst_pos _) (g71a_lcmFirst_mono (by omega : 2 * t + 1 ≤ 2 * t + 2))
    calc 2 ^ (2 * t + 2) = 4 * 4 ^ t := by rw [pow_add, pow_mul]; norm_num; ring
      _ ≤ t * 4 ^ t := Nat.mul_le_mul_right _ h
      _ ≤ _ := this
      _ ≤ _ := hd

theorem g71a_ordR_spec (r n : ℕ) (hr : 1 < r) (hc : Nat.Coprime n r) :
    0 < ordR r n ∧ n ^ ordR r n % r = 1 % r := by
  have hmem : Nat.totient r ∈ (List.range r).filter (fun k => decide (0 < k ∧ n ^ k % r = 1 % r)) := by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨Nat.totient_lt r hr, Nat.totient_pos.2 (by omega), Nat.ModEq.pow_totient hc⟩
  unfold ordR
  split
  next h => rw [h] at hmem; simp at hmem
  next k t h =>
    have : k ∈ (List.range r).filter (fun k => decide (0 < k ∧ n ^ k % r = 1 % r)) := by
      rw [h]; exact List.mem_cons_self
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at this
    exact this.2

theorem g71a_coprime_part (j n E : ℕ) (hj : 1 ≤ j) (hn : 1 ≤ n) (hjE : j < 2 ^ (E + 1)) :
    Nat.Coprime (j / Nat.gcd j (n ^ E)) n := by
  apply Nat.coprime_of_dvd
  intro p hp hpc hpn
  have hg : Nat.gcd j (n ^ E) ∣ j := Nat.gcd_dvd_left _ _
  have hc0 : j / Nat.gcd j (n ^ E) ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (by omega) hg) (Nat.gcd_pos_of_pos_left _ (by omega))
    omega
  have h1 := (hp.dvd_iff_one_le_factorization hc0).1 hpc
  have hnE : n ^ E ≠ 0 := by positivity
  rw [Nat.factorization_div hg, Nat.factorization_gcd (by omega) hnE] at h1
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.inf_apply, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul] at h1
  have hnp := (hp.dvd_iff_one_le_factorization (by omega)).1 hpn
  have h2 : E + 1 ≤ j.factorization p := by
    rcases le_total (j.factorization p) (E * n.factorization p) with h | h
    · rw [min_eq_left h] at h1; omega
    · rw [min_eq_right h] at h1
      have : E ≤ E * n.factorization p := Nat.le_mul_of_pos_right _ hnp
      omega
  have h3 : p ^ (E + 1) ∣ j := dvd_trans (pow_dvd_pow p h2) (Nat.ordProj_dvd j p)
  have h4 := Nat.le_of_dvd (by omega) h3
  have h5 : 2 ^ (E + 1) ≤ p ^ (E + 1) := Nat.pow_le_pow_left hp.two_le _
  omega

theorem solution (n : ℕ) (hn : 1 < n) :
    ∃ r, 1 < r ∧ r ≤ max 3 ((logUp n) ^ 5) ∧ (logUp n) ^ 2 < ordR r n := by
  set L := logUp n with hLdef
  have hnL : n < 2 ^ L := Nat.lt_log2_self
  have hL2 : 2 ≤ L := by
    have : 1 ≤ Nat.log2 n := by
      rw [Nat.log2_eq_log_two]; exact Nat.le_log_of_pow_le (by norm_num) (by omega)
    simp only [hLdef, logUp]; omega
  set B := L ^ 5 with hB
  have hB32 : 32 ≤ B := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ L ^ 5 := Nat.pow_le_pow_left hL2 5
  have hmax : max 3 B = B := by omega
  rw [hmax]
  by_contra hcon
  push Not at hcon
  set M := L ^ 2 with hM
  set E := Nat.log 2 B with hE
  set P := ∏ i ∈ Finset.range M, (n ^ (i + 1) - 1) with hP
  set Q := n ^ E * P with hQ
  have hPpos : 0 < P := Finset.prod_pos fun i _ => by
    have := Nat.one_lt_pow (by omega : i + 1 ≠ 0) hn; omega
  have hQpos : 0 < Q := Nat.mul_pos (by positivity) hPpos
  -- every j ≤ B divides Q
  have hdiv : lcmFirst B ∣ Q := by
    apply g71a_lcmFirst_dvd
    intro j hj1 hjB
    set a := Nat.gcd j (n ^ E)
    have hjeq : j = a * (j / a) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
    have hcop : Nat.Coprime (j / a) n :=
      g71a_coprime_part j n E hj1 (by omega)
        (lt_of_le_of_lt hjB (Nat.lt_pow_succ_log_self (by norm_num) B))
    have hc1 : j / a ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hjeq; omega
    have hcP : j / a ∣ P := by
      rcases Nat.lt_or_ge (j / a) 2 with h | h
      · have : j / a = 1 := by
          generalize j / a = c at h hc1
          omega
        rw [this]; exact one_dvd _
      · have hle : j / a ≤ B := le_trans (Nat.div_le_self _ _) hjB
        have hord := hcon (j / a) (by omega) hle
        obtain ⟨hk0, hk⟩ := g71a_ordR_spec (j / a) n (by omega) hcop.symm
        have hdk : j / a ∣ n ^ ordR (j / a) n - 1 :=
          (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 hk.symm
        refine dvd_trans hdk ?_
        have hmem : ordR (j / a) n - 1 ∈ Finset.range M := by
          simp only [Finset.mem_range]; omega
        have := Finset.dvd_prod_of_mem (fun i => n ^ (i + 1) - 1) hmem
        rwa [Nat.sub_add_cancel (by omega)] at this
    rw [hjeq]
    exact mul_dvd_mul (Nat.gcd_dvd_right _ _) hcP
  have hlow : 2 ^ B ≤ lcmFirst B := g71a_lcm_lower B (by omega)
  have hle : lcmFirst B ≤ Q := Nat.le_of_dvd hQpos hdiv
  -- upper bound on Q
  set s := E + ∑ i ∈ Finset.range M, (i + 1) with hs
  have hQs : Q ≤ n ^ s := by
    have : P ≤ ∏ i ∈ Finset.range M, n ^ (i + 1) :=
      Finset.prod_le_prod' fun i _ => Nat.sub_le _ _
    rw [Finset.prod_pow_eq_pow_sum] at this
    rw [hs, pow_add]
    exact Nat.mul_le_mul_left _ this
  have hsum : (∑ i ∈ Finset.range M, (i + 1)) * 2 = M * (M - 1) + 2 * M := by
    rw [Finset.sum_add_distrib, add_mul, Finset.sum_range_id_mul_two]; simp; ring
  have hM4 : 4 ≤ M := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ L ^ 2 := Nat.pow_le_pow_left hL2 2
  have hEb : 2 * E + M ≤ M * M := by
    have h2E : 2 ^ E ≤ B := Nat.pow_log_le_self 2 (by omega)
    rcases Nat.lt_or_ge L 3 with h | h
    · have hL : L = 2 := by omega
      have : E = 5 := by
        rw [hE]; apply Nat.log_eq_of_pow_le_of_lt_pow <;> rw [hB, hL] <;> norm_num
      rw [this, hM, hL]; norm_num
    · have h5 : E < 5 * L := by
        have : B < 2 ^ (5 * L) := by
          rw [hB, pow_mul']
          exact Nat.pow_lt_pow_left Nat.lt_two_pow_self (by norm_num)
        have := lt_of_le_of_lt h2E this
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
      rw [hM]
      have hL3 : 9 ≤ L * L := by nlinarith
      nlinarith
  have hsle : s ≤ M * M := by
    have : (M - 1) * M + M = M * M := by
      rcases M with _ | M
      · omega
      · simp; ring
    have h1 : s * 2 = 2 * E + M * (M - 1) + 2 * M := by rw [hs, add_mul, hsum]; ring
    have h2 : M * (M - 1) = (M - 1) * M := by ring
    omega
  have hspos : s ≠ 0 := by
    have : 0 < ∑ i ∈ Finset.range M, (i + 1) :=
      Finset.sum_pos (fun i _ => by omega) ⟨0, by simp; omega⟩
    omega
  have hup : n ^ s < 2 ^ B := by
    calc n ^ s < (2 ^ L) ^ s := Nat.pow_lt_pow_left hnL hspos
      _ = 2 ^ (L * s) := by rw [← pow_mul]
      _ ≤ 2 ^ B := by
        apply Nat.pow_le_pow_right (by norm_num)
        have : L * s ≤ L * (M * M) := Nat.mul_le_mul_left _ hsle
        calc L * s ≤ L * (M * M) := this
          _ = B := by rw [hB, hM]; ring
  omega
