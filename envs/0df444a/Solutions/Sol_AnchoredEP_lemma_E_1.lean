-- Prove2me | solution 1 for AnchoredEP.lemma_E_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-18T14:47:44.382074+00:00
-- url     : https://prove2.me/submissions/ae4d430f-e182-4765-89b0-57d8ccf096e8

import Mathlib

set_option maxHeartbeats 1200000

private lemma rpow_sub_rpow_ge {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≤ y)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r * (y ^ (r - 1) * (y - x)) ≤ y ^ r - x ^ r := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  have hxy' : 0 ≤ x / y := div_nonneg hx hy.le
  have hs : -1 ≤ x / y - 1 := by linarith
  have hb := rpow_one_add_le_one_add_mul_self (s := x / y - 1) hs hr0 hr1
  have hs1 : 1 + (x / y - 1) = x / y := by ring
  rw [hs1] at hb
  have hpos : 0 < y ^ r := Real.rpow_pos_of_pos hy r
  have hmul : x ^ r ≤ (1 + r * (x / y - 1)) * y ^ r := by
    have h1 : (x / y) ^ r * y ^ r = x ^ r := by
      rw [← Real.mul_rpow hxy' hy.le]
      congr 1
      field_simp
    calc x ^ r = (x / y) ^ r * y ^ r := h1.symm
      _ ≤ (1 + r * (x / y - 1)) * y ^ r := mul_le_mul_of_nonneg_right hb hpos.le
  have hyr : y ^ r = y ^ (r - 1) * y := by
    have h := Real.rpow_add hy (r - 1) 1
    rw [show r - 1 + 1 = r by ring, Real.rpow_one] at h
    exact h
  have hxr : (x / y) * y ^ r = x * y ^ (r - 1) := by
    rw [hyr]
    field_simp
  have hexp : (1 + r * (x / y - 1)) * y ^ r = y ^ r - r * (y ^ (r - 1) * (y - x)) := by
    have h3 : (1 + r * (x / y - 1)) * y ^ r = y ^ r + r * ((x / y) * y ^ r) - r * y ^ r := by
      ring
    rw [h3, hxr, hyr]
    ring
  rw [hexp] at hmul
  linarith

theorem solution (B : ℕ → ℝ) (hpos : ∀ k, 1 ≤ k → 0 < B k)
    (hmono : ∀ k, 1 ≤ k → B k ≤ B (k + 1)) (α c : ℝ) (hα : 1 < α) (hc : 0 < c)
    (hrec : ∀ k, 1 ≤ k → c * ∑ j ∈ Finset.Icc 1 k, B j ≤ B k ^ α) :
    ∀ k, 1 ≤ k → ((α - 1) / α * c * k) ^ (1 / (α - 1)) ≤ B k := by
  intro n hn
  have hα0 : 0 < α := by linarith
  have hαm : 0 < α - 1 := by linarith
  set r : ℝ := (α - 1) / α with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hr0' : 0 ≤ r := hr0.le
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one hα0]; linarith
  have hrα : r * α = α - 1 := by rw [hrdef]; field_simp
  set a : ℝ := c ^ (1 / α) with hadef
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  set T : ℕ → ℝ := fun k => ∑ j ∈ Finset.Icc 1 k, B j with hTdef
  have hT0 : T 0 = 0 := by simp [hTdef]
  have hTnonneg : ∀ m : ℕ, 0 ≤ T m := by
    intro m
    rw [hTdef]
    apply Finset.sum_nonneg
    intro j hj
    obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hj
    exact (hpos j h1).le
  have hTpos : ∀ k, 1 ≤ k → 0 < T k := by
    intro k hk
    have h1 : B k ≤ T k := by
      rw [hTdef]
      apply Finset.single_le_sum (f := B)
      · intro j hj
        obtain ⟨h1, -⟩ := Finset.mem_Icc.mp hj
        exact (hpos j h1).le
      · exact Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
    exact lt_of_lt_of_le (hpos k hk) h1
  have hTstep : ∀ k, 1 ≤ k → T k = T (k - 1) + B k := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h := Finset.sum_Icc_succ_top (a := 1) (b := m) (f := B) (by omega)
    simpa [hTdef] using h
  have hclemma : ∀ k, 1 ≤ k → (c * T k) ^ (1 / α) ≤ B k := by
    intro k hk
    have h1 : (c * T k) ^ (1 / α) ≤ (B k ^ α) ^ (1 / α) :=
      Real.rpow_le_rpow (mul_nonneg hc.le (hTpos k hk).le) (hrec k hk) (by positivity)
    have h2 : (B k ^ α) ^ (1 / α) = B k := by
      rw [← Real.rpow_mul (hpos k hk).le]
      have h3 : α * (1 / α) = 1 := by field_simp
      rw [h3, Real.rpow_one]
    rwa [h2] at h1
  have hmul_a : ∀ k, 1 ≤ k → T k ^ (r - 1) * (c * T k) ^ (1 / α) = a := by
    intro k hk
    have hTk : 0 < T k := hTpos k hk
    have h1 : (c * T k) ^ (1 / α) = a * T k ^ (1 / α) := by
      rw [Real.mul_rpow hc.le hTk.le, hadef]
    rw [h1]
    have h2 : T k ^ (r - 1) * T k ^ (1 / α) = T k ^ ((r - 1) + 1 / α) := by
      rw [← Real.rpow_add hTk]
    calc T k ^ (r - 1) * (a * T k ^ (1 / α))
        = a * (T k ^ (r - 1) * T k ^ (1 / α)) := by ring
      _ = a * T k ^ ((r - 1) + 1 / α) := by rw [h2]
      _ = a := by
          have hexp : r - 1 + 1 / α = 0 := by rw [hrdef]; field_simp; ring
          rw [hexp, Real.rpow_zero, mul_one]
  have hstep : ∀ k, 1 ≤ k → r * a ≤ T k ^ r - T (k - 1) ^ r := by
    intro k hk
    have hTk : 0 < T k := hTpos k hk
    have hTle : T (k - 1) ≤ T k := by
      have h := hTstep k hk
      have hB : 0 < B k := hpos k hk
      linarith
    have hBk : B k = T k - T (k - 1) := by
      have h := hTstep k hk
      linarith
    have h2 : T k ^ (r - 1) * (c * T k) ^ (1 / α) ≤ T k ^ (r - 1) * B k :=
      mul_le_mul_of_nonneg_left (hclemma k hk) (Real.rpow_pos_of_pos hTk (r - 1)).le
    have h3 : r * a ≤ r * (T k ^ (r - 1) * B k) := by
      have h4 := hmul_a k hk
      have hle : a ≤ T k ^ (r - 1) * B k := by linarith
      exact mul_le_mul_of_nonneg_left hle hr0'
    have h5 : r * (T k ^ (r - 1) * B k) ≤ T k ^ r - T (k - 1) ^ r := by
      have h6 := rpow_sub_rpow_ge (hTnonneg (k - 1)) hTk hTle hr0' hr1
      rwa [← hBk] at h6
    linarith
  have hind : ∀ k : ℕ, (k : ℝ) * (r * a) ≤ T k ^ r := by
    intro k
    induction k with
    | zero => simp [hT0, Real.zero_rpow (ne_of_gt hr0)]
    | succ k ih =>
      have h1 : r * a ≤ T (k + 1) ^ r - T k ^ r := hstep (k + 1) (by omega)
      have h2 : ((k + 1 : ℕ) : ℝ) * (r * a) = (k : ℝ) * (r * a) + r * a := by
        push_cast
        ring
      rw [h2]
      linarith
  have hna : 0 ≤ (n : ℝ) * (r * a) := mul_nonneg (Nat.cast_nonneg n) (mul_nonneg hr0' ha.le)
  have hTn : ((n : ℝ) * (r * a)) ^ (1 / r) ≤ T n := by
    have h1 : ((n : ℝ) * (r * a)) ^ (1 / r) ≤ (T n ^ r) ^ (1 / r) :=
      Real.rpow_le_rpow hna (hind n) (by positivity)
    have h2 : (T n ^ r) ^ (1 / r) = T n := by
      rw [← Real.rpow_mul (hTnonneg n)]
      have h3 : r * (1 / r) = 1 := by field_simp
      rw [h3, Real.rpow_one]
    rwa [h2] at h1
  have hTn' : ((n : ℝ) * (r * a)) ^ (1 / (r * α)) ≤ T n ^ (1 / α) := by
    have h1 : (((n : ℝ) * (r * a)) ^ (1 / r)) ^ (1 / α) ≤ T n ^ (1 / α) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hna _) hTn (by positivity)
    have h2 : (((n : ℝ) * (r * a)) ^ (1 / r)) ^ (1 / α) =
        ((n : ℝ) * (r * a)) ^ (1 / (r * α)) := by
      rw [← Real.rpow_mul hna]
      have hexp : 1 / r * (1 / α) = 1 / (r * α) := by field_simp
      rw [hexp]
    rwa [h2] at h1
  have hconst : a * ((n : ℝ) * (r * a)) ^ (1 / (r * α)) = (r * c * (n : ℝ)) ^ (1 / (α - 1)) := by
    have e1 : 1 / (r * α) = 1 / (α - 1) := by rw [hrα]
    have h1 : ((n : ℝ) * (r * a)) ^ (1 / (r * α)) =
        (n : ℝ) ^ (1 / (α - 1)) * r ^ (1 / (α - 1)) * a ^ (1 / (α - 1)) := by
      rw [e1]
      calc ((n : ℝ) * (r * a)) ^ (1 / (α - 1))
          = ((n : ℝ) * r * a) ^ (1 / (α - 1)) := by
            congr 1
            ring
        _ = ((n : ℝ) * r) ^ (1 / (α - 1)) * a ^ (1 / (α - 1)) :=
            Real.mul_rpow (by positivity) (le_of_lt ha)
        _ = ((n : ℝ) ^ (1 / (α - 1)) * r ^ (1 / (α - 1))) * a ^ (1 / (α - 1)) := by
            rw [Real.mul_rpow (Nat.cast_nonneg n) hr0']
        _ = (n : ℝ) ^ (1 / (α - 1)) * r ^ (1 / (α - 1)) * a ^ (1 / (α - 1)) := by ring
    have h2 : a ^ (1 / (α - 1)) = c ^ (1 / α * (1 / (α - 1))) := by
      rw [hadef, Real.rpow_mul hc.le]
    have hexp : 1 / α + 1 / α * (1 / (α - 1)) = 1 / (α - 1) := by
      field_simp
      ring
    have h6 : c ^ (1 / α) * c ^ (1 / α * (1 / (α - 1))) = c ^ (1 / (α - 1)) := by
      rw [← Real.rpow_add hc, hexp]
    calc a * ((n : ℝ) * (r * a)) ^ (1 / (r * α))
        = c ^ (1 / α) *
            ((n : ℝ) ^ (1 / (α - 1)) * r ^ (1 / (α - 1)) * a ^ (1 / (α - 1))) := by
          rw [hadef, h1]
      _ = c ^ (1 / α) * ((n : ℝ) ^ (1 / (α - 1)) * r ^ (1 / (α - 1)) *
            c ^ (1 / α * (1 / (α - 1)))) := by rw [h2]
      _ = (n : ℝ) ^ (1 / (α - 1)) * r ^ (1 / (α - 1)) *
            (c ^ (1 / α) * c ^ (1 / α * (1 / (α - 1)))) := by ring
      _ = (n : ℝ) ^ (1 / (α - 1)) * r ^ (1 / (α - 1)) * c ^ (1 / (α - 1)) := by rw [h6]
      _ = ((n : ℝ) * r * c) ^ (1 / (α - 1)) := by
          conv_rhs =>
            rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (n : ℝ) * r) hc.le,
              Real.mul_rpow (Nat.cast_nonneg n) hr0']
      _ = (r * c * (n : ℝ)) ^ (1 / (α - 1)) := by
          rw [show (n : ℝ) * r * c = r * c * (n : ℝ) by ring]
  calc ((α - 1) / α * c * (n : ℝ)) ^ (1 / (α - 1))
      = (r * c * (n : ℝ)) ^ (1 / (α - 1)) := by rw [hrdef]
    _ = a * ((n : ℝ) * (r * a)) ^ (1 / (r * α)) := hconst.symm
    _ ≤ a * T n ^ (1 / α) := mul_le_mul_of_nonneg_left hTn' ha.le
    _ = (c * T n) ^ (1 / α) := by
        rw [Real.mul_rpow hc.le (hTnonneg n), hadef]
    _ ≤ B n := hclemma n hn
