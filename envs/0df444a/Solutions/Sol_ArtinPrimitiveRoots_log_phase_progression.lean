-- Prove2me | solution 1 for ArtinPrimitiveRoots.log_phase_progression
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T15:19:36.117344+00:00
-- url     : https://prove2.me/submissions/6704ecd6-23b4-4808-b91c-a63bd718dc86

import Mathlib
import Definitions.Def_ArtinVinogradov
import Theorems.Thm_ArtinPrimitiveRoots_vinogradov_mean_value
import Theorems.Thm_ArtinPrimitiveRoots_weylSum_box_sup_moment

section
/-! # Shared tools for prover S (A106): Bonferroni truncation, residue counts, Abel summation -/

namespace ArtinPrimitiveRoots.A106S

open Real Finset

/-! ## Bonferroni truncation -/

/-! ## Residue classes in intervals -/

/-! ## Abel summation over tails -/

/-! ## Exponential sums over progressions -/

lemma norm_cpow_I_mul_sub (y t u : ℝ) (hy : 0 < y) (ht : 0 < t) :
    ‖(y : ℂ) ^ (Complex.I * u) - (t : ℂ) ^ (Complex.I * u)‖ ≤ |u| * |log y - log t| := by
  have ey : (y : ℂ) ^ (Complex.I * u) = Complex.exp (Complex.I * ((u * log y : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le]
    push_cast; ring_nf
  have et : (t : ℂ) ^ (Complex.I * u) = Complex.exp (Complex.I * ((u * log t : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne'), ← Complex.ofReal_log ht.le]
    push_cast; ring_nf
  rw [ey, et]
  have : Complex.exp (Complex.I * ((u * log y : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((u * log t : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((u * log t : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * ((u * log y - u * log t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; push_cast; ring_nf
  rw [this, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul]

/-- One step of the telescoping comparison: `F(t+k) - F(t) - k t^{iu}` is small, where
`F(y) = y^{1+iu}/(1+iu)`. -/
lemma step_bound (u t k : ℝ) (ht : 0 < t) (hk : 0 ≤ k) :
    ‖((t + k : ℝ) : ℂ) ^ (Complex.I * u + 1) / (Complex.I * u + 1) -
        (t : ℂ) ^ (Complex.I * u + 1) / (Complex.I * u + 1) -
        (k : ℂ) * (t : ℂ) ^ (Complex.I * u)‖ ≤ |u| * k / t * k := by
  set r : ℂ := Complex.I * u
  have hr : r ≠ -1 := by
    intro h
    have := congrArg Complex.re h
    simp [r] at this
  let G : ℝ → ℂ := fun y => (y : ℂ) ^ (r + 1) / (r + 1) - (y : ℂ) * (t : ℂ) ^ r
  have hG : ∀ y ∈ Set.Icc t (t + k), HasDerivWithinAt G ((y : ℂ) ^ r - (t : ℂ) ^ r)
      (Set.Icc t (t + k)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by linarith [hy.1]
    have h1 := hasDerivAt_ofReal_cpow_const' hy0 hr
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * (t : ℂ) ^ r) (1 * (t : ℂ) ^ r) y :=
      (hasDerivAt_id y).ofReal_comp.mul_const _
    rw [one_mul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hbd : ∀ y ∈ Set.Ico t (t + k), ‖(y : ℂ) ^ r - (t : ℂ) ^ r‖ ≤ |u| * k / t := by
    intro y hy
    have hy0 : 0 < y := by linarith [hy.1]
    refine (norm_cpow_I_mul_sub y t u hy0 ht).trans ?_
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg u)
    have hl : log t ≤ log y := log_le_log ht hy.1
    rw [abs_of_nonneg (by linarith)]
    have : log y - log t = log (y / t) := (log_div hy0.ne' ht.ne').symm
    rw [this]
    refine (log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one ht.ne']
    exact div_le_div_of_nonneg_right (by linarith [hy.2]) ht.le
  have := norm_image_sub_le_of_norm_deriv_le_segment' hG hbd (t + k) ⟨by linarith, le_refl _⟩
  simp only [G] at this
  rw [show t + k - t = k by ring] at this
  have e : ((t + k : ℝ) : ℂ) ^ (r + 1) / (r + 1) - (t : ℂ) ^ (r + 1) / (r + 1) -
      (k : ℂ) * (t : ℂ) ^ r = ((t + k : ℝ) : ℂ) ^ (r + 1) / (r + 1) - ((t + k : ℝ) : ℂ) * (t : ℂ) ^ r -
      ((t : ℂ) ^ (r + 1) / (r + 1) - (t : ℂ) * (t : ℂ) ^ r) := by
    push_cast; ring
  rw [e]; exact this

lemma norm_F_le (u y : ℝ) (hy : 0 < y) (hu : u ≠ 0) :
    ‖(y : ℂ) ^ (Complex.I * u + 1) / (Complex.I * u + 1)‖ ≤ y / |u| := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (Complex.I * u + 1).re = 1 := by simp
  rw [hre, rpow_one]
  have h1 : |u| ≤ ‖Complex.I * u + 1‖ := by
    have := Complex.abs_im_le_norm (Complex.I * u + 1)
    simpa using this
  exact div_le_div_of_nonneg_left hy.le (abs_pos.2 hu) h1

lemma ap_sum_telescope (u : ℝ) (hu : u ≠ 0) (t₀ k : ℝ) (ht₀ : 0 < t₀) (hk : 0 < k) (c : ℕ) :
    ‖∑ j ∈ range c, (((t₀ + k * j : ℝ)) : ℂ) ^ (Complex.I * u)‖ ≤
      ((t₀ + k * c) + t₀) / (k * |u|) + ∑ j ∈ range c, k * |u| / (t₀ + k * j) := by
  set r : ℂ := Complex.I * u
  let F : ℝ → ℂ := fun y => (y : ℂ) ^ (r + 1) / (r + 1)
  have hstep : ∀ j ∈ range c, ‖F (t₀ + k * (j + 1 : ℕ)) - F (t₀ + k * j) -
      (k : ℂ) * ((t₀ + k * j : ℝ) : ℂ) ^ r‖ ≤ |u| * k / (t₀ + k * j) * k := by
    intro j _
    have hpos : 0 < t₀ + k * j := by positivity
    have := step_bound u (t₀ + k * j) k hpos hk.le
    simp only [F]
    rw [show t₀ + k * ((j + 1 : ℕ) : ℝ) = t₀ + k * j + k by push_cast; ring]
    exact this
  have htel : ∑ j ∈ range c, (F (t₀ + k * (j + 1 : ℕ)) - F (t₀ + k * j)) =
      F (t₀ + k * c) - F (t₀ + k * (0 : ℕ)) :=
    Finset.sum_range_sub (fun j : ℕ => F (t₀ + k * j)) c
  have hsplit : (k : ℂ) * ∑ j ∈ range c, ((t₀ + k * j : ℝ) : ℂ) ^ r =
      (F (t₀ + k * c) - F (t₀ + k * (0 : ℕ))) -
        ∑ j ∈ range c, (F (t₀ + k * (j + 1 : ℕ)) - F (t₀ + k * j) -
          (k : ℂ) * ((t₀ + k * j : ℝ) : ℂ) ^ r) := by
    rw [← htel, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hnorm : k * ‖∑ j ∈ range c, ((t₀ + k * j : ℝ) : ℂ) ^ r‖ ≤
      (t₀ + k * c) / |u| + t₀ / |u| + ∑ j ∈ range c, |u| * k / (t₀ + k * j) * k := by
    have e : k * ‖∑ j ∈ range c, ((t₀ + k * j : ℝ) : ℂ) ^ r‖ =
        ‖(k : ℂ) * ∑ j ∈ range c, ((t₀ + k * j : ℝ) : ℂ) ^ r‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
    rw [e, hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
      ((norm_sum_le _ _).trans (Finset.sum_le_sum hstep)))
    · exact norm_F_le u _ (by positivity) hu
    · simp only [CharP.cast_eq_zero, mul_zero, add_zero]
      exact norm_F_le u _ ht₀ hu
  have hu' : 0 < |u| := abs_pos.2 hu
  rw [← le_div_iff₀' hk] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  rw [add_div, add_div, Finset.sum_div, div_div, div_div, add_div]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    have : 0 < t₀ + k * j := by positivity
    field_simp

/-- A finset of naturals in one residue class mod `q`, closed under betweenness within the
class, is an arithmetic progression. -/
lemma ap_structure (T : Finset ℕ) (hT : T.Nonempty) (q : ℕ) (_hq : 0 < q)
    (hmod : ∀ n ∈ T, ∀ n' ∈ T, n ≡ n' [MOD q])
    (hconv : ∀ n ∈ T, ∀ n' ∈ T, ∀ m : ℕ, n ≤ m → m ≤ n' → m ≡ n [MOD q] → m ∈ T) :
    T = (range ((T.max' hT - T.min' hT) / q + 1)).image (fun j => T.min' hT + q * j) := by
  set n₀ := T.min' hT
  set n₁ := T.max' hT
  have h0 : n₀ ∈ T := T.min'_mem hT
  have h1 : n₁ ∈ T := T.max'_mem hT
  ext n
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · intro hn
    have hle : n₀ ≤ n := T.min'_le n hn
    have hle1 : n ≤ n₁ := T.le_max' n hn
    have hdvd : q ∣ n - n₀ := (Nat.modEq_iff_dvd' hle).1 (hmod n₀ h0 n hn)
    refine ⟨(n - n₀) / q, ?_, ?_⟩
    · have : (n - n₀) / q ≤ (n₁ - n₀) / q := Nat.div_le_div_right (by omega)
      omega
    · rw [Nat.mul_div_cancel' hdvd]; omega
  · rintro ⟨j, hj, rfl⟩
    have hj' : j ≤ (n₁ - n₀) / q := by omega
    have hqj : q * j ≤ n₁ - n₀ := by
      calc q * j ≤ q * ((n₁ - n₀) / q) := Nat.mul_le_mul_left q hj'
        _ ≤ n₁ - n₀ := Nat.mul_div_le (n₁ - n₀) q
    have hn₀₁ : n₀ ≤ n₁ := T.min'_le n₁ h1
    refine hconv n₀ h0 n₁ h1 (n₀ + q * j) (by omega) (by omega) ?_
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]

open Classical in
/-- The exponential sum over a progression in an interval, by telescoping (the
"comparison with the integral of `y^{iu}`"). -/
lemma prog_sum_bound (u : ℝ) (hu : u ≠ 0) (q : ℕ) (hq : 0 < q) (N : ℝ) (hqN : (q : ℝ) ≤ N)
    (J : Set ℝ) (hJ : J.OrdConnected) (hJN : J ⊆ Set.Icc N (2 * N)) (a : ℕ) :
    ‖∑ n ∈ (range (⌊2 * N⌋₊ + 1)).filter (fun n => n ≡ a [MOD q]),
        (if (n : ℝ) ∈ J then (n : ℂ) ^ (Complex.I * u) else 0)‖ ≤
      5 * N / (q * |u|) + 2 * |u| := by
  classical
  have hu' : 0 < |u| := abs_pos.2 hu
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hN : 0 < N := lt_of_lt_of_le hq' hqN
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
  set T := (range (⌊2 * N⌋₊ + 1)).filter (fun n => n ≡ a [MOD q] ∧ (n : ℝ) ∈ J)
  have hRHS : 0 ≤ 5 * N / (q * |u|) + 2 * |u| := by positivity
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT, Finset.sum_empty, norm_zero]; exact hRHS
  have hmemT : ∀ n ∈ T, n ≡ a [MOD q] ∧ (n : ℝ) ∈ J := fun n hn => (Finset.mem_filter.1 hn).2
  have hstr := ap_structure T hT q hq
    (fun n hn n' hn' => ((hmemT n hn).1).trans (hmemT n' hn').1.symm)
    (fun n hn n' hn' m h1 h2 h3 => by
      simp only [T, Finset.mem_filter, Finset.mem_range] at hn hn' ⊢
      refine ⟨by omega, h3.trans hn.2.1, hJ.out hn.2.2 hn'.2.2 ⟨?_, ?_⟩⟩
      · exact_mod_cast h1
      · exact_mod_cast h2)
  set n₀ := T.min' hT
  set n₁ := T.max' hT
  set c := (n₁ - n₀) / q + 1
  have hn₀J := (hmemT n₀ (T.min'_mem hT)).2
  have hn₁J := (hmemT n₁ (T.max'_mem hT)).2
  have hn₀N : N ≤ (n₀ : ℝ) := (hJN hn₀J).1
  have hn₁N : (n₁ : ℝ) ≤ 2 * N := (hJN hn₁J).2
  have hn₀₁ : n₀ ≤ n₁ := T.min'_le n₁ (T.max'_mem hT)
  rw [hstr, Finset.sum_image (fun j _ j' _ h => by
    have := Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel h); exact this)]
  have hcast : ∀ j ∈ range c, (((n₀ + q * j : ℕ) : ℂ)) ^ (Complex.I * u) =
      (((n₀ + q * j : ℝ)) : ℂ) ^ (Complex.I * u) := by
    intro j _; push_cast; rfl
  rw [Finset.sum_congr rfl hcast]
  refine (ap_sum_telescope u hu n₀ q (by linarith) hq' c).trans ?_
  -- bounds on the progression
  have hqc : (q : ℝ) * c ≤ N + q := by
    have h1 : q * ((n₁ - n₀) / q) ≤ n₁ - n₀ := Nat.mul_div_le (n₁ - n₀) q
    have h2 : ((n₁ - n₀ : ℕ) : ℝ) ≤ N := by
      rw [Nat.cast_sub hn₀₁]; linarith
    have h3 : ((q * ((n₁ - n₀) / q) : ℕ) : ℝ) ≤ ((n₁ - n₀ : ℕ) : ℝ) := by exact_mod_cast h1
    simp only [c]; push_cast at h3 ⊢; nlinarith
  have hfirst : ((n₀ : ℝ) + q * c + n₀) / (q * |u|) ≤ 5 * N / (q * |u|) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (q : ℝ) * c ≤ n₁ - n₀ + q := by
      have h1 : q * ((n₁ - n₀) / q) ≤ n₁ - n₀ := Nat.mul_div_le (n₁ - n₀) q
      have h3 : ((q * ((n₁ - n₀) / q) : ℕ) : ℝ) ≤ ((n₁ - n₀ : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_sub hn₀₁] at h3
      simp only [c]; push_cast at h3 ⊢; nlinarith
    have : (n₀ : ℝ) ≤ n₁ := by exact_mod_cast hn₀₁
    nlinarith
  have hsecond : ∑ j ∈ range c, (q : ℝ) * |u| / (n₀ + q * j) ≤ 2 * |u| := by
    calc ∑ j ∈ range c, (q : ℝ) * |u| / (n₀ + q * j) ≤ ∑ j ∈ range c, (q : ℝ) * |u| / N := by
          refine Finset.sum_le_sum fun j _ => ?_
          apply div_le_div_of_nonneg_left (by positivity) hN
          have : (0 : ℝ) ≤ q * j := by positivity
          linarith
      _ = (q * c) * |u| / N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ (N + N) * |u| / N := by
          apply div_le_div_of_nonneg_right _ hN.le
          exact mul_le_mul_of_nonneg_right (by linarith) hu'.le
      _ = 2 * |u| := by field_simp; ring
  linarith

/-! ## Brun's pure sieve and character sums -/

/-! ## Dilated intervals -/

end ArtinPrimitiveRoots.A106S
end

section
/-!
# Tools for `log_phase_progression` (prover L33A)

* `average_shift`: averaging a unimodular sum over forward shifts `1 ≤ h ≤ M` costs `2M`.
* `weyl_taylor`: Taylor expansion of `v log (X + h)` to degree `k` turns the shifted sum into the
  Weyl sum `weylSum M k (coef v X k)`, up to `M · 2|v| (M/X)^(k+1)`.
* `weylSum_fract`: the Weyl sum is `1`-periodic in each coefficient.
* `box_count`: the points `fract (coef v (w₀ + j) k)` lie at most `B` to a box (one coordinate
  is monotone in `j` with derivative bounded below).
* `sum_pow_le_boxes`: summing `|S|^{2s}` over the points, box by box.
-/

namespace ArtinPrimitiveRoots.L33A

open Real Finset

/-! ## Averaging over shifts -/

lemma norm_sum_range_le_card (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (h : ℕ) :
    ‖∑ j ∈ range h, g j‖ ≤ h := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ range h, ‖g j‖ ≤ ∑ j ∈ range h, (1 : ℝ) := sum_le_sum fun j _ => hg j
    _ = h := by simp

lemma shift_sum (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (c h : ℕ) :
    ‖∑ j ∈ range c, g j - ∑ j ∈ range c, g (j + h)‖ ≤ 2 * h := by
  have e1 := Finset.sum_range_add g h c
  have e2 := Finset.sum_range_add g c h
  rw [add_comm h c] at e1
  have e3 : ∑ j ∈ range c, g (j + h) = ∑ j ∈ range c, g (h + j) :=
    sum_congr rfl fun j _ => by rw [add_comm]
  have : ∑ j ∈ range c, g j - ∑ j ∈ range c, g (j + h) =
      ∑ j ∈ range h, g j - ∑ j ∈ range h, g (c + j) := by
    rw [e3]; linear_combination e1 - e2
  rw [this]
  calc _ ≤ ‖∑ j ∈ range h, g j‖ + ‖∑ j ∈ range h, g (c + j)‖ := norm_sub_le _ _
    _ ≤ h + h := add_le_add (norm_sum_range_le_card g hg h)
        (norm_sum_range_le_card (fun j => g (c + j)) (fun j => hg _) h)
    _ = 2 * h := by ring

lemma average_shift (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (c M : ℕ) (hM : 1 ≤ M) :
    ‖∑ j ∈ range c, g j‖ ≤
      (∑ j ∈ range c, ‖∑ h ∈ Icc 1 M, g (j + h)‖) / M + 2 * M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have key : (M : ℂ) * ∑ j ∈ range c, g j = ∑ j ∈ range c, ∑ h ∈ Icc 1 M, g (j + h) +
      ∑ h ∈ Icc 1 M, (∑ j ∈ range c, g j - ∑ j ∈ range c, g (j + h)) := by
    rw [sum_sub_distrib, sum_const, Nat.card_Icc, Finset.sum_comm (s := range c), nsmul_eq_mul]
    simp only [Nat.add_sub_cancel]
    ring
  have h1 : (M : ℝ) * ‖∑ j ∈ range c, g j‖ ≤
      ∑ j ∈ range c, ‖∑ h ∈ Icc 1 M, g (j + h)‖ + 2 * M * M := by
    have := congrArg norm key
    rw [norm_mul, Complex.norm_natCast] at this
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) ?_)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ h ∈ Icc 1 M, ‖∑ j ∈ range c, g j - ∑ j ∈ range c, g (j + h)‖
        ≤ ∑ h ∈ Icc 1 M, (2 * M : ℝ) := sum_le_sum fun h hh => (shift_sum g hg c h).trans (by
          have h2 : (h : ℝ) ≤ M := by exact_mod_cast (mem_Icc.1 hh).2
          linarith)
      _ = 2 * M * M := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  rw [div_add' _ _ _ hM'.ne', le_div_iff₀ hM']
  linarith

/-! ## Taylor expansion of the logarithmic phase -/

/-- `coef v X k i`: the coefficient of `h^(i+1)` in the Taylor expansion of `(v/2π) log (X + h)`
about `h = 0`. -/
noncomputable def coef (v X : ℝ) (k : ℕ) (i : Fin k) : ℝ :=
  (-1) ^ (i.val) * v / (2 * π * ((i.val : ℝ) + 1) * X ^ (i.val + 1))

lemma norm_exp_two_pi_I (t : ℝ) : ‖Complex.exp (2 * π * Complex.I * (t : ℂ))‖ = 1 := by
  rw [show 2 * (π : ℂ) * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma taylor_step (v X h : ℝ) (k : ℕ) (hX : 0 < X) (hh0 : 0 ≤ h) (hh : 2 * h ≤ X) :
    ‖Complex.exp (Complex.I * ((v * log (X + h) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * ((v * log X : ℝ) : ℂ)) *
        Complex.exp (2 * π * Complex.I *
          ((∑ i : Fin k, coef v X k i * h ^ (i.val + 1) : ℝ) : ℂ))‖ ≤
      2 * |v| * (h / X) ^ (k + 1) := by
  set t := h / X with ht
  have ht0 : 0 ≤ t := div_nonneg hh0 hX.le
  have ht1 : t ≤ 1 / 2 := by rw [ht, div_le_iff₀ hX]; linarith
  have habs : |-t| < 1 := by rw [abs_neg, abs_of_nonneg ht0]; linarith
  have hlog := Real.abs_log_sub_add_sum_range_le habs k
  rw [sub_neg_eq_add, abs_neg, abs_of_nonneg ht0] at hlog
  set R := ∑ i ∈ range k, (-t) ^ (i + 1) / (i + 1) + log (1 + t) with hR
  have hR' : |R| ≤ 2 * t ^ (k + 1) := by
    refine hlog.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg ht0 (k + 1)]
  have hXh : log (X + h) = log X + log (1 + t) := by
    rw [← log_mul hX.ne' (by linarith)]
    congr 1; rw [ht]; field_simp
  have hpoly : 2 * π * ∑ i : Fin k, coef v X k i * h ^ (i.val + 1) =
      - v * ∑ i ∈ range k, (-t) ^ (i + 1) / (i + 1) := by
    simp only [coef]
    rw [Fin.sum_univ_eq_sum_range
      (fun i : ℕ => (-1) ^ i * v / (2 * π * ((i : ℝ) + 1) * X ^ (i + 1)) * h ^ (i + 1)) k]
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [ht, neg_pow (h / X) (i + 1), div_pow, pow_succ (-1 : ℝ) i]
    field_simp
  have hphase : v * log (X + h) =
      v * log X + 2 * π * (∑ i : Fin k, coef v X k i * h ^ (i.val + 1)) + v * R := by
    rw [hpoly, hXh, hR]; ring
  have e1 : Complex.exp (Complex.I * ((v * log (X + h) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((v * log X : ℝ) : ℂ)) *
        Complex.exp (2 * π * Complex.I *
          ((∑ i : Fin k, coef v X k i * h ^ (i.val + 1) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((v * R : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hphase]
    congr 1; push_cast; ring
  rw [e1, show ∀ a b c : ℂ, a * b * c - a * b = a * b * (c - 1) from fun a b c => by ring,
    norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, norm_exp_two_pi_I, one_mul, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc |v| * |R| ≤ |v| * (2 * t ^ (k + 1)) := mul_le_mul_of_nonneg_left hR' (abs_nonneg v)
    _ = 2 * |v| * t ^ (k + 1) := by ring

lemma weyl_taylor (v X : ℝ) (k M : ℕ) (hX : 0 < X) (hM : 2 * (M : ℝ) ≤ X) :
    ‖∑ h ∈ Icc 1 M, Complex.exp (Complex.I * ((v * log (X + h) : ℝ) : ℂ))‖ ≤
      ‖weylSum M k (coef v X k)‖ + M * (2 * |v| * (M / X) ^ (k + 1)) := by
  have e : ∑ h ∈ Icc 1 M, Complex.exp (Complex.I * ((v * log (X + h) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((v * log X : ℝ) : ℂ)) * weylSum M k (coef v X k) +
      ∑ h ∈ Icc 1 M, (Complex.exp (Complex.I * ((v * log (X + h) : ℝ) : ℂ)) -
        Complex.exp (Complex.I * ((v * log X : ℝ) : ℂ)) *
        Complex.exp (2 * π * Complex.I *
          ((∑ i : Fin k, coef v X k i * (h : ℝ) ^ (i.val + 1) : ℝ) : ℂ))) := by
    rw [weylSum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun h _ => by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  · refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ h ∈ Icc 1 M, 2 * |v| * ((M : ℝ) / X) ^ (k + 1) := by
          refine sum_le_sum fun h hh => ?_
          have hhM : (h : ℝ) ≤ M := by exact_mod_cast (mem_Icc.1 hh).2
          refine (taylor_step v X h k hX (by positivity) (by linarith)).trans ?_
          gcongr
      _ = M * (2 * |v| * (M / X) ^ (k + 1)) := by
          simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

/-! ## Periodicity and the size of a Weyl sum -/

lemma weylSum_fract (M k : ℕ) (α : Fin k → ℝ) :
    weylSum M k (fun i => Int.fract (α i)) = weylSum M k α := by
  unfold weylSum
  refine sum_congr rfl fun h _ => ?_
  have hs : (∑ j : Fin k, Int.fract (α j) * (h : ℝ) ^ (j.val + 1)) =
      (∑ j : Fin k, α j * (h : ℝ) ^ (j.val + 1)) -
        ((∑ j : Fin k, ⌊α j⌋ * (h : ℤ) ^ (j.val + 1) : ℤ) : ℝ) := by
    push_cast
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← Int.self_sub_floor]; ring
  rw [hs]
  set n : ℤ := ∑ j : Fin k, ⌊α j⌋ * (h : ℤ) ^ (j.val + 1)
  rw [Complex.ofReal_sub, mul_sub, Complex.exp_sub]
  have : Complex.exp (2 * π * Complex.I * ((n : ℝ) : ℂ)) = 1 := by
    rw [show 2 * (π : ℂ) * Complex.I * ((n : ℝ) : ℂ) = n * (2 * π * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [this, div_one]

lemma norm_weylSum_le (M k : ℕ) (α : Fin k → ℝ) : ‖weylSum M k α‖ ≤ M := by
  unfold weylSum
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ h ∈ Icc 1 M, (1 : ℝ) := sum_le_sum fun h _ => (norm_exp_two_pi_I _).le
    _ = M := by simp

/-! ## Counting points in a box -/

lemma card_le_of_sep (S : Finset ℕ) (g : ℕ → ℝ) (δ u w : ℝ) (hδ : 0 < δ) (hw : 0 ≤ w)
    (hsep : ∀ j ∈ S, ∀ j' ∈ S, j ≤ j' → δ * ((j' : ℝ) - j) ≤ |g j' - g j|)
    (hrange : ∀ j ∈ S, u ≤ g j ∧ g j ≤ u + w) : (S.card : ℝ) ≤ w / δ + 1 := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp only [card_empty, CharP.cast_eq_zero]; positivity
  set a := S.min' hS
  set b := S.max' hS
  have ha := S.min'_mem hS
  have hb := S.max'_mem hS
  have hab : a ≤ b := S.min'_le b hb
  have hsub : S ⊆ Icc a b := fun j hj => mem_Icc.2 ⟨S.min'_le j hj, S.le_max' j hj⟩
  have hc : (S.card : ℝ) ≤ (b : ℝ) - a + 1 := by
    have h1 := card_le_card hsub
    rw [Nat.card_Icc] at h1
    have h2 : ((S.card : ℕ) : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_sub (by omega)] at h2; push_cast at h2; linarith
  have h1 := hsep a ha b hb hab
  have h2 : |g b - g a| ≤ w := by
    have := hrange a ha; have := hrange b hb
    rw [abs_le]; constructor <;> linarith
  have h3 : (b : ℝ) - a ≤ w / δ := by rw [le_div_iff₀ hδ]; linarith
  linarith

lemma inv_pow_sep (X X' U : ℝ) (p : ℕ) (hX : 0 < X) (hXX' : X ≤ X') (hX'U : X' ≤ U) :
    (p : ℝ) * (X' - X) / U ^ (p + 1) ≤ 1 / X ^ p - 1 / X' ^ p := by
  have hX' : 0 < X' := lt_of_lt_of_le hX hXX'
  have hd : 0 ≤ X' - X := sub_nonneg.2 hXX'
  have hbern : (1 + p * ((X' - X) / X)) * X ^ p ≤ X' ^ p := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ (X' - X) / X by
      have := div_nonneg hd hX.le; linarith) p
    have e : (1 + (X' - X) / X) = X' / X := by field_simp; ring
    rw [e, div_pow, le_div_iff₀ (pow_pos hX p)] at h
    exact h
  have hb2 : (p : ℝ) * (X' - X) * X ^ p ≤ (X' ^ p - X ^ p) * X := by
    have h := mul_le_mul_of_nonneg_right hbern hX.le
    have e : (1 + p * ((X' - X) / X)) * X ^ p * X = X ^ p * X + p * (X' - X) * X ^ p := by
      field_simp
    rw [e] at h; linarith
  have step1 : (p : ℝ) * (X' - X) / (X * X' ^ p) ≤ 1 / X ^ p - 1 / X' ^ p := by
    rw [div_sub_div _ _ (pow_pos hX p).ne' (pow_pos hX' p).ne', one_mul, mul_one,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hb2 (pow_nonneg hX'.le p)
    nlinarith
  have step2 : (p : ℝ) * (X' - X) / U ^ (p + 1) ≤ (p : ℝ) * (X' - X) / (X * X' ^ p) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    rw [pow_succ']
    exact mul_le_mul (by linarith) (pow_le_pow_left₀ hX'.le hX'U p) (by positivity) (by linarith)
  linarith

lemma coef_sep (v X X' U : ℝ) (k : ℕ) (i : Fin k) (hX : 0 < X) (hXX' : X ≤ X')
    (hX'U : X' ≤ U) :
    |v| * (X' - X) / (2 * π * U ^ (i.val + 2)) ≤ |coef v X' k i - coef v X k i| := by
  have hX' : 0 < X' := lt_of_lt_of_le hX hXX'
  have hi : (0 : ℝ) < (i.val : ℝ) + 1 := by positivity
  have hrep : coef v X' k i - coef v X k i = -((-1) ^ i.val * v / (2 * π * ((i.val : ℝ) + 1)) *
      (1 / X ^ (i.val + 1) - 1 / X' ^ (i.val + 1))) := by
    unfold coef; field_simp; ring
  have hs := inv_pow_sep X X' U (i.val + 1) hX hXX' hX'U
  have hnn : 0 ≤ 1 / X ^ (i.val + 1) - 1 / X' ^ (i.val + 1) :=
    le_trans (div_nonneg (mul_nonneg (by positivity) (by linarith))
      (pow_nonneg (by linarith) _)) hs
  rw [hrep, abs_neg, abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : 0 < 2 * π * ((i.val : ℝ) + 1)), abs_of_nonneg hnn]
  calc |v| * (X' - X) / (2 * π * U ^ (i.val + 2))
      = |v| / (2 * π * ((i.val : ℝ) + 1)) *
          (((i.val + 1 : ℕ) : ℝ) * (X' - X) / U ^ (i.val + 1 + 1)) := by
        push_cast; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

open Classical in
lemma box_count (v H w₀ : ℝ) (k M c : ℕ) (i : Fin k) (hH : 0 < H) (hM : 1 ≤ M) (hv0 : v ≠ 0)
    (hv : |v| ≤ H ^ (i.val + 1))
    (hX : ∀ j ∈ range c, H ≤ w₀ + j ∧ w₀ + j ≤ 2 * H) (m₀ : ℕ) :
    ((((range c).filter (fun j : ℕ =>
        ⌊Int.fract (coef v (w₀ + j) k i) * (M : ℝ) ^ (i.val + 1)⌋₊ = m₀)).card : ℕ) : ℝ) ≤
      2 * (2 * π * (2 * H) ^ (i.val + 2) / (|v| * (M : ℝ) ^ (i.val + 1)) + 1) := by
  set S := (range c).filter
    (fun j : ℕ => ⌊Int.fract (coef v (w₀ + j) k i) * (M : ℝ) ^ (i.val + 1)⌋₊ = m₀)
  set g : ℕ → ℝ := fun j => coef v (w₀ + j) k i
  set δ := |v| / (2 * π * (2 * H) ^ (i.val + 2))
  set Mp := (M : ℝ) ^ (i.val + 1)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hMp : 0 < Mp := by positivity
  have hv' : 0 < |v| := abs_pos.2 hv0
  have hδ : 0 < δ := by positivity
  have hg1 : ∀ j ∈ range c, |g j| < 1 := by
    intro j hj
    have hXj := hX j hj
    have hXp : H ^ (i.val + 1) ≤ (w₀ + j) ^ (i.val + 1) := pow_le_pow_left₀ hH.le hXj.1 _
    have hpos : 0 < (w₀ + j) ^ (i.val + 1) := pow_pos (by linarith [hXj.1]) _
    simp only [g, coef]
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (by positivity : 0 < 2 * π * ((i.val : ℝ) + 1) * (w₀ + j) ^ (i.val + 1)),
      div_lt_one (by positivity)]
    have h2 : (2 : ℝ) ≤ 2 * π * ((i.val : ℝ) + 1) := by
      have : (1 : ℝ) ≤ (i.val : ℝ) + 1 := by linarith [(Nat.cast_nonneg i.val : (0 : ℝ) ≤ i.val)]
      nlinarith [Real.pi_gt_three]
    have := mul_le_mul_of_nonneg_right h2 hpos.le
    linarith
  have hsep : ∀ j ∈ range c, ∀ j' ∈ range c, j ≤ j' → δ * ((j' : ℝ) - j) ≤ |g j' - g j| := by
    intro j hj j' hj' hjj'
    have hjj'r : (j : ℝ) ≤ j' := by exact_mod_cast hjj'
    have := coef_sep v (w₀ + j) (w₀ + j') (2 * H) k i (by linarith [(hX j hj).1])
      (by linarith) (hX j' hj').2
    refine le_trans (le_of_eq ?_) this
    simp only [δ]; ring
  have hfr : ∀ j ∈ S, (m₀ : ℝ) / Mp ≤ Int.fract (g j) ∧ Int.fract (g j) ≤ m₀ / Mp + 1 / Mp := by
    intro j hj
    have h := (mem_filter.1 hj).2
    have h0 : 0 ≤ Int.fract (g j) * Mp := mul_nonneg (Int.fract_nonneg _) hMp.le
    rw [Nat.floor_eq_iff h0] at h
    constructor
    · rw [div_le_iff₀ hMp]; exact h.1
    · rw [← add_div, le_div_iff₀ hMp]; exact h.2.le
  have hSc : S ⊆ range c := filter_subset _ _
  have hc1 : ((S.filter (fun j => 0 ≤ g j)).card : ℝ) ≤ (1 / Mp) / δ + 1 := by
    apply card_le_of_sep _ g δ (m₀ / Mp) (1 / Mp) hδ (by positivity)
    · intro j hj j' hj' hjj'
      exact hsep j (hSc (mem_filter.1 hj).1) j' (hSc (mem_filter.1 hj').1) hjj'
    · intro j hj
      have hjS := (mem_filter.1 hj).1
      have hfrac : Int.fract (g j) = g j :=
        Int.fract_eq_self.2 ⟨(mem_filter.1 hj).2, (abs_lt.1 (hg1 j (hSc hjS))).2⟩
      rw [← hfrac]; exact hfr j hjS
  have hc2 : ((S.filter (fun j => ¬ 0 ≤ g j)).card : ℝ) ≤ (1 / Mp) / δ + 1 := by
    apply card_le_of_sep _ (fun j => g j + 1) δ (m₀ / Mp) (1 / Mp) hδ (by positivity)
    · intro j hj j' hj' hjj'
      simp only [add_sub_add_right_eq_sub]
      exact hsep j (hSc (mem_filter.1 hj).1) j' (hSc (mem_filter.1 hj').1) hjj'
    · intro j hj
      have hjS := (mem_filter.1 hj).1
      have hneg : g j < 0 := lt_of_not_ge (mem_filter.1 hj).2
      have hgt : -1 < g j := (abs_lt.1 (hg1 j (hSc hjS))).1
      have hfrac : Int.fract (g j) = g j + 1 := by
        rw [Int.fract, Int.floor_eq_iff.2 (show (((-1 : ℤ)) : ℝ) ≤ g j ∧ g j < ((-1 : ℤ) : ℝ) + 1 by
          push_cast; constructor <;> linarith)]
        push_cast; ring
      rw [← hfrac]; exact hfr j hjS
  have hcard : (S.card : ℝ) ≤ ((S.filter (fun j => 0 ≤ g j)).card : ℝ) +
      ((S.filter (fun j => ¬ 0 ≤ g j)).card : ℝ) := by
    exact_mod_cast (card_filter_add_card_filter_not (s := S) (fun j => 0 ≤ g j)).ge
  calc (S.card : ℝ) ≤ 2 * ((1 / Mp) / δ + 1) := by linarith
    _ = 2 * (2 * π * (2 * H) ^ (i.val + 2) / (|v| * (M : ℝ) ^ (i.val + 1)) + 1) := by
        simp only [δ, Mp]; field_simp

/-! ## Summing over boxes -/

open Classical in
lemma sum_pow_le_boxes (s k M c : ℕ) (hM : 1 ≤ M) (β : ℕ → Fin k → ℝ)
    (hβ : ∀ j ∈ range c, ∀ i, 0 ≤ β j i ∧ β j i < 1) (B : ℝ)
    (hB : ∀ m : Fin k → ℕ, ((#{j ∈ range c | (fun i : Fin k => ⌊β j i * (M : ℝ) ^ (i.val + 1)⌋₊) = m}
        : ℕ) : ℝ) ≤ B) :
    ∑ j ∈ range c, ‖weylSum M k (β j)‖ ^ (2 * s) ≤
      B * ∑ m ∈ Fintype.piFinset (fun j : Fin k => Finset.range (M ^ (j.val + 1))),
          (⨆ α : {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧
              α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)},
            ‖weylSum M k α.1‖ ^ (2 * s)) := by
  set idx : ℕ → (Fin k → ℕ) := fun j i => ⌊β j i * (M : ℝ) ^ (i.val + 1)⌋₊ with hidx
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hmaps : ∀ j ∈ range c,
      idx j ∈ Fintype.piFinset (fun j : Fin k => Finset.range (M ^ (j.val + 1))) := by
    intro j hj
    rw [Fintype.mem_piFinset]; intro i
    rw [mem_range]
    have h0 : 0 ≤ β j i * (M : ℝ) ^ (i.val + 1) := mul_nonneg (hβ j hj i).1 (by positivity)
    simp only [idx]
    rw [Nat.floor_lt h0]; push_cast
    have := (hβ j hj i).2
    have hp : (0 : ℝ) < (M : ℝ) ^ (i.val + 1) := by positivity
    nlinarith
  rw [← sum_fiberwise_of_maps_to hmaps, mul_sum]
  refine sum_le_sum fun m _ => ?_
  have hbdd : BddAbove (Set.range fun α : {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1)
      ≤ α j ∧ α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)} => ‖weylSum M k α.1‖ ^ (2 * s)) := by
    refine ⟨(M : ℝ) ^ (2 * s), ?_⟩
    rintro _ ⟨α, rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_weylSum_le M k α.1) _
  have hle : ∀ j ∈ (range c).filter (fun j => idx j = m),
      ‖weylSum M k (β j)‖ ^ (2 * s) ≤ ⨆ α : {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1)
        ≤ α j ∧ α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)}, ‖weylSum M k α.1‖ ^ (2 * s) := by
    intro j hj
    have hjc := (mem_filter.1 hj).1
    have hjm := (mem_filter.1 hj).2
    refine le_ciSup hbdd ⟨β j, fun i => ?_⟩
    have hi := congrFun hjm i
    simp only [idx] at hi
    have h0 : 0 ≤ β j i * (M : ℝ) ^ (i.val + 1) := mul_nonneg (hβ j hjc i).1 (by positivity)
    rw [Nat.floor_eq_iff h0] at hi
    have hp : (0 : ℝ) < (M : ℝ) ^ (i.val + 1) := by positivity
    constructor
    · rw [div_le_iff₀ hp]; exact hi.1
    · rw [lt_div_iff₀ hp]; exact hi.2
  have hsup0 : 0 ≤ ⨆ α : {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1)
        ≤ α j ∧ α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)}, ‖weylSum M k α.1‖ ^ (2 * s) :=
    Real.iSup_nonneg fun α => by positivity
  calc _ ≤ ∑ j ∈ (range c).filter (fun j => idx j = m), ⨆ α : {α : Fin k → ℝ // ∀ j,
          (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧ α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)},
          ‖weylSum M k α.1‖ ^ (2 * s) := sum_le_sum hle
    _ = ((#{j ∈ range c | idx j = m} : ℕ) : ℝ) * ⨆ α : {α : Fin k → ℝ // ∀ j,
          (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧ α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)},
          ‖weylSum M k α.1‖ ^ (2 * s) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hB m) hsup0

end ArtinPrimitiveRoots.L33A
end

section
/-!
# The large-frequency case of `log_phase_progression` (prover L33A)

`main_case`: with `H = e^ℓ`, `|v| ≥ H^{4/5}`, `k ≥ 4y + 8` (`y = log|v|/ℓ`), `M = ⌊H^{3/4}⌋`, a
coordinate `i` with `i ≤ y ≤ i + 1`, and the two mean-value inputs (Vinogradov's bound with
constant `E₁`, the box-supremum moment with constant `E₂`) as hypotheses, the sum
`Σ_{j<c} e^{iv log(w₀+j)}` over `H ≤ w₀ + j ≤ 2H` is at most `3 H e^{-ε}` whenever
`2s + 2(i+1) + 6 + log E₁ + log E₂ + 2sε ≤ 137ℓ/400`.
-/

namespace ArtinPrimitiveRoots.L33A

open Real Finset

lemma exp_neg_le_one_div (x : ℝ) (hx : 0 ≤ x) : exp (-x) ≤ 1 / (1 + x) := by
  rw [exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by linarith) (by linarith [add_one_le_exp x])

lemma two_pow_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ exp n := by
  calc (2 : ℝ) ^ n ≤ (exp 1) ^ n :=
        pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp 1]) n
    _ = exp n := by rw [← exp_nat_mul, mul_one]

/-- The number of points per box, in exponential form. -/
lemma B_bound (v ℓ : ℝ) (i M : ℕ) (hℓ : 0 ≤ ℓ) (hv0 : v ≠ 0) (hM1 : 1 ≤ M)
    (hM : exp (3 / 4 * ℓ) / 2 ≤ M) (hlam : 4 / 5 * ℓ ≤ log |v|) (hiv : (i : ℝ) * ℓ ≤ log |v|) :
    2 * (2 * π * (2 * exp ℓ) ^ (i + 2) / (|v| * (M : ℝ) ^ (i + 1)) + 1) ≤
      exp (2 * ((i : ℝ) + 1) + 5 + 13 / 20 * ℓ) := by
  have hv : 0 < |v| := abs_pos.2 hv0
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hQpos : 0 < 2 * π * (2 * exp ℓ) ^ (i + 2) / (|v| * (M : ℝ) ^ (i + 1)) := by positivity
  have hlogM : 3 / 4 * ℓ - log 2 ≤ log M := by
    have := Real.log_le_log (by positivity) hM
    rw [Real.log_div (by positivity) (by norm_num), Real.log_exp] at this
    exact this
  have hlogQ : log (2 * π * (2 * exp ℓ) ^ (i + 2) / (|v| * (M : ℝ) ^ (i + 1))) =
      log (2 * π) + ((i : ℝ) + 2) * (log 2 + ℓ) - (log |v| + ((i : ℝ) + 1) * log M) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_mul (x := 2) (y := exp ℓ) (by norm_num) (by positivity), Real.log_exp,
      Real.log_mul (x := |v|) (y := (M : ℝ) ^ (i + 1)) (by positivity) (by positivity),
      Real.log_pow]
    push_cast; ring
  have hl2 : log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
  have hlpi : log (2 * π) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 := Real.exp_one_gt_d9
    have h2 : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith [Real.pi_lt_d2]
  have hQle : 2 * π * (2 * exp ℓ) ^ (i + 2) / (|v| * (M : ℝ) ^ (i + 1)) ≤
      exp (2 * ((i : ℝ) + 1) + 3 + 13 / 20 * ℓ) := by
    rw [← Real.log_le_iff_le_exp hQpos, hlogQ]
    have h1 : ((i : ℝ) + 1) * (3 / 4 * ℓ - log 2) ≤ ((i : ℝ) + 1) * log M :=
      mul_le_mul_of_nonneg_left hlogM (by positivity)
    have h2 : ((i : ℝ) + 2) * log 2 ≤ ((i : ℝ) + 2) * 0.7 :=
      mul_le_mul_of_nonneg_left hl2.le (by positivity)
    have h3 : ((i : ℝ) + 1) * log 2 ≤ ((i : ℝ) + 1) * 0.7 :=
      mul_le_mul_of_nonneg_left hl2.le (by positivity)
    nlinarith
  have he2 : (4 : ℝ) ≤ exp 2 := by
    have h1 := Real.exp_one_gt_d9
    have h2 : exp 2 = exp 1 * exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h2]; nlinarith
  have hpos : 1 ≤ exp (2 * ((i : ℝ) + 1) + 3 + 13 / 20 * ℓ) := one_le_exp (by positivity)
  calc 2 * (2 * π * (2 * exp ℓ) ^ (i + 2) / (|v| * (M : ℝ) ^ (i + 1)) + 1)
      ≤ 4 * exp (2 * ((i : ℝ) + 1) + 3 + 13 / 20 * ℓ) := by linarith
    _ ≤ exp 2 * exp (2 * ((i : ℝ) + 1) + 3 + 13 / 20 * ℓ) :=
        mul_le_mul_of_nonneg_right he2 (exp_pos _).le
    _ = exp (2 * ((i : ℝ) + 1) + 5 + 13 / 20 * ℓ) := by rw [← exp_add]; ring_nf

theorem main_case (v ℓ w₀ ε E₁ E₂ : ℝ) (c k i s M : ℕ)
    (hℓ : 20 ≤ ℓ) (hv0 : v ≠ 0) (hlam : 4 / 5 * ℓ ≤ log |v|)
    (hk : 4 * log |v| + 8 * ℓ ≤ k * ℓ) (hik : i < k) (hiv : log |v| ≤ ((i : ℝ) + 1) * ℓ)
    (hiv' : (i : ℝ) * ℓ ≤ log |v|)
    (hMdef : M = ⌊exp (3 / 4 * ℓ)⌋₊)
    (hX : ∀ j ∈ range c, exp ℓ ≤ w₀ + j ∧ w₀ + j ≤ 2 * exp ℓ) (hc : (c : ℝ) ≤ exp ℓ + 1)
    (hs : 1 ≤ s) (hE₁ : 1 ≤ E₁) (hE₂ : 1 ≤ E₂) (hε : 0 ≤ ε)
    (hJ : (vinogradovCount s k M : ℝ) ≤
      E₁ * (M : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) / 2 : ℕ) : ℝ) + 1 / 100))
    (hbox : ∑ m ∈ Fintype.piFinset (fun j : Fin k => Finset.range (M ^ (j.val + 1))),
          (⨆ α : {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧
              α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)},
            ‖weylSum M k α.1‖ ^ (2 * s)) ≤
        E₂ * (M : ℝ) ^ (k * (k + 1) / 2) * (vinogradovCount s k M : ℝ))
    (hbudget : 2 * (s : ℝ) + 2 * ((i : ℝ) + 1) + 6 + log E₁ + log E₂ + 2 * s * ε ≤
      137 / 400 * ℓ) :
    ‖∑ j ∈ range c, Complex.exp (Complex.I * ((v * log (w₀ + j) : ℝ) : ℂ))‖ ≤
      3 * exp ℓ * exp (-ε) := by
  have hH0 : 0 < exp ℓ := exp_pos ℓ
  have hH1 : 1 ≤ exp ℓ := one_le_exp (by linarith)
  have hMr2 : 2 ≤ exp (3 / 4 * ℓ) := by have := Real.add_one_le_exp (3 / 4 * ℓ); linarith
  have hMle : (M : ℝ) ≤ exp (3 / 4 * ℓ) := by rw [hMdef]; exact Nat.floor_le (exp_pos _).le
  have hMge : exp (3 / 4 * ℓ) / 2 ≤ M := by
    have := Nat.lt_floor_add_one (exp (3 / 4 * ℓ))
    rw [hMdef]; linarith
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have h2Mr : 2 * exp (3 / 4 * ℓ) ≤ exp ℓ := by
    have : 2 ≤ exp (1 / 4 * ℓ) := by have := Real.add_one_le_exp (1 / 4 * ℓ); linarith
    calc 2 * exp (3 / 4 * ℓ) ≤ exp (1 / 4 * ℓ) * exp (3 / 4 * ℓ) :=
          mul_le_mul_of_nonneg_right this (exp_pos _).le
      _ = exp ℓ := by rw [← exp_add]; ring_nf
  have hlE₁ : 0 ≤ log E₁ := Real.log_nonneg hE₁
  have hlE₂ : 0 ≤ log E₂ := Real.log_nonneg hE₂
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsε : ε ≤ s * ε := by have := mul_le_mul_of_nonneg_right hs' hε; linarith
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hεℓ : ε ≤ 137 / 800 * ℓ := by linarith
  -- Step 1: averaging over shifts.
  have hg1 : ∀ n : ℕ, ‖Complex.exp (Complex.I * ((v * log (w₀ + n) : ℝ) : ℂ))‖ ≤ 1 :=
    fun n => (Complex.norm_exp_I_mul_ofReal _).le
  have hstep1 := average_shift (fun n : ℕ => Complex.exp (Complex.I * ((v * log (w₀ + n) : ℝ) : ℂ)))
    hg1 c M hM1
  -- Step 2: Taylor expansion.
  have hstep2 : ∀ j ∈ range c,
      ‖∑ h ∈ Icc 1 M, Complex.exp (Complex.I * ((v * log (w₀ + ((j + h : ℕ) : ℝ)) : ℝ) : ℂ))‖ ≤
        ‖weylSum M k (coef v (w₀ + j) k)‖ + M * (2 * |v| * ((M : ℝ) / exp ℓ) ^ (k + 1)) := by
    intro j hj
    have hXj := hX j hj
    have hXpos : 0 < w₀ + j := by linarith
    simp only [Nat.cast_add, ← add_assoc]
    refine (weyl_taylor v (w₀ + j) k M hXpos (by linarith)).trans ?_
    gcongr
    exact hXj.1
  set A := ∑ j ∈ range c, ‖weylSum M k (coef v (w₀ + j) k)‖ with hA
  set Err := 2 * |v| * ((M : ℝ) / exp ℓ) ^ (k + 1) with hErr
  have hsum2 : ∑ j ∈ range c,
      ‖∑ h ∈ Icc 1 M, Complex.exp (Complex.I * ((v * log (w₀ + ((j + h : ℕ) : ℝ)) : ℝ) : ℂ))‖ ≤
        A + c * (M * Err) := by
    calc _ ≤ ∑ j ∈ range c, (‖weylSum M k (coef v (w₀ + j) k)‖ + M * Err) := sum_le_sum hstep2
      _ = _ := by rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have hmain1 : ‖∑ j ∈ range c, Complex.exp (Complex.I * ((v * log (w₀ + j) : ℝ) : ℂ))‖ ≤
      A / M + c * Err + 2 * M := by
    refine hstep1.trans ?_
    have h1 := div_le_div_of_nonneg_right hsum2 hM0.le
    have e : (A + c * (M * Err)) / M = A / M + c * Err := by field_simp
    linarith
  -- Step 3: the Taylor error.
  have hMH : (M : ℝ) / exp ℓ ≤ exp (-(1 / 4) * ℓ) := by
    rw [div_le_iff₀ hH0, ← exp_add]
    refine hMle.trans (le_of_eq ?_); ring_nf
  have hvexp : |v| = exp (log |v|) := (exp_log (abs_pos.2 hv0)).symm
  have hErrle : Err ≤ 2 * exp (-(9 / 4) * ℓ) := by
    calc Err ≤ 2 * exp (log |v|) * exp (((k + 1 : ℕ) : ℝ) * (-(1 / 4) * ℓ)) := by
          rw [hErr, ← hvexp, exp_nat_mul]
          gcongr
      _ = 2 * exp (log |v| + ((k + 1 : ℕ) : ℝ) * (-(1 / 4) * ℓ)) := by rw [exp_add]; ring
      _ ≤ 2 * exp (-(9 / 4) * ℓ) := by
          gcongr; push_cast; nlinarith
  have hcErr : c * Err ≤ 1 := by
    have hErr0 : 0 ≤ Err := by positivity
    have h54 := exp_neg_le_one_div (5 / 4 * ℓ) (by linarith)
    have h54' : 1 / (1 + 5 / 4 * ℓ) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    calc (c : ℝ) * Err ≤ (2 * exp ℓ) * (2 * exp (-(9 / 4) * ℓ)) :=
          mul_le_mul (by linarith) hErrle hErr0 (by positivity)
      _ = 4 * exp (-(5 / 4 * ℓ)) := by rw [mul_mul_mul_comm, ← exp_add]; ring_nf
      _ ≤ 1 := by linarith
  -- Step 4: Hölder, boxes and the mean value theorem.
  have hvH : |v| ≤ exp ℓ ^ (i + 1) := by
    rw [hvexp, ← exp_nat_mul]
    exact exp_le_exp.2 (by push_cast; linarith)
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 2 * (2 * π * (2 * exp ℓ) ^ (i + 2) /
      (|v| * (M : ℝ) ^ (i + 1)) + 1) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hBle : B ≤ exp (2 * ((i : ℝ) + 1) + 5 + 13 / 20 * ℓ) := by
    rw [hBdef]; exact B_bound v ℓ i M (by linarith) hv0 hM1 hMge hlam hiv'
  have hβ : ∀ j ∈ range c, ∀ i', 0 ≤ Int.fract (coef v (w₀ + j) k i') ∧
      Int.fract (coef v (w₀ + j) k i') < 1 :=
    fun j _ i' => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hBbox : ∀ m : Fin k → ℕ, ((((range c).filter (fun j : ℕ => (fun i' : Fin k =>
      ⌊Int.fract (coef v (w₀ + j) k i') * (M : ℝ) ^ (i'.val + 1)⌋₊) = m)).card : ℕ) : ℝ) ≤ B := by
    intro m
    have hsub : (range c).filter (fun j : ℕ => (fun i' : Fin k =>
        ⌊Int.fract (coef v (w₀ + j) k i') * (M : ℝ) ^ (i'.val + 1)⌋₊) = m) ⊆
        (range c).filter (fun j : ℕ =>
          ⌊Int.fract (coef v (w₀ + j) k ⟨i, hik⟩) * (M : ℝ) ^ (i + 1)⌋₊ = m ⟨i, hik⟩) := by
      intro j hj
      rw [mem_filter] at hj ⊢
      exact ⟨hj.1, congrFun hj.2 ⟨i, hik⟩⟩
    refine le_trans (Nat.cast_le.2 (card_le_card hsub)) ?_
    rw [hBdef]
    exact box_count v (exp ℓ) w₀ k M c ⟨i, hik⟩ hH0 hM1 hv0 hvH hX (m ⟨i, hik⟩)
  have hsumpow : ∑ j ∈ range c, ‖weylSum M k (coef v (w₀ + j) k)‖ ^ (2 * s) ≤
      B * (E₂ * (M : ℝ) ^ (k * (k + 1) / 2) * (vinogradovCount s k M : ℝ)) := by
    have h := sum_pow_le_boxes s k M c hM1 (fun j i' => Int.fract (coef v (w₀ + j) k i')) hβ B
      hBbox
    simp only [weylSum_fract] at h
    exact h.trans (mul_le_mul_of_nonneg_left hbox hB0)
  have hJ' : E₂ * (M : ℝ) ^ (k * (k + 1) / 2) * (vinogradovCount s k M : ℝ) ≤
      E₁ * E₂ * ((M : ℝ) ^ (2 * s) * (M : ℝ) ^ ((1 : ℝ) / 100)) := by
    have e : (M : ℝ) ^ (k * (k + 1) / 2) *
        (M : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) / 2 : ℕ) : ℝ) + 1 / 100) =
        (M : ℝ) ^ (2 * s) * (M : ℝ) ^ ((1 : ℝ) / 100) := by
      rw [← Real.rpow_natCast (M : ℝ) (k * (k + 1) / 2), ← Real.rpow_add hM0,
        ← Real.rpow_natCast (M : ℝ) (2 * s), ← Real.rpow_add hM0]
      congr 1; push_cast; ring
    calc E₂ * (M : ℝ) ^ (k * (k + 1) / 2) * (vinogradovCount s k M : ℝ)
        ≤ E₂ * (M : ℝ) ^ (k * (k + 1) / 2) *
          (E₁ * (M : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) / 2 : ℕ) : ℝ) + 1 / 100)) :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = E₁ * E₂ * ((M : ℝ) ^ (k * (k + 1) / 2) *
          (M : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) / 2 : ℕ) : ℝ) + 1 / 100)) := by ring
      _ = _ := by rw [e]
  have hHol : A ^ (2 * s) ≤ (c : ℝ) ^ (2 * s - 1) *
      ∑ j ∈ range c, ‖weylSum M k (coef v (w₀ + j) k)‖ ^ (2 * s) := by
    have h := pow_sum_le_card_mul_sum_pow (s := range c)
      (f := fun j => ‖weylSum M k (coef v (w₀ + j) k)‖) (fun j _ => norm_nonneg _) (2 * s - 1)
    rw [card_range, show 2 * s - 1 + 1 = 2 * s by omega] at h
    exact h
  have hkey : (2 : ℝ) ^ (2 * s - 1) * B * E₁ * E₂ * (M : ℝ) ^ ((1 : ℝ) / 100) ≤
      exp ℓ * exp (-(2 * s * ε)) := by
    have h2 : (2 : ℝ) ^ (2 * s - 1) ≤ exp (2 * s) := by
      refine (two_pow_le_exp _).trans (exp_le_exp.2 ?_)
      have : ((2 * s - 1 : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := Nat.cast_le.2 (Nat.sub_le _ _)
      push_cast at this; linarith
    have hE₁' : E₁ = exp (log E₁) := (exp_log (by linarith)).symm
    have hE₂' : E₂ = exp (log E₂) := (exp_log (by linarith)).symm
    have hMp : (M : ℝ) ^ ((1 : ℝ) / 100) ≤ exp (3 / 400 * ℓ) := by
      calc (M : ℝ) ^ ((1 : ℝ) / 100) ≤ (exp (3 / 4 * ℓ)) ^ ((1 : ℝ) / 100) :=
            Real.rpow_le_rpow hM0.le hMle (by norm_num)
        _ = exp (3 / 400 * ℓ) := by rw [← Real.exp_mul]; ring_nf
    calc (2 : ℝ) ^ (2 * s - 1) * B * E₁ * E₂ * (M : ℝ) ^ ((1 : ℝ) / 100)
        ≤ exp (2 * s) * exp (2 * ((i : ℝ) + 1) + 5 + 13 / 20 * ℓ) * exp (log E₁) *
            exp (log E₂) * exp (3 / 400 * ℓ) := by
          rw [← hE₁', ← hE₂']
          gcongr
      _ = exp (2 * s + (2 * ((i : ℝ) + 1) + 5 + 13 / 20 * ℓ) + log E₁ + log E₂ +
            3 / 400 * ℓ) := by simp only [exp_add]
      _ ≤ exp (ℓ + -(2 * s * ε)) := exp_le_exp.2 (by linarith)
      _ = exp ℓ * exp (-(2 * s * ε)) := exp_add _ _
  have hA : A ≤ M * exp ℓ * exp (-ε) := by
    have hA0 : 0 ≤ A := sum_nonneg fun j _ => norm_nonneg _
    have hc2 : (c : ℝ) ^ (2 * s - 1) ≤ (2 * exp ℓ) ^ (2 * s - 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg c) (by linarith) _
    have hpow : A ^ (2 * s) ≤ (M * exp ℓ * exp (-ε)) ^ (2 * s) := by
      calc A ^ (2 * s) ≤ (c : ℝ) ^ (2 * s - 1) *
            (B * (E₁ * E₂ * ((M : ℝ) ^ (2 * s) * (M : ℝ) ^ ((1 : ℝ) / 100)))) :=
            hHol.trans (mul_le_mul_of_nonneg_left (hsumpow.trans
              (mul_le_mul_of_nonneg_left hJ' hB0)) (by positivity))
        _ ≤ (2 * exp ℓ) ^ (2 * s - 1) *
            (B * (E₁ * E₂ * ((M : ℝ) ^ (2 * s) * (M : ℝ) ^ ((1 : ℝ) / 100)))) :=
            mul_le_mul_of_nonneg_right hc2 (by positivity)
        _ = exp ℓ ^ (2 * s - 1) * (M : ℝ) ^ (2 * s) *
            ((2 : ℝ) ^ (2 * s - 1) * B * E₁ * E₂ * (M : ℝ) ^ ((1 : ℝ) / 100)) := by
            rw [mul_pow]; ring
        _ ≤ exp ℓ ^ (2 * s - 1) * (M : ℝ) ^ (2 * s) * (exp ℓ * exp (-(2 * s * ε))) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = (M * exp ℓ * exp (-ε)) ^ (2 * s) := by
            rw [mul_pow, mul_pow, ← exp_nat_mul (-ε) (2 * s)]
            have e2 : exp ℓ ^ (2 * s) = exp ℓ ^ (2 * s - 1) * exp ℓ := by
              rw [← pow_succ]; congr 1; omega
            rw [e2]; push_cast; ring_nf
    exact le_of_pow_le_pow_left₀ (by omega) (by positivity) hpow
  have hAM : A / M ≤ exp ℓ * exp (-ε) := by
    rw [div_le_iff₀ hM0]; linarith
  -- Step 5: assemble.
  have hHe1 : 1 ≤ exp ℓ * exp (-ε) := by
    rw [← exp_add]; exact one_le_exp (by linarith)
  have hHe2 : 2 * (M : ℝ) ≤ exp ℓ * exp (-ε) := by
    have h1 : 2 ≤ exp (1 / 4 * ℓ - ε) := by
      have := Real.add_one_le_exp (1 / 4 * ℓ - ε); linarith
    calc 2 * (M : ℝ) ≤ exp (1 / 4 * ℓ - ε) * exp (3 / 4 * ℓ) :=
          mul_le_mul h1 hMle hM0.le (exp_pos _).le
      _ = exp ℓ * exp (-ε) := by rw [← exp_add, ← exp_add]; ring_nf
  linarith

end ArtinPrimitiveRoots.L33A
end

section
/-!
# Reduction of the progression sum, and an asymptotic helper (prover L33A)

* `reduce`: the sum `Σ_{n ≤ 2N, n ≡ a (q), n ∈ J} n^{iv}` has the norm of
  `Σ_{j<c} e^{iv log(w₀ + j)}` with `N/q ≤ w₀ + j ≤ 2N/q` and `c ≤ N/q + 1`
  (write `n = q (n₀/q + j)` along the progression given by `A106S.ap_structure`).
* `ev_pow_le_exp`: `a T^n ≤ e^T` for all large `T`.
-/

namespace ArtinPrimitiveRoots.L33A

open Real Finset

lemma natCast_cpow_I_mul' (n : ℕ) (u : ℝ) (hn : 0 < n) :
    (n : ℂ) ^ (Complex.I * u) = Complex.exp (Complex.I * ((u * Real.log n : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]
  push_cast; ring_nf

open Classical in
lemma reduce (v N : ℝ) (q : ℕ) (hq : 0 < q) (hN : 0 < N) (J : Set ℝ) (hJ : J.OrdConnected)
    (hJN : J ⊆ Set.Icc N (2 * N)) (a : ℕ) :
    ∃ c : ℕ, ∃ w₀ : ℝ, (c : ℝ) ≤ N / q + 1 ∧
      (∀ j ∈ range c, N / q ≤ w₀ + j ∧ w₀ + j ≤ 2 * (N / q)) ∧
      ‖∑ n ∈ (range (⌊2 * N⌋₊ + 1)).filter (fun n => n ≡ a [MOD q]),
          (if (n : ℝ) ∈ J then (n : ℂ) ^ (Complex.I * v) else 0)‖ =
        ‖∑ j ∈ range c, Complex.exp (Complex.I * ((v * log (w₀ + j) : ℝ) : ℂ))‖ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
  set T := (range (⌊2 * N⌋₊ + 1)).filter (fun n => n ≡ a [MOD q] ∧ (n : ℝ) ∈ J)
  rcases T.eq_empty_or_nonempty with hT | hT
  · refine ⟨0, 0, by simp only [CharP.cast_eq_zero]; positivity, by simp, ?_⟩
    rw [hT]; simp
  have hmemT : ∀ n ∈ T, n ≡ a [MOD q] ∧ (n : ℝ) ∈ J := fun n hn => (Finset.mem_filter.1 hn).2
  have hstr := A106S.ap_structure T hT q hq
    (fun n hn n' hn' => ((hmemT n hn).1).trans (hmemT n' hn').1.symm)
    (fun n hn n' hn' m h1 h2 h3 => by
      simp only [T, Finset.mem_filter, Finset.mem_range] at hn hn' ⊢
      refine ⟨by omega, h3.trans hn.2.1, hJ.out hn.2.2 hn'.2.2 ⟨?_, ?_⟩⟩
      · exact_mod_cast h1
      · exact_mod_cast h2)
  set n₀ := T.min' hT
  set n₁ := T.max' hT
  have hn₀J := (hmemT n₀ (T.min'_mem hT)).2
  have hn₁J := (hmemT n₁ (T.max'_mem hT)).2
  have hn₀N : N ≤ (n₀ : ℝ) := (hJN hn₀J).1
  have hn₁N : (n₁ : ℝ) ≤ 2 * N := (hJN hn₁J).2
  have hn₀₁ : n₀ ≤ n₁ := T.min'_le n₁ (T.max'_mem hT)
  have hn₀pos : (0 : ℝ) < n₀ := lt_of_lt_of_le hN hn₀N
  refine ⟨(n₁ - n₀) / q + 1, n₀ / q, ?_, ?_, ?_⟩
  · have h1 : ((n₁ - n₀) / q : ℕ) * q ≤ n₁ - n₀ := Nat.div_mul_le_self _ _
    have h2 : (((n₁ - n₀) / q : ℕ) : ℝ) * q ≤ (n₁ : ℝ) - n₀ := by
      have := (Nat.cast_le (α := ℝ)).2 h1
      rw [Nat.cast_mul, Nat.cast_sub hn₀₁] at this; exact this
    rw [Nat.cast_add, Nat.cast_one]
    have : (((n₁ - n₀) / q : ℕ) : ℝ) ≤ N / q := by rw [le_div_iff₀ hq']; linarith
    linarith
  · intro j hj
    have hj' : j ≤ (n₁ - n₀) / q := by rw [mem_range] at hj; omega
    have h1 : j * q ≤ n₁ - n₀ := (Nat.mul_le_mul_right q hj').trans (Nat.div_mul_le_self _ _)
    have h2 : (j : ℝ) * q ≤ (n₁ : ℝ) - n₀ := by
      have := (Nat.cast_le (α := ℝ)).2 h1
      rw [Nat.cast_mul, Nat.cast_sub hn₀₁] at this; exact this
    have e : (n₀ : ℝ) / q + j = (n₀ + j * q) / q := by field_simp
    rw [e]
    constructor
    · rw [div_le_div_iff_of_pos_right hq']
      have : (0 : ℝ) ≤ j * q := by positivity
      linarith
    · rw [mul_div_assoc', div_le_div_iff_of_pos_right hq']; linarith
  · rw [hstr, Finset.sum_image (fun j _ j' _ h => by
      have := Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel h); exact this)]
    have hterm : ∀ j ∈ range ((n₁ - n₀) / q + 1), ((n₀ + q * j : ℕ) : ℂ) ^ (Complex.I * v) =
        Complex.exp (Complex.I * ((v * log q : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((v * log ((n₀ : ℝ) / q + j) : ℝ) : ℂ)) := by
      intro j _
      have hpos : 0 < n₀ + q * j := by
        have : 0 < n₀ := by exact_mod_cast hn₀pos
        omega
      rw [natCast_cpow_I_mul' _ _ hpos, ← Complex.exp_add]
      congr 1
      have hw : (0 : ℝ) < (n₀ : ℝ) / q + j := by
        have := div_pos hn₀pos hq'
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      have e : ((n₀ + q * j : ℕ) : ℝ) = q * ((n₀ : ℝ) / q + j) := by push_cast; field_simp
      rw [e, Real.log_mul hq'.ne' hw.ne']
      push_cast; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, norm_mul, Complex.norm_exp_I_mul_ofReal,
      one_mul]

lemma ev_pow_le_exp (a : ℝ) (n : ℕ) : ∀ᶠ T in Filter.atTop, a * T ^ n ≤ exp T := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hpos : (0 : ℝ) < 1 / (|a| + 1) := by positivity
  filter_upwards [h.eventually (gt_mem_nhds hpos), Filter.eventually_ge_atTop (0 : ℝ)]
    with T hT hT0
  have hTn : 0 ≤ T ^ n := pow_nonneg hT0 n
  have h1 : (|a| + 1) * (T ^ n * exp (-T)) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hT; linarith
  have hexp : exp (-T) * exp T = 1 := by rw [← exp_add]; simp
  calc a * T ^ n ≤ (|a| + 1) * T ^ n :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self a]) hTn
    _ = (|a| + 1) * (T ^ n * exp (-T)) * exp T := by
        linear_combination (-(|a| + 1) * T ^ n) * hexp
    _ ≤ 1 * exp T := mul_le_mul_of_nonneg_right h1 (exp_pos _).le
    _ = exp T := one_mul _

end ArtinPrimitiveRoots.L33A
end

section
/-!
# `log_phase_progression` ([22] Lemma 3.3) from `vinogradov_mean_value` and
`weylSum_box_sup_moment`

`C₃ = 11`, `K = 8`. With `L = log x`, `T = log L`, `H = N/q = e^ℓ`, `ε = L/T^11`:
* `|v| < H^{4/5}`: `A106S.prog_sum_bound` gives `5H/|v| + 2|v| ≤ 7 H e^{-ε}`;
* `|v| ≥ H^{4/5}`: `L33A.reduce` and `L33A.main_case` give `3 H e^{-ε}`, with
  `k = ⌈4y + 8⌉`, `i = ⌊y⌋` (`y = log|v|/ℓ`), `M = ⌊H^{3/4}⌋`, `k ≤ 41T²`, `s ≤ C₁k⁴`.
-/

namespace ArtinPrimitiveRoots.L33A

open Real Finset

/-- The exponent budget of `main_case`, from `k ≤ 41T²`, `s ≤ C₁k⁴` and the conditions on `T`. -/
lemma budget (C₁ C₂ Cb P T ℓ ε : ℝ) (k i s n₂ : ℕ) (hC₁ : 0 < C₁) (hn₂ : C₂ ≤ n₂)
    (hP : P = 3 * C₁ + 8 + |Cb| * C₁ + |Cb|) (G1 : 2 ≤ T)
    (G4 : 12 * P * 41 ^ (n₂ + 5) * T ^ (2 * n₂ + 12) ≤ exp T) (G5 : 24 * C₁ * 41 ^ 4 ≤ T)
    (hℓ : exp T / (2 * T ^ 2) ≤ ℓ) (hε : ε = exp T / T ^ 11)
    (hk1 : (1 : ℝ) ≤ k) (hku : (k : ℝ) ≤ 41 * T ^ 2) (hik : i < k)
    (hsC : (s : ℝ) ≤ C₁ * (k : ℝ) ^ 4) :
    2 * (s : ℝ) + 2 * ((i : ℝ) + 1) + 6 + log (exp (C₁ * (k : ℝ) ^ C₂)) +
        log (exp (|Cb| * ((s : ℝ) * k + k))) + 2 * s * ε ≤ 137 / 400 * ℓ := by
  rw [Real.log_exp, Real.log_exp]
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 41 * T ^ 2 := ⟨_, rfl⟩
  rw [← hu] at hku
  have hT0 : 0 < T := by linarith
  have hu1 : 1 ≤ u := by rw [hu]; nlinarith
  have hsu : (s : ℝ) ≤ C₁ * u ^ 4 :=
    hsC.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hku 4) hC₁.le)
  have hkC₂ : (k : ℝ) ^ C₂ ≤ u ^ n₂ := by
    refine (Real.rpow_le_rpow_of_exponent_le hk1 hn₂).trans ?_
    rw [Real.rpow_natCast]; exact pow_le_pow_left₀ (by positivity) hku _
  have hsk : (s : ℝ) * k ≤ C₁ * u ^ 4 * u :=
    mul_le_mul hsu hku (by positivity) (by positivity)
  have hik' : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
  have hU : ∀ j ≤ n₂ + 5, u ^ j ≤ u ^ (n₂ + 5) := fun j hj => pow_le_pow_right₀ hu1 hj
  have a4 := hU 4 (by omega)
  have a5 := hU 5 (by omega)
  have a1 : u ≤ u ^ (n₂ + 5) := by simpa using hU 1 (by omega)
  have a0 : 1 ≤ u ^ (n₂ + 5) := one_le_pow₀ hu1
  have an := hU n₂ (by omega)
  have hCb0 : 0 ≤ |Cb| := abs_nonneg Cb
  have b1 : C₁ * u ^ 4 ≤ C₁ * u ^ (n₂ + 5) := mul_le_mul_of_nonneg_left a4 hC₁.le
  have b2 : C₁ * u ^ n₂ ≤ C₁ * u ^ (n₂ + 5) := mul_le_mul_of_nonneg_left an hC₁.le
  have b3 : |Cb| * ((s : ℝ) * k + k) ≤ |Cb| * C₁ * u ^ (n₂ + 5) + |Cb| * u ^ (n₂ + 5) := by
    have h5 := mul_le_mul_of_nonneg_left a5 hC₁.le
    have e : C₁ * u ^ 4 * u = C₁ * u ^ 5 := by ring
    have : (s : ℝ) * k + k ≤ C₁ * u ^ (n₂ + 5) + u ^ (n₂ + 5) := by linarith
    have := mul_le_mul_of_nonneg_left this hCb0
    linarith
  have b4 : C₁ * (k : ℝ) ^ C₂ ≤ C₁ * u ^ n₂ := mul_le_mul_of_nonneg_left hkC₂ hC₁.le
  have hpoly : 2 * (s : ℝ) + 2 * ((i : ℝ) + 1) + 6 + C₁ * (k : ℝ) ^ C₂ +
      |Cb| * ((s : ℝ) * k + k) ≤ P * u ^ (n₂ + 5) := by
    rw [hP]; linarith
  have hPu : P * u ^ (n₂ + 5) ≤ exp T / (12 * T ^ 2) := by
    rw [le_div_iff₀ (by positivity), hu, mul_pow, ← pow_mul]
    have e : P * (41 ^ (n₂ + 5) * T ^ (2 * (n₂ + 5))) * (12 * T ^ 2) =
        12 * P * 41 ^ (n₂ + 5) * T ^ (2 * n₂ + 12) := by ring
    rw [e]; exact G4
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hsε : 2 * s * ε ≤ exp T / (12 * T ^ 2) := by
    have h1 : 2 * (s : ℝ) * ε ≤ 2 * (C₁ * u ^ 4) * ε := by gcongr
    have h2 : 2 * (C₁ * u ^ 4) * ε = 2 * C₁ * 41 ^ 4 * exp T / T ^ 3 := by
      rw [hu, hε]; field_simp
    have h3 : 2 * C₁ * 41 ^ 4 * exp T / T ^ 3 ≤ exp T / (12 * T ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left G5 (by positivity : (0 : ℝ) ≤ exp T * T ^ 2)
      have e1 : 2 * C₁ * 41 ^ 4 * exp T * (12 * T ^ 2) = exp T * T ^ 2 * (24 * C₁ * 41 ^ 4) := by
        ring
      have e2 : exp T * T ^ 3 = exp T * T ^ 2 * T := by ring
      rw [e1, e2]; exact this
    linarith
  have : exp T / (12 * T ^ 2) = (exp T / (2 * T ^ 2)) / 6 := by field_simp; ring
  have : 0 ≤ exp T / (2 * T ^ 2) := by positivity
  linarith

/-- The large-frequency case, from the two mean-value statements. -/
theorem large_case (C₁ C₂ Cb P T ℓ ε v w₀ : ℝ) (n₂ c : ℕ)
    (hVMV : ∀ k : ℕ, 2 ≤ k → ∃ s : ℕ, k ≤ s ∧ (s : ℝ) ≤ C₁ * (k : ℝ) ^ 4 ∧ ∀ M : ℕ, 1 ≤ M →
        (vinogradovCount s k M : ℝ) ≤
          exp (C₁ * (k : ℝ) ^ C₂) *
            (M : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) / 2 : ℕ) : ℝ) + 1 / 100))
    (hbox : ∀ M k s : ℕ, 1 ≤ M → 1 ≤ k → 1 ≤ s →
      ∑ m ∈ Fintype.piFinset (fun j : Fin k => Finset.range (M ^ (j.val + 1))),
          (⨆ α : {α : Fin k → ℝ // ∀ j, (m j : ℝ) / (M : ℝ) ^ (j.val + 1) ≤ α j ∧
              α j < ((m j : ℝ) + 1) / (M : ℝ) ^ (j.val + 1)},
            ‖weylSum M k α.1‖ ^ (2 * s)) ≤
        exp (Cb * ((s : ℝ) * k + k)) * (M : ℝ) ^ (k * (k + 1) / 2) * (vinogradovCount s k M : ℝ))
    (hC₁ : 0 < C₁) (hn₂ : C₂ ≤ n₂) (hP : P = 3 * C₁ + 8 + |Cb| * C₁ + |Cb|) (G1 : 2 ≤ T)
    (G4 : 12 * P * 41 ^ (n₂ + 5) * T ^ (2 * n₂ + 12) ≤ exp T) (G5 : 24 * C₁ * 41 ^ 4 ≤ T)
    (hℓ : exp T / (2 * T ^ 2) ≤ ℓ) (hℓ20 : 20 ≤ ℓ) (hε : ε = exp T / T ^ 11)
    (hv0 : v ≠ 0) (hlv : 4 / 5 * ℓ ≤ log |v|) (h4L : log |v| ≤ 4 * exp T)
    (hX : ∀ j ∈ range c, exp ℓ ≤ w₀ + j ∧ w₀ + j ≤ 2 * exp ℓ) (hc : (c : ℝ) ≤ exp ℓ + 1) :
    ‖∑ j ∈ range c, Complex.exp (Complex.I * ((v * log (w₀ + j) : ℝ) : ℂ))‖ ≤
      3 * exp ℓ * exp (-ε) := by
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = log |v| / ℓ := ⟨_, rfl⟩
  have hyℓ : y * ℓ = log |v| := by rw [hy]; field_simp
  have hy45 : 4 / 5 ≤ y := by rw [hy, le_div_iff₀ hℓ0]; linarith
  have hy8 : y ≤ 8 * T ^ 2 := by
    rw [hy, div_le_iff₀ hℓ0]
    have e : 8 * T ^ 2 * (exp T / (2 * T ^ 2)) = 4 * exp T := by field_simp; ring
    have := mul_le_mul_of_nonneg_left hℓ (by positivity : (0 : ℝ) ≤ 8 * T ^ 2)
    linarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌈4 * y + 8⌉₊ := ⟨_, rfl⟩
  obtain ⟨i, hidef⟩ : ∃ i : ℕ, i = ⌊y⌋₊ := ⟨_, rfl⟩
  have hk_ge : 4 * y + 8 ≤ k := by rw [hkdef]; exact Nat.le_ceil _
  have hk_lt : (k : ℝ) < 4 * y + 8 + 1 := by
    rw [hkdef]; exact Nat.ceil_lt_add_one (by linarith)
  have hi_le : (i : ℝ) ≤ y := by rw [hidef]; exact Nat.floor_le (by linarith)
  have hi_lt : y < i + 1 := by rw [hidef]; exact Nat.lt_floor_add_one y
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hik : i < k := by
    have : (i : ℝ) < k := by linarith
    exact_mod_cast this
  have hkℓ : 4 * log |v| + 8 * ℓ ≤ k * ℓ := by
    rw [← hyℓ]; have := mul_le_mul_of_nonneg_right hk_ge hℓ0.le; linarith
  have hiv : log |v| ≤ ((i : ℝ) + 1) * ℓ := by
    rw [← hyℓ]; exact mul_le_mul_of_nonneg_right hi_lt.le hℓ0.le
  have hiv' : (i : ℝ) * ℓ ≤ log |v| := by
    rw [← hyℓ]; exact mul_le_mul_of_nonneg_right hi_le hℓ0.le
  have hku : (k : ℝ) ≤ 41 * T ^ 2 := by nlinarith
  have hk1 : (1 : ℝ) ≤ k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    linarith
  obtain ⟨s, hks, hsC, hJs⟩ := hVMV k hk2
  have hs1 : 1 ≤ s := by omega
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌊exp (3 / 4 * ℓ)⌋₊ := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    rw [hMdef]; exact Nat.le_floor (by push_cast; exact one_le_exp (by linarith))
  have hbox' := (hbox M k s hM1 (by omega) hs1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self Cb) (by positivity)))
      (by positivity)) (by positivity))
  exact main_case v ℓ w₀ ε (exp (C₁ * (k : ℝ) ^ C₂)) (exp (|Cb| * ((s : ℝ) * k + k)))
    c k i s M hℓ20 hv0 hlv hkℓ hik hiv hiv' hMdef hX hc hs1
    (one_le_exp (by positivity)) (one_le_exp (by positivity)) (by rw [hε]; positivity)
    (hJs M hM1) hbox'
    (budget C₁ C₂ Cb P T ℓ ε k i s n₂ hC₁ hn₂ hP G1 G4 G5 hℓ hε hk1 hku hik hsC)

open Classical in
/-- The small-frequency case: the telescoping bound `A106S.prog_sum_bound`. -/
theorem small_case (N v ℓ ε : ℝ) (q : ℕ) (hq : 0 < q) (hN0 : 0 < N) (hH : N / q = exp ℓ)
    (hqN : (q : ℝ) ≤ N) (hv : exp ε ≤ |v|) (hcase : |v| < exp (4 / 5 * ℓ)) (hεℓ : ε ≤ ℓ / 5)
    (J : Set ℝ) (hJ : J.OrdConnected) (hJN : J ⊆ Set.Icc N (2 * N)) (a : ℕ) :
    ‖∑ n ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun n => n ≡ a [MOD q]),
        (if (n : ℝ) ∈ J then (n : ℂ) ^ (Complex.I * v) else 0)‖ ≤
      8 * (N / q) * exp (-ε) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hvpos : 0 < |v| := lt_of_lt_of_le (exp_pos _) hv
  have hv0 : v ≠ 0 := abs_pos.1 hvpos
  have h := A106S.prog_sum_bound v hv0 q hq N hqN J hJ hJN a
  have h1 : 5 * N / (q * |v|) ≤ 5 * (N / q) * exp (-ε) := by
    have hone : 1 ≤ exp (-ε) * |v| := by
      calc (1 : ℝ) = exp (-ε) * exp ε := by rw [← exp_add]; simp
        _ ≤ exp (-ε) * |v| := mul_le_mul_of_nonneg_left hv (exp_pos _).le
    rw [div_le_iff₀ (by positivity)]
    calc 5 * N = 5 * N * 1 := by ring
      _ ≤ 5 * N * (exp (-ε) * |v|) := mul_le_mul_of_nonneg_left hone (by positivity)
      _ = 5 * (N / q) * exp (-ε) * (q * |v|) := by field_simp
  have h2 : 2 * |v| ≤ 2 * (N / q) * exp (-ε) := by
    rw [hH, mul_assoc, ← exp_add]
    have : exp (4 / 5 * ℓ) ≤ exp (ℓ + -ε) := exp_le_exp.2 (by linarith)
    linarith
  have h3 : 0 ≤ (N / q) * exp (-ε) := by positivity
  linarith

end ArtinPrimitiveRoots.L33A

namespace ArtinPrimitiveRoots

open Real Finset

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real Finset
open Classical in
theorem solution :
    ∃ C₃ K : ℝ, 0 < C₃ ∧ ∀ C : ℝ, 0 < C → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ N : ℝ, exp (log x / log (log x) ^ 2) ≤ N → N ≤ 2 * x ^ 5 →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ log x ^ C →
      ∀ v : ℝ, exp (log x / (2 * log (log x) ^ 2)) ≤ |v| → |v| ≤ 4 * x ^ 3 →
      ∀ a : ℕ, ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc N (2 * N) →
        ‖∑ n ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun n => n ≡ a [MOD q]),
            (if (n : ℝ) ∈ J then (n : ℂ) ^ (Complex.I * v) else 0)‖ ≤
          K * (N / q) * exp (-(log x / log (log x) ^ C₃)) := by
  obtain ⟨C₁, C₂, hC₁, _hC₂, hVMV⟩ := vinogradov_mean_value
  obtain ⟨Cb, hbox⟩ := weylSum_box_sup_moment
  refine ⟨11, 8, by norm_num, fun Cq _hCq => ?_⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n₂ : ℕ, n₂ = ⌈C₂⌉₊ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 3 * C₁ + 8 + |Cb| * C₁ + |Cb| := ⟨_, rfl⟩
  have hev : ∀ᶠ T in Filter.atTop, 2 ≤ T ∧ (2 * Cq) * T ^ 3 ≤ exp T ∧ 40 * T ^ 2 ≤ exp T ∧
      (12 * P * 41 ^ (n₂ + 5)) * T ^ (2 * n₂ + 12) ≤ exp T ∧ 24 * C₁ * 41 ^ 4 ≤ T :=
    (Filter.eventually_ge_atTop 2).and ((L33A.ev_pow_le_exp _ 3).and
      ((L33A.ev_pow_le_exp _ 2).and ((L33A.ev_pow_le_exp _ _).and
        (Filter.eventually_ge_atTop _))))
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨exp (exp (max T₀ 2)), fun x hx N hN1 _hN2 q hq hqC v hv1 hv2 a J hJ hJN => ?_⟩
  -- `L = log x = e^T`
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos _) hx
  have hL : exp (max T₀ 2) ≤ log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx
  have hL0 : 0 < log x := lt_of_lt_of_le (exp_pos _) hL
  have hTge : max T₀ 2 ≤ log (log x) := by rw [Real.le_log_iff_exp_le hL0]; exact hL
  have hlogx4 : log |v| ≤ log 4 + 3 * log x := by
    have hv0' : 0 < |v| := lt_of_lt_of_le (exp_pos _) hv1
    have := Real.log_le_log hv0' hv2
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    push_cast at this; linarith
  rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  generalize log x = L at hL hL0 hTge hN1 hqC hv1 hlogx4 ⊢
  have hLT : L = exp (log L) := (exp_log hL0).symm
  generalize log L = T at hLT hTge hN1 hqC hv1 ⊢
  subst hLT
  obtain ⟨G1, G2, G3, G4, G5⟩ := hT₀ T (le_trans (le_max_left _ _) hTge)
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := lt_of_lt_of_le (exp_pos _) hN1
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  -- `ℓ = log (N/q) ≥ L/(2T²) ≥ 20`
  have hlogN : exp T / T ^ 2 ≤ log N := (Real.le_log_iff_exp_le hN0).2 hN1
  have hlogq : log q ≤ Cq * T := by
    have := Real.log_le_log hq' hqC
    rwa [Real.log_rpow hL0, Real.log_exp] at this
  have hCqT : Cq * T ≤ exp T / (2 * T ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hhalf : exp T / T ^ 2 = 2 * (exp T / (2 * T ^ 2)) := by field_simp
  have hℓ : exp T / (2 * T ^ 2) ≤ log (N / q) := by
    rw [Real.log_div hN0.ne' hq'.ne']; linarith
  have hℓ20 : 20 ≤ log (N / q) := by
    have : 20 ≤ exp T / (2 * T ^ 2) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hH : N / q = exp (log (N / q)) := (exp_log (div_pos hN0 hq')).symm
  -- `ε = L/T^11`
  have hT9 : (512 : ℝ) ≤ T ^ 9 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) G1 9; norm_num at this; linarith
  have hε10 : exp T / T ^ 11 ≤ exp T / (10 * T ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : T ^ 11 = T ^ 2 * T ^ 9 := by ring
    rw [this]; nlinarith
  have h10 : exp T / (10 * T ^ 2) = (exp T / (2 * T ^ 2)) / 5 := by field_simp; ring
  have hεℓ : exp T / T ^ 11 ≤ log (N / q) / 5 := by linarith
  have hε2 : exp T / T ^ 11 ≤ exp T / (2 * T ^ 2) := by
    have : 0 ≤ exp T / (2 * T ^ 2) := by positivity
    linarith
  by_cases hcase : |v| < exp (4 / 5 * log (N / q))
  · have h0 : 0 ≤ exp T / (2 * T ^ 2) := by positivity
    have hqN : (q : ℝ) ≤ N := (Real.log_le_log_iff hq' hN0).1 (by linarith)
    exact L33A.small_case N v (log (N / q)) _ q hq hN0 hH hqN
      ((exp_le_exp.2 hε2).trans hv1) hcase hεℓ J hJ hJN a
  · push Not at hcase
    have hvpos : 0 < |v| := lt_of_lt_of_le (exp_pos _) hcase
    have hlv : 4 / 5 * log (N / q) ≤ log |v| := (Real.le_log_iff_exp_le hvpos).2 hcase
    have h4L : log |v| ≤ 4 * exp T := by
      have : log 4 < 2 := by
        have := Real.log_two_lt_d9
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
      have : (2 : ℝ) ≤ exp T := by nlinarith
      linarith
    obtain ⟨c, w₀, hc, hX, heq⟩ := L33A.reduce v N q hq hN0 J hJ hJN a
    rw [heq]
    rw [hH] at hc hX
    have h := L33A.large_case C₁ C₂ Cb P T (log (N / q)) _ v w₀ n₂ c hVMV hbox hC₁
      (hn₂ ▸ Nat.le_ceil C₂) hP G1 G4 G5 hℓ hℓ20 rfl (abs_pos.1 hvpos) hlv h4L hX hc
    rw [← hH] at h
    have : 0 ≤ N / q * exp (-(exp T / T ^ 11)) := by positivity
    linarith
end
