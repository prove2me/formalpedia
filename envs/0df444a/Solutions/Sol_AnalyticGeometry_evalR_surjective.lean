-- Prove2me | solution 1 for AnalyticGeometry.evalR_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:39:13.915073+00:00
-- url     : https://prove2.me/submissions/6aafbd96-b365-4d22-a89d-4cb2f0407aee

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

set_option autoImplicit false

/-- Greedy remainders: `rem 0 = y`, `rem (n+1) = (rem n - ⌊rem n⌋) / x`. -/
noncomputable def pf8a_rem (x y : ℝ) : ℕ → ℝ
  | 0 => y
  | n + 1 => (pf8a_rem x y n - ⌊pf8a_rem x y n⌋) / x

theorem pf8a_rem_zero (x y : ℝ) : pf8a_rem x y 0 = y := rfl

theorem pf8a_rem_succ (x y : ℝ) (n : ℕ) :
    pf8a_rem x y (n + 1) = (pf8a_rem x y n - ⌊pf8a_rem x y n⌋) / x := rfl

theorem pf8a_rem_bounds (x y : ℝ) (hx0 : 0 < x) (n : ℕ) :
    0 ≤ pf8a_rem x y (n + 1) ∧ pf8a_rem x y (n + 1) < 1 / x := by
  rw [pf8a_rem_succ]
  have h1 := Int.floor_le (pf8a_rem x y n)
  have h2 := Int.lt_floor_add_one (pf8a_rem x y n)
  constructor
  · apply div_nonneg <;> linarith
  · rw [div_lt_div_iff_of_pos_right hx0]; linarith

theorem pf8a_rem_abs (x y : ℝ) (hx0 : 0 < x) (n : ℕ) :
    |pf8a_rem x y n| ≤ |y| + 1 / x := by
  have hx1 : 0 < 1 / x := by positivity
  cases n with
  | zero => rw [pf8a_rem_zero]; linarith
  | succ n =>
    obtain ⟨h1, h2⟩ := pf8a_rem_bounds x y hx0 n
    rw [abs_of_nonneg h1]
    linarith [abs_nonneg y]

theorem pf8a_coeff_abs (x y : ℝ) (hx0 : 0 < x) (n : ℕ) :
    |((⌊pf8a_rem x y n⌋ : ℤ) : ℝ)| ≤ |(⌊y⌋ : ℝ)| + 1 / x := by
  have hx1 : 0 < 1 / x := by positivity
  cases n with
  | zero => rw [pf8a_rem_zero]; linarith
  | succ n =>
    obtain ⟨h1, h2⟩ := pf8a_rem_bounds x y hx0 n
    have h3 : (0 : ℝ) ≤ (⌊pf8a_rem x y (n + 1)⌋ : ℝ) := by
      exact_mod_cast Int.floor_nonneg.mpr h1
    have h4 := Int.floor_le (pf8a_rem x y (n + 1))
    rw [abs_of_nonneg h3]
    linarith [abs_nonneg (⌊y⌋ : ℝ)]

theorem pf8a_partial (x y : ℝ) (hx0 : 0 < x) (n : ℕ) :
    y = ∑ k ∈ Finset.range n, ((⌊pf8a_rem x y k⌋ : ℤ) : ℝ) * x ^ k
      + pf8a_rem x y n * x ^ n := by
  induction n with
  | zero => simp [pf8a_rem_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have key : pf8a_rem x y n * x ^ n = ((⌊pf8a_rem x y n⌋ : ℤ) : ℝ) * x ^ n
        + pf8a_rem x y (n + 1) * x ^ (n + 1) := by
      rw [pf8a_rem_succ, pow_succ]
      field_simp
      ring
    linarith

open AnalyticGeometry in
theorem solution (r x : ℝ) (hr1 : r < 1) (hx0 : 0 < x) (hxr : x ≤ r) (y : ℝ) :
    ∃ f ∈ zLaurentGT r,
      Summable (fun n : ℤ => (f.coeff n : ℝ) * x ^ n) ∧ evalR x f = y := by
  set a : ℕ → ℤ := fun n => ⌊pf8a_rem x y n⌋ with ha
  set P : PowerSeries ℤ := PowerSeries.mk a with hP
  set f : LaurentSeries ℤ := HahnSeries.ofPowerSeries ℤ ℤ P with hf
  have hx1 : x < 1 := lt_of_le_of_lt hxr hr1
  have hcoeff_nat : ∀ k : ℕ, f.coeff (k : ℤ) = a k := by
    intro k
    rw [hf, LaurentSeries.coeff_coe_powerSeries, hP, PowerSeries.coeff_mk]
  have hcoeff_neg : ∀ n : ℤ, n < 0 → f.coeff n = 0 := by
    intro n hn
    rw [hf, PowerSeries.coeff_coe, if_pos hn]
  set C : ℝ := |(⌊y⌋ : ℝ)| + 1 / x with hC
  have hC0 : 0 ≤ C := by
    have : 0 < 1 / x := by positivity
    rw [hC]; linarith [abs_nonneg (⌊y⌋ : ℝ)]
  have hCa : ∀ k : ℕ, |((a k : ℤ) : ℝ)| ≤ C := fun k => pf8a_coeff_abs x y hx0 k
  -- the ℕ-indexed series
  set g : ℕ → ℝ := fun k => ((a k : ℤ) : ℝ) * x ^ k with hg
  have hgeo : Summable (fun k : ℕ => C * x ^ k) :=
    (summable_geometric_of_lt_one hx0.le hx1).mul_left C
  have hgsum : Summable g := by
    refine Summable.of_norm_bounded hgeo ?_
    intro k
    rw [hg, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hx0]
    exact mul_le_mul_of_nonneg_right (hCa k) (by positivity)
  have hgy : HasSum g y := by
    rw [hgsum.hasSum_iff_tendsto_nat]
    have hrem : Filter.Tendsto (fun n : ℕ => pf8a_rem x y n * x ^ n) Filter.atTop (nhds 0) := by
      have hlim : Filter.Tendsto (fun n : ℕ => (|y| + 1 / x) * x ^ n) Filter.atTop (nhds 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1).const_mul (|y| + 1 / x)
        simpa using this
      refine squeeze_zero_norm ?_ hlim
      intro n
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hx0]
      exact mul_le_mul_of_nonneg_right (pf8a_rem_abs x y hx0 n) (by positivity)
    have hy : (fun n : ℕ => ∑ i ∈ Finset.range n, g i)
        = fun n : ℕ => y - pf8a_rem x y n * x ^ n := by
      funext n
      have := pf8a_partial x y hx0 n
      rw [hg]
      simp only [ha]
      linarith
    rw [hy]
    have := (tendsto_const_nhds (x := y)).sub hrem
    simpa using this
  -- transfer to ℤ
  set F : ℤ → ℝ := fun n : ℤ => (f.coeff n : ℝ) * x ^ n with hF
  have hFg : F ∘ (Nat.cast : ℕ → ℤ) = g := by
    funext k
    simp only [Function.comp, hF, hg, hcoeff_nat, zpow_natCast]
  have hF0 : ∀ n ∉ Set.range (Nat.cast : ℕ → ℤ), F n = 0 := by
    intro n hn
    have hneg : n < 0 := by
      by_contra h
      exact hn ⟨n.toNat, Int.toNat_of_nonneg (not_lt.mp h)⟩
    simp only [hF, hcoeff_neg n hneg, Int.cast_zero, zero_mul]
  have hFy : HasSum F y := by
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff hF0, hFg]
    exact hgy
  refine ⟨f, ?_, hFy.summable, hFy.tsum_eq⟩
  -- membership in zLaurentGT r
  refine ⟨(r + 1) / 2, by linarith, ?_⟩
  have hs0 : 0 < (r + 1) / 2 := by linarith
  have hs1 : (r + 1) / 2 < 1 := by linarith
  unfold DecaysAt
  rw [← Nat.map_cast_int_atTop, Filter.tendsto_map'_iff]
  have hlim : Filter.Tendsto (fun k : ℕ => C * ((r + 1) / 2) ^ k) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hs0.le hs1).const_mul C
    simpa using this
  refine squeeze_zero (fun k => ?_) (fun k => ?_) hlim
  · simp only [Function.comp]
    positivity
  · simp only [Function.comp, hcoeff_nat, zpow_natCast]
    exact mul_le_mul_of_nonneg_right (hCa k) (by positivity)
