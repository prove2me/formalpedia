-- Prove2me | solution 1 for Arxiv2003_13288.effective_wavenumber_momentum_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T20:42:57.814466+00:00
-- url     : https://prove2.me/submissions/bd2c115c-483a-4ec7-8939-9d4f1323b92e

import Mathlib
import Definitions.Def_Arxiv2003_13288_Basic

open MeasureTheory Filter Topology

lemma s70ew_re_sqrt_nonneg (z : ℂ) : 0 ≤ (z ^ (1 / 2 : ℂ)).re := by
  by_cases hz : z = 0
  · subst hz; rw [Complex.zero_cpow (by norm_num)]; simp
  · rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
    apply mul_nonneg (Real.exp_pos _).le
    apply Real.cos_nonneg_of_mem_Icc
    have h1 := Complex.neg_pi_lt_arg z
    have h2 := Complex.arg_le_pi z
    have him : (Complex.log z * (1 / 2 : ℂ)).im = Complex.arg z / 2 := by
      simp [Complex.log_im]; ring
    rw [him]; constructor <;> linarith

open Arxiv2003_13288 in
theorem solution (k : ℝ) (hk : 0 < k) (epsPerp : ℝ → ℂ)
    (pmax : ℝ) (hpmax : 0 ≤ pmax) (hpeak : (epsPerp pmax).re - pmax ^ 2 / k ^ 2 = 0) :
    (effWavenumber k (epsPerp pmax)).re ^ 2 - (effWavenumber k (epsPerp pmax)).im ^ 2 = pmax ^ 2 ∧
    ((epsPerp pmax).im ≠ 0 → pmax < (effWavenumber k (epsPerp pmax)).re) := by
  set ε := epsPerp pmax
  set w : ℂ := ε ^ (1 / 2 : ℂ) with hw
  have hw2 : w ^ 2 = ε := by
    rw [hw, one_div]
    exact_mod_cast Complex.cpow_nat_inv_pow ε (by norm_num : (2 : ℕ) ≠ 0)
  have hre : w.re ^ 2 - w.im ^ 2 = ε.re := by
    rw [← hw2]; simp [sq]
  have him : 2 * w.re * w.im = ε.im := by
    rw [← hw2]; simp [sq]; ring
  have hwre := s70ew_re_sqrt_nonneg ε
  have hKre : (effWavenumber k ε).re = w.re * k := by simp [effWavenumber, hw]
  have hKim : (effWavenumber k ε).im = w.im * k := by simp [effWavenumber, hw]
  have hεre : ε.re = pmax ^ 2 / k ^ 2 := by linarith
  have hk2 : k ^ 2 ≠ 0 := by positivity
  have main : (w.re * k) ^ 2 - (w.im * k) ^ 2 = pmax ^ 2 := by
    have : (w.re * k) ^ 2 - (w.im * k) ^ 2 = (w.re ^ 2 - w.im ^ 2) * k ^ 2 := by ring
    rw [this, hre, hεre]; field_simp
  rw [hKre, hKim]
  refine ⟨main, fun hne => ?_⟩
  have hb : w.im ≠ 0 := by
    intro h0; apply hne; rw [← him, h0]; ring
  have hpos : 0 < (w.im * k) ^ 2 := by positivity
  by_contra hle
  push Not at hle
  have h0 : 0 ≤ w.re * k := mul_nonneg hwre hk.le
  have := pow_le_pow_left₀ h0 hle 2
  linarith
