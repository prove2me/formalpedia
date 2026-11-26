-- Prove2me | Definitions.Def_RHGram655_20261117_P02_v1
-- name    : RHGram655_20261117_P02_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T14:04:08.623205+00:00
-- url     : https://prove2.me/theorems/e1c6baab-728e-458a-8aaa-481eb68c9e8b
-- title:
--   Gram 655 ordinary certificate dependencies 02
-- statement:
--   Ordinary Lean proof dependencies for a numerical Gram-point certificate. Complete mathematical proofs and explicit kernel proof terms; no custom elaborators, unchecked numerical assumptions or added axioms.
-- source:
--   smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Apache-2.0; PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe. Dependency extraction and ordinary proof-term sharing by Desenvolvimento RH. AXLE standalone ordinary source 758e7c92-e198-48f4-8e6c-1f3233ed3277; combined source audit recorded separately.

import Definitions.Def_RHGram655_20261117_P01_v1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
section CertificatePort151
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The Olver–Borwein error bound for the Euler–Maclaurin expansion of `ζ`

The sharp bound on the `ζ` remainder `zetaRemainder` (`thm:zeta_error_bound`), together with the
sign and Fourier properties of the centered even Bernoulli kernel `B̃_{2m} - B_{2m}` it rests on.
Here `B̃_{2m}(x) = bernoulliFun (2m) (Int.fract x)` is the periodized even Bernoulli function and
`B_{2m} = bernoulli (2m)` the Bernoulli number.

## Main results

- `bernoulliFun_sub_self_eq_tsum_cos`: the cosine–Fourier expansion
  `B̃_{2m}(x) - B_{2m} = (-1)^{m+1} A_m ∑_k (cos(2πkx) - 1)/k^{2m}`, `A_m = 2(2m)!/(2π)^{2m}`.
- `centered_kernel_mul_sign_nonneg`: the centered kernel has constant sign `(-1)^m`.
- `integral_abs_bernoulliFun_sub_self`: the period-mean
  `∫_0^1 |bernoulliFun (2m) x - B_{2m}| dx = |B_{2m}|`.
- `integral_Ioi_cos_mul_rpow_nonneg`: **Pólya's positivity lemma**,
  `∫_N^∞ cos(2πkx) x^{-a} dx ≥ 0` for `N ≥ 1` and `a > 1`.
- `integral_Ioi_abs_bernoulliFun_fract_sub_mul_rpow_le`: the weighted averaging bound.
- `zetaRemainder_eq_integral_bernoulliFun_fract_sub`: the centered-kernel representation of the
  `ζ` remainder.
- `norm_zetaRemainder_le`: the error bound `‖R_M(s,N)‖ ≤ zetaRemainderBound s M N`.
-/
section


open MeasureTheory Real Filter Topology
open scoped Nat

/- If `0 ≤ (-1)^m * y`, the sign `(-1)^m` pulls out of the absolute value: `|y| = (-1)^m * y`. -/
private theorem abs_eq_neg_one_pow_mul {m : ℕ} {y : ℝ} (h : 0 ≤ (-1 : ℝ) ^ m * y) :
    |y| = (-1 : ℝ) ^ m * y := by
  rw [← abs_of_nonneg h, abs_mul, abs_neg_one_pow, one_mul]

/- The even zeta value `∑_{n} 1/n^{2m} = (-1)^{m+1} (2π)^{2m} / (2·(2m)!) · B_{2m}` (mathlib's
`hasSum_zeta_nat`, with the factor `(2π)^{2m}/2` in place of `2^{2m-1} π^{2m}`). -/
private theorem hasSum_one_div_nat_pow_bernoulli (m : ℕ) (hm0 : m ≠ 0) :
    HasSum (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ (2 * m))
      ((-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! * (bernoulli (2 * m) : ℝ)) := by
  have h2 : (2 : ℝ) ^ (2 * m - 1) * 2 = 2 ^ (2 * m) := by rw [← pow_succ]; congr 1; lia
  rw [show (-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! * (bernoulli (2 * m) : ℝ)
        = (-1 : ℝ) ^ (m + 1) * 2 ^ (2 * m - 1) * π ^ (2 * m) * (bernoulli (2 * m) : ℝ)
            / (2 * m)! from by rw [mul_pow, ← h2]; ring]
  exact hasSum_zeta_nat hm0

/- **Centered cosine–Fourier expansion of the periodized even Bernoulli kernel.** For `m ≥ 1`
and all `x ∈ ℝ`, with `A_m = 2(2m)!/(2π)^{2m}`,
`bernoulliFun (2m) (Int.fract x) - B_{2m} = (-1)^{m+1} A_m ∑_k (cos(2πkx) - 1)/k^{2m}`. -/
theorem bernoulliFun_sub_self_eq_tsum_cos (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)
      = (-1 : ℝ) ^ (m + 1) * (2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m))
          * ∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m) := by
  have hm0 : m ≠ 0 := by lia
  set B : ℝ := bernoulliFun (2 * m) (Int.fract x)
  set b : ℝ := (bernoulli (2 * m) : ℝ)
  set Cval : ℝ := (-1 : ℝ) ^ (m + 1) * (2 * π) ^ (2 * m) / 2 / (2 * m)! with hCval
  have hfracmem : Int.fract x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  -- cosine periodicity: `cos(2πn·fract x) = cos(2πnx)`.
  have hcos : ∀ n : ℕ, cos (2 * π * n * Int.fract x) = cos (2 * π * n * x) := by
    intro n
    have heq : (2 : ℝ) * π * n * x
        = 2 * π * n * Int.fract x + ((n : ℤ) * ⌊x⌋ : ℤ) * (2 * π) := by
      have := Int.floor_add_fract x
      push_cast
      linear_combination (-(2 * π * (n : ℝ))) * this
    rw [heq, Real.cos_add_int_mul_two_pi]
  -- the Fourier expansion at `fract x`, with `cos` argument unwrapped to `x`.
  have hsx : HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ (2 * m) * cos (2 * π * n * x)) (Cval * B) := by
    have h := hasSum_one_div_nat_pow_mul_cos hm0 hfracmem
    rw [show (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * m))).eval (Int.fract x)
          = B from rfl] at h
    simpa only [hcos] using h
  -- the same expansion at `x = 0`, giving the Bernoulli number.
  have hs0 : HasSum (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ (2 * m)) (Cval * b) :=
    hasSum_one_div_nat_pow_bernoulli m hm0
  -- subtract and identify the tsum.
  have hdiff := hsx.sub hs0
  have key : (∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m)) = Cval * B - Cval * b := by
    rw [← hdiff.tsum_eq]; exact tsum_congr fun n ↦ by ring
  rw [key, hCval]
  -- final algebra: `(-1)^{m+1} A_m · Cval = 1`.
  set a : ℝ := (-1 : ℝ) ^ (m + 1) with ha
  have ha2 : a * a = 1 := by rw [ha, ← pow_add]; exact Even.neg_one_pow ⟨m + 1, by ring⟩
  have hpi : ((2 * π) ^ (2 * m) : ℝ) ≠ 0 := by positivity
  have hfac : ((2 * m)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hEF : a * (2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m))
      * (a * (2 * π) ^ (2 * m) / 2 / (2 * m)!) = 1 := by
    field_simp; linear_combination ha2
  linear_combination (-(B - b)) * hEF

/- **Constant sign of the centered even Bernoulli kernel.** For `m ≥ 1` and all `x`,
`(-1)^m (B̃_{2m}(x) - B_{2m}) ≥ 0`. -/
theorem centered_kernel_mul_sign_nonneg (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    0 ≤ (-1 : ℝ) ^ m * (bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)) := by
  have hA : (0 : ℝ) ≤ 2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m) := by positivity
  have hS : (∑' n : ℕ, (cos (2 * π * n * x) - 1) / (n : ℝ) ^ (2 * m)) ≤ 0 :=
    tsum_nonpos fun n ↦
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (Real.cos_le_one _)) (by positivity)
  have hs3 : (-1 : ℝ) ^ m * (-1) ^ (m + 1) = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨m, by ring⟩
  rw [bernoulliFun_sub_self_eq_tsum_cos m hm x, ← mul_assoc, ← mul_assoc, hs3]
  linarith [mul_nonneg hA (neg_nonneg.mpr hS)]

/- **Period-mean of the centered even Bernoulli kernel.** For `m ≥ 1`,
`∫_0^1 |bernoulliFun (2m) x - B_{2m}| dx = |B_{2m}|`. The integrand uses the Bernoulli polynomial
`bernoulliFun (2m)`, which agrees on `[0,1)` with the periodized kernel `B̃_{2m}`. -/
private theorem integrableOn_Ioi_of_bound_mul_rpow {f : ℝ → ℝ} (hf : Continuous f)
    (hbound : ∀ x, |f x| ≤ 1) {q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ f x * x ^ q) (Set.Ioi N) := by
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt hq hN)
    ((hf.continuousOn.mul (fun x hx ↦
      (Real.continuousAt_rpow_const x q
        (Or.inl (hN.trans (Set.mem_Ioi.mp hx)).ne')).continuousWithinAt)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hN.trans (Set.mem_Ioi.mp hx)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) (hbound x)

/- Integrability on `(N, ∞)` of `x ↦ sin (ω x) · x ^ q` for `q < -1` and `0 < N`. -/
private theorem integrableOn_Ioi_sin_mul_rpow {ω q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ sin (ω * x) * x ^ q) (Set.Ioi N) :=
  integrableOn_Ioi_of_bound_mul_rpow (Real.continuous_sin.comp (continuous_const.mul continuous_id))
    (fun _ ↦ abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) hq hN

/- Integrability on `(N, ∞)` of `x ↦ cos (ω x) · x ^ q` for `q < -1` and `0 < N`. -/
private theorem integrableOn_Ioi_cos_mul_rpow {ω q N : ℝ} (hq : q < -1) (hN : 0 < N) :
    IntegrableOn (fun x ↦ cos (ω * x) * x ^ q) (Set.Ioi N) :=
  integrableOn_Ioi_of_bound_mul_rpow (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    (fun _ ↦ abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) hq hN

/- **Positivity of the weighted sine integral.** For `p > 1` and integers `N, k ≥ 1`,
`∫_N^∞ sin(2πkx) x^{-p} dx ≥ 0`. -/
private theorem integral_Ioi_sin_mul_rpow_nonneg {p : ℝ} (hp : 1 < p) {N k : ℕ}
    (hN : 1 ≤ N) (hk : 1 ≤ k) :
    0 ≤ ∫ x in Set.Ioi (N : ℝ), sin (2 * π * k * x) * x ^ (-p) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  set ω : ℝ := 2 * π * (k : ℝ) with hω
  have hω0 : 0 < ω := by rw [hω]; positivity
  set T : ℝ := 1 / (2 * (k : ℝ)) with hT
  have hT0 : 0 < T := by rw [hT]; positivity
  have hωT : ω * T = π := by rw [hω, hT]; field_simp
  set A : ℕ → ℝ := fun j ↦ (N : ℝ) + j * T with hA
  have hAsucc : ∀ j, A (j + 1) = A j + T := fun j ↦ by simp only [hA]; push_cast; ring
  have hApos : ∀ j, 0 < A j := fun j ↦ by simp only [hA]; positivity
  have hAle : ∀ j, A j ≤ A (j + 1) := fun j ↦ by rw [hAsucc]; linarith
  set g : ℝ → ℝ := fun x ↦ sin (ω * x) * x ^ (-p) with hg
  -- `c j` is the `j`-th half-period mass, written on the *shifted* window `[0, T]`.
  set c : ℕ → ℝ := fun j ↦ ∫ u in (0 : ℝ)..T, sin (ω * u) * (A j + u) ^ (-p) with hc
  have hsincont : Continuous fun x : ℝ ↦ sin (ω * x) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hrpow : ContinuousOn (fun x : ℝ ↦ x ^ (-p)) (Set.Ioi (0 : ℝ)) := fun x hx ↦
    (Real.continuousAt_rpow_const x (-p) (Or.inl (Set.mem_Ioi.mp hx).ne')).continuousWithinAt
  have hgint : ∀ j, IntervalIntegrable g volume (A j) (A (j + 1)) := fun j ↦
    (hsincont.continuousOn.mul (hrpow.mono fun x hx ↦ by
      rw [Set.uIcc_of_le (hAle j)] at hx
      exact lt_of_lt_of_le (hApos j) hx.1)).intervalIntegrable
  have hcint : ∀ j, IntervalIntegrable
      (fun u ↦ sin (ω * u) * (A j + u) ^ (-p)) volume 0 T := fun j ↦ by
    refine (hsincont.continuousOn.mul (ContinuousOn.rpow_const
      (continuous_const.add continuous_id).continuousOn fun u hu ↦ Or.inl ?_)).intervalIntegrable
    rw [Set.uIcc_of_le hT0.le] at hu
    exact (by linarith [hApos j, hu.1] : (0 : ℝ) < A j + u).ne'
  -- `sin (ω ·)` is nonnegative on the shifted window, since `ω T = π`.
  have hsinu : ∀ u ∈ Set.Icc (0 : ℝ) T, 0 ≤ sin (ω * u) := fun u hu ↦
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hω0.le hu.1)
      (by linarith [mul_le_mul_of_nonneg_left hu.2 hω0.le, hωT])
  -- antitonicity is now pointwise: the weight `(A j + u)^(-p)` decreases in `j`.
  have hcanti : Antitone c := antitone_nat_of_succ_le fun j ↦ by
    simp only [hc]
    refine intervalIntegral.integral_mono_on hT0.le (hcint (j + 1)) (hcint j) fun u hu ↦ ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
      (by linarith [hApos j, hu.1]) (by linarith [hAsucc j, hT0]) (by linarith)) (hsinu u hu)
  -- each signed piece-integral equals `(-1)^j c j`: on `[A j, A j + T]`, `sin (ω x) =
  -- (-1)^j sin (ω (x - A j))` because `ω A j = (j + 2kN) π`.
  have hpiece : ∀ j, (∫ x in A j..A (j + 1), g x) = (-1 : ℝ) ^ j * c j := fun j ↦ by
    rw [show (∫ x in A j..A (j + 1), g x) = ∫ u in (0 : ℝ)..T, g (A j + u) from by
      rw [intervalIntegral.integral_comp_add_left g (A j), add_zero, ← hAsucc j]]
    simp only [hc, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    have key : sin (ω * (A j + u)) = (-1 : ℝ) ^ j * sin (ω * u) := by
      rw [show ω * (A j + u) = ω * u + ((j + 2 * k * N : ℕ) : ℝ) * π by
            simp only [hA, hω, hT]; field_simp; push_cast; ring,
        Real.sin_add_nat_mul_pi,
        show ((-1 : ℝ)) ^ (j + 2 * k * N) = (-1 : ℝ) ^ j by
          rw [pow_add, show 2 * k * N = 2 * (k * N) by ring, pow_mul]; norm_num]
    simp only [hg, key]
    ring
  -- the partial sums of the alternating series are the truncated improper integrals
  have hA0 : A 0 = (N : ℝ) := by simp [hA]
  have hpartial : ∀ n, ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * c i = ∫ x in (N : ℝ)..A n, g x :=
    fun n ↦ by
      rw [← hA0, ← intervalIntegral.sum_integral_adjacent_intervals
        (f := g) fun k (_ : k < n) ↦ hgint k]
      exact Finset.sum_congr rfl fun i _ ↦ (hpiece i).symm
  -- the truncated integrals converge to the improper integral
  have hgintegrable : IntegrableOn g (Set.Ioi (N : ℝ)) := by
    rw [hg]; exact integrableOn_Ioi_sin_mul_rpow (by linarith) hN0
  have hAtop : Tendsto A atTop atTop :=
    (tendsto_atTop_add_const_left atTop (N : ℝ)
      (tendsto_natCast_atTop_atTop.atTop_mul_const hT0)).congr fun _ ↦ rfl
  have htend_sum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * c i) atTop
      (𝓝 (∫ x in Set.Ioi (N : ℝ), g x)) :=
    (intervalIntegral_tendsto_integral_Ioi (N : ℝ) hgintegrable hAtop).congr
      fun n ↦ (hpartial n).symm
  simpa using Antitone.alternating_series_le_tendsto htend_sum hcanti 0

/- **Pólya's positivity lemma (1918).** For an integer `N ≥ 1`, a real `a > 1`, and any natural
`k`, `∫_N^∞ cos(2πkx) x^{-a} dx ≥ 0`. -/
theorem integral_Ioi_cos_mul_rpow_nonneg {a : ℝ} (ha : 1 < a) {N k : ℕ} (hN : 1 ≤ N) :
    0 ≤ ∫ x in Set.Ioi (N : ℝ), cos (2 * π * k * x) * x ^ (-a) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine setIntegral_nonneg measurableSet_Ioi fun x hx ↦ ?_
    simpa using Real.rpow_nonneg (hN0.trans hx).le (-a)
  set ω : ℝ := 2 * π * (k : ℝ) with hω
  have hω0 : 0 < ω := by rw [hω]; positivity
  -- the conjugate sine integral is nonnegative (`p = a + 1 > 1`)
  have hJ : 0 ≤ ∫ x in Set.Ioi (N : ℝ), sin (ω * x) * x ^ (-(a + 1)) := by
    rw [hω]; exact integral_Ioi_sin_mul_rpow_nonneg (p := a + 1) (by linarith) hN hk
  -- the cosine and sine tail integrands are integrable on `(N, ∞)`
  have hcoscont : Continuous fun x : ℝ ↦ cos (ω * x) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcosint : IntegrableOn (fun x ↦ cos (ω * x) * x ^ (-a)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cos_mul_rpow (by linarith) hN0
  have hsinint : IntegrableOn (fun x ↦ sin (ω * x) * x ^ (-(a + 1))) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_sin_mul_rpow (by linarith) hN0
  -- the boundary value `sin (ω N)` vanishes
  have hsinN : sin (ω * N) = 0 := by
    rw [show ω * (N : ℝ) = ((2 * k * N : ℕ) : ℝ) * π by rw [hω]; push_cast; ring]
    exact Real.sin_nat_mul_pi _
  -- integration by parts: `∫_N^R cos·x^{-a} = R^{-a} sin(ωR)/ω + (a/ω) ∫_N^R sin·x^{-(a+1)}`
  have hrel : ∀ᶠ R in atTop, (∫ x in (N : ℝ)..R, cos (ω * x) * x ^ (-a))
      = R ^ (-a) * sin (ω * R) / ω
        + a / ω * ∫ x in (N : ℝ)..R, sin (ω * x) * x ^ (-(a + 1)) := by
    filter_upwards [eventually_ge_atTop (N : ℝ)] with R hR
    have hne : ∀ x ∈ Set.uIcc (N : ℝ) R, x ≠ 0 := fun x hx ↦ by
      rw [Set.uIcc_of_le hR] at hx; exact (lt_of_lt_of_le hN0 hx.1).ne'
    have hu : ∀ x ∈ Set.uIcc (N : ℝ) R, HasDerivAt (fun x ↦ x ^ (-a)) (-a * x ^ (-(a + 1))) x :=
      fun x hx ↦ by
        have hd := hasDerivAt_rpow_const (x := x) (p := -a) (Or.inl (hne x hx))
        rwa [show -a - 1 = -(a + 1) by ring] at hd
    have hv : ∀ x ∈ Set.uIcc (N : ℝ) R,
        HasDerivAt (fun x ↦ sin (ω * x) / ω) (cos (ω * x)) x := fun x _ ↦ by
      have h2 : HasDerivAt (fun t ↦ sin (ω * t)) (cos (ω * x) * ω) x :=
        (Real.hasDerivAt_sin (ω * x)).comp x (by simpa using (hasDerivAt_id x).const_mul ω)
      have h3 := h2.div_const ω
      rwa [mul_div_assoc, div_self hω0.ne', mul_one] at h3
    have hu'int : IntervalIntegrable (fun x ↦ -a * x ^ (-(a + 1))) volume (N : ℝ) R :=
      (continuousOn_const.mul fun x hx ↦
        (Real.continuousAt_rpow_const x (-(a + 1))
          (Or.inl (hne x hx))).continuousWithinAt).intervalIntegrable
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu'int
      (hcoscont.intervalIntegrable _ _)
    rw [intervalIntegral.integral_congr fun x _ ↦ mul_comm (x ^ (-a)) (cos (ω * x))] at hibp
    rw [hibp, show (∫ x in (N : ℝ)..R, -a * x ^ (-(a + 1)) * (sin (ω * x) / ω))
          = -(a / ω) * ∫ x in (N : ℝ)..R, sin (ω * x) * x ^ (-(a + 1)) by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr fun x _ ↦ by ring, hsinN]
    ring
  -- pass to the limit `R → ∞`
  have hbdry : Tendsto (fun R : ℝ ↦ R ^ (-a) * sin (ω * R) / ω) atTop (𝓝 0) := by
    have hb0 : Tendsto (fun R : ℝ ↦ R ^ (-a) / ω) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < a by linarith)).div_const ω
    refine squeeze_zero_norm' ?_ hb0
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hRa : (0 : ℝ) ≤ R ^ (-a) := Real.rpow_nonneg hR.le _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hω0, abs_mul, abs_of_nonneg hRa,
      div_le_div_iff_of_pos_right hω0]
    simpa using mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨Real.neg_one_le_sin (ω * R), Real.sin_le_one (ω * R)⟩) hRa
  have heq := tendsto_nhds_unique
    ((intervalIntegral_tendsto_integral_Ioi (N : ℝ) hcosint tendsto_id).congr' hrel)
    (hbdry.add ((intervalIntegral_tendsto_integral_Ioi (N : ℝ) hsinint
      tendsto_id).const_mul (a / ω)))
  rw [heq, zero_add]
  exact mul_nonneg (div_nonneg (by linarith) hω0.le) hJ

/- **Centered-kernel representation of the `ζ` remainder.** For `1 ≤ N` and `Re s > -(2M+1)`,
the remainder `zetaRemainder` is a single integral of the *centered* even Bernoulli kernel:
`R_M(s, N) = -(s)_{2M+2}/(2M+2)! · ∫_N^∞ (B̃_{2M+2}(x) - B_{2M+2}) x^{-s-(2M+2)} dx`. -/
theorem zetaRemainder_eq_integral_bernoulliFun_fract_sub (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M + 1 : ℝ) < s.re) :
    zetaRemainder s M N
      = -((ascPochhammer ℂ (2 * M + 2)).eval s / ((2 * M + 2)! : ℂ))
          * ∫ x in Set.Ioi (N : ℝ),
              ((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
                * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ)) := by
  rw [zetaRemainder, Complex.eulerMaclaurinRemainderIoi_cpow_eq s (2 * M + 2) N]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set p : ℕ := 2 * M + 2 with hp
  set w : ℂ := -s - (p : ℂ) with hw
  have hwre : w.re < -1 := by
    rw [hw, Complex.sub_re, Complex.neg_re, Complex.natCast_re, hp]; push_cast; linarith
  have hxint : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ w) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt hwre hN0
  have hBint : IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) := Complex.integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN hwre
  have hsubint : IntegrableOn
      (fun x : ℝ ↦ ((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) :=
    (hBint.sub (hxint.const_mul ((bernoulli p : ℝ) : ℂ))).congr
      (.of_forall fun x ↦ by simp only [Pi.sub_apply]; push_cast; ring)
  have hsplit : (∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      = (∫ x in Set.Ioi (N : ℝ),
            ((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w)
        + ((bernoulli p : ℝ) : ℂ) * ∫ x in Set.Ioi (N : ℝ), (x : ℂ) ^ w := by
    rw [show (∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
          = ∫ x in Set.Ioi (N : ℝ),
              (((bernoulliFun p (Int.fract x) : ℝ) - (bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w
                + ((bernoulli p : ℝ) : ℂ) * (x : ℂ) ^ w) from
        setIntegral_congr_fun measurableSet_Ioi (fun x _ ↦ by push_cast; ring),
      integral_add hsubint (hxint.const_mul ((bernoulli p : ℝ) : ℂ)), integral_const_mul]
  rw [hsplit, integral_Ioi_cpow_of_lt hwre hN0]
  have hwone : w + 1 = -s - ((2 * M + 1 : ℕ) : ℂ) := by rw [hw, hp]; push_cast; ring
  have hPp : (ascPochhammer ℂ p).eval s
      = (ascPochhammer ℂ (2 * M + 1)).eval s * (s + ((2 * M + 1 : ℕ) : ℂ)) := by
    rw [show p = (2 * M + 1) + 1 from by lia, ascPochhammer_succ_eval]
  have hpne : (p ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
  have hden : -s - ((2 * M + 1 : ℕ) : ℂ) ≠ 0 := fun h ↦ by
    have hre : (-s - ((2 * M + 1 : ℕ) : ℂ)).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re] at hre
    push_cast at hre; linarith
  rw [hwone, hPp]
  push_cast at hden hpne ⊢
  field_simp
  ring

/- **Weighted averaging bound for the centered kernel.** For `m ≥ 1`, real `a > 1`, and integer
`N ≥ 1`, `∫_N^∞ |B̃_{2m}(x) - B_{2m}| x^{-a} dx ≤ |B_{2m}| ∫_N^∞ x^{-a} dx`. -/
theorem integral_Ioi_abs_bernoulliFun_fract_sub_mul_rpow_le (m : ℕ) (hm : 1 ≤ m) {a : ℝ}
    (ha : 1 < a) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in Set.Ioi (N : ℝ),
        |bernoulliFun (2 * m) (Int.fract x) - (bernoulli (2 * m) : ℝ)| * x ^ (-a)
      ≤ |(bernoulli (2 * m) : ℝ)| * ∫ x in Set.Ioi (N : ℝ), x ^ (-a) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by lia : 0 < N)
  have hxa_neg : -a < -1 := by linarith
  set b : ℝ := (bernoulli (2 * m) : ℝ)
  set Am : ℝ := 2 * ((2 * m)! : ℝ) / (2 * π) ^ (2 * m) with hAm
  have hAm0 : 0 < Am := by rw [hAm]; positivity
  set W : ℝ := ∫ x in Set.Ioi (N : ℝ), x ^ (-a) with hW
  have hweight_int : IntegrableOn (fun x : ℝ ↦ x ^ (-a)) (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hxa_neg hN0
  have hcos_int : ∀ k : ℕ,
      IntegrableOn (fun x ↦ cos (2 * π * (k : ℝ) * x) * x ^ (-a)) (Set.Ioi (N : ℝ)) := fun _ ↦
    integrableOn_Ioi_cos_mul_rpow hxa_neg hN0
  -- the family of nonnegative termwise integrands.
  set f : ℕ → ℝ → ℝ :=
    fun k x ↦ Am / (k : ℝ) ^ (2 * m) * (1 - cos (2 * π * (k : ℝ) * x)) * x ^ (-a) with hf
  have hf_int : ∀ k, IntegrableOn (f k) (Set.Ioi (N : ℝ)) := fun k ↦
    ((hweight_int.sub (hcos_int k)).const_mul (Am / (k : ℝ) ^ (2 * m))).congr <| by
      filter_upwards with x
      simp only [hf, Pi.sub_apply]; ring
  have hf_nonneg : ∀ k, ∀ x ∈ Set.Ioi (N : ℝ), 0 ≤ f k x := fun k x hx ↦ by
    simp only [hf]
    exact mul_nonneg (mul_nonneg (div_nonneg hAm0.le (by positivity))
        (by linarith [Real.cos_le_one (2 * π * (k : ℝ) * x)]))
      (Real.rpow_nonneg (lt_trans hN0 hx).le _)
  -- bound for each termwise integral: `∫ f_k = Am/k^{2m}·(W - Iᶜ) ≤ Am/k^{2m}·W`.
  have hbound : ∀ k, (∫ x in Set.Ioi (N : ℝ), f k x) ≤ Am / (k : ℝ) ^ (2 * m) * W := fun k ↦ by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x _ ↦
      show f k x = Am / (k : ℝ) ^ (2 * m) * (x ^ (-a) - cos (2 * π * (k : ℝ) * x) * x ^ (-a))
        by simp only [hf]; ring, integral_const_mul, integral_sub hweight_int (hcos_int k)]
    exact mul_le_mul_of_nonneg_left
      (by linarith [integral_Ioi_cos_mul_rpow_nonneg (a := a) (N := N) (k := k) ha hN])
      (div_nonneg hAm0.le (by positivity))
  -- summability of the bounding series `∑ Am/k^{2m} · W` and hence of `∑ ∫ f_k`.
  have hsummable_bound : Summable (fun k : ℕ ↦ Am / (k : ℝ) ^ (2 * m) * W) :=
    ((((Real.summable_one_div_nat_pow (p := 2 * m)).mpr (by lia)).mul_left Am).congr
      fun k ↦ by ring).mul_right W
  have hsummable_int : Summable (fun k : ℕ ↦ ∫ x in Set.Ioi (N : ℝ), f k x) :=
    Summable.of_nonneg_of_le
      (fun k ↦ setIntegral_nonneg measurableSet_Ioi (hf_nonneg k)) hbound hsummable_bound
  -- the centered kernel as a nonnegative cosine series.
  have habs : ∀ x : ℝ, |bernoulliFun (2 * m) (Int.fract x) - b|
      = Am * ∑' k : ℕ, (1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m) := fun x ↦ by
    rw [abs_eq_neg_one_pow_mul (centered_kernel_mul_sign_nonneg m hm x),
      bernoulliFun_sub_self_eq_tsum_cos m hm x,
      show ∑' k : ℕ, (1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m)
          = -∑' k : ℕ, (cos (2 * π * (k : ℝ) * x) - 1) / (k : ℝ) ^ (2 * m) from by
        rw [← tsum_neg]; exact tsum_congr fun k ↦ by ring]
    have hsq : (-1 : ℝ) ^ m * (-1) ^ (m + 1) = -1 := by
      rw [← pow_add]; exact Odd.neg_one_pow ⟨m, by ring⟩
    linear_combination
      (Am * ∑' k : ℕ, (cos (2 * π * (k : ℝ) * x) - 1) / (k : ℝ) ^ (2 * m)) * hsq
  -- assemble: Tonelli, then drop the nonnegative cosine integrals.
  calc ∫ x in Set.Ioi (N : ℝ),
        |bernoulliFun (2 * m) (Int.fract x) - b| * x ^ (-a)
      = ∫ x in Set.Ioi (N : ℝ), ∑' k : ℕ, f k x :=
        setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ by
          rw [tsum_congr fun k ↦ show f k x
                = Am * ((1 - cos (2 * π * (k : ℝ) * x)) / (k : ℝ) ^ (2 * m)) * x ^ (-a) by
              simp only [hf]; ring, tsum_mul_right, tsum_mul_left, ← habs x]
    _ = ∑' k : ℕ, ∫ x in Set.Ioi (N : ℝ), f k x :=
        (integral_tsum_of_summable_integral_norm hf_int (hsummable_int.congr fun k ↦
          setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
            (Real.norm_of_nonneg (hf_nonneg k x hx)).symm)).symm
    _ ≤ ∑' k : ℕ, Am / (k : ℝ) ^ (2 * m) * W :=
        hsummable_int.tsum_mono hsummable_bound hbound
    _ = |b| * W := by
        -- `Am · ζ(2m) = (-1)^{m+1} B_{2m} = |B_{2m}|`.
        have hAmζ : (∑' k : ℕ, Am / (k : ℝ) ^ (2 * m)) = (-1 : ℝ) ^ (m + 1) * b := by
          have hpi : ((2 * π) ^ (2 * m) : ℝ) ≠ 0 := by positivity
          have hfac : ((2 * m)! : ℝ) ≠ 0 := by positivity
          rw [tsum_congr fun k : ℕ ↦ div_eq_mul_one_div Am ((k : ℝ) ^ (2 * m)), tsum_mul_left,
            (hasSum_one_div_nat_pow_bernoulli m (by lia)).tsum_eq, hAm]
          field_simp
          ring
        have hnn : 0 ≤ (-1 : ℝ) ^ (m + 1) * b :=
          hAmζ ▸ tsum_nonneg fun k ↦ div_nonneg hAm0.le (by positivity)
        rw [tsum_mul_right, hAmζ, ← abs_eq_neg_one_pow_mul hnn]

/- **The explicit Euler–Maclaurin remainder bound for `ζ`**, `K · ‖t_{M+1}(s,N)‖`, with the
constant `K = ‖s + (2M+1)‖ / (Re s + (2M+1))` and the leading Bernoulli term
`t_{M+1}(s,N) = B_{2M+2}/(2M+2)! · (s)_{2M+1} · N^{-s-(2M+1)}`. -/
noncomputable abbrev zetaRemainderBound (s : ℂ) (M N : ℕ) : ℝ :=
  ‖s + ((2 * M + 1 : ℕ) : ℂ)‖ / (s.re + ((2 * M + 1 : ℕ) : ℝ))
    * ‖((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s
        * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))‖

/- **Borwein error bound.** For `1 ≤ N` and `Re s > -(2M+1)`, the Euler–Maclaurin remainder for
`ζ` is bounded by the first omitted term, scaled by `K = |s+2M+1|/(Re s+2M+1) ≥ 1`
(`thm:zeta_error_bound`). -/
theorem norm_zetaRemainder_le (s : ℂ) (M N : ℕ) (hN : 1 ≤ N) (hs : -(2 * M + 1 : ℝ) < s.re) :
    ‖zetaRemainder s M N‖ ≤ zetaRemainderBound s M N := by
  simp only [zetaRemainderBound]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℝ := s.re + ((2 * M + 2 : ℕ) : ℝ) with ha_def
  have ha : 1 < a := by rw [ha_def]; push_cast; linarith
  set W : ℝ := ∫ x in Set.Ioi (N : ℝ), x ^ (-a) with hW
  -- real part of the complex exponent equals `-a`.
  have hwre : (-s - ((2 * M + 2 : ℕ) : ℂ)).re = -a := by
    rw [ha_def]; simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; push_cast; ring
  have hre1 : (-s - ((2 * M + 1 : ℕ) : ℂ)).re = -(s.re + ((2 * M + 1 : ℕ) : ℝ)) := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; ring
  have hrel : -a + 1 = -(s.re + ((2 * M + 1 : ℕ) : ℝ)) := by rw [ha_def]; push_cast; ring
  -- norm of the Pochhammer prefactor splits via `(s)_{2M+2} = (s)_{2M+1}(s+2M+1)`.
  have hP : ‖(ascPochhammer ℂ (2 * M + 2)).eval s‖
      = ‖(ascPochhammer ℂ (2 * M + 1)).eval s‖ * ‖s + ((2 * M + 1 : ℕ) : ℂ)‖ := by
    rw [show 2 * M + 2 = (2 * M + 1) + 1 from by lia, ascPochhammer_succ_eval, norm_mul]
  -- norm of the first term `t_{M+1}`.
  have ht : ‖((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))‖
      = |(bernoulli (2 * M + 2) : ℝ)| / ((2 * M + 2)! : ℝ)
          * ‖(ascPochhammer ℂ (2 * M + 1)).eval s‖
          * (N : ℝ) ^ (-(s.re + ((2 * M + 1 : ℕ) : ℝ))) := by
    rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * M + 2)! : ℝ)),
      ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hN0, hre1]
  -- value of the weight integral.
  have hWval : W = -(N : ℝ) ^ (-a + 1) / (-a + 1) := by
    rw [hW]; exact integral_Ioi_rpow_of_lt (by linarith : -a < -1) hN0
  -- bound on the centered-kernel integral.
  have hInorm : ‖∫ x in Set.Ioi (N : ℝ),
        ((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
          * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ))‖
      ≤ |(bernoulli (2 * M + 2) : ℝ)| * W := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
      show ‖((bernoulliFun (2 * M + 2) (Int.fract x) : ℝ) - (bernoulli (2 * M + 2) : ℝ) : ℂ)
            * (x : ℂ) ^ (-s - ((2 * M + 2 : ℕ) : ℂ))‖
          = |bernoulliFun (2 * M + 2) (Int.fract x) - (bernoulli (2 * M + 2) : ℝ)| * x ^ (-a) by
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans hN0 hx), hwre]]
    have h3 := integral_Ioi_abs_bernoulliFun_fract_sub_mul_rpow_le (M + 1) (by lia) ha hN
    rwa [show 2 * (M + 1) = 2 * M + 2 from by ring] at h3
  rw [zetaRemainder_eq_integral_bernoulliFun_fract_sub s M N hN hs, norm_mul, norm_neg, norm_div,
    Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left hInorm (by positivity)).trans (le_of_eq ?_)
  rw [hP, ht, hWval, hrel]
  have hFacne : ((2 * M + 2)! : ℝ) ≠ 0 := by positivity
  have hDne : s.re + ((2 * M + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (by push_cast; linarith : (0 : ℝ) < s.re + ((2 * M + 1 : ℕ) : ℝ))
  field_simp

end

end CertificatePort151
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/Complex/RealDeriv.lean -/
/- SOURCE quantitative_sources/compatible_pnt/AlexKontorovich-PrimeNumberTheoremAnd-0a2c672/PrimeNumberTheoremAnd/Auxiliary.lean -/
/- SOURCE quantitative_sources/compatible_pnt/AlexKontorovich-PrimeNumberTheoremAnd-0a2c672/PrimeNumberTheoremAnd/Sobolev.lean -/
/- SOURCE quantitative_sources/compatible_pnt/AlexKontorovich-PrimeNumberTheoremAnd-0a2c672/PrimeNumberTheoremAnd/Fourier.lean -/
/- SOURCE quantitative_sources/compatible_pnt/AlexKontorovich-PrimeNumberTheoremAnd-0a2c672/PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean -/
/- SOURCE quantitative_sources/compatible_pnt/AlexKontorovich-PrimeNumberTheoremAnd-0a2c672/PrimeNumberTheoremAnd/Rectangle.lean -/
/- SOURCE quantitative_sources/compatible_pnt/AlexKontorovich-PrimeNumberTheoremAnd-0a2c672/PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean -/
/- SOURCE quantitative_sources/compatible_pnt/AlexKontorovich-PrimeNumberTheoremAnd-0a2c672/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean -/
/- SOURCE quantitative_sources/compatible_pnt/AlexKontorovich-PrimeNumberTheoremAnd-0a2c672/PrimeNumberTheoremAnd/EulerMaclaurin.lean -/
/- SOURCE quantitative_sources/compatible_pnt/AlexKontorovich-PrimeNumberTheoremAnd-0a2c672/PrimeNumberTheoremAnd/ZetaBounds.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Shift.lean -/
section CertificatePort106
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The Riemann–Siegel contour shift

Moving the slanted contour `Zeta.RiemannSiegel.line` from one half-integer crossing point to a
larger one sweeps across the integers in between, and each of them contributes its residue: the
difference of the two contour integrals is the partial sum `∑ n^{-s}` (`riemann_siegel.tex`,
`sec:rs_shift`).

The argument is carried out in the rotated coordinate `z = e^{iπ/4} x`, in which the slanted lines
become the *vertical* lines `Re z = a/√2` and the contour becomes an honest axis-parallel
rectangle; that is what lets it reuse `PrimeNumberTheoremAnd`'s rectangle residue calculus rather
than developing parallelogram contours. It suffices to cross one integer at a time, and three
inputs then feed the single-pole rectangle theorem `ResidueTheoremOnRectangleWithSimplePole'`:

* the integrand is holomorphic on the closed rectangle minus the pole — the branch
  `Zeta.RiemannSiegel.slantCpow` because the rectangle lies in the rotated right half-plane, and
  the kernel `Zeta.RiemannSiegel.kernel` because the only integer in a slanted strip of width one
  is the one being crossed;
* the pole is simple, with residue `n^{-s}/(2πi)`;
* the horizontal sides vanish as the truncation height `H` grows: there the Gaussian factor
  `e^{iπx²}` contributes `e^{-π(H² − ξ²)}`, while the power and the reciprocal of the kernel's
  denominator grow at most exponentially in `H`.

The vertical sides are affine reparametrisations of truncations of the contour integral, so they
converge to `I(s, a)` and `I(s, b)` by `Zeta.RiemannSiegel.integrable_contourIntegrand` and
dominated convergence.

The rectangle apparatus is developed for an arbitrary integrand
(`Zeta.RiemannSiegel.slantIntegral_sub_slantIntegral_of_pole`, and the three lemmas feeding it),
because the first-order chapter deforms the contour of the *model* integrand
`Zeta.RiemannSiegel.modelFun` across the same kind of strip; the Riemann–Siegel results below are
its corollaries. Two of those lemmas — `Zeta.RiemannSiegel.tendsto_HIntegral_of_norm_le` and
`Zeta.RiemannSiegel.tendsto_RectangleIntegral_of_tendsto` — mention no Riemann–Siegel object at all,
and live here only because `PrimeNumberTheoremAnd`'s `HIntegral` and `RectangleIntegral` are
declared in the root namespace of a package this project does not own.

## Main results

* `Zeta.RiemannSiegel.rotatedFun`: the rotation `f ↦ e^{-iπ/4} f(e^{-iπ/4} ·)`, together with its
  evaluation, modulus, holomorphy and residues;
* `Zeta.RiemannSiegel.rotatedIntegrand`: the integrand in the rotated coordinate;
* `Zeta.RiemannSiegel.tendsto_sub_mul_rotatedIntegrand`: its simple poles and their residues;
* `Zeta.RiemannSiegel.norm_integrand_le`: a Gaussian bound for the integrand off the real axis;
* `Zeta.RiemannSiegel.tendsto_HIntegral_rotatedIntegrand`,
  `Zeta.RiemannSiegel.tendsto_VIntegral_rotatedIntegrand`: the four sides of the rectangle in the
  limit `H → ∞`;
* `Zeta.RiemannSiegel.tendsto_RectangleIntegral_rotatedIntegrand`: the four together, converging to
  the difference of the two contour integrals;
* `Zeta.RiemannSiegel.slantIntegral_sub_slantIntegral_of_pole`: the one-step shift for an arbitrary
  integrand;
* `Zeta.RiemannSiegel.contourIntegral_sub_contourIntegral_eq_sum_cpow_neg`: the contour-shift
  identity `I(s, k + ½) − I(s, j + ½) = ∑_{j < n ≤ k} n^{-s}`;
* `Zeta.RiemannSiegel.sum_cpow_neg_eq_contourIntegral_sub_contourIntegral`: its corollary
  `∑_{n = 1}^{k} n^{-s} = I(s, k + ½) − I(s, ½)`.
-/
section


open Asymptotics Complex Filter MeasureTheory Topology

open scoped Real

namespace Zeta.RiemannSiegel

/- The rotation by `-π/4` has modulus one. -/
noncomputable def rotatedFun (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  exp (-((π / 4 : ℝ) * I)) * f (exp (-((π / 4 : ℝ) * I)) * z)

/- **A rotated integrand, evaluated at a rotated point.** -/
noncomputable def rotatedIntegrand (s : ℂ) : ℂ → ℂ := rotatedFun (integrand s)

/- **The rotated integrand, evaluated at a rotated point.** -/
end Zeta.RiemannSiegel

end

end CertificatePort106
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/ModelShift.lean -/
section CertificatePort107
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The unit shift for the Riemann–Siegel model integral

The second of the two functional equations that pin the model integral `M(p)` of
`Zeta.RiemannSiegel.modelIntegral` algebraically is the **unit shift**

`M(p) + M(p + 1) = e^{2πip²}`

(`riemann_siegel_first.tex`, `lem:rsf_unit_shift`). It is the only contour deformation of the
first-order chapter: moving the contour from `L(1/2)` out to `L(3/2)` crosses the single pole
`v = 1` of the kernel denominator, and the translation `v ↦ v + 1` carries the far contour back onto
the near one at the cost of a sign and a unit shift in `p`
(`Zeta.RiemannSiegel.modelFun_add_one`).

The rectangle apparatus is not redone here: it is the general
`Zeta.RiemannSiegel.slantIntegral_sub_slantIntegral_of_pole` of `Shift.lean`, whose hypotheses are
supplied by the Gaussian bound on the horizontal sides and by the residue at the pole. Both are
easier than their order-zero analogues, because the model integrand carries no branch of a power:
it is holomorphic off `ℤ` outright, and its modulus is a bare Gaussian.

## Main results

* `Zeta.RiemannSiegel.rotatedModelFun`: the model integrand in the rotated coordinate of
  `Shift.lean`;
* `Zeta.RiemannSiegel.tendsto_sub_mul_rotatedModelFun`: its simple poles and their residues;
* `Zeta.RiemannSiegel.tendsto_HIntegral_rotatedModelFun`: the horizontal sides vanish;
* `Zeta.RiemannSiegel.modelIntegral_add_modelIntegral_add_one`: the unit shift.
-/
section


open Complex Filter MeasureTheory Topology

open scoped Real

namespace Zeta.RiemannSiegel

/- The **model integrand in rotated coordinates**, `F(z) = e^{-iπ/4} m_p(e^{-iπ/4} z)`. -/
noncomputable def rotatedModelFun (p : ℂ) : ℂ → ℂ := rotatedFun (modelFun p)

/- **The rotated model integrand, evaluated at a rotated point.** -/
end Zeta.RiemannSiegel

end

end CertificatePort107
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Correction.lean -/
section CertificatePort108
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The Riemann–Siegel correction function

The half shift `Zeta.RiemannSiegel.modelIntegral_add_half` and the unit shift
`Zeta.RiemannSiegel.modelIntegral_add_modelIntegral_add_one` are incompatible in a useful way:
iterating the half shift twice computes `M(p + 1)` from `M(p)` with coefficient `e^{4πip}`, whereas
the unit shift computes it with coefficient `−1`. At each fixed `p` these are two linear equations
in the two unknowns `M(p)` and `M(p + 1)`, so eliminating `M(p + 1)` determines `M(p)`
**algebraically** — with no analytic continuation, no Liouville argument and no growth estimate
(`riemann_siegel_first.tex`, `thm:rsf_model_closed` and `rem:rsf_why_algebraic`).

The resulting closed form is stated in product form, never as a quotient: the coefficient
`1 + e^{4πip}` vanishes exactly where `cos (2πp)` does, and there the right-hand side vanishes with
it. For the same reason the **correction function** `Ψ` of `def:rsf_correction`, which carries the
whole of the first-order correction to Hardy's function, is defined through `M` rather than through
the classical quotient `cos (2π(p² − p − 1/16)) / cos (2πp)`.

## Main results

* `Zeta.RiemannSiegel.two_mul_cos_mul_modelIntegral`:
  `2 cos(2πp) M(p) = e^{2πi(p² − p)} + √2 e^{5iπ/8} sin(πp)`;
* `Zeta.RiemannSiegel.correction`: the correction function `Ψ(p) = 2 Re(e^{−iπ/8} M(p))`;
* `Zeta.RiemannSiegel.cos_mul_correction`: `cos(2πp) Ψ(p) = cos(2π(p² − p − 1/16))`;
* `Zeta.RiemannSiegel.abs_correction_le`: `|Ψ(p)| ≤ e^{π/4}` on `[0, 1]`;
* `Zeta.RiemannSiegel.iteratedDeriv_three_correction`: `Ψ''' = 2 Re(e^{−iπ/8} M''')`;
* `Zeta.RiemannSiegel.neg_iteratedDeriv_three_correction_div_eq`: the linear Riemann–Siegel
  coefficient `C₁(p) = −Ψ'''(p)/(96π²)` as a combination of the moments `N₁` and `N₃`.
-/
section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/- **The closed form of the model integral** (`riemann_siegel_first.tex`,
`thm:rsf_model_closed`): `2 cos(2πp) M(p) = e^{2πi(p² − p)} + √2 e^{5iπ/8} sin(πp)`. It is stated in
product form because the factor `1 + e^{4πip}` eliminated in its proof vanishes exactly where
`cos (2πp)` does. -/
private noncomputable def modelCorrection (q : ℂ) : ℂ :=
  2 * exp (-((π / 8 : ℝ) * I)) * modelIntegral q (1 / 2)

end Zeta.RiemannSiegel

end

end CertificatePort108
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/Complex/Exponential.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Linear.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Saddle.lean -/
section CertificatePort111
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The saddle-point reduction of the Riemann–Siegel integral

The Riemann–Siegel contour integral `I(s, a)` of `Zeta.RiemannSiegel.contourIntegral` is taken over
the line `L(a)` with `a = ν + 1/2`, `ν = ⌊√T⌋`, `T = t/2π`, which passes within `1/2` of the saddle
`√T` of the integrand. Writing `p = √T - ν` and `v = x - ν`, the substitution `x ↦ x - ν` carries
`L(a)` onto `L(1/2)`, the contour of the model integral `M(p)` of
`Zeta.RiemannSiegel.modelIntegral`, and the true integrand becomes the model integrand times
`e^Δ`, where

`Δ(x) = iπx² - s Log x + (log T)/4 + i(ϑ(t) + π/8) - 2πi(x - √T)²`

is the **saddle discrepancy** (`riemann_siegel_first.tex`, `def:rsf_discrepancy`). Since `Δ` is
*defined* as this difference of logarithms, the factorisation
`Zeta.RiemannSiegel.integrand_eq_modelFun_mul` is exact and unconditional; all the analytic content
of the chapter is then the single statement that `Δ` is small, which is what makes `√T` a saddle:
the terms of `Δ` linear in `x - √T` cancel, leaving
`Δ = -½ log (1 + u) - 2πiT (log (1 + u) - u + u²/2)` with `u = (x - √T)/√T`, hence
`|Δ| ≲ |x - √T|³/√T`.

## Main results

* `Zeta.RiemannSiegel.norm_modelIntegrand_le_exp_neg_mul_sq`: the Gaussian majorant for the model
  integrand along `L(½)`;
* `Zeta.RiemannSiegel.leadingTheta`: the leading Stirling phase `ϑ(t)`;
* `Zeta.RiemannSiegel.saddleDiscrepancy`, `Zeta.RiemannSiegel.saddleFactor`: the discrepancy `Δ` and
  the constant `(-1)^ν T^{-1/4} e^{-i(ϑ + π/8)}` accompanying it;
* `Zeta.RiemannSiegel.integrand_eq_modelFun_mul`: the exact factorisation of the integrand;
* `Zeta.RiemannSiegel.norm_modelIntegrand_mul_exp_saddleDiscrepancy`: the modulus of the
  renormalised integrand;
* `Zeta.RiemannSiegel.contourIntegral_eq_modelIntegrand_mul`,
  `Zeta.RiemannSiegel.contourIntegral_sub_mul_modelIntegral`: its integrated forms, the second
  isolating the error `I(s, a) - saddleFactor * M(p)`;
* `Zeta.RiemannSiegel.saddleDiscrepancy_eq_log_sub_logTaylor`,
  `Zeta.RiemannSiegel.saddleDiscrepancy_eq_tsum`: the two forms of the series expansion of `Δ`;
* `Zeta.RiemannSiegel.norm_saddleDiscrepancy_le`: the explicit bound
  `|Δ| ≤ (|y| + 4π|y|³/3)/√T` for `|y| ≤ √T/2`, `y = x - √T`;
* `Zeta.RiemannSiegel.saddleLinear`, `Zeta.RiemannSiegel.norm_saddleLinear_le`,
  `Zeta.RiemannSiegel.norm_saddleDiscrepancy_sub_linear_le`: the polynomial
  `P₁(y) = -y/2 - 2πiy³/3` carrying the `T^{-1/2}` term of `Δ`, its modulus
  `|P₁(y)| ≤ |y|/2 + 2π|y|³/3`, and the resulting `|Δ - P₁(y)/√T| ≤ (|y|²/2 + π|y|⁴)/T`;
* `Zeta.RiemannSiegel.norm_saddleDiscrepancy_le'`,
  `Zeta.RiemannSiegel.exp_norm_saddleDiscrepancy_mul_exp_le`: the bound `|Δ| ≤ ½ + 2π|y|²/3` and
  the exponent budget it buys, `e^{|Δ|}e^{-2π|y|²} ≤ e^{1/2}e^{-4π|y|²/3}`.

`saddleLinear` and `exp_norm_saddleDiscrepancy_mul_exp_le` are what the sharp first-order estimate
of `sec:rsf_sharp` runs on: it retains the `T^{-1/2}` term instead of bounding it away, and
integrates the remainder against the narrowed Gaussian `e^{-4π|y|²/3}` that survives `e^{|Δ|}`.
-/
section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/- **The Gaussian majorant for the model integrand along `L(½)`**: `|m_p| ≤ e^{π/4}e^{-4πξ²}/√2`
in the centred parameter `ξ = w + (½ - p)/2`, whenever the fractional part `p` lies within `½` of
the contour. -/
noncomputable def leadingTheta (t : ℝ) : ℝ :=
  t / 2 * Real.log (t / (2 * π)) - t / 2 - π / 8

/- **The leading phase, shorn of its constant term**, `T = t/2π`. -/
noncomputable def saddleDiscrepancy (t : ℝ) (x : ℂ) : ℂ :=
  π * I * x ^ 2 - (1 / 2 + t * I) * slantLog x + (Real.log (t / (2 * π)) : ℂ) / 4
    + I * ((leadingTheta t : ℂ) + π / 8)
    - 2 * π * I * (x - (Real.sqrt (t / (2 * π)) : ℂ)) ^ 2

/- The **saddle factor** `(-1)^ν T^{-1/4} e^{-i(ϑ(t) + π/8)}` with `T = t/2π`, the constant of
modulus `T^{-1/4}` relating the Riemann–Siegel integral to the model integral. -/
noncomputable def saddleFactor (t : ℝ) (ν : ℕ) : ℂ :=
  (-1) ^ ν * ((t / (2 * π)) ^ (-(1 / 4) : ℝ) : ℝ)
    * exp (-(I * ((leadingTheta t : ℂ) + π / 8)))

noncomputable def saddleLinear (y : ℂ) : ℂ := -(y / 2) - 2 * π * I / 3 * y ^ 3

/- **The linear part of the saddle discrepancy is a cubic in `|y|`.** -/
end Zeta.RiemannSiegel

end

end CertificatePort111
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/InnerSharp.lean -/
section CertificatePort112
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The sharp inner saddle-point estimate

The crude inner estimate `Zeta.RiemannSiegel.norm_integral_inner_le` bounds `|e^Δ - 1|` by `2|Δ|`
and integrates in absolute value, discarding the cancellation that produces the next classical
Riemann–Siegel coefficient. This file keeps that term instead: it subtracts the `T^{-1/2}`-linear
part `P₁(y)/√T` of the saddle discrepancy — `Zeta.RiemannSiegel.saddleLinear` — before estimating,
and so bounds the *second-order* remainder (`riemann_siegel_first.tex`, `lem:rsf_inner_sharp`).

Two features distinguish it from the crude chain. The splitting radius is
`Zeta.RiemannSiegel.sharpSplitRadius`, proportional to `√T` rather than to `T^{1/12}`, chosen so
that `|y| ≤ √T/2` holds on the whole inner region and the Taylor radius `1/2` of
`Zeta.RiemannSiegel.norm_saddleDiscrepancy_le` is available with no further hypothesis. And the two
contributions are integrated against *different* Gaussians: the linear discrepancy against the
model Gaussian `e^{-4πξ²}`, and the exponential remainder against the widened `e^{-8πξ²/3}` left
over after `e^{|Δ|}` has eaten a third of the exponent.

## Main results

* `Zeta.RiemannSiegel.sharpSplitRadius`: the splitting radius `W = (√T - 1)/(2√2)`;
* `Zeta.RiemannSiegel.integrable_modelIntegrand_mul_saddleLinear_div`: absolute convergence of the
  linear term against the model integrand;
* `Zeta.RiemannSiegel.norm_integral_inner_sub_linear_le`
  (`riemann_siegel_first.tex`, `lem:rsf_inner_sharp`): over `|w| ≤ W`, the model integrand against
  `e^Δ - 1 - P₁(y)/√T` contributes at most `(299/100) T^{-1}`.
-/
section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/- The **splitting radius of the sharp saddle estimate** `W = (√T - 1)/(2√2)`, `T = t/2π`
(`riemann_siegel_first.tex`, `sec:rsf_sharp`). -/
noncomputable def sharpSplitRadius (t : ℝ) : ℝ :=
  (Real.sqrt (t / (2 * π)) - 1) / (2 * Real.sqrt 2)

/- An explicit upper bound for `√2`. -/
end Zeta.RiemannSiegel

end

end CertificatePort112
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/LinearTail.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Phase.lean -/
section CertificatePort114
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The Gaussian majorant for the Riemann–Siegel phase

Along the slanted contour `Zeta.RiemannSiegel.line a` the modulus of the Riemann–Siegel integrand
`x^{-1/2-it} e^{iπx²}` is `‖x‖^{-1/2} e^{φ(w)}`, where
`φ(w) = t · slantArg (L(a)(w)) - 2πw(a + w)` (`riemann_siegel.tex`, `sec:rs_bound`). This file
bounds `φ` by a Gaussian, `φ(w) ≤ -πw² + B|w|`, which makes the shifted contour integral small: the
constant `B = 2π|T - a²|/a` measures how far the crossing point `a` sits from the saddle `√T`, and
vanishes when the contour crosses exactly at the saddle.

Everything reduces to elementary inequalities for `arctan`, stated here for the normalised argument
`g(r) = arctan(1 + 2r) - π/4` of the contour point `L(a)(ra)`, which is independent of `a` — whence
the name `Zeta.RiemannSiegel.lineArg`.

That majorant discards a factor `4` in the Gaussian exponent, which is irrelevant when the region
of interest starts at `|w| ≍ T^{1/12}` and fatal when it starts at `|w| ≍ √T/(2√2)`, so the sharp
forms are recorded here as well (`riemann_siegel.tex`, `lem:rs_arctan_sharp` onwards). The gain
comes from never estimating `g` itself but only the *defect* `ψ(r) = r - g(r)`, in terms of which
`λ g - r - r² = ε g - r² - ψ` identically, with `ε = λ - 1`. The sharp phase bound splits at
`w = -a/2`, and is sharp to leading order on the half carrying the saddle: at `ε = 0` and `|w| ≪ a`
it reads `φ(w) ≤ -4πw² + O(w³/a)`, against the truth `φ(w) = -4πw² + O(w³/a)`. The linear term
`B|w|` is the same in both, and cannot be improved: it is the genuine displacement of the crossing
point from the saddle.

## Main results

* `Zeta.RiemannSiegel.lineArg_eq_arctan`: the Möbius form `g(r) = arctan(r/(1 + r))`;
* `Zeta.RiemannSiegel.strictMono_lineArg`: `g` is strictly increasing, with `g(0) = 0`;
* `Zeta.RiemannSiegel.lineArg_le`, `Zeta.RiemannSiegel.lineArg_le_self`: the quadratic majorant
  `g(r) ≤ r + r²/2`, and `g(r) ≤ r` for `r ≥ 0`;
* `Zeta.RiemannSiegel.lineArg_le_sub_div`: the sharp majorant `ψ(r) ≥ r²/(1 + |r|)`, `r ≥ -½`;
* `Zeta.RiemannSiegel.mul_lineArg_sub_le`: the perturbed majorant
  `λ g(r) - r - r² ≤ -r²/2 + |λ - 1| |r|` for `|λ - 1| ≤ 1`;
* `Zeta.RiemannSiegel.mul_lineArg_sub_le'`,
  `Zeta.RiemannSiegel.mul_lineArg_sub_le_of_le_neg_half`: the sharp perturbed majorants on the two
  ranges `r ≥ -½` and `r ≤ -½`;
* `Zeta.RiemannSiegel.phase`, `Zeta.RiemannSiegel.norm_slantCpow_mul_exp_eq_phase`: the exponent
  `φ` and the factorisation of the integrand's modulus through it;
* `Zeta.RiemannSiegel.phase_le`: the Gaussian majorant `φ(w) ≤ -πw² + B|w|`;
* `Zeta.RiemannSiegel.phase_le'`, `Zeta.RiemannSiegel.phase_le_of_le_neg_half`: the sharp Gaussian
  majorants `φ(w) ≤ -2πw² - (1 - |ε|) 2πaw²/(a + |w|) + B|w|` and `φ(w) ≤ -πw²`.
-/
section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/- The **normalised argument along the slanted contour**, `g(r) = arctan(1 + 2r) - π/4`: the value
of `Zeta.RiemannSiegel.slantArg` at the contour point `L(a)(ra)`, which depends only on `r`. -/
noncomputable def lineArg (r : ℝ) : ℝ := Real.arctan (1 + 2 * r) - π / 4

@[simp]
theorem lineArg_zero : lineArg 0 = 0 := by simp [lineArg, Real.arctan_one]

noncomputable def phase (t a w : ℝ) : ℝ := t * slantArg (line a w) - 2 * π * w * (a + w)

/- **The Riemann–Siegel phase exponentiates to the modulus of the integrand.** -/
end Zeta.RiemannSiegel

end

end CertificatePort114
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Bound.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Inner.lean -/
section CertificatePort116
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The inner saddle-point estimate

The error committed by replacing the Riemann–Siegel integrand by its Gaussian model at the saddle is
`Zeta.RiemannSiegel.contourIntegral_sub_mul_modelIntegral`: the model integrand integrated against
`e^Δ - 1`, with `Δ` the saddle discrepancy `Zeta.RiemannSiegel.saddleDiscrepancy`. That integral is
estimated by splitting the contour at `|w| = W`, `W = T^{1/12}` the **splitting radius**
`Zeta.RiemannSiegel.splitRadius`; this file treats the inner region `|w| ≤ W`
(`riemann_siegel_first.tex`, `lem:rsf_inner`).

The exponent `1/12` enters only through `splitRadius_pow_six`, `√T = W^6`, in the parametrisation of
which every estimate on the inner region becomes a polynomial inequality in `W` alone.

## Main results

* `Zeta.RiemannSiegel.splitRadius`: the splitting radius `W = T^{1/12}`;
* `Zeta.RiemannSiegel.norm_integral_inner_le` (`riemann_siegel_first.tex`, `lem:rsf_inner`): the
  inner integral is at most `21 T^{-1/2}`.
-/
section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/- The **splitting radius** `W = T^{1/12}`, `T = t/2π` (`riemann_siegel_first.tex`,
`sec:rsf_saddle`). -/
noncomputable def splitRadius (t : ℝ) : ℝ := (t / (2 * π)) ^ ((12 : ℝ)⁻¹)

end Zeta.RiemannSiegel

end

end CertificatePort116
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Outer.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/OuterSharp.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Theta.lean -/
section CertificatePort119
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The leading Stirling form of the Riemann–Siegel theta function

The saddle-point reduction of `Zeta/RiemannSiegel/FirstOrder.lean` produces the *Stirling* phase
`ϑ(t) = (t/2) log (t/2π) - t/2 - π/8` (`Zeta.RiemannSiegel.leadingTheta`), whereas the exact
Riemann–Siegel formula produces the true `θ = riemannSiegelTheta`. This file quantifies the
difference (`riemann_siegel_first.tex`, `lem:rsf_theta`).

The error splits into two *independent* contributions at `w_t = ¼ + it/2`, and both must be
bounded, since the order-`2` Stirling polynomial itself contributes at orders `t^{-1}` and
`t^{-3}`:

* the elementary part `Im S_2(w_t) - (t/2) log π - ϑ(t)`, whose expansion begins `1/(48t)` —
  note that `Re w_t = ¼` also contributes at order `t^{-1}` (for instance
  `Im 1/(12 w_t) = -(t/2)/(12‖w_t‖²)` is *not* `-1/(6t)`), so every such contribution is
  collected before any estimate is made;
* the remainder `Im ρ_2(w_t)`, controlled by the `‖·‖`-form
  `Complex.Stirling.norm_logGammaRemainderIoi_le'`. The project's
  `riemannSiegelThetaStirlingErrorBound` records the weaker `(¼+N)^{-2M}` form, which uses only
  `Re w_t` and is therefore bounded in `t`.

Both halves hold for every `t > 0`, so the sharp estimate carries no threshold; the two forms that
do carry one (`t ≥ 32π` and `t ≥ 10³`) are deduced from it.

## Main results

* `Zeta.RiemannSiegel.abs_riemannSiegelTheta_sub_leading_sub_inv_le`
  (`riemann_siegel_first.tex`, `lem:rsf_theta_sharp`):
  `|θ(t) - ϑ(t) - 1/(48t)| ≤ 319/(2880t³) + 12/t⁴` for every `t > 0`, which is what pins the
  coefficient of `t^{-1}`;
* `Zeta.RiemannSiegel.abs_riemannSiegelTheta_sub_leading_le'`: `|θ(t) - ϑ(t)| ≤ 101/(4800t)` for
  `t ≥ 32π`, the threshold at which the sharp first-order formula applies it;
* `Zeta.RiemannSiegel.abs_riemannSiegelTheta_sub_leading_le`
  (`riemann_siegel_first.tex`, `lem:rsf_theta`): `|θ(t) - ϑ(t)| ≤ 1/(40t)` for `t ≥ 10³`.
-/
section


open Complex Complex.Stirling

open scoped Nat Real

namespace Zeta.RiemannSiegel

-- A `def` rather than an `abbrev` deliberately: the estimates below drive `simp only`, `norm_num`
-- and `positivity` at goals mentioning `w_t`, and they stay legible only while `w_t` is an atom.
/- The **Stirling argument** `w_t = ¼ + i t/2` of the Riemann–Siegel theta function. -/
private noncomputable def thetaArg (t : ℝ) : ℂ := 1 / 4 + Complex.I * (t / 2)

end Zeta.RiemannSiegel

end

end CertificatePort119
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/SpecialFunctions/Sqrt.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Entire.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/SpecialFunctions/GammaIntegral.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Hankel.lean -/
section CertificatePort123
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The Hankel ray integral

The contour `Zeta.RiemannSiegel.line` through the *origin* is the diagonal
`L(0)(w) = √2 w e^{iπ/4}`, whose two halves are the Hankel rays `ρ e^{iπ/4}` and `ρ e^{-3iπ/4}`.
Along them the Riemann–Siegel integrand collapses to a single integral over the positive reals
(`riemann_siegel_zero.tex`, `lem:rsz_hankel`): `I(s, 0) = -e^{iπ(1+s)/4} sin (πs/2) Φ(s)`, where
`Φ(s) = ∫_0^∞ ρ^{-s} e^{-πρ²} / sin (πρ e^{iπ/4}) dρ`.

The hypothesis `Re s < 0` is exactly what makes `Φ` converge: the kernel has a simple pole at the
origin, so the integrand is `O(ρ^{-Re s - 1})` there. It is therefore also the hypothesis under
which `L(0)` — unlike every contour of `Zeta/RiemannSiegel/Shift.lean` — may be used at all,
passing as it does straight through that pole.

This file does *not* deform the contour: what is proved here concerns `I(s, 0)`, and identifying it
with `I(s, ½)` is separate.

## Main results

* `Zeta.RiemannSiegel.hankelIntegrand`, `Zeta.RiemannSiegel.hankelIntegral`: the integrand of `Φ`
  and `Φ` itself;
* `Zeta.RiemannSiegel.norm_hankelIntegrand_le`: the bound `O(ρ^{-Re s - 1} e^{-πρ²})`;
* `Zeta.RiemannSiegel.integrableOn_hankelIntegrand`: absolute convergence of `Φ(s)` for
  `Re s < 0`;
* `Zeta.RiemannSiegel.exp_pi_mul_I_mul_ofReal_mul_exp_pi_div_four_mul_I_sq`: the Gaussian factor
  of the kernel is real on the ray;
* `Zeta.RiemannSiegel.integrand_ofReal_mul_exp_pi_div_four_mul_I`,
  `Zeta.RiemannSiegel.integrand_neg_ofReal_mul_exp_pi_div_four_mul_I`: the integrand on the two
  rays;
* `Zeta.RiemannSiegel.integrable_contourIntegrand_zero`: absolute integrability along `L(0)`;
* `Zeta.RiemannSiegel.contourIntegral_zero_eq_neg_exp_mul_sin_mul_hankelIntegral`:
  `I(s, 0) = -e^{iπ(1+s)/4} sin (πs/2) Φ(s)`.
-/
section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/- The **Hankel ray integrand** `ρ ↦ ρ^{-s} e^{-πρ²} / sin (πρ e^{iπ/4})`, the restriction of the
Riemann–Siegel integrand to the diagonal ray with the constant phases stripped off. -/
noncomputable def hankelIntegrand (s : ℂ) (ρ : ℝ) : ℂ :=
  (ρ : ℂ) ^ (-s) * exp (-(π * (ρ : ℂ) ^ 2)) / sin (π * ρ * exp ((π / 4 : ℝ) * I))

/- The **Hankel ray integral** `Φ(s) = ∫_0^∞ ρ^{-s} e^{-πρ²} / sin (πρ e^{iπ/4}) dρ`. The
integrand is integrable only for `Re s < 0` (`integrableOn_hankelIntegrand`); elsewhere the value
is the junk value `0`. -/
noncomputable def hankelIntegral (s : ℂ) : ℂ :=
  ∫ ρ in Set.Ioi (0 : ℝ), hankelIntegrand s ρ

/-! ### Convergence -/

/- **Linear lower bound for the kernel denominator along the diagonal ray.** -/
end Zeta.RiemannSiegel

end

end CertificatePort123
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Deform.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Mirror.lean -/
section CertificatePort125
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The mirror Riemann–Siegel contour integral

Siegel's identity pairs the Riemann–Siegel contour integral `I(s, a)` of
`Zeta/RiemannSiegel/Integral.lean` with its reflection across the real axis,
`Ĩ(s, a) = conj (I(conj s, a))` (`riemann_siegel_zero.tex`, `def:rsz_mirror`). Taking the mirror by
conjugation rather than by a second contour is what keeps it free of a second branch of the power:
`Ĩ` needs no contour and no integral of its own, and inherits everything already proved about `I`.

The functional-equation factor `χ` that completes Siegel's identity is *not* Riemann–Siegel
mathematics and lives in `Zeta/Analysis/SpecialFunctions/GammaFactor.lean`.

## Main results

* `Zeta.RiemannSiegel.mirrorContourIntegral`, `Zeta.RiemannSiegel.mirrorHankelIntegral`: the
  mirrors of `Zeta.RiemannSiegel.contourIntegral` and `Zeta.RiemannSiegel.hankelIntegral`;
* `Zeta.RiemannSiegel.mirrorContourIntegral_one_sub_eq`:
  `Ĩ(1-s, ½) = -e^{-iπ(2-s)/4} cos(πs/2) Φ̃(1-s)` for `Re s > 1`;
* `Zeta.RiemannSiegel.mirrorHankelIntegral_eq_integral`: `Φ̃` as an honest integral,
  `Φ̃(s) = ∫_0^∞ ρ^{-s} e^{-πρ²} / sin (πρ e^{-iπ/4}) dρ`.
-/
section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/- The **mirror Riemann–Siegel contour integral** `Ĩ(s, a) = conj (I(conj s, a))`. -/
noncomputable def mirrorContourIntegral (s : ℂ) (a : ℝ) : ℂ :=
  starRingEnd ℂ (contourIntegral (starRingEnd ℂ s) a)

/- The **mirror Hankel ray integrand** `ρ ↦ ρ^{-s} e^{-πρ²} / sin (πρ e^{-iπ/4})`, the pointwise
conjugate of `Zeta.RiemannSiegel.hankelIntegrand`. -/
noncomputable def mirrorHankelIntegrand (s : ℂ) (ρ : ℝ) : ℂ :=
  (ρ : ℂ) ^ (-s) * exp (-(π * (ρ : ℂ) ^ 2)) / sin (π * ρ * exp (-((π / 4 : ℝ) * I)))

/- The **mirror Hankel ray integral** `Φ̃(s) = conj (Φ(conj s))`. -/
noncomputable def mirrorHankelIntegral (s : ℂ) : ℂ :=
  starRingEnd ℂ (hankelIntegral (starRingEnd ℂ s))

/- **The mirror Hankel ray integrand is the conjugate of the Hankel ray integrand.** -/
end Zeta.RiemannSiegel

end

end CertificatePort125
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Mordell.lean -/
section CertificatePort126
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# Riemann's Mordell integral

Siegel's identity rests on one auxiliary function of a *complex* parameter `u`: the integral

`N(u, a) = ∫_{L(a)} e^{-2πiux} G(x) dx`

of the Riemann–Siegel kernel `Zeta.RiemannSiegel.kernel` against an exponential rather than
against a power, taken along the slanted contour `Zeta.RiemannSiegel.line`
(`riemann_siegel_zero.tex`, `sec:rsz_mordell`). This is the integral studied by Kronecker and
Mordell, at the parameter Riemann needed.

Unlike the contour integral `I(s, a)` of `Zeta/RiemannSiegel/Integral.lean` it can be evaluated in
closed form by elementary means, because the exponential — unlike the power — interacts with *both*
structural symmetries of `G`: the quasi-periodicity `G(x + 1) = e^{2πix} G(x)`, and the simple pole
at every integer. Each symmetry yields one of the two difference equations below.

The pole shift reuses the rectangle apparatus of `Zeta/RiemannSiegel/Shift.lean` unchanged, that
apparatus taking the integrand as a parameter; comparing `L(½)` with `L(3/2)` rather than with
`L(-½)` keeps the crossed pole at `n = 1 > 0`, inside its existing hypotheses.

## Main results

* `Zeta.RiemannSiegel.mordellIntegrand`, `Zeta.RiemannSiegel.mordellIntegral`: the integrand
  `x ↦ e^{-2πiux} G(x)` and the integral `N(u, a)` (`def:rsz_mordell`);
* `Zeta.RiemannSiegel.integrable_mordellIntegrand`: absolute convergence (`lem:rsz_mordell_conv`);
* `Zeta.RiemannSiegel.mordellIntegral_sub_mordellIntegral_add_one`: the Gaussian difference
  equation `N(u, a) - N(u + 1, a) = e^{iπ/4} e^{-iπ(u + ½)²}` (`lem:rsz_mordell_gauss`);
* `Zeta.RiemannSiegel.mordellIntegral_sub_exp_mul_mordellIntegral_add_one`: the pole difference
  equation `N(u) - e^{2πiu} N(u + 1) = 1` (`lem:rsz_mordell_pole`);
* `Zeta.RiemannSiegel.mordellIntegral_eq`: the closed form
  `N(u) = (e^{-iπu²} - e^{-iπu}) / (e^{iπu} - e^{-iπu})` (`thm:rsz_mordell`).
-/
section


open Complex Filter MeasureTheory Topology

open scoped Real

namespace Zeta.RiemannSiegel

/- The **Mordell integrand** `x ↦ e^{-2πiux} G(x)`, the Riemann–Siegel kernel against an
exponential in place of a power. -/
noncomputable def mordellIntegrand (u x : ℂ) : ℂ :=
  exp (-(2 * π * I * u * x)) * kernel x

/- **Riemann's Mordell integral** `N(u, a) = ∫_{L(a)} e^{-2πiux} G(x) dx`, taken along the slanted
contour `Zeta.RiemannSiegel.line`. -/
noncomputable def mordellIntegral (u : ℂ) (a : ℝ) : ℂ :=
  slantIntegral (mordellIntegrand u) a

/- The **Mordell integrand in rotated coordinates**, `F(z) = e^{-iπ/4} f(e^{-iπ/4} z)` for
`f(x) = e^{-2πiux} G(x)`. -/
noncomputable def rotatedMordellIntegrand (u : ℂ) : ℂ → ℂ := rotatedFun (mordellIntegrand u)

/- **The rotated Mordell integrand, evaluated at a rotated point.** -/
end Zeta.RiemannSiegel

end

end CertificatePort126
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Ray.lean -/
section CertificatePort127
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The Mellin transform of the Mordell integral along the diagonal ray

Riemann's passage from the closed form of the Mordell integral `N(u)`
(`Zeta/RiemannSiegel/Mordell.lean`) to `ζ` multiplies that identity by `u^{-s}` and integrates `u`
over the ray `e^{-iπ/4}(0, ∞)` (`riemann_siegel_zero.tex`, `sec:rsz_mellin`). It is the step that
crosses the critical strip: the left-hand side produces the Riemann–Siegel contour integral
`I(1-s, ½)`, and the right-hand side produces `ζ(1-s)` together with the mirror Hankel integral
`Φ̃(s)`.

The ray is forced. It must lie in the lower half-plane for the geometric series to converge, and
`e^{-iπ/4}` is the unique direction for which the exponential rate is positive *uniformly along*
`L(a)`, because `Re (e^{iπ/4} x) = a/√2` is *constant* on `L(a)`
(`Zeta.RiemannSiegel.re_exp_pi_div_four_mul_I_mul_line`). That constancy is what makes the double
integral absolutely convergent, hence Fubini applicable. No contour in `x` is ever moved.

Two of the three terms are evaluated by one workhorse, `rayIntegral_exp_neg_two_pi_mul_I_mul`: the
ray integral of `u ↦ e^{-2πiuz}` is `(2π)^{s-1} e^{iπ(s-1)/2} Γ(1-s) z^{s-1}`, the last power taken
in the slanted branch `Zeta.RiemannSiegel.slantCpow`. Taking `z = n` gives the Dirichlet series of
`ζ`, and taking `z` on `L(½)` gives, after Fubini, the contour integral. The third, Gaussian, term
is instead a constant multiple of the mirror Hankel ray integral of
`Zeta/RiemannSiegel/Mirror.lean`.

## Main results

* `Zeta.RiemannSiegel.rayIntegral`: the operator `𝓡F(s) = ω ∫_0^∞ (ρω)^{-s} F(ρω) dρ`,
  `ω = e^{-iπ/4}`;
* `Zeta.RiemannSiegel.rayIntegral_exp_neg_two_pi_mul_I_mul`: its value on an exponential;
* `Zeta.RiemannSiegel.rayIntegral_inv_one_sub_exp`: the geometric term,
  `-(2π)^{s-1} e^{iπ(s-1)/2} Γ(1-s) ζ(1-s)` (`lem:rsz_ray_zeta`);
* `Zeta.RiemannSiegel.rayIntegral_mordellIntegral`: the contour term,
  `(2π)^{s-1} e^{iπ(s-1)/2} Γ(1-s) I(1-s, ½)` (`lem:rsz_ray_contour`);
* `Zeta.RiemannSiegel.rayIntegral_mirrorKernel`: the Gaussian term,
  `e^{iπ(s-1)/4} Φ̃(s) / (2i)` (`lem:rsz_ray_hankel`);
* `Zeta.RiemannSiegel.riemannZeta_add_contourIntegral_half_eq`: the Mellin form of Siegel's
  identity, `ζ(s) + I(s, ½) = (2π)^s e^{-iπ(2-s)/4} Φ̃(1-s) / (2 Γ(s))` for `Re s > 1`
  (`thm:rsz_mellin`).
-/
section


open Complex MeasureTheory Set

open scoped Real

namespace Zeta.RiemannSiegel

/-! ### The Mellin transform along the diagonal ray -/

/- The **diagonal ray integrand** `ρ ↦ (ρω)^{-s} F(ρω)` with `ω = e^{-iπ/4}`, the power being the
principal branch — legitimate, since `arg (ρω) = -π/4`. -/
noncomputable def rayIntegrand (f : ℂ → ℂ) (s : ℂ) (ρ : ℝ) : ℂ :=
  ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I))) ^ (-s) * f ((ρ : ℂ) * exp (-((π / 4 : ℝ) * I)))

/- The **Mellin transform along the diagonal ray**, `𝓡F(s) = ω ∫_0^∞ (ρω)^{-s} F(ρω) dρ` with
`ω = e^{-iπ/4}`. The `ω` in front is the velocity of the ray. -/
noncomputable def rayIntegral (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  exp (-((π / 4 : ℝ) * I)) * ∫ ρ in Ioi (0 : ℝ), rayIntegrand f s ρ

/- **The ray is the mirror of the outgoing Hankel ray**, `ρω = conj (e^{iπ/4} ρ)`. -/
private noncomputable def contourRayIntegrand (s : ℂ) (ρ w : ℝ) : ℂ :=
  rayIntegrand (fun u ↦ exp (-(2 * π * I * u * line (1 / 2) w))) s ρ * kernel (line (1 / 2) w)

/- **The double integrand is dominated by a product of a function of `ρ` and one of `w`.** -/
end Zeta.RiemannSiegel

end

end CertificatePort127
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Siegel.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/ZeroOrder.lean -/
section CertificatePort129
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The order-zero Riemann–Siegel formula

Hardy's `Z(t)` is evaluated to within `O(T^{-1/4})` by the **main sum**
`S(t, ν) = 2 ∑_{n ≤ ν} n^{-1/2} cos (θ(t) − t log n)` of `⌊√T⌋` terms, `T = t/2π`
(`riemann_siegel_zero.tex`, `cha:rs_zero`). This is the asymptotic gain over the `Θ(t)` terms per
point of the Euler–Maclaurin evaluation of `Zeta/Zeros/HardyZ.lean`.

The passage from the contour integral `I(s, a)` of `Zeta/RiemannSiegel/Integral.lean` to the main
sum is exact and unconditional: it is the contour-shift identity
`Zeta.RiemannSiegel.sum_cpow_neg_eq_contourIntegral_sub_contourIntegral` read through the phase
`e^{iθ(t)}`, and it is `mainSum_eq_two_re_exp_mul_contourIntegral_sub` below.

Identifying the remaining `ν`-independent term `2 Re (e^{iθ(t)} I(s, ½))` as `−Z(t)` is **Siegel's
identity** (`riemann_siegel_zero.tex`, `thm:rsz_siegel`), proved in
`Zeta/RiemannSiegel/Siegel.lean`. The whole chain is therefore unconditional.

## Main definitions

* `Zeta.RiemannSiegel.mainSum`: the main sum `S(t, ν)`;
* `Zeta.RiemannSiegel.mainSumOfPhase`: the same sum with the phase `θ` a parameter, which is what
  an implementation evaluates, at a Stirling approximant of `riemannSiegelTheta`.

## Main results

* `Zeta.RiemannSiegel.mainSum_eq_two_re_exp_mul_contourIntegral_sub`: the exact reduction
  `S(t, ν) = 2 Re (e^{iθ(t)} I(s, ν+½)) − 2 Re (e^{iθ(t)} I(s, ½))`;
* `Zeta.RiemannSiegel.hardyZ_eq_mainSum_sub`: the order-zero formula
  `Z(t) = S(t, ν) − 2 Re (e^{iθ(t)} I(s, ν+½))`;
* `Zeta.RiemannSiegel.abs_hardyZ_sub_mainSum_le_two_mul_norm`: the error is at most
  `2 ‖I(s, ν+½)‖`;
* `Zeta.RiemannSiegel.abs_hardyZ_sub_mainSum_le_hundredNinety`,
  `Zeta.RiemannSiegel.abs_hardyZ_sub_mainSum_le_threeHundredTwo`: the resulting bounds
  `|Z(t) − S(t, ⌊√T⌋)| ≤ 190 T^{-1/4} ≤ 302 t^{-1/4}` for `t ≥ 32π`;
* `Zeta.RiemannSiegel.abs_mainSumOfPhase_sub_mainSumOfPhase_le`: the main sum is `4√ν`-Lipschitz
  in its phase, so a phase error is amplified by `4√ν` rather than carried through unchanged.
-/
section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/- The **Riemann–Siegel main sum**
`S(t, ν) = 2 ∑_{n = 1}^{ν} n^{-1/2} cos (θ(t) − t log n)`. -/
noncomputable def mainSum (t : ℝ) (ν : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ν, Real.cos (riemannSiegelTheta t - t * Real.log n) / Real.sqrt n

/- **The exact reduction of the main sum to the contour integral.** -/
end Zeta.RiemannSiegel

end

end CertificatePort129
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/FirstOrder.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Certificate/HardyZDefs.lean -/


