-- Prove2me | Definitions.Def_LevyStochCalc_Probability_HermiteGenerating_F000
-- name    : LevyStochCalc_Probability_HermiteGenerating_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:30:25.84058+00:00
-- url     : https://prove2.me/theorems/c0f5a943-1b28-4a6c-b19b-6eaeca00abe7
-- title:
--   Source declarations: LevyStochCalc.Probability.HermiteGenerating
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.HermiteGenerating. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Hermite_F000
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Sum

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The generating function of the Hermite polynomials of variance `τ`

The Hermite polynomials of variance `τ` are generated over `ℂ` by
`e^(t x - t ^ 2 τ / 2) = ∑_r (t ^ r / r!) H_r(x; τ)`, which follows from the Appell binomial
decomposition `H_n(x; τ) / n! = ∑_(a + m = n) (x ^ a / a!) (H_m(0; τ) / m!)` by an antidiagonal
Cauchy product of the exponential series with the series of the values at the origin, the latter
summing to `e^(-t ^ 2 τ / 2)` because `H_(2b)(0; τ) = (-τ / 2) ^ b (2b)! / b!` and
`H_(2b+1)(0; τ) = 0`. A complex scalar covers the purely imaginary frequencies `t = i a`, where
the identity reads `e^(i a x + a ^ 2 τ / 2) = ∑_r ((i a) ^ r / r!) H_r(x; τ)`. Both factors of
the Cauchy product are absolutely summable, hence so is the scaled Hermite series itself, at
every argument and every complex scalar.

## Main statements

* `LevyStochCalc.Probability.hermiteScaled_two_mul_zero` —
  `H_(2b)(0; τ) = (-τ / 2) ^ b (2b)! / b!`.
* `LevyStochCalc.Probability.hermiteScaled_two_mul_add_one_zero` — `H_(2b+1)(0; τ) = 0`.
* `LevyStochCalc.Probability.sum_antidiagonal_hermiteScaled` — the Appell binomial identity
  `H_n(x; τ) / n! = ∑_(a + m = n) (x ^ a / a!) (H_m(0; τ) / m!)`.
* `LevyStochCalc.Probability.hasSum_hermiteScaled_zero` —
  `e^(-t ^ 2 τ / 2) = ∑_m (t ^ m / m!) H_m(0; τ)`.
* `LevyStochCalc.Probability.hasSum_hermiteScaled` —
  `e^(t x - t ^ 2 τ / 2) = ∑_r (t ^ r / r!) H_r(x; τ)` for `t : ℂ`.
* `LevyStochCalc.Probability.summable_norm_expTerm` — absolute summability of `z ^ a / a!`.
* `LevyStochCalc.Probability.summable_norm_hermiteScaled_zero` — absolute summability of
  `t ^ m / m! · H_m(0; τ)`.
* `LevyStochCalc.Probability.summable_norm_hermiteScaled` — absolute summability of
  `t ^ r / r! · H_r(x; τ)` at every argument.
* `LevyStochCalc.Probability.hasSum_hermiteScaled_real` — the same identity for a real scalar.
* `LevyStochCalc.Probability.hasSum_hermiteScaled_I` —
  `e^(i a x + a ^ 2 τ / 2) = ∑_r ((i a) ^ r / r!) H_r(x; τ)`.
* `LevyStochCalc.Probability.sum_antidiagonal_div_factorial` —
  `∑_(r + s = d) A ^ r B ^ s / (r! s!) = (A + B) ^ d / d!`.
-/

namespace LevyStochCalc.Probability

open Finset

/-- `H_(2b)(0; τ) = (-τ/2)^b (2b)! / b!`. -/
theorem hermiteScaled_two_mul_zero (τ : ℝ) (b : ℕ) :
    hermiteScaled (2 * b) τ 0
      = (-(τ / 2)) ^ b * ((2 * b).factorial / b.factorial : ℝ) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h : 2 * (b + 1) = 2 * b + 2 := by ring
    rw [h, hermiteScaled_succ_succ, ih]
    have hb : (b.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr b.factorial_ne_zero
    have h2 : ((2 * b + 2).factorial : ℝ)
        = ((2 * b + 2) * (2 * b + 1) : ℕ) * ((2 * b).factorial : ℝ) := by
      rw [show 2 * b + 2 = (2 * b + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [show 2 * b + 2 = 2 * b + 2 from rfl]
    rw [h2, Nat.factorial_succ]
    push_cast
    field_simp
    ring
/-- `H_(2b+1)(0; τ) = 0`. -/
theorem hermiteScaled_two_mul_add_one_zero (τ : ℝ) (b : ℕ) :
    hermiteScaled (2 * b + 1) τ 0 = 0 := by
  induction b with
  | zero => simp
  | succ b ih =>
    have h : 2 * (b + 1) + 1 = (2 * b + 1) + 2 := by ring
    rw [h, hermiteScaled_succ_succ, ih]
    ring
/-- The antidiagonal convolution `∑_(a + m = n) (x ^ a / a!) (H_m(0; τ) / m!)` of the exponential
coefficients with the coefficients of the Hermite values at the origin. -/
private noncomputable def appellSum (τ x : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ antidiagonal n,
    x ^ p.1 / (p.1.factorial : ℝ) * (hermiteScaled p.2 τ 0 / (p.2.factorial : ℝ))
/-- The antidiagonal convolution weighted by the first index,
`∑_(a + m = n + 1) a (x ^ a / a!) (H_m(0; τ) / m!) = x S_n`, where `S_n` is the
convolution at `n`. -/
private theorem appellSum_fst_weighted (τ x : ℝ) (n : ℕ) :
    ∑ p ∈ antidiagonal (n + 1), (p.1 : ℝ) *
        (x ^ p.1 / (p.1.factorial : ℝ) * (hermiteScaled p.2 τ 0 / (p.2.factorial : ℝ)))
      = x * appellSum τ x n := by
  rw [Finset.Nat.sum_antidiagonal_succ]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  rw [appellSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp : ((p.1 + 1).factorial : ℝ) = ((p.1 : ℝ) + 1) * (p.1.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h0 : (p.1.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.1.factorial_ne_zero
  have h1 : ((p.1 : ℝ) + 1) ≠ 0 := by positivity
  rw [hp]
  push_cast
  field_simp
  ring
/-- The three-term recursion at the origin, `H_(m+2)(0; τ) = -(m + 1) τ H_m(0; τ)`. -/
private theorem hermiteScaled_add_two_zero (τ : ℝ) (m : ℕ) :
    hermiteScaled (m + 2) τ 0 = -(((m : ℝ) + 1) * τ) * hermiteScaled m τ 0 := by
  rw [hermiteScaled_succ_succ]; ring
/-- The antidiagonal convolution weighted by the second index,
`∑_(a + m = n + 2) m (x ^ a / a!) (H_m(0; τ) / m!) = -τ S_n`, where `S_n` is the
convolution at `n`. -/
private theorem appellSum_snd_weighted (τ x : ℝ) (n : ℕ) :
    ∑ p ∈ antidiagonal (n + 2), (p.2 : ℝ) *
        (x ^ p.1 / (p.1.factorial : ℝ) * (hermiteScaled p.2 τ 0 / (p.2.factorial : ℝ)))
      = -τ * appellSum τ x n := by
  rw [show n + 2 = (n + 1) + 1 from rfl, Finset.Nat.sum_antidiagonal_succ']
  simp only [Nat.cast_zero, zero_mul, zero_add]
  have step1 : ∀ p : ℕ × ℕ, ((p.2 : ℝ) + 1) *
      (x ^ p.1 / (p.1.factorial : ℝ)
        * (hermiteScaled (p.2 + 1) τ 0 / ((p.2 + 1).factorial : ℝ)))
      = x ^ p.1 / (p.1.factorial : ℝ)
        * (hermiteScaled (p.2 + 1) τ 0 / (p.2.factorial : ℝ)) := by
    intro p
    have hp : ((p.2 + 1).factorial : ℝ) = ((p.2 : ℝ) + 1) * (p.2.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h0 : (p.2.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.factorial_ne_zero
    have h1 : ((p.2 : ℝ) + 1) ≠ 0 := by positivity
    rw [hp]; field_simp
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_congr rfl fun p _ => step1 p]
  rw [Finset.Nat.sum_antidiagonal_succ']
  have hone : hermiteScaled (0 + 1) τ 0 = 0 := by simp
  rw [hone]
  simp only [zero_div, mul_zero, zero_add]
  rw [appellSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp : ((p.2 + 1).factorial : ℝ) = ((p.2 : ℝ) + 1) * (p.2.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h0 : (p.2.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.factorial_ne_zero
  have h1 : ((p.2 : ℝ) + 1) ≠ 0 := by positivity
  rw [show p.2 + 1 + 1 = p.2 + 2 from rfl, hermiteScaled_add_two_zero, hp]
  field_simp
/-- The three-term recursion of the antidiagonal convolutions,
`(n + 2) S_(n+2) = x S_(n+1) - τ S_n`. -/
private theorem appellSum_succ_succ (τ x : ℝ) (n : ℕ) :
    ((n : ℝ) + 2) * appellSum τ x (n + 2)
      = x * appellSum τ x (n + 1) - τ * appellSum τ x n := by
  have hsplit : ((n : ℝ) + 2) * appellSum τ x (n + 2)
      = ∑ p ∈ antidiagonal (n + 2), ((p.1 : ℝ) + (p.2 : ℝ)) *
          (x ^ p.1 / (p.1.factorial : ℝ) * (hermiteScaled p.2 τ 0 / (p.2.factorial : ℝ))) := by
    rw [appellSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have := Finset.mem_antidiagonal.mp hp
    have hc : ((p.1 : ℝ) + (p.2 : ℝ)) = (n : ℝ) + 2 := by
      rw [← Nat.cast_add, this]; push_cast; ring
    rw [hc]
  rw [hsplit]
  simp only [add_mul]
  rw [Finset.sum_add_distrib, appellSum_snd_weighted]
  have h1 : ∑ p ∈ antidiagonal (n + 2), (p.1 : ℝ) *
      (x ^ p.1 / (p.1.factorial : ℝ) * (hermiteScaled p.2 τ 0 / (p.2.factorial : ℝ)))
      = x * appellSum τ x (n + 1) := appellSum_fst_weighted τ x (n + 1)
  rw [h1]
  ring
/-- The Appell binomial identity `H_n(x; τ)/n! = ∑_(a+m=n) x^a/a! · H_m(0; τ)/m!`. -/
theorem sum_antidiagonal_hermiteScaled (τ x : ℝ) (n : ℕ) :
    ∑ p ∈ antidiagonal n,
        x ^ p.1 / (p.1.factorial : ℝ) * (hermiteScaled p.2 τ 0 / (p.2.factorial : ℝ))
      = hermiteScaled n τ x / (n.factorial : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Finset.Nat.sum_antidiagonal_succ]
  | more n ih1 ih2 =>
    have hrec := appellSum_succ_succ τ x n
    rw [show appellSum τ x (n + 2) = ∑ p ∈ antidiagonal (n + 2),
        x ^ p.1 / (p.1.factorial : ℝ) * (hermiteScaled p.2 τ 0 / (p.2.factorial : ℝ)) from rfl,
      show appellSum τ x (n + 1) = ∑ p ∈ antidiagonal (n + 1),
        x ^ p.1 / (p.1.factorial : ℝ) * (hermiteScaled p.2 τ 0 / (p.2.factorial : ℝ)) from rfl,
      show appellSum τ x n = ∑ p ∈ antidiagonal n,
        x ^ p.1 / (p.1.factorial : ℝ) * (hermiteScaled p.2 τ 0 / (p.2.factorial : ℝ)) from rfl,
      ih2, ih1] at hrec
    have hne : ((n : ℝ) + 2) ≠ 0 := by positivity
    have hf : ((n + 2).factorial : ℝ)
        = ((n : ℝ) + 2) * (((n + 1).factorial : ℝ)) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf1 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * ((n.factorial : ℝ)) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h0 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    refine mul_left_cancel₀ hne ?_
    rw [hrec, hermiteScaled_succ_succ, hf, hf1]
    field_simp
/-- Doubling is injective on the naturals. -/
private theorem two_mul_injective : Function.Injective (fun b : ℕ => 2 * b) := fun a b h =>
  Nat.eq_of_mul_eq_mul_left (by norm_num) h
/-- A natural number outside the range of doubling is odd. -/
private theorem exists_odd_of_notMem_range_two_mul {m : ℕ}
    (hm : m ∉ Set.range (fun b : ℕ => 2 * b)) : ∃ b, m = 2 * b + 1 := by
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨c, hc⟩ := he
    refine absurd (Set.mem_range.mpr ⟨c, ?_⟩) hm
    show 2 * c = m
    omega
  · obtain ⟨b, hb⟩ := ho
    exact ⟨b, by omega⟩
/-- The Hermite generating function at `x = 0`. -/
theorem hasSum_hermiteScaled_zero (τ : ℝ) (t : ℂ) :
    HasSum (fun m : ℕ => t ^ m / (m.factorial : ℂ) * (hermiteScaled m τ 0 : ℂ))
      (Complex.exp (-(t ^ 2 * τ / 2))) := by
  refine (Function.Injective.hasSum_iff two_mul_injective ?_).mp ?_
  · intro m hm
    obtain ⟨b, rfl⟩ := exists_odd_of_notMem_range_two_mul hm
    rw [hermiteScaled_two_mul_add_one_zero]
    simp
  · have key : ∀ b : ℕ,
        ((fun m : ℕ => t ^ m / (m.factorial : ℂ) * (hermiteScaled m τ 0 : ℂ))
          ∘ (fun b : ℕ => 2 * b)) b
          = (-(t ^ 2 * (τ : ℂ) / 2)) ^ b / (b.factorial : ℂ) := by
      intro b
      simp only [Function.comp_apply]
      rw [hermiteScaled_two_mul_zero]
      have hb : ((b.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr b.factorial_ne_zero
      have h2b : (((2 * b).factorial : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (2 * b).factorial_ne_zero
      have h2b' : (((b * 2).factorial : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (b * 2).factorial_ne_zero
      push_cast
      rw [pow_mul, show (-(t ^ 2 * (τ : ℂ) / 2)) = t ^ 2 * (-((τ : ℂ) / 2)) by ring, mul_pow]
      field_simp [hb, h2b, h2b']
    rw [funext key, Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
/-- The exponential coefficient sequence `z ^ a / a!` is absolutely summable. -/
theorem summable_norm_expTerm (z : ℂ) :
    Summable fun a : ℕ => ‖z ^ a / (a.factorial : ℂ)‖ := by
  have h : (fun a : ℕ => ‖z ^ a / (a.factorial : ℂ)‖)
      = fun a : ℕ => ‖z‖ ^ a / (a.factorial : ℝ) := by
    funext a
    rw [norm_div, norm_pow, Complex.norm_natCast]
  rw [h]
  exact (NormedSpace.expSeries_div_hasSum_exp ‖z‖).summable
/-- The sequence `t ^ m / m! * H_m(0; τ)` of the values at the origin is absolutely
summable. -/
theorem summable_norm_hermiteScaled_zero (τ : ℝ) (t : ℂ) :
    Summable fun m : ℕ => ‖t ^ m / (m.factorial : ℂ) * (hermiteScaled m τ 0 : ℂ)‖ := by
  refine (Function.Injective.summable_iff two_mul_injective ?_).mp ?_
  · intro m hm
    obtain ⟨b, rfl⟩ := exists_odd_of_notMem_range_two_mul hm
    rw [hermiteScaled_two_mul_add_one_zero]
    simp
  · have key : ∀ b : ℕ,
        ((fun m : ℕ => ‖t ^ m / (m.factorial : ℂ) * (hermiteScaled m τ 0 : ℂ)‖)
          ∘ (fun b : ℕ => 2 * b)) b
          = (‖t‖ ^ 2 * (|τ| / 2)) ^ b / (b.factorial : ℝ) := by
      intro b
      simp only [Function.comp_apply]
      rw [hermiteScaled_two_mul_zero, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      have hb : (b.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr b.factorial_ne_zero
      have h2b : ((2 * b).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (2 * b).factorial_ne_zero
      have hnorm : ‖(((-(τ / 2)) ^ b * ((2 * b).factorial / b.factorial : ℝ) : ℝ) : ℂ)‖
          = (|τ| / 2) ^ b * ((2 * b).factorial / b.factorial : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_div]
        have h1 : |(-(τ / 2))| = |τ| / 2 := by
          rw [abs_neg, abs_div]; norm_num
        rw [h1, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * b).factorial : ℝ)),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.factorial : ℝ))]
      rw [hnorm, pow_mul, mul_pow]
      field_simp
    rw [funext key]
    exact (NormedSpace.expSeries_div_hasSum_exp (‖t‖ ^ 2 * (|τ| / 2))).summable
/-- The Hermite generating function `e^(t x - t² τ / 2) = ∑_r (t^r / r!) H_r(x; τ)`. -/
theorem hasSum_hermiteScaled (τ x : ℝ) (t : ℂ) :
    HasSum (fun r : ℕ => t ^ r / (r.factorial : ℂ) * (hermiteScaled r τ x : ℂ))
      (Complex.exp (t * x - t ^ 2 * τ / 2)) := by
  set f : ℕ → ℂ := fun a => (t * (x : ℂ)) ^ a / (a.factorial : ℂ) with hf_def
  set g : ℕ → ℂ := fun m => t ^ m / (m.factorial : ℂ) * (hermiteScaled m τ 0 : ℂ) with hg_def
  have hfn : Summable fun a => ‖f a‖ := summable_norm_expTerm (t * (x : ℂ))
  have hgn : Summable fun m => ‖g m‖ := summable_norm_hermiteScaled_zero τ t
  have hf : HasSum f (Complex.exp (t * x)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hg : HasSum g (Complex.exp (-(t ^ 2 * τ / 2))) := hasSum_hermiteScaled_zero τ t
  have hprod : Summable fun n : ℕ => ∑ p ∈ antidiagonal n, f p.1 * g p.2 :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
  have hval : (∑' n : ℕ, ∑ p ∈ antidiagonal n, f p.1 * g p.2)
      = Complex.exp (t * x) * Complex.exp (-(t ^ 2 * τ / 2)) := by
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn, hf.tsum_eq, hg.tsum_eq]
  have hsum : HasSum (fun n : ℕ => ∑ p ∈ antidiagonal n, f p.1 * g p.2)
      (Complex.exp (t * x - t ^ 2 * τ / 2)) := by
    have := hprod.hasSum
    rw [hval, ← Complex.exp_add] at this
    convert this using 2
    ring
  refine hsum.congr_fun fun n => ?_
  have hterm : ∀ p : ℕ × ℕ, p ∈ antidiagonal n →
      f p.1 * g p.2
        = t ^ n * ((x : ℂ) ^ p.1 / (p.1.factorial : ℂ)
            * ((hermiteScaled p.2 τ 0 : ℂ) / (p.2.factorial : ℂ))) := by
    intro p hp
    have hn : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    simp only [hf_def, hg_def]
    rw [← hn, pow_add, mul_pow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hreal := sum_antidiagonal_hermiteScaled τ x n
  have hcast : ∑ p ∈ antidiagonal n, ((x : ℂ) ^ p.1 / (p.1.factorial : ℂ)
      * ((hermiteScaled p.2 τ 0 : ℂ) / (p.2.factorial : ℂ)))
      = ((hermiteScaled n τ x / (n.factorial : ℝ) : ℝ) : ℂ) := by
    rw [← hreal]
    push_cast
    rfl
  rw [hcast]
  push_cast
  ring
end LevyStochCalc.Probability


