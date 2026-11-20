-- Prove2me | Definitions.Def_LevyStochCalc_Probability_CharlierAdd_F000
-- name    : LevyStochCalc_Probability_CharlierAdd_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:16:06.493891+00:00
-- url     : https://prove2.me/theorems/ac82ad81-10c4-47c0-a1c6-675bb91a32ba
-- title:
--   Source declarations: LevyStochCalc.Probability.CharlierAdd
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.CharlierAdd. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_CharlierGenerating_F000
import Mathlib.RingTheory.PowerSeries.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The addition formula of the Charlier polynomials

The Charlier polynomials with parameter `lam`, the mean of the Poisson law that makes them
orthogonal, are of binomial type jointly in the argument and the parameter:
`C_n(x + y; lam + mu) = ∑_(i + j = n) (n choose i) C_i(x; lam) C_j(y; mu)`. The induction
on `n` runs the recursion `C_(n+1)(x) = x C_n(x - 1) - lam C_n(x)` on both sides and uses Pascal's
rule for the binomial coefficients.

In terms of the exponential generating series `S(lam, x; c) = ∑_n (c ^ n / n!) C_n(x; lam) X ^ n`
over `ℂ`, a formal power series in `X` at a complex scalar `c`, the formula says that
`S(lam, x; c) S(mu, y; c) = S(lam + mu, x + y; c)`. The series of parameter and argument zero is
`1`, and so is every series at `c = 0`, so over a finite family carrying one common scalar the
product of the series is the series of the summed parameters at the summed arguments.

## Main definitions

* `LevyStochCalc.Probability.charlierSeries` — the exponential generating series
  `∑_n (c ^ n / n!) C_n(x; lam) X ^ n`.

## Main statements

* `LevyStochCalc.Probability.charlierScaled_add` — the addition formula
  `C_n(x + y; lam + mu) = ∑_(i + j = n) (n choose i) C_i(x; lam) C_j(y; mu)`.
* `LevyStochCalc.Probability.charlierSeries_mul` —
  `S(lam, x; c) S(mu, y; c) = S(lam + mu, x + y; c)`.
* `LevyStochCalc.Probability.charlierSeries_zero_zero`,
  `LevyStochCalc.Probability.charlierSeries_zero_scalar` — the series of parameter and argument
  zero, and every series at the scalar zero, is `1`.
* `LevyStochCalc.Probability.prod_charlierSeries` — over a finite family at a common scalar,
  `∏_i S(lam_i, x_i; c) = S(∑_i lam_i, ∑_i x_i; c)`.
-/

namespace LevyStochCalc.Probability

open Finset PowerSeries

/-- **The Charlier addition formula**,
`C_n(x + y; lam + mu) = ∑_(i + j = n) (n choose i) C_i(x; lam) C_j(y; mu)`. -/
theorem charlierScaled_add (n : ℕ) (lam mu : ℝ) :
    ∀ x y : ℝ, charlierScaled n (lam + mu) (x + y)
      = ∑ ij ∈ antidiagonal n, (n.choose ij.1 : ℝ)
          * (charlierScaled ij.1 lam x * charlierScaled ij.2 mu y) := by
  induction n with
  | zero => intro x y; simp
  | succ n ih =>
    intro x y
    rw [charlierScaled_succ, Finset.sum_antidiagonal_choose_succ_mul
      (fun i j => charlierScaled i lam x * charlierScaled j mu y)]
    have h1 : x + y - 1 = (x - 1) + y := by ring
    have h2 : x + y - 1 = x + (y - 1) := by ring
    have e : (x + y) * charlierScaled n (lam + mu) (x + y - 1)
        = x * charlierScaled n (lam + mu) ((x - 1) + y)
          + y * charlierScaled n (lam + mu) (x + (y - 1)) := by
      rw [← h1, ← h2]; ring
    rw [e, ih (x - 1) y, ih x (y - 1), ih x y]
    simp only [charlierScaled_succ, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    have hsymm : ∀ ij ∈ antidiagonal n, (n.choose ij.2 : ℝ) = n.choose ij.1 := by
      intro ij hij
      rw [mem_antidiagonal] at hij
      rw [← hij, Nat.choose_symm_add]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [hsymm ij hij]
    ring
/-- The exponential generating series `∑_n (c ^ n / n!) C_n(x; lam) X ^ n` of the Charlier
polynomials with parameter `lam` at the argument `x` and the complex scalar `c`. -/
noncomputable def charlierSeries (lam x : ℝ) (c : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => c ^ n / (n.factorial : ℂ) * (charlierScaled n lam x : ℂ)
/-- The coefficient of `X ^ n` in the generating series is `(c ^ n / n!) C_n(x; lam)`. -/
theorem coeff_charlierSeries (lam x : ℝ) (c : ℂ) (n : ℕ) :
    coeff n (charlierSeries lam x c)
      = c ^ n / (n.factorial : ℂ) * (charlierScaled n lam x : ℂ) :=
  coeff_mk _ _
/-- **The Charlier addition formula as a product of generating series**,
`S(lam, x; c) S(mu, y; c) = S(lam + mu, x + y; c)`. -/
theorem charlierSeries_mul (lam mu x y : ℝ) (c : ℂ) :
    charlierSeries lam x c * charlierSeries mu y c = charlierSeries (lam + mu) (x + y) c := by
  ext n
  rw [coeff_mul, coeff_charlierSeries, charlierScaled_add n lam mu x y]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [coeff_charlierSeries, coeff_charlierSeries]
  have hn : ij.1 + ij.2 = n := mem_antidiagonal.1 hij
  have hc : (n.choose ij.1 : ℂ) * ((ij.1.factorial : ℂ) * (ij.2.factorial : ℂ))
      = (n.factorial : ℂ) := by
    rw [← hn, ← mul_assoc, Nat.choose_symm_add]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial ij.1 ij.2
  have h1 : (ij.1.factorial : ℂ) ≠ 0 := by exact_mod_cast ij.1.factorial_ne_zero
  have h2 : (ij.2.factorial : ℂ) ≠ 0 := by exact_mod_cast ij.2.factorial_ne_zero
  have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : (n.choose ij.1 : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hn ▸ Nat.le_add_right ij.1 ij.2)).ne'
  rw [← hc, ← hn, pow_add]
  rw [← hn] at h4
  field_simp
/-- The generating series of parameter and argument zero is `1`. -/
@[simp] theorem charlierSeries_zero_zero (c : ℂ) : charlierSeries 0 0 c = 1 := by
  ext n
  rw [coeff_charlierSeries, charlierScaled_zero_arg, coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn]
/-- Every generating series at the scalar zero is `1`. -/
@[simp] theorem charlierSeries_zero_scalar (lam x : ℝ) : charlierSeries lam x 0 = 1 := by
  ext n
  rw [coeff_charlierSeries, coeff_one]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [hn]
/-- Over a finite family carrying a common scalar, the product of the generating series is the
series of the summed parameters at the summed arguments. -/
theorem prod_charlierSeries {ι : Type*} (s : Finset ι) (lam x : ι → ℝ) (c : ℂ) :
    ∏ i ∈ s, charlierSeries (lam i) (x i) c
      = charlierSeries (∑ i ∈ s, lam i) (∑ i ∈ s, x i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, charlierSeries_mul, Finset.sum_insert ha,
      Finset.sum_insert ha]
end LevyStochCalc.Probability


