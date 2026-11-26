-- Prove2me | Definitions.Def_RHGram655_20261117_P01_v1
-- name    : RHGram655_20261117_P01_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-17T13:59:11.113478+00:00
-- url     : https://prove2.me/theorems/8b1e92c4-8ca8-4e1e-ac6c-388a097e8d95
-- title:
--   Gram 655 ordinary certificate dependencies 01
-- statement:
--   Ordinary Lean proof dependencies for a numerical Gram-point certificate. Complete mathematical proofs and explicit kernel proof terms; no custom elaborators, unchecked numerical assumptions or added axioms.
-- source:
--   smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033, Apache-2.0; PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe. Dependency extraction and ordinary proof-term sharing by Desenvolvimento RH. AXLE standalone ordinary source 758e7c92-e198-48f4-8e6c-1f3233ed3277; combined source audit recorded separately.

import Definitions.Def_RHHeight1000_20261117_P04_v3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000


/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Bernoulli/TangentNumbers.lean -/
section CertificatePort135


/-!
# Tangent numbers

The *tangent numbers* `T₁, T₂, T₃, … = 1, 2, 16, 272, 7936, …` are the numerators
appearing in the Taylor expansion of the tangent function:
`tan x = ∑ₙ Tₙ · x^(2n-1) / (2n-1)!`.

The tangent numbers are *defined* here following Knuth and Buckholtz (*Math. Comp.* **21**
(1967)): the `n`-th derivative of `tan` is a polynomial in `tan`,
`dⁿ/dxⁿ tan x = Pₙ(tan x)`, where `P₀ = X` and `Pₙ₊₁ = (1 + X²)·Pₙ′`, and `Tₙ = Pₙ(0)`.

## Main definitions

* `tangentPoly`  : the tangent polynomials `Pₙ`, exactly Knuth's `P₀ = X`, `Pₙ₊₁ = (1 + X²)·Pₙ′`.
* `tangentNumber`: the `n`-th tangent number `Tₙ = P_{2n-1}(0)`; these come out *positive* with
                   no sign correction (`tangentNumber 1 = 1, 2 = 2, 3 = 16, 4 = 272, …`).
* `tanhPoly`     : the hyperbolic analogue `Qₙ₊₁ = (1 − X²)·Qₙ′`, used to bridge to the rational
                   power series `tanhSeries`.
* `tanhSeries`   : the formal power series `tanh x = (e^{2x} - 1)/(e^{2x} + 1) ∈ ℚ⟦X⟧`,
                   the link to Mathlib's Bernoulli generating functions.

## Main results

* `derivative_tanhSeries` : the ODE `(tanh)′ = 1 − tanh²` behind the polynomial recurrence.
* `eval_tangentPoly`      : the bridge `P_{2m+1}(0) = (−1)^m · (2m+1)! · [x^{2m+1}] tanh x` linking
                            the elementary definition to the power series.
* `coeff_tanhSeries`      : the relationship to the Bernoulli numbers,
    `[x^{2m+1}] tanh x = 2^(2m+2) · (2^(2m+2) − 1) · bernoulli (2m+2) / (2m+2)!`.
* `tangentNumber_eq`      : the resulting closed form for the tangent numbers.

We carry the *power-series* half of the development over `tanh` rather than `tan` because
`tanh x = (e^{2x}−1)/(e^{2x}+1)` has *rational* coefficients, so it lives in `ℚ⟦X⟧` and is directly
comparable with Mathlib's Bernoulli generating functions.  The tangent polynomials `Pₙ` (`1 + X²`)
and their hyperbolic analogues `Qₙ` (`1 − X²`) are related by `x ↦ i·x`; that substitution, proved
as `map_tanhPoly` over `ℂ[X]`, is the only place complex numbers enter, and it lets the
positive `Pₙ(0)` inherit the Bernoulli closed form.
-/
section


open scoped Nat

namespace TangentNumbers

noncomputable section

section Poly

open Polynomial

/-! ## The tangent polynomials `Pₙ` and the tangent numbers

The polynomial recurrence `P₀ = X`, `Pₙ₊₁ = (1 + X²)·Pₙ′`, and the tangent numbers
`Tₙ = P_{2n-1}(0)`. -/

/- The tangent polynomials `Pₙ` (Knuth & Buckholtz, *Math. Comp.* **21** (1967)):
`P₀ = X`, `Pₙ₊₁ = (1 + X²)·Pₙ′`, so that `dⁿ/dxⁿ tan x = Pₙ(tan x)`.  The tangent numbers are the
(positive) constant terms `P_{2n-1}(0) = 1, 2, 16, 272, …`. -/
def tangentPoly : ℕ → ℕ[X]
  | 0 => X
  | (n + 1) => (1 + X ^ 2) * derivative (tangentPoly n)

lemma tangentPoly_succ (n : ℕ) :
    tangentPoly (n + 1) = (1 + X ^ 2) * derivative (tangentPoly n) :=
  rfl

/- The `n`-th tangent number (for `n ≥ 1`): `T₁ = 1, T₂ = 2, T₃ = 16, T₄ = 272, …`, the constant
term `P_{2n-1}(0)` of the tangent polynomial.  These come out *positive*, with no sign
correction. -/
def tangentNumber (n : ℕ) : ℕ :=
  (tangentPoly (2 * n - 1)).eval 0

/-! ## The hyperbolic tangent polynomials `Qₙ`

The hyperbolic analogue `Q₀ = X`, `Qₙ₊₁ = (1 − X²)·Qₙ′`, satisfying `Dⁿ(tanh) = Qₙ(tanh)`, from
which `Qₙ(0) = n! · [xⁿ] tanh x`. -/

/- The hyperbolic tangent polynomials: the same construction with `1 − X²` in place of
`1 + X²`, so that `dⁿ/dxⁿ tanh x = Qₙ(tanh x)`.
`Pₙ` and `Qₙ` are related by `x ↦ i·x` (see `eval_tangentPoly`). -/
def tanhPoly : ℕ → ℤ[X]
  | 0 => .X
  | (n + 1) => (1 - .X ^ 2 : ℤ[X]) * .derivative (tanhPoly n)

private lemma tanhPoly_succ (n : ℕ) :
    tanhPoly (n + 1) = (1 - .X ^ 2 : ℤ[X]) * .derivative (tanhPoly n) :=
  rfl

open Complex

/- The relation `Qₙ = (−i)^{n+1} · Pₙ(i·x)` between the `tan` and `tanh` polynomials, over `ℂ`. -/
private lemma map_tanhPoly (n : ℕ) :
    (tanhPoly n).map (algebraMap ℤ ℂ) =
      C (-I ^ (n + 1)) *
        ((tangentPoly n).map (algebraMap ℕ ℂ)).comp (C I * X) := by
  induction n with
  | zero =>
    simp only [tanhPoly, tangentPoly, map_X, X_comp, zero_add, pow_one]
    rw [← mul_assoc, ← C_mul, neg_mul, I_mul_I]
    simp
  | succ n ih =>
    have hCI : C I ^ 2 = -1 := by
      rw [← C_pow, I_sq, C_neg, C_1]
    have hI : C (-I ^ (n + 2)) = C (-I ^ (n + 1)) * C I := by
      grind [C_mul, pow_succ]
    rw [tanhPoly_succ, tangentPoly_succ]
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_one,
      Polynomial.map_pow, map_X, ← derivative_map, ih, derivative_comp, derivative_mul,
      derivative_C, derivative_X, mul_comp, add_comp, one_comp, pow_comp, X_comp]
    grind

end Poly

section PowerSeries

open PowerSeries

section ForMathlib

/- The `k`-th coefficient of the `n`-th formal derivative `Dⁿ f` is `(k+1)(k+2)⋯(k+n)` times the
`(k+n)`-th coefficient of `f`. -/
private lemma coeff_iterate_derivative {R : Type*} [CommRing R] (f : R⟦X⟧) (n k : ℕ) :
    coeff k ((d⁄dX R)^[n] f) = (k + 1).ascFactorial n * coeff (k + n) f := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', coeff_derivative, ih, Nat.ascFactorial_succ,
      ← Nat.succ_ascFactorial]
    grind

/- Specialisation at `k = 0`: the constant term of `Dⁿ f` is `n!` times the `n`-th coefficient of
`f`, that is, `coeff 0 (Dⁿ f) = n! · coeff n f`. -/
private lemma coeff_zero_iterate {R : Type*} [CommRing R] (f : R⟦X⟧) (n : ℕ) :
    coeff 0 ((d⁄dX R)^[n] f) = n ! * coeff n f := by simpa using coeff_iterate_derivative f n 0

end ForMathlib

/-! ## The hyperbolic generating series `tanhSeries`

The power series `tanh x = (e^{2x} - 1)/(e^{2x} + 1) ∈ ℚ⟦X⟧`, its well-definedness, and the ODE
`(tanh)′ = 1 − tanh²`. -/

/- `tanh x = (e^{2x} - 1)/(e^{2x} + 1)`, as a formal power series over `ℚ` (rational since
`e^{2x} = (eˣ)²`).  Its coefficients `(2n-1)! · [x^{2n-1}] tanh x` are the tangent numbers up to
sign. -/
def tanhSeries : ℚ⟦X⟧ :=
  (exp ℚ ^ 2 - 1) * (exp ℚ ^ 2 + 1)⁻¹

/- The constant term of `e^{2x} + 1` is `2`, hence nonzero. -/
private lemma tanhSeries_mul_expSq_add_one :
    tanhSeries * (exp ℚ ^ 2 + 1) = exp ℚ ^ 2 - 1 := by
  simp [tanhSeries, mul_assoc, PowerSeries.inv_mul_cancel]

lemma ne_zero_of_coeff_ne_zero {R : Type*} [Semiring R] {p : R⟦X⟧} (n : ℕ) (h : p.coeff n ≠ 0) :
    p ≠ 0 := by
  grind

private lemma expSq_add_one_ne_zero : exp ℚ ^ 2 + 1 ≠ 0 :=
  ne_zero_of_coeff_ne_zero 0 (by simp)

/- `tanh` has no constant term: `tanh 0 = 0`. -/
private lemma constantCoeff_tanhSeries : constantCoeff tanhSeries = 0 := by simp [tanhSeries]

/- `tanhSeries` satisfies the ODE `(tanh)′ = 1 − tanh²`. -/
private lemma derivative_tanhSeries :
    d⁄dX ℚ tanhSeries = 1 - tanhSeries ^ 2 := by
  have hd : tanhSeries * (2 * (exp ℚ * exp ℚ)) + (exp ℚ ^ 2 + 1) * d⁄dX ℚ tanhSeries =
      2 * (exp ℚ * exp ℚ) := by
    simpa [derivative_exp] using congr(d⁄dX ℚ $tanhSeries_mul_expSq_add_one)
  refine mul_left_cancel₀ expSq_add_one_ne_zero ?_
  linear_combination hd - (1 - tanhSeries) * tanhSeries_mul_expSq_add_one

open scoped Polynomial

-- dumb helper lemma
private lemma aeval_tanhSeries_map (p : ℤ[X]) :
    Polynomial.aeval tanhSeries (p.map (algebraMap ℤ ℚ)) = Polynomial.aeval tanhSeries p :=
  (Polynomial.aeval_eq_aeval_map (by ext; simp) p tanhSeries).symm

/- The defining property of the hyperbolic tangent polynomials at the level of power series:
`Dⁿ(tanh) = Qₙ(tanh)`. -/
private lemma iterate_derivative_tanhSeries (n : ℕ) :
    (d⁄dX ℚ)^[n] tanhSeries = (tanhPoly n).aeval tanhSeries := by
  induction n with
  | zero => simp [tanhPoly]
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, ← aeval_tanhSeries_map (tanhPoly n), Derivation.map_aeval, derivative_tanhSeries,
      smul_eq_mul, Polynomial.derivative_map, aeval_tanhSeries_map, tanhPoly_succ]
    simp
    ring

private lemma constantCoeff_aeval_tanhSeries (p : ℤ[X]) :
    constantCoeff (p.aeval tanhSeries) = p.eval 0 := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n a _ => simp [map_mul, map_pow, constantCoeff_tanhSeries]

/- The constant term of the `n`-th hyperbolic tangent polynomial is `n!` times the `n`-th
coefficient of `tanh`:  `Qₙ(0) = n! · [xⁿ] tanh x`. -/
private lemma eval_tanhPoly (n : ℕ) :
    (tanhPoly n).eval 0 = n ! * coeff n tanhSeries := by
  rw [← constantCoeff_aeval_tanhSeries, ← coeff_zero_eq_constantCoeff_apply,
    ← iterate_derivative_tanhSeries n, coeff_zero_iterate]

/-! ## Connecting to Bernoulli -/

/- Evaluating a mapped polynomial at `0` applies the ring map to its constant term. -/
private lemma eval_zero_map {R S : Type*} [CommSemiring R] [Semiring S] (f : R →+* S) (p : R[X]) :
    (p.map f).eval 0 = f (p.eval 0) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
      Polynomial.coeff_zero_eq_eval_zero]

/- The constant term of the `(2m+1)`-st tangent polynomial is the corresponding
Taylor numerator of `tan`:
`P_{2m+1}(0) = (−1)^m · (2m+1)! · [x^{2m+1}] tanh x`. -/
private lemma eval_tangentPoly (m : ℕ) :
    (tangentPoly (2 * m + 1)).eval 0 = (-1) ^ m * (2 * m + 1)! * coeff (2 * m + 1) tanhSeries := by
  -- evaluate the `ℂ[X]` relation at `0`; `eval_zero_map` + the cast lemmas turn each mapped
  -- constant term (over `ℤ` and over `ℕ`) into the matching cast, and `hI` collapses `-i^{2m+2}` to
  -- `(-1)^m`.
  have hmap := congrArg (Polynomial.eval 0) (map_tanhPoly (2 * m + 1))
  have hI : -Complex.I ^ (2 * m + 2) = (-1) ^ m := by
    have he : 2 * m + 2 = 2 * (m + 1) := by ring
    rw [he, pow_mul, Complex.I_sq]
    ring
  simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
    mul_zero, eval_zero_map, eq_intCast, eq_natCast, hI] at hmap
  have hq : (tanhPoly (2 * m + 1)).eval 0
      = (-1) ^ m * (((tangentPoly (2 * m + 1)).eval 0 : ℕ) : ℚ) := mod_cast hmap
  rw [eval_tanhPoly] at hq
  rw [mul_assoc, hq, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨m, rfl⟩, one_mul]

-- TODO: put in ForMathlib, and then in mathlib
section

variable {R : Type*} [Semiring R] {p : R⟦X⟧}

@[simp] lemma coeff_mul_natCast {a k : ℕ} :
    coeff k (p * a : R⟦X⟧) = coeff k p * a := coeff_mul_C _ _ _

@[simp] lemma coeff_natCast_mul {a k : ℕ} :
    coeff k (a * p : R⟦X⟧) = a * coeff k p := coeff_C_mul _ _ _

@[simp] lemma coeff_mul_ofNat {a k : ℕ} [Nat.AtLeastTwo a] :
    coeff k (p * (ofNat(a) : R⟦X⟧)) = coeff k p * ofNat(a) := coeff_mul_C _ _ _

@[simp] lemma coeff_ofNat_mul {a k : ℕ} [Nat.AtLeastTwo a] :
    coeff k ((ofNat(a) : R⟦X⟧) * p) = ofNat(a) * coeff k p := coeff_C_mul _ _ _

end

/- The coefficient of `x^{2m+1}` in `tanh x`, in terms of the Bernoulli numbers:
`2^(2m+2) · (2^(2m+2) - 1) · bernoulli (2m+2) / (2m+2)!`,
where `bernoulli` is Mathlib's (first) Bernoulli number. -/
theorem coeff_tanhSeries (m : ℕ) :
    coeff (2 * m + 1) tanhSeries =
      2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) * bernoulli (2 * m + 2) / (2 * m + 2)! := by
  -- `D` is `x·coth(x/2)`'s generating series, written via the two Bernoulli series so that
  -- its even coefficients are `2·bernoulli/(2m)!` and its odd ones vanish.
  set D := bernoulliPowerSeries ℚ + bernoulli'PowerSeries ℚ with hD
  -- the even coefficients of `D` are `2·bernoulli/(2m+2)!`.
  have hcoeffD : coeff (2 * m + 2) D = 2 * bernoulli (2 * m + 2) / (2 * m + 2)! := by
    simp [hD, map_add, bernoulliPowerSeries, bernoulli'PowerSeries]
    grind [bernoulli_eq_bernoulli'_of_ne_one]
  -- relate tanhSeries with D (and therefore with bernoulliPowerSeries)
  have main : 2 * X * tanhSeries = rescale 4 D - rescale 2 D := by
    have B3 : D * (exp ℚ - 1) = .X * (exp ℚ + 1) := by
      rw [hD, add_mul, bernoulliPowerSeries_mul_exp_sub_one,
        bernoulli'PowerSeries_mul_exp_sub_one]
      grind
    have h2 : rescale 2 D * (exp ℚ ^ 2 - 1) = 2 * .X * (exp ℚ ^ 2 + 1) := by
      simpa [exp_pow_eq_rescale_exp, map_ofNat] using congrArg (rescale 2) B3
    have h4 : rescale 4 D * (exp ℚ ^ 4 - 1) = 4 * .X * (exp ℚ ^ 4 + 1) := by
      simpa [exp_pow_eq_rescale_exp, map_ofNat] using congrArg (rescale 4) B3
    -- `e^{2x} ± 1` are both nonzero, so their product can be cancelled
    have hP : (exp ℚ ^ 2 + 1) * (exp ℚ ^ 2 - 1) ≠ 0 := by
      apply mul_ne_zero <;>
      · apply ne_zero_of_coeff_ne_zero 1
        simp [exp_pow_eq_rescale_exp]
    apply mul_right_cancel₀ hP
    linear_combination (2 * X * (exp ℚ ^ 2 - 1)) * tanhSeries_mul_expSq_add_one - h4 +
      (exp ℚ ^ 2 + 1) * h2
  -- Read off the coefficient of `x^{2m+2}` from the main identity.
  have hcoeff := congrArg (coeff (2 * m + 2)) main
  have lhs : coeff (2 * m + 2) (X * (2 • tanhSeries)) = 2 * coeff (2 * m + 1) tanhSeries := by simp
  have rhs : coeff (2 * m + 2) (rescale 4 D - rescale 2 D) =
      (4 ^ (2 * m + 2) - 2 ^ (2 * m + 2)) * coeff (2 * m + 2) D := by grind [coeff_rescale]
  have h4eq : (4 ^ (2 * m + 2) : ℚ) = (2 ^ (2 * m + 2)) ^ 2 := by
    have : (4 : ℚ) = 2 ^ 2 := by norm_num
    rw [this, pow_right_comm]
  grind

/- Closed form for the tangent numbers in terms of the Bernoulli numbers:
`T_{m+1} = (-1)^m · (2m+1)! · 2^(2m+2) · (2^(2m+2) - 1) · bernoulli (2m+2) / (2m+2)!`. -/
theorem tangentNumber_eq (m : ℕ) :
    tangentNumber (m + 1) =
      (-1) ^ m * (2 * m + 1)! *
        2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) * bernoulli (2 * m + 2) / (2 * m + 2)! := by
  grind [tangentNumber, eval_tangentPoly, coeff_tanhSeries]

end PowerSeries

/-! ### Sanity checks: the first few tangent numbers -/

/- Unused anonymous example omitted; no theorem body replaced. -/
/- Unused anonymous example omitted; no theorem body replaced. -/
/- Unused anonymous example omitted; no theorem body replaced. -/
/- Unused anonymous example omitted; no theorem body replaced. -/
end

end TangentNumbers

end

end CertificatePort135

theorem TangentNumbers.tangentNumberLit_1 : TangentNumbers.tangentNumber 1 = 1 := by
  simp [TangentNumbers.tangentNumber, TangentNumbers.tangentPoly]
theorem TangentNumbers.tangentNumberLit_2 : TangentNumbers.tangentNumber 2 = 2 := by
  simp [TangentNumbers.tangentNumber, TangentNumbers.tangentPoly]
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Bernoulli/TangentVerify.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Bernoulli/FoldExperiment.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Bernoulli/BernoulliValues.lean -/
section CertificatePort138


/-!
# Exact Bernoulli numerators via tangent numbers

Rearranging the closed form `tangentNumber_eq`, an even Bernoulli number is an explicit integer
fraction built from a tangent number:
`B_{2m+2} = A / B`,  with  `A = (-1)^m·(2m+2)·T_{m+1}`,  `B = 2^{2m+2}·(2^{2m+2}-1)`.
`num_eq_of_eq_intDiv` turns this into the reduced numerator once a candidate `p / q` is supplied and
validated by the integer identities `p·B = q·A` and `gcd = 1`.

This module emits the shared data the downstream development reads by reference: the tangent numbers
`T₀..T₉₉` (`tangentNumberLit_k`) and the reduced numerators `num(B₂)..num(B₁₉₈)` (`bernNumLit_m`),
each a standalone environment lemma generated in `MetaM`, every side condition a `reflBoolTrue`.
The reduced numerators feed the regular-prime sweeps in `Bernoulli.Kummer`.

The full rational values `bernoulli n = p / q` and the `derive_bernoulli` generator live in
`Bernoulli.BernoulliExact`.  No `native_decide`.
-/
section


open scoped Nat

namespace TangentNumbers

/-! ## The exact reduced value -/

/- If `A/B = p/q` with `q > 0` and `p, q` coprime, then `p` is the reduced numerator of `A/B`. -/
theorem num_eq_of_eq_intDiv {A B p q : ℤ} (hB : B ≠ 0) (hq : 0 < q)
    (hcop : Int.gcd p q = 1) (hcross : p * B = q * A) :
    ((A : ℚ) / (B : ℚ)).num = p := by
  have heq : (A : ℚ) / (B : ℚ) = (p : ℚ) / (q : ℚ) := by
    rw [div_eq_div_iff (by exact_mod_cast hB) (by exact_mod_cast hq.ne')]
    have : A * q = p * B := by linear_combination -hcross
    exact_mod_cast this
  rw [heq]
  exact Rat.num_div_eq_of_coprime hq hcop

open PowerSeries in
/- `B_{2m+2}` as an explicit integer fraction using the tangent number `T_{m+1}`. -/
theorem bernoulli_eq_tangent_intDiv (m : ℕ) :
    bernoulli (2 * m + 2) =
      (((-1) ^ m * (2 * m + 2) * (tangentNumber (m + 1) : ℤ) : ℤ) : ℚ) /
        (((2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) : ℤ) : ℚ)) := by
  have h := tangentNumber_eq m
  have hfac : ((2 * m + 2)! : ℚ) = (2 * m + 2) * (2 * m + 1)! := by
    have hidx : 2 * m + 2 = (2 * m + 1) + 1 := rfl
    rw [hidx, Nat.factorial_succ]
    push_cast
    ring
  have hP : (2 : ℚ) ^ (2 * m + 2) ≠ 0 := by positivity
  have hQ : (2 : ℚ) ^ (2 * m + 2) - 1 ≠ 0 := by
    have h1 : (1 : ℚ) < 2 ^ (2 * m + 2) := one_lt_pow₀ (by norm_num) (by positivity)
    linarith
  have hfac' : ((2 * m + 1)! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [hfac] at h
  push_cast at h ⊢
  rw [h]
  field_simp
  have hs : (((-1 : ℚ)) ^ m) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [hs, mul_one]

theorem intDenom_ne_zero (m : ℕ) : (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1) : ℤ) ≠ 0 :=
  mul_ne_zero (by positivity) (sub_ne_zero.mpr (one_lt_pow₀ (by norm_num) (by omega)).ne')

/-! ## Per-`m` certificate: the reduced numerator from a tangent number

`bernoulli_num_of` gives the reduced numerator of `B_{2m+2}` from its tangent number `Tₙ` and a
candidate `p/q`, with the validating identities as kernel `decide`s (each a `reflBoolTrue`). -/

/- The reduced numerator of `B_{2m+2}` is `p`, from the tangent number and a validated `p/q`. -/
theorem bernoulli_num_of (m : ℕ) (Tn : ℕ) (p q : ℤ)
    (hT : tangentNumber (m + 1) = Tn)
    (hq : decide (0 < q) = true)
    (hcop : (Int.gcd p q).beq 1 = true)
    (hcross : decide (p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1))
                = q * ((-1) ^ m * (2 * m + 2) * (Tn : ℤ))) = true) :
    (bernoulli (2 * m + 2)).num = p := by
  have hq' : 0 < q := of_decide_eq_true hq
  have hcop' : Int.gcd p q = 1 := Nat.eq_of_beq_eq_true hcop
  have hcross' : p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1))
      = q * ((-1) ^ m * (2 * m + 2) * (Tn : ℤ)) := of_decide_eq_true hcross
  have hTn : (tangentNumber (m + 1) : ℤ) = (Tn : ℤ) := by rw [hT]
  rw [bernoulli_eq_tangent_intDiv m, hTn]
  exact num_eq_of_eq_intDiv (intDenom_ne_zero m) hq' hcop' hcross'

/- `|num(B_{2m+2})| = n` from the reduced numerator `p` and `|p| = n` (checked once, as a
`Nat.beq`). The regular-prime sweep tests divisibility on this `Nat` literal, so `natAbs` is reduced
once per `m` here rather than per prime. -/
theorem numAbs_of (m n : ℕ) (p : ℤ) (hnum : (bernoulli (2 * m + 2)).num = p)
    (hn : p.natAbs.beq n = true) : (bernoulli (2 * m + 2)).num.natAbs = n := by
  rw [hnum]; exact Nat.eq_of_beq_eq_true hn

end TangentNumbers
end
end CertificatePort138
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/Sfrac.lean -/
section CertificatePort132


/-!
# The signed rational `sfrac`

The signed rational `sfrac neg cn cd = ±cn/cd` (centre and radius are ratios of naturals with the
sign a separate `Bool`) and its recasting/positivity lemmas. Each recasting lemma proves
`<surface form> = sfrac neg num den`, so together they form the vocabulary of the rational
recogniser and the endpoint representation used by the interval-enclosure layer.

This module depends only on Mathlib. It is the base of the `Enclosure` namespace: the
interval-arithmetic layer (`Enclosure.*`) builds directly on it, and the binary-split engine
(`Enclosure.BinarySplit.Basic`) opens `Enclosure` for the `sfrac` vocabulary.
-/
section


namespace Enclosure

/-! ### The signed rational `sfrac` -/

/- The real value of a sign-flagged natural fraction: `−cn/cd` when `neg`, else `cn/cd`. -/
noncomputable def sfrac (neg : Bool) (cn cd : ℕ) : ℝ := (if neg then -1 else 1) * ((cn : ℝ) / cd)

/- Flipping the sign flag negates the signed fraction. -/
theorem sfrac_not (neg : Bool) (cn cd : ℕ) : sfrac (!neg) cn cd = - sfrac neg cn cd := by
  cases neg <;> simp [sfrac]

/- A `false`-signed fraction is the bare quotient `↑cn/↑cd` (the form the certificate lemmas
emit). -/
theorem sfrac_false_div (cn cd : ℕ) : sfrac false cn cd = (cn : ℝ) / cd := by simp [sfrac]

/- A `true`-signed fraction is the negated quotient `(-↑cn)/↑cd` (the form the reciprocal
certificate lemmas emit for a negative argument). -/
theorem sfrac_true_div (cn cd : ℕ) : sfrac true cn cd = (-(cn : ℝ)) / cd := by simp [sfrac, neg_div]

/- Decimal literal `OfScientific m true e` (`= m·10⁻ᵉ`) as the fraction `↑m/↑v` with `v = 10^e`. -/
theorem ofScientific_dyadic_arg (m e v : ℕ) (hv : (Nat.pow 10 e).beq v = true) :
    (OfScientific.ofScientific m true e : ℝ) = (m : ℝ) / (v : ℝ) := by
  have hv : 10 ^ e = v := Nat.eq_of_beq_eq_true hv
  subst hv
  rw [← Rat.cast_ofScientific, Rat.ofScientific_def_eq_if]
  simp

/-! ### Recasting lemmas (each proves `<surface> = sfrac neg num den`) -/

/- Integer atom in `Nat.cast` form: `↑n = sfrac false n 1`. Used for numerals `≥ 2` (whose `↑n` is
defeq to the goal's `OfNat` literal) and for `Nat.cast` arguments. -/
theorem sfrac_natCast (n : ℕ) : (n : ℝ) = sfrac false n 1 := by simp [sfrac]

/- The literal `0`, kept as the goal's `OfNat` form. -/
theorem sfrac_zero_eq : (0 : ℝ) = sfrac false (nat_lit 0) (nat_lit 1) := by simp [sfrac]

/- The literal `1`, kept as the goal's `OfNat` form. -/
theorem sfrac_one_eq : (1 : ℝ) = sfrac false (nat_lit 1) (nat_lit 1) := by simp [sfrac]

/- Negation flips the sign flag. -/
theorem sfrac_neg_eq (x : ℝ) (neg : Bool) (num den : ℕ) (h : x = sfrac neg num den) :
    -x = sfrac (!neg) num den := by rw [h, sfrac_not]

/- A quotient of two signed integers `±an / ±bn` is the signed fraction with `xor`-ed sign. -/
theorem sfrac_div_eq (na nb : ℝ) (an bn : ℕ) (aneg bneg : Bool)
    (hn : na = sfrac aneg an 1) (hd : nb = sfrac bneg bn 1) :
    na / nb = sfrac (aneg != bneg) an bn := by
  rw [hn, hd]
  cases aneg <;> cases bneg <;> simp [sfrac] <;> ring

/- A decimal literal `OfScientific m true e` (`= m·10⁻ᵉ`, `v = 10^e`) as `sfrac false m v`. -/
theorem sfrac_ofScientific_eq (m e v : ℕ) (hv : (Nat.pow 10 e).beq v = true) :
    (OfScientific.ofScientific m true e : ℝ) = sfrac false m v := by
  rw [ofScientific_dyadic_arg m e v hv]; simp [sfrac]

/- `0 < n` (in `ℕ`) from a kernel `Nat.ble 1 n` side condition (`Nat.blt 0 n` unfolds to
exactly `Nat.ble 1 n`, so the conditions are stated as `ble` to save the kernel one unfold
per evaluation). -/
theorem pos_of_ble {n : ℕ} (h : Nat.ble 1 n = true) : 0 < n :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_ble_eq_true h)

/- `(0:ℝ) < n` from a kernel `Nat.ble 1 n` side condition (`Nat.blt 0 n` unfolds to
exactly `Nat.ble 1 n`, so the conditions are stated as `ble` to save the kernel one
unfold per evaluation). -/
theorem pos_real_of_ble {n : ℕ} (h : Nat.ble 1 n = true) : (0 : ℝ) < n := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_ble_eq_true h)

/- Strict comparison of two nonnegative rational-literal reals through their `sfrac` forms:
one cross-multiplied `Nat.blt`, kernel-evaluated. The certificate bundles' interval-disjointness
chains are nested `List.IsChain.cons_cons` proof terms over this. -/
theorem sfrac_ratCast_natDiv (p Q : ℕ) : (((p : ℚ) / (Q : ℚ) : ℚ) : ℝ) = sfrac false p Q := by
  rw [sfrac_false_div]; push_cast; ring

/- The real cast of a signed dyadic `ℚ` value `(↑mp − ↑mn)/↑Q` (the `mkSignedDyadic` shape) when
`mp ≥ mn`: sign `false`, magnitude `mp − mn`. -/
theorem sfrac_ratCast_intSub_nonneg (mp mn Q : ℕ) (hge : Nat.ble mn mp = true) :
    (((((mp : ℤ) - (mn : ℤ) : ℤ) : ℚ) / (Q : ℚ) : ℚ) : ℝ) = sfrac false (mp - mn) Q := by
  simp only [Nat.ble_eq] at hge
  rw [sfrac_false_div]; push_cast [Nat.cast_sub hge]; ring

/- The real cast of a signed dyadic `ℚ` value `(↑mp − ↑mn)/↑Q` when `mp ≤ mn`: sign `true`,
magnitude `mn − mp`. -/
theorem sfrac_ratCast_intSub_neg (mp mn Q : ℕ) (hle : Nat.ble mp mn = true) :
    (((((mp : ℤ) - (mn : ℤ) : ℤ) : ℚ) / (Q : ℚ) : ℚ) : ℝ) = sfrac true (mn - mp) Q := by
  simp only [Nat.ble_eq] at hle
  rw [sfrac_true_div]; push_cast [Nat.cast_sub hle]; ring

/- The real cast of a negated `ℚ` value flips the sign flag of its recognised `sfrac` form. -/
theorem sfrac_ratCast_neg (q : ℚ) (neg : Bool) (num den : ℕ)
    (h : ((q : ℚ) : ℝ) = sfrac neg num den) : ((-q : ℚ) : ℝ) = sfrac (!neg) num den := by
  rw [sfrac_not, ← h]; push_cast; ring

/- Natural power of a recognised rational: from `x = sfrac neg u v`, `x ^ n = sfrac neg' un vn`
with `un = u^n`, `vn = v^n` and the sign `neg' = neg && n odd`. Holds for every `u`, `v`, `n`,
including `v = 0` (both sides are then `0` for `n > 0`) and `n = 0` (both sides are `1`). -/
theorem sfrac_pow_eq (x : ℝ) (neg neg' : Bool) (u v n un vn : ℕ)
    (hx : x = sfrac neg u v)
    (hs : (Bool.xor neg' (Bool.and neg ((Nat.mod n 2).beq 1))).not = true)
    (hun : un.beq (Nat.pow u n) = true) (hvn : vn.beq (Nat.pow v n) = true) :
    x ^ n = sfrac neg' un vn := by
  obtain rfl : un = u ^ n := Nat.eq_of_beq_eq_true hun
  obtain rfl : vn = v ^ n := Nat.eq_of_beq_eq_true hvn
  subst hx
  have hdiv : ((u : ℝ) / v) ^ n = ((u ^ n : ℕ) : ℝ) / ((v ^ n : ℕ) : ℝ) := by
    push_cast
    rw [div_pow]
  cases neg with
  | false =>
    obtain rfl : neg' = false := by simpa using hs
    rw [sfrac_false_div, sfrac_false_div, hdiv]
  | true =>
    cases neg' with
    | true =>
      have hodd : Odd n := by
        have h1 : Nat.mod n 2 = 1 := Nat.eq_of_beq_eq_true (by simpa using hs)
        exact Nat.odd_iff.2 (by omega)
      rw [sfrac_true_div, sfrac_true_div, neg_div, neg_div, hodd.neg_pow, hdiv]
    | false =>
      have heven : Even n := by
        have h1 : Nat.beq (Nat.mod n 2) 1 = false := by simpa using hs
        have h2 : n % 2 ≠ 1 := Nat.ne_of_beq_eq_false h1
        exact Nat.even_iff.2 (by omega)
      rw [sfrac_true_div, sfrac_false_div, neg_div, heven.neg_pow, hdiv]

end Enclosure

end

end CertificatePort132
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/BinarySplit/Defs.lean -/
section CertificatePort139

/-!
# Binary-splitting definitions that need no `Mathlib`

`binarySplit` and the series coefficients the `*_dyadic_bound` lemmas are stated with, kept free of
`Mathlib` so that compiled checkers (the `NativeCode` library) can use exactly the same functions
the lemmas mention. Their specs live with the lemmas (`Enclosure.BinarySplit.Basic`,
`Enclosure.BinarySplit.Functions.*`).
-/
section

namespace BSN

/- Minimal binary split. `(T, Q, P)` with `∑_{m≤i<n} ∏_{m≤j≤i}(p j/q j) = T/Q` and
`∏_{m≤j<n}(p j/q j) = P/Q`. -/
def binarySplit (p q : Nat → Nat) (m n : Nat) : Nat × Nat × Nat :=
  if _h : m < n then
    if _h2 : m + 1 = n then (p m, q m, p m)
    else
      let (tl, ql, pl) := binarySplit p q m ((m + n) / 2)
      let (tr, qr, pr) := binarySplit p q ((m + n) / 2) n
      (tl * qr + pl * tr, ql * qr, pl * pr)
  else (0, 1, 1)
termination_by n - m
decreasing_by all_goals omega

/-! ### Series coefficients -/

/- Even-indexed cos sub-series `∑_j (u/v)^{4j}/(4j)!`: leading factor `1`,
ratio `u^4 / (v^4·(4k+1)(4k+2)(4k+3)(4k+4))`. -/
def cosEvenP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def cosEvenQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.succ (Nat.mul 4 k)) (Nat.add (Nat.mul 4 k) 2))
      (Nat.add (Nat.mul 4 k) 3)) (Nat.add (Nat.mul 4 k) 4))

/- Odd-indexed cos sub-series `∑_j (u/v)^{4j+2}/(4j+2)!`: leading factor
`u^2/(2 v^2)`, ratio `u^4 / (v^4·(4k+3)(4k+4)(4k+5)(4k+6))`. -/
def cosOddP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def cosOddQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 3) (Nat.add (Nat.mul 4 k) 4))
      (Nat.add (Nat.mul 4 k) 5)) (Nat.add (Nat.mul 4 k) 6))

/- Even-indexed sin sub-series `∑_j (u/v)^{4j+1}/(4j+1)!`: leading factor `u/v`,
ratio `u^4 / (v^4·(4k+2)(4k+3)(4k+4)(4k+5))`. -/
def sinEvenP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def sinEvenQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 2) (Nat.add (Nat.mul 4 k) 3))
      (Nat.add (Nat.mul 4 k) 4)) (Nat.add (Nat.mul 4 k) 5))

/- Odd-indexed sin sub-series `∑_j (u/v)^{4j+3}/(4j+3)!`: leading factor
`u^3/(6 v^3)`, ratio `u^4 / (v^4·(4k+4)(4k+5)(4k+6)(4k+7))`. -/
def sinOddP (u : Nat) : Nat → Nat := fun _ => Nat.pow u 4
def sinOddQ (v : Nat) : Nat → Nat := fun k =>
  Nat.mul (Nat.pow v 4)
    (Nat.mul (Nat.mul (Nat.mul (Nat.add (Nat.mul 4 k) 4) (Nat.add (Nat.mul 4 k) 5))
      (Nat.add (Nat.mul 4 k) 6)) (Nat.add (Nat.mul 4 k) 7))

/- `artanh(u/v)`: leading factor `u/v`, ratio `u^2(2k+1) / (v^2(2k+3))`. -/
def artanhP (u : Nat) : Nat
    → Nat := fun k => Nat.mul (Nat.pow u (nat_lit 2)) (Nat.succ (Nat.mul (nat_lit 2) k))
def artanhQ (v : Nat) : Nat
    → Nat := fun k => Nat.mul (Nat.pow v (nat_lit 2)) (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 3))

/- Even-indexed arctan sub-series `∑_j (u/v)^{4j+1}/(4j+1)`: leading factor `u/v`,
ratio `u^4·(4k+1) / (v^4·(4k+5))`. -/
def arctanEvenP (u : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow u 4) (Nat.succ (Nat.mul 4 k))
def arctanEvenQ (v : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow v 4) (Nat.add (Nat.mul 4 k) 5)

/- Odd-indexed arctan sub-series `∑_j (u/v)^{4j+3}/(4j+3)`: leading factor `u^3/(3 v^3)`,
ratio `u^4·(4k+3) / (v^4·(4k+7))`. -/
def arctanOddP (u : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow u 4) (Nat.add (Nat.mul 4 k) 3)
def arctanOddQ (v : Nat) : Nat → Nat := fun k => Nat.mul (Nat.pow v 4) (Nat.add (Nat.mul 4 k) 7)

end BSN

end

end CertificatePort139
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/BinarySplit/Basic.lean -/
section CertificatePort140


/-!
# The binary-split engine over `ℕ`

`binarySplit`, computing `∑_{m≤i<n} (a i / b i) · ∏_{m≤j<i} (p j / q j)` and the running product as
integer numerator/denominator pairs over `ℕ`, with its spec and the certificate equation lemmas
(`binarySplit_of_le`/`_of_base`/`_rec`), whose boolean side conditions (`Nat.beq`/`ble`/`blt`) the
proof metaprogram discharges by reflection. The signed rational `sfrac` it works over lives in
`Enclosure.Sfrac` (opened below).

The design follows Bhavik Mehta's `Compute/LogSmallBig.lean`: the certificate lemmas carry the
literal result tuple, and the companion metaprogram (`Enclosure.BinarySplit.Tactic.Engine`) computes
the tuple in `MetaM` and emits these literals, leaving the kernel only `Nat.beq` equalities on
concrete numerals to check.
-/
section


namespace BSN
open Enclosure

/-! ### The binary-split engine

Each term is a running product `term_i = ∏_{m≤j≤i} (p j / q j)`, and `binarySplit` returns
`(T, Q, P)` with `∑ term_i = T/Q`, `∏ (p/q) = P/Q`, where `Q = ∏q` is the true common denominator
(no redundant factor). Combine: `T = Tl·Qr + Pl·Tr`, `Q = Ql·Qr`, `P = Pl·Pr`. The certificate
lemmas (`binarySplit_of_le`/`_of_base`/`_rec`) carry literal outputs tied by `beq`; `proveBS` emits
the tuple with `beq` reflection. -/

open Finset

/- The `P`, `Q` components are products over the range. -/
theorem binarySplit_PQ {p q : ℕ → ℕ} {m n : ℕ} :
    (binarySplit p q m n).2.2 = ∏ j ∈ Ico m n, p j ∧
    (binarySplit p q m n).2.1 = ∏ j ∈ Ico m n, q j := by
  fun_induction binarySplit with
  | case1 m hlt => simp [Nat.Ico_succ_singleton]
  | case3 m n => simp_all
  | case2 m n hlt hne tl ql pl hL tr qr pr hR ihL ihR =>
    simp only [hL] at ihL; simp only [hR] at ihR
    have hmk : m ≤ (m + n) / 2 := by omega
    have hkn : (m + n) / 2 ≤ n := by omega
    refine ⟨?_, ?_⟩ <;>
      rw [← prod_Ico_consecutive _ hmk hkn] <;> simp [ihL.1, ihL.2, ihR.1, ihR.2]

theorem binarySplit_nonzero {p q : ℕ → ℕ} {m n : ℕ} (hq : ∀ i, q i ≠ 0) :
    (binarySplit p q m n).2.1 ≠ 0 := by
  fun_induction binarySplit <;> simp_all

/- Spec: `T/Q` is the sum and `P/Q` is the product. -/
theorem binarySplit_spec {p q : ℕ → ℕ} {m n T Q P : ℕ} (hq : ∀ i, q i ≠ 0)
    (h : (T, Q, P) = binarySplit p q m n) :
    (∏ j ∈ Ico m n, ((p j : ℚ) / q j) = (P : ℚ) / Q) ∧
    (∑ i ∈ Ico m n, ∏ j ∈ Ico m (i + 1), ((p j : ℚ) / q j) = (T : ℚ) / Q) := by
  fun_induction binarySplit generalizing T Q P with
  | case1 m hlt =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hIco : Finset.Ico m (m + 1) = {m} := by
      ext x; rw [Finset.mem_Ico, Finset.mem_singleton]; omega
    simp [hIco]
  | case3 m n =>
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [Ico_eq_empty (by omega : ¬ m < n)]
  | case2 m n hlt hne tl ql pl hL tr qr pr hR ihL ihR =>
    specialize ihL hL.symm; specialize ihR hR.symm
    have hmk : m ≤ (m + n) / 2 := by omega
    have hkn : (m + n) / 2 ≤ n := by omega
    obtain ⟨hPl, hSl⟩ := ihL
    obtain ⟨hPr, hSr⟩ := ihR
    obtain ⟨hPpl, hQl⟩ := (binarySplit_PQ (p := p) (q := q) (m := m) (n := (m + n) / 2))
    simp only [hL] at hPpl hQl
    obtain ⟨hPpr, hQr⟩ := (binarySplit_PQ (p := p) (q := q) (m := (m + n) / 2) (n := n))
    simp only [hR] at hPpr hQr
    have hqtl := binarySplit_nonzero (p := p) (m := m) (n := (m + n) / 2) hq
    simp only [hL] at hqtl
    have hqtr := binarySplit_nonzero (p := p) (m := (m + n) / 2) (n := n) hq
    simp only [hR] at hqtr
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hqlr : (ql : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqtl
    have hqrr : (qr : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqtr
    constructor
    · rw [← prod_Ico_consecutive _ hmk hkn, hPl, hPr]; push_cast; field_simp
    · rw [← sum_Ico_consecutive _ hmk hkn, hSl]
      have hsplit : ∑ i ∈ Ico ((m + n) / 2) n, ∏ j ∈ Ico m (i + 1), ((p j : ℚ) / q j)
          = ((pl : ℚ) / ql) * ∑ i ∈ Ico ((m + n) / 2) n, ∏ j ∈ Ico ((m + n) / 2) (i + 1),
              ((p j : ℚ) / q j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [Finset.mem_Ico] at hi
        rw [← prod_Ico_consecutive _ hmk (by omega : (m + n) / 2 ≤ i + 1), hPl]
      rw [hsplit, hSr]
      push_cast
      field_simp

/-! ### Certificate equation lemmas (literal outputs tied by `beq`), for the proof metaprogram.

The boolean side conditions are phrased with the primitive `Nat.add`/`Nat.mul`/... so the
kernel meets them directly, without unfolding `HAdd.hAdd → Add.add → Nat.add` per condition. -/

/- Primitive-to-notation form of `Nat.div`, the companion of `Nat.add_eq`/`Nat.mul_eq`. -/
theorem Nat.div_eq' {a b : ℕ} : a.div b = a / b := rfl

theorem binarySplit_of_le {p q : ℕ → ℕ} {m n : ℕ} (h : n.ble m) :
    binarySplit p q m n = (0, 1, 1) := by
  rw [binarySplit]; simp only [Nat.ble_eq] at h; rw [dif_neg (by omega)]

theorem binarySplit_of_base {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.succ).beq n) (hT : T.beq (p m)) (hQ : Q.beq (q m)) (hP : P.beq (p m)) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  rw [binarySplit, dif_pos (by omega), dif_pos rfl]

theorem binarySplit_rec {p q : ℕ → ℕ}
    {m n k tl ql pl tr qr pr T Q P : ℕ}
    (h1 : (m.succ).blt n) (hk : k.beq ((m.add n).div 2))
    (hT : T.beq ((tl.mul qr).add (pl.mul tr))) (hQ : Q.beq (ql.mul qr))
    (hP : P.beq (pl.mul pr))
    (hl : binarySplit p q m k = (tl, ql, pl))
    (hr : binarySplit p q k n = (tr, qr, pr)) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.div_eq'] at h1 hk hT hQ hP
  subst hk hT hQ hP
  rw [binarySplit, dif_pos (by omega), dif_neg (by omega), hl, hr]

/-! Wider base cases collapse a two- to four-leaf subtree into one application, so the proof
metaprogram materializes one node where the leaf/leaf/`_rec` shape needed three (`_of_base2`),
five (`_of_base3`), or seven (`_of_base4`). The tuples are the same combines over the same
midpoint splits, so the emitted literals match the narrow-base tree's roots exactly, and the
side conditions stay single `Nat.beq`s over the sequence values. -/

theorem binarySplit_of_base2 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 2).beq n)
    (hT : T.beq (((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))))
    (hQ : Q.beq ((q m).mul (q (m.succ))))
    (hP : P.beq ((p m).mul (p (m.succ)))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 1) = (p m, q m, p m) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  have hr : binarySplit p q (m + 1) (m + 2) = (p (m + 1), q (m + 1), p (m + 1)) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base3 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 3).beq n)
    (hT : T.beq (((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add
      ((p m).mul (((p (m.succ)).mul (q (m.add 2))).add
        ((p (m.succ)).mul (p (m.add 2)))))))
    (hQ : Q.beq ((q m).mul ((q (m.succ)).mul (q (m.add 2)))))
    (hP : P.beq ((p m).mul ((p (m.succ)).mul (p (m.add 2))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 1) = (p m, q m, p m) :=
    binarySplit_of_base (by simp) (by simp) (by simp) (by simp)
  have hr : binarySplit p q (m + 1) (m + 3) =
      (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2), q (m + 1) * q (m + 2),
        p (m + 1) * p (m + 2)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base4 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 4).beq n)
    (hT : T.beq (((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul
        ((q (m.add 2)).mul (q (m.add 3)))).add
      (((p m).mul (p (m.succ))).mul
        (((p (m.add 2)).mul (q (m.add 3))).add ((p (m.add 2)).mul (p (m.add 3)))))))
    (hQ : Q.beq (((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))))
    (hP : P.beq (((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 2) =
      (p m * q (m + 1) + p m * p (m + 1), q m * q (m + 1), p m * p (m + 1)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 2) (m + 4) =
      (p (m + 2) * q (m + 3) + p (m + 2) * p (m + 3), q (m + 2) * q (m + 3),
        p (m + 2) * p (m + 3)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

/-! The rest of the ladder (widths 5-16, generated mechanically as midpoint combines of two
narrower bases; see `dev/gen_base_lemmas.py`): `proveBS` dispatches on `n - m` up to its cap. -/

theorem binarySplit_of_base5 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 5).beq n)
    (hT : T.beq (((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add 2)).mul
        ((q (m.add 3)).mul (q (m.add 4))))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul
        ((q (m.add 3)).mul (q (m.add 4)))).add ((p (m.add 2)).mul (((p (m.add 3)).mul (q (m.add
        4))).add ((p (m.add 3)).mul (p (m.add 4)))))))))
    (hQ : Q.beq (((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul ((q (m.add 3)).mul (q (m.add
        4))))))
    (hP : P.beq (((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add
        4)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 2) =
      (p m * q (m + 1) + p m * p (m + 1), q m * q (m + 1), p m * p (m + 1)) :=
    binarySplit_of_base2 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 2) (m + 5) =
      (p (m + 2) * (q (m + 3) * q (m + 4)) + p (m + 2) * (p (m + 3) * q (m + 4) + p (m + 3) * p (m
          + 4)), q (m + 2) * (q (m + 3) * q (m + 4)), p (m + 2) * (p (m + 3) * p (m + 4))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base6 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 6).beq n)
    (hT : T.beq (((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5)))))))))
    (hQ : Q.beq (((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))))
    (hP : P.beq (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 3) =
      (p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2)), q m
          * (q (m + 1) * q (m + 2)), p m * (p (m + 1) * p (m + 2))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 3) (m + 6) =
      (p (m + 3) * (q (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m
          + 5)), q (m + 3) * (q (m + 4) * q (m + 5)), p (m + 3) * (p (m + 4) * p (m + 5))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base7 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 7).beq n)
    (hT : T.beq (((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul (((q (m.add 3)).mul (q
        (m.add 4))).mul ((q (m.add 5)).mul (q (m.add 6))))).add (((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((((p (m.add 3)).mul (q (m.add 4))).add ((p (m.add 3)).mul (p (m.add
        4)))).mul ((q (m.add 5)).mul (q (m.add 6)))).add (((p (m.add 3)).mul (p (m.add 4))).mul
        (((p (m.add 5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))))))))
    (hQ : Q.beq (((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul (((q (m.add 3)).mul (q (m.add
        4))).mul ((q (m.add 5)).mul (q (m.add 6))))))
    (hP : P.beq (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add
        4))).mul ((p (m.add 5)).mul (p (m.add 6)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 3) =
      (p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2)), q m
          * (q (m + 1) * q (m + 2)), p m * (p (m + 1) * p (m + 2))) :=
    binarySplit_of_base3 (by simp +arith) (by simp +arith) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 3) (m + 7) =
      ((p (m + 3) * q (m + 4) + p (m + 3) * p (m + 4)) * (q (m + 5) * q (m + 6)) + p (m + 3) * p
          (m + 4) * (p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6)), q (m + 3) * q (m + 4) * (q (m
          + 5) * q (m + 6)), p (m + 3) * p (m + 4) * (p (m + 5) * p (m + 6))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base8 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 8).beq n)
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul (q (m.add 7))))).add ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul
        (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add
        5)))).mul ((q (m.add 6)).mul (q (m.add 7)))).add (((p (m.add 4)).mul (p (m.add 5))).mul
        (((p (m.add 6)).mul (q (m.add 7))).add ((p (m.add 6)).mul (p (m.add 7)))))))))
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q (m.add
        4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul (q (m.add 7))))))
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add
        4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul (p (m.add 7)))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 4) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3)), q m * q (m + 1) * (q (m + 2) * q (m + 3)), p m
          * p (m + 1) * (p (m + 2) * p (m + 3))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 4) (m + 8) =
      ((p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5)) * (q (m + 6) * q (m + 7)) + p (m + 4) * p
          (m + 5) * (p (m + 6) * q (m + 7) + p (m + 6) * p (m + 7)), q (m + 4) * q (m + 5) * (q (m
          + 6) * q (m + 7)), p (m + 4) * p (m + 5) * (p (m + 6) * p (m + 7))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base9 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 9).beq n)
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))))).add ((((p m).mul (p (m.add
        1))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add
        ((p (m.add 4)).mul (p (m.add 5)))).mul ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add
        8))))).add (((p (m.add 4)).mul (p (m.add 5))).mul (((p (m.add 6)).mul ((q (m.add 7)).mul
        (q (m.add 8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p (m.add
        7)).mul (p (m.add 8)))))))))))
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q (m.add
        4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))))))
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add
        4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 4) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3)), q m * q (m + 1) * (q (m + 2) * q (m + 3)), p m
          * p (m + 1) * (p (m + 2) * p (m + 3))) :=
    binarySplit_of_base4 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 4) (m + 9) =
      ((p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5)) * (q (m + 6) * (q (m + 7) * q (m + 8))) + p
          (m + 4) * p (m + 5) * (p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q
          (m + 8) + p (m + 7) * p (m + 8))), q (m + 4) * q (m + 5) * (q (m + 6) * (q (m + 7) * q
          (m + 8))), p (m + 4) * p (m + 5) * (p (m + 6) * (p (m + 7) * p (m + 8)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base10 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 10).beq n)
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4))))).add (((p m).mul (p (m.succ))).mul (((p (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4)))).add ((p (m.add 2)).mul (((p (m.add 3)).mul (q
        (m.add 4))).add ((p (m.add 3)).mul (p (m.add 4)))))))).mul (((q (m.add 5)).mul (q (m.add
        6))).mul ((q (m.add 7)).mul ((q (m.add 8)).mul (q (m.add 9)))))).add ((((p m).mul (p
        (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add 4))))).mul (((((p (m.add
        5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))).mul ((q (m.add 7)).mul ((q
        (m.add 8)).mul (q (m.add 9))))).add (((p (m.add 5)).mul (p (m.add 6))).mul (((p (m.add
        7)).mul ((q (m.add 8)).mul (q (m.add 9)))).add ((p (m.add 7)).mul (((p (m.add 8)).mul (q
        (m.add 9))).add ((p (m.add 8)).mul (p (m.add 9)))))))))))
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul ((q (m.add 3)).mul (q (m.add
        4))))).mul (((q (m.add 5)).mul (q (m.add 6))).mul ((q (m.add 7)).mul ((q (m.add 8)).mul (q
        (m.add 9)))))))
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add
        4))))).mul (((p (m.add 5)).mul (p (m.add 6))).mul ((p (m.add 7)).mul ((p (m.add 8)).mul (p
        (m.add 9))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 5) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * (q (m + 3) * q (m + 4))) + p m * p (m +
          1) * (p (m + 2) * (q (m + 3) * q (m + 4)) + p (m + 2) * (p (m + 3) * q (m + 4) + p (m +
          3) * p (m + 4))), q m * q (m + 1) * (q (m + 2) * (q (m + 3) * q (m + 4))), p m * p (m +
          1) * (p (m + 2) * (p (m + 3) * p (m + 4)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 5) (m + 10) =
      ((p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6)) * (q (m + 7) * (q (m + 8) * q (m + 9))) + p
          (m + 5) * p (m + 6) * (p (m + 7) * (q (m + 8) * q (m + 9)) + p (m + 7) * (p (m + 8) * q
          (m + 9) + p (m + 8) * p (m + 9))), q (m + 5) * q (m + 6) * (q (m + 7) * (q (m + 8) * q
          (m + 9))), p (m + 5) * p (m + 6) * (p (m + 7) * (p (m + 8) * p (m + 9)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base11 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 11).beq n)
    (hT : T.beq (((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4))))).add (((p m).mul (p (m.succ))).mul (((p (m.add
        2)).mul ((q (m.add 3)).mul (q (m.add 4)))).add ((p (m.add 2)).mul (((p (m.add 3)).mul (q
        (m.add 4))).add ((p (m.add 3)).mul (p (m.add 4)))))))).mul (((q (m.add 5)).mul ((q (m.add
        6)).mul (q (m.add 7)))).mul ((q (m.add 8)).mul ((q (m.add 9)).mul (q (m.add 10)))))).add
        ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add 4))))).mul
        (((((p (m.add 5)).mul ((q (m.add 6)).mul (q (m.add 7)))).add ((p (m.add 5)).mul (((p
        (m.add 6)).mul (q (m.add 7))).add ((p (m.add 6)).mul (p (m.add 7)))))).mul ((q (m.add
        8)).mul ((q (m.add 9)).mul (q (m.add 10))))).add (((p (m.add 5)).mul ((p (m.add 6)).mul (p
        (m.add 7)))).mul (((p (m.add 8)).mul ((q (m.add 9)).mul (q (m.add 10)))).add ((p (m.add
        8)).mul (((p (m.add 9)).mul (q (m.add 10))).add ((p (m.add 9)).mul (p (m.add 10)))))))))))
    (hQ : Q.beq ((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul ((q (m.add 3)).mul (q (m.add
        4))))).mul (((q (m.add 5)).mul ((q (m.add 6)).mul (q (m.add 7)))).mul ((q (m.add 8)).mul
        ((q (m.add 9)).mul (q (m.add 10)))))))
    (hP : P.beq ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul ((p (m.add 3)).mul (p (m.add
        4))))).mul (((p (m.add 5)).mul ((p (m.add 6)).mul (p (m.add 7)))).mul ((p (m.add 8)).mul
        ((p (m.add 9)).mul (p (m.add 10))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 5) =
      ((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * (q (m + 3) * q (m + 4))) + p m * p (m +
          1) * (p (m + 2) * (q (m + 3) * q (m + 4)) + p (m + 2) * (p (m + 3) * q (m + 4) + p (m +
          3) * p (m + 4))), q m * q (m + 1) * (q (m + 2) * (q (m + 3) * q (m + 4))), p m * p (m +
          1) * (p (m + 2) * (p (m + 3) * p (m + 4)))) :=
    binarySplit_of_base5 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 5) (m + 11) =
      ((p (m + 5) * (q (m + 6) * q (m + 7)) + p (m + 5) * (p (m + 6) * q (m + 7) + p (m + 6) * p
          (m + 7))) * (q (m + 8) * (q (m + 9) * q (m + 10))) + p (m + 5) * (p (m + 6) * p (m + 7))
          * (p (m + 8) * (q (m + 9) * q (m + 10)) + p (m + 8) * (p (m + 9) * q (m + 10) + p (m +
          9) * p (m + 10))), q (m + 5) * (q (m + 6) * q (m + 7)) * (q (m + 8) * (q (m + 9) * q (m
          + 10))), p (m + 5) * (p (m + 6) * p (m + 7)) * (p (m + 8) * (p (m + 9) * p (m + 10))))
          :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base12 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 12).beq n)
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5)))))))).mul (((q (m.add 6)).mul
        ((q (m.add 7)).mul (q (m.add 8)))).mul ((q (m.add 9)).mul ((q (m.add 10)).mul (q (m.add
        11)))))).add ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p
        (m.add 4)).mul (p (m.add 5))))).mul (((((p (m.add 6)).mul ((q (m.add 7)).mul (q (m.add
        8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p (m.add 7)).mul (p
        (m.add 8)))))).mul ((q (m.add 9)).mul ((q (m.add 10)).mul (q (m.add 11))))).add (((p
        (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul (((p (m.add 9)).mul ((q (m.add
        10)).mul (q (m.add 11)))).add ((p (m.add 9)).mul (((p (m.add 10)).mul (q (m.add 11))).add
        ((p (m.add 10)).mul (p (m.add 11)))))))))))
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))).mul (((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))).mul
        ((q (m.add 9)).mul ((q (m.add 10)).mul (q (m.add 11)))))))
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5))))).mul (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        ((p (m.add 9)).mul ((p (m.add 10)).mul (p (m.add 11))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 6) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * (q (m + 4) * q (m + 5))) + p m * (p (m + 1) * p (m + 2)) * (p (m + 3) * (q
          (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5))), q m
          * (q (m + 1) * q (m + 2)) * (q (m + 3) * (q (m + 4) * q (m + 5))), p m * (p (m + 1) * p
          (m + 2)) * (p (m + 3) * (p (m + 4) * p (m + 5)))) :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 6) (m + 12) =
      ((p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q (m + 8) + p (m + 7) * p
          (m + 8))) * (q (m + 9) * (q (m + 10) * q (m + 11))) + p (m + 6) * (p (m + 7) * p (m +
          8)) * (p (m + 9) * (q (m + 10) * q (m + 11)) + p (m + 9) * (p (m + 10) * q (m + 11) + p
          (m + 10) * p (m + 11))), q (m + 6) * (q (m + 7) * q (m + 8)) * (q (m + 9) * (q (m + 10)
          * q (m + 11))), p (m + 6) * (p (m + 7) * p (m + 8)) * (p (m + 9) * (p (m + 10) * p (m +
          11)))) :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base13 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 13).beq n)
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul ((q (m.add 3)).mul ((q
        (m.add 4)).mul (q (m.add 5))))).add (((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul
        (((p (m.add 3)).mul ((q (m.add 4)).mul (q (m.add 5)))).add ((p (m.add 3)).mul (((p (m.add
        4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add 5)))))))).mul (((q (m.add 6)).mul
        ((q (m.add 7)).mul (q (m.add 8)))).mul (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add
        11)).mul (q (m.add 12)))))).add ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p
        (m.add 3)).mul ((p (m.add 4)).mul (p (m.add 5))))).mul (((((p (m.add 6)).mul ((q (m.add
        7)).mul (q (m.add 8)))).add ((p (m.add 6)).mul (((p (m.add 7)).mul (q (m.add 8))).add ((p
        (m.add 7)).mul (p (m.add 8)))))).mul (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add
        11)).mul (q (m.add 12))))).add (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        (((((p (m.add 9)).mul (q (m.add 10))).add ((p (m.add 9)).mul (p (m.add 10)))).mul ((q
        (m.add 11)).mul (q (m.add 12)))).add (((p (m.add 9)).mul (p (m.add 10))).mul (((p (m.add
        11)).mul (q (m.add 12))).add ((p (m.add 11)).mul (p (m.add 12)))))))))))
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul ((q (m.add 3)).mul ((q (m.add
        4)).mul (q (m.add 5))))).mul (((q (m.add 6)).mul ((q (m.add 7)).mul (q (m.add 8)))).mul
        (((q (m.add 9)).mul (q (m.add 10))).mul ((q (m.add 11)).mul (q (m.add 12)))))))
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul ((p (m.add 3)).mul ((p (m.add
        4)).mul (p (m.add 5))))).mul (((p (m.add 6)).mul ((p (m.add 7)).mul (p (m.add 8)))).mul
        (((p (m.add 9)).mul (p (m.add 10))).mul ((p (m.add 11)).mul (p (m.add 12))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 6) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * (q (m + 4) * q (m + 5))) + p m * (p (m + 1) * p (m + 2)) * (p (m + 3) * (q
          (m + 4) * q (m + 5)) + p (m + 3) * (p (m + 4) * q (m + 5) + p (m + 4) * p (m + 5))), q m
          * (q (m + 1) * q (m + 2)) * (q (m + 3) * (q (m + 4) * q (m + 5))), p m * (p (m + 1) * p
          (m + 2)) * (p (m + 3) * (p (m + 4) * p (m + 5)))) :=
    binarySplit_of_base6 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 6) (m + 13) =
      ((p (m + 6) * (q (m + 7) * q (m + 8)) + p (m + 6) * (p (m + 7) * q (m + 8) + p (m + 7) * p
          (m + 8))) * (q (m + 9) * q (m + 10) * (q (m + 11) * q (m + 12))) + p (m + 6) * (p (m +
          7) * p (m + 8)) * ((p (m + 9) * q (m + 10) + p (m + 9) * p (m + 10)) * (q (m + 11) * q
          (m + 12)) + p (m + 9) * p (m + 10) * (p (m + 11) * q (m + 12) + p (m + 11) * p (m +
          12))), q (m + 6) * (q (m + 7) * q (m + 8)) * (q (m + 9) * q (m + 10) * (q (m + 11) * q
          (m + 12))), p (m + 6) * (p (m + 7) * p (m + 8)) * (p (m + 9) * p (m + 10) * (p (m + 11)
          * p (m + 12)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base14 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 14).beq n)
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul (((q (m.add 3)).mul (q
        (m.add 4))).mul ((q (m.add 5)).mul (q (m.add 6))))).add (((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((((p (m.add 3)).mul (q (m.add 4))).add ((p (m.add 3)).mul (p (m.add
        4)))).mul ((q (m.add 5)).mul (q (m.add 6)))).add (((p (m.add 3)).mul (p (m.add 4))).mul
        (((p (m.add 5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))))))).mul (((q
        (m.add 7)).mul ((q (m.add 8)).mul (q (m.add 9)))).mul (((q (m.add 10)).mul (q (m.add
        11))).mul ((q (m.add 12)).mul (q (m.add 13)))))).add ((((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add 4))).mul ((p (m.add 5)).mul (p (m.add
        6))))).mul (((((p (m.add 7)).mul ((q (m.add 8)).mul (q (m.add 9)))).add ((p (m.add 7)).mul
        (((p (m.add 8)).mul (q (m.add 9))).add ((p (m.add 8)).mul (p (m.add 9)))))).mul (((q
        (m.add 10)).mul (q (m.add 11))).mul ((q (m.add 12)).mul (q (m.add 13))))).add (((p (m.add
        7)).mul ((p (m.add 8)).mul (p (m.add 9)))).mul (((((p (m.add 10)).mul (q (m.add 11))).add
        ((p (m.add 10)).mul (p (m.add 11)))).mul ((q (m.add 12)).mul (q (m.add 13)))).add (((p
        (m.add 10)).mul (p (m.add 11))).mul (((p (m.add 12)).mul (q (m.add 13))).add ((p (m.add
        12)).mul (p (m.add 13)))))))))))
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul (((q (m.add 3)).mul (q (m.add
        4))).mul ((q (m.add 5)).mul (q (m.add 6))))).mul (((q (m.add 7)).mul ((q (m.add 8)).mul (q
        (m.add 9)))).mul (((q (m.add 10)).mul (q (m.add 11))).mul ((q (m.add 12)).mul (q (m.add
        13)))))))
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add
        4))).mul ((p (m.add 5)).mul (p (m.add 6))))).mul (((p (m.add 7)).mul ((p (m.add 8)).mul (p
        (m.add 9)))).mul (((p (m.add 10)).mul (p (m.add 11))).mul ((p (m.add 12)).mul (p (m.add
        13))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 7) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))) + p m * (p (m + 1) * p (m + 2)) * ((p
          (m + 3) * q (m + 4) + p (m + 3) * p (m + 4)) * (q (m + 5) * q (m + 6)) + p (m + 3) * p
          (m + 4) * (p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6))), q m * (q (m + 1) * q (m +
          2)) * (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))), p m * (p (m + 1) * p (m + 2)) *
          (p (m + 3) * p (m + 4) * (p (m + 5) * p (m + 6)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 7) (m + 14) =
      ((p (m + 7) * (q (m + 8) * q (m + 9)) + p (m + 7) * (p (m + 8) * q (m + 9) + p (m + 8) * p
          (m + 9))) * (q (m + 10) * q (m + 11) * (q (m + 12) * q (m + 13))) + p (m + 7) * (p (m +
          8) * p (m + 9)) * ((p (m + 10) * q (m + 11) + p (m + 10) * p (m + 11)) * (q (m + 12) * q
          (m + 13)) + p (m + 10) * p (m + 11) * (p (m + 12) * q (m + 13) + p (m + 12) * p (m +
          13))), q (m + 7) * (q (m + 8) * q (m + 9)) * (q (m + 10) * q (m + 11) * (q (m + 12) * q
          (m + 13))), p (m + 7) * (p (m + 8) * p (m + 9)) * (p (m + 10) * p (m + 11) * (p (m + 12)
          * p (m + 13)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base15 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 15).beq n)
    (hT : T.beq (((((((p m).mul ((q (m.succ)).mul (q (m.add 2)))).add ((p m).mul (((p (m.add
        1)).mul (q (m.add 2))).add ((p (m.succ)).mul (p (m.add 2)))))).mul (((q (m.add 3)).mul (q
        (m.add 4))).mul ((q (m.add 5)).mul (q (m.add 6))))).add (((p m).mul ((p (m.succ)).mul (p
        (m.add 2)))).mul (((((p (m.add 3)).mul (q (m.add 4))).add ((p (m.add 3)).mul (p (m.add
        4)))).mul ((q (m.add 5)).mul (q (m.add 6)))).add (((p (m.add 3)).mul (p (m.add 4))).mul
        (((p (m.add 5)).mul (q (m.add 6))).add ((p (m.add 5)).mul (p (m.add 6)))))))).mul ((((q
        (m.add 7)).mul (q (m.add 8))).mul ((q (m.add 9)).mul (q (m.add 10)))).mul (((q (m.add
        11)).mul (q (m.add 12))).mul ((q (m.add 13)).mul (q (m.add 14)))))).add ((((p m).mul ((p
        (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add 4))).mul ((p (m.add
        5)).mul (p (m.add 6))))).mul (((((((p (m.add 7)).mul (q (m.add 8))).add ((p (m.add 7)).mul
        (p (m.add 8)))).mul ((q (m.add 9)).mul (q (m.add 10)))).add (((p (m.add 7)).mul (p (m.add
        8))).mul (((p (m.add 9)).mul (q (m.add 10))).add ((p (m.add 9)).mul (p (m.add 10)))))).mul
        (((q (m.add 11)).mul (q (m.add 12))).mul ((q (m.add 13)).mul (q (m.add 14))))).add ((((p
        (m.add 7)).mul (p (m.add 8))).mul ((p (m.add 9)).mul (p (m.add 10)))).mul (((((p (m.add
        11)).mul (q (m.add 12))).add ((p (m.add 11)).mul (p (m.add 12)))).mul ((q (m.add 13)).mul
        (q (m.add 14)))).add (((p (m.add 11)).mul (p (m.add 12))).mul (((p (m.add 13)).mul (q
        (m.add 14))).add ((p (m.add 13)).mul (p (m.add 14)))))))))))
    (hQ : Q.beq ((((q m).mul ((q (m.succ)).mul (q (m.add 2)))).mul (((q (m.add 3)).mul (q (m.add
        4))).mul ((q (m.add 5)).mul (q (m.add 6))))).mul ((((q (m.add 7)).mul (q (m.add 8))).mul
        ((q (m.add 9)).mul (q (m.add 10)))).mul (((q (m.add 11)).mul (q (m.add 12))).mul ((q
        (m.add 13)).mul (q (m.add 14)))))))
    (hP : P.beq ((((p m).mul ((p (m.succ)).mul (p (m.add 2)))).mul (((p (m.add 3)).mul (p (m.add
        4))).mul ((p (m.add 5)).mul (p (m.add 6))))).mul ((((p (m.add 7)).mul (p (m.add 8))).mul
        ((p (m.add 9)).mul (p (m.add 10)))).mul (((p (m.add 11)).mul (p (m.add 12))).mul ((p
        (m.add 13)).mul (p (m.add 14))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 7) =
      ((p m * (q (m + 1) * q (m + 2)) + p m * (p (m + 1) * q (m + 2) + p (m + 1) * p (m + 2))) *
          (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))) + p m * (p (m + 1) * p (m + 2)) * ((p
          (m + 3) * q (m + 4) + p (m + 3) * p (m + 4)) * (q (m + 5) * q (m + 6)) + p (m + 3) * p
          (m + 4) * (p (m + 5) * q (m + 6) + p (m + 5) * p (m + 6))), q m * (q (m + 1) * q (m +
          2)) * (q (m + 3) * q (m + 4) * (q (m + 5) * q (m + 6))), p m * (p (m + 1) * p (m + 2)) *
          (p (m + 3) * p (m + 4) * (p (m + 5) * p (m + 6)))) :=
    binarySplit_of_base7 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 7) (m + 15) =
      (((p (m + 7) * q (m + 8) + p (m + 7) * p (m + 8)) * (q (m + 9) * q (m + 10)) + p (m + 7) * p
          (m + 8) * (p (m + 9) * q (m + 10) + p (m + 9) * p (m + 10))) * (q (m + 11) * q (m + 12)
          * (q (m + 13) * q (m + 14))) + p (m + 7) * p (m + 8) * (p (m + 9) * p (m + 10)) * ((p (m
          + 11) * q (m + 12) + p (m + 11) * p (m + 12)) * (q (m + 13) * q (m + 14)) + p (m + 11) *
          p (m + 12) * (p (m + 13) * q (m + 14) + p (m + 13) * p (m + 14))), q (m + 7) * q (m + 8)
          * (q (m + 9) * q (m + 10)) * (q (m + 11) * q (m + 12) * (q (m + 13) * q (m + 14))), p (m
          + 7) * p (m + 8) * (p (m + 9) * p (m + 10)) * (p (m + 11) * p (m + 12) * (p (m + 13) * p
          (m + 14)))) :=
    binarySplit_of_base8 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

theorem binarySplit_of_base16 {p q : ℕ → ℕ} {m n T Q P : ℕ}
    (h2 : (m.add 16).beq n)
    (hT : T.beq (((((((((p m).mul (q (m.succ))).add ((p m).mul (p (m.succ)))).mul ((q (m.add
        2)).mul (q (m.add 3)))).add (((p m).mul (p (m.succ))).mul (((p (m.add 2)).mul (q (m.add
        3))).add ((p (m.add 2)).mul (p (m.add 3)))))).mul (((q (m.add 4)).mul (q (m.add 5))).mul
        ((q (m.add 6)).mul (q (m.add 7))))).add ((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul
        (p (m.add 3)))).mul (((((p (m.add 4)).mul (q (m.add 5))).add ((p (m.add 4)).mul (p (m.add
        5)))).mul ((q (m.add 6)).mul (q (m.add 7)))).add (((p (m.add 4)).mul (p (m.add 5))).mul
        (((p (m.add 6)).mul (q (m.add 7))).add ((p (m.add 6)).mul (p (m.add 7)))))))).mul ((((q
        (m.add 8)).mul (q (m.add 9))).mul ((q (m.add 10)).mul (q (m.add 11)))).mul (((q (m.add
        12)).mul (q (m.add 13))).mul ((q (m.add 14)).mul (q (m.add 15)))))).add (((((p m).mul (p
        (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p (m.add 4)).mul (p (m.add
        5))).mul ((p (m.add 6)).mul (p (m.add 7))))).mul (((((((p (m.add 8)).mul (q (m.add
        9))).add ((p (m.add 8)).mul (p (m.add 9)))).mul ((q (m.add 10)).mul (q (m.add 11)))).add
        (((p (m.add 8)).mul (p (m.add 9))).mul (((p (m.add 10)).mul (q (m.add 11))).add ((p (m.add
        10)).mul (p (m.add 11)))))).mul (((q (m.add 12)).mul (q (m.add 13))).mul ((q (m.add
        14)).mul (q (m.add 15))))).add ((((p (m.add 8)).mul (p (m.add 9))).mul ((p (m.add 10)).mul
        (p (m.add 11)))).mul (((((p (m.add 12)).mul (q (m.add 13))).add ((p (m.add 12)).mul (p
        (m.add 13)))).mul ((q (m.add 14)).mul (q (m.add 15)))).add (((p (m.add 12)).mul (p (m.add
        13))).mul (((p (m.add 14)).mul (q (m.add 15))).add ((p (m.add 14)).mul (p (m.add
        15)))))))))))
    (hQ : Q.beq (((((q m).mul (q (m.succ))).mul ((q (m.add 2)).mul (q (m.add 3)))).mul (((q
        (m.add 4)).mul (q (m.add 5))).mul ((q (m.add 6)).mul (q (m.add 7))))).mul ((((q (m.add
        8)).mul (q (m.add 9))).mul ((q (m.add 10)).mul (q (m.add 11)))).mul (((q (m.add 12)).mul
        (q (m.add 13))).mul ((q (m.add 14)).mul (q (m.add 15)))))))
    (hP : P.beq (((((p m).mul (p (m.succ))).mul ((p (m.add 2)).mul (p (m.add 3)))).mul (((p
        (m.add 4)).mul (p (m.add 5))).mul ((p (m.add 6)).mul (p (m.add 7))))).mul ((((p (m.add
        8)).mul (p (m.add 9))).mul ((p (m.add 10)).mul (p (m.add 11)))).mul (((p (m.add 12)).mul
        (p (m.add 13))).mul ((p (m.add 14)).mul (p (m.add 15))))))) :
    binarySplit p q m n = (T, Q, P) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one] at h2 hT hQ hP
  subst h2 hT hQ hP
  have hl : binarySplit p q m (m + 8) =
      (((p m * q (m + 1) + p m * p (m + 1)) * (q (m + 2) * q (m + 3)) + p m * p (m + 1) * (p (m +
          2) * q (m + 3) + p (m + 2) * p (m + 3))) * (q (m + 4) * q (m + 5) * (q (m + 6) * q (m +
          7))) + p m * p (m + 1) * (p (m + 2) * p (m + 3)) * ((p (m + 4) * q (m + 5) + p (m + 4) *
          p (m + 5)) * (q (m + 6) * q (m + 7)) + p (m + 4) * p (m + 5) * (p (m + 6) * q (m + 7) +
          p (m + 6) * p (m + 7))), q m * q (m + 1) * (q (m + 2) * q (m + 3)) * (q (m + 4) * q (m +
          5) * (q (m + 6) * q (m + 7))), p m * p (m + 1) * (p (m + 2) * p (m + 3)) * (p (m + 4) *
          p (m + 5) * (p (m + 6) * p (m + 7)))) :=
    binarySplit_of_base8 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  have hr : binarySplit p q (m + 8) (m + 16) =
      (((p (m + 8) * q (m + 9) + p (m + 8) * p (m + 9)) * (q (m + 10) * q (m + 11)) + p (m + 8) *
          p (m + 9) * (p (m + 10) * q (m + 11) + p (m + 10) * p (m + 11))) * (q (m + 12) * q (m +
          13) * (q (m + 14) * q (m + 15))) + p (m + 8) * p (m + 9) * (p (m + 10) * p (m + 11)) *
          ((p (m + 12) * q (m + 13) + p (m + 12) * p (m + 13)) * (q (m + 14) * q (m + 15)) + p (m
          + 12) * p (m + 13) * (p (m + 14) * q (m + 15) + p (m + 14) * p (m + 15))), q (m + 8) * q
          (m + 9) * (q (m + 10) * q (m + 11)) * (q (m + 12) * q (m + 13) * (q (m + 14) * q (m +
          15))), p (m + 8) * p (m + 9) * (p (m + 10) * p (m + 11)) * (p (m + 12) * p (m + 13) * (p
          (m + 14) * p (m + 15)))) :=
    binarySplit_of_base8 (by simp +arith) (by simp +arith; ring) (by simp +arith) (by simp +arith)
  exact binarySplit_rec (by simp [Nat.blt_eq]) (by simp [Nat.div_eq']; omega)
    (by simp) (by simp) (by simp) hl hr

end BSN

end

end CertificatePort140
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Certificate/Bernoulli.lean -/
section CertificatePort141


/-!
# Bernoulli values in real `sfrac` form

Bridges `Bernoulli.BernoulliValues` to the form the zeta certificate tactics consume:
`(bernoulli (2*k) : ℝ) = sfrac neg p q` with literal `p`, `q`. `bern_real_tangent_pos`/`_neg`
certify one value from the tangent number `T_{m+1}`; `derive_bern_real N` materialises
`bern_real_1 … bern_real_N`.
-/
section


namespace BSN
open Enclosure

open TangentNumbers

/- `B_{2m+2}` for even `m` (positive value) in real `sfrac` form: `p/q` validated against
`(2m+2)·T_{m+1} / (2^{2m+2}(2^{2m+2}−1))` by one cross-multiplication. -/
theorem bern_real_tangent_pos (m Tn p q : ℕ)
    (hT : tangentNumber (m + 1) = Tn)
    (hm : Nat.beq (m % 2) 0 = true)
    (hq : Nat.ble 1 q = true)
    (hcross : Nat.beq (p.mul ((Nat.pow 2 ((Nat.mul 2 m).add 2)).mul
          ((Nat.pow 2 ((Nat.mul 2 m).add 2)).sub 1)))
        (q.mul (((Nat.mul 2 m).add 2).mul Tn)) = true) :
    (bernoulli (2 * m + 2) : ℝ) = sfrac false p q := by
  have hme : Even m := Nat.even_iff.mpr (Nat.eq_of_beq_eq_true hm)
  have hq : 0 < q := pos_of_ble hq
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Nat.sub_eq] at hcross
  have h1 : (1 : ℕ) ≤ 2 ^ (2 * m + 2) := Nat.one_le_two_pow
  have hcQ : ((p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1)) : ℕ) : ℚ)
      = ((q * ((2 * m + 2) * Tn) : ℕ) : ℚ) := by
    exact_mod_cast Nat.eq_of_beq_eq_true hcross
  push_cast [Nat.cast_sub h1] at hcQ
  have hQ : bernoulli (2 * m + 2) = (p : ℚ) / (q : ℚ) := by
    rw [bernoulli_eq_tangent_intDiv m, hT, hme.neg_one_pow, one_mul,
      div_eq_div_iff (by exact_mod_cast intDenom_ne_zero m)
        (by exact_mod_cast hq.ne')]
    push_cast [Nat.cast_sub h1]
    linear_combination -hcQ
  rw [hQ]
  exact sfrac_ratCast_natDiv p q

/- `B_{2m+2}` for odd `m` (where the value is negative) in real `sfrac` form; the mirror of
`bern_real_tangent_pos`. -/
theorem bern_real_tangent_neg (m Tn p q : ℕ)
    (hT : tangentNumber (m + 1) = Tn)
    (hm : Nat.beq (m % 2) 1 = true)
    (hq : Nat.ble 1 q = true)
    (hcross : Nat.beq (p.mul ((Nat.pow 2 ((Nat.mul 2 m).add 2)).mul
          ((Nat.pow 2 ((Nat.mul 2 m).add 2)).sub 1)))
        (q.mul (((Nat.mul 2 m).add 2).mul Tn)) = true) :
    (bernoulli (2 * m + 2) : ℝ) = sfrac true p q := by
  have hmo : Odd m := Nat.odd_iff.mpr (Nat.eq_of_beq_eq_true hm)
  have hq : 0 < q := pos_of_ble hq
  simp only [Nat.mul_eq, Nat.pow_eq, Nat.add_eq, Nat.sub_eq] at hcross
  have h1 : (1 : ℕ) ≤ 2 ^ (2 * m + 2) := Nat.one_le_two_pow
  have hcQ : ((p * (2 ^ (2 * m + 2) * (2 ^ (2 * m + 2) - 1)) : ℕ) : ℚ)
      = ((q * ((2 * m + 2) * Tn) : ℕ) : ℚ) := by
    exact_mod_cast Nat.eq_of_beq_eq_true hcross
  push_cast [Nat.cast_sub h1] at hcQ
  have hQ : bernoulli (2 * m + 2) = -((p : ℚ) / (q : ℚ)) := by
    rw [bernoulli_eq_tangent_intDiv m, hT, hmo.neg_one_pow, ← neg_div,
      div_eq_div_iff (by exact_mod_cast intDenom_ne_zero m)
        (by exact_mod_cast hq.ne')]
    push_cast [Nat.cast_sub h1]
    linear_combination hcQ
  rw [hQ, sfrac_true_div]
  push_cast
  ring

end BSN
end
end CertificatePort141
theorem BSN.bern_real_1 : @Eq Real
  (@Rat.cast Real Real.instRatCast
    (bernoulli
      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (Enclosure.sfrac Bool.false (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) :=
BSN.bern_real_tangent_pos (nat_lit 0) (nat_lit 1) (nat_lit 1) (nat_lit 6) TangentNumbers.tangentNumberLit_1
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)

theorem BSN.bern_real_2 : @Eq Real
  (@Rat.cast Real Real.instRatCast
    (bernoulli
      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
  (Enclosure.sfrac Bool.true (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) :=
BSN.bern_real_tangent_neg (nat_lit 1) (nat_lit 2) (nat_lit 1) (nat_lit 30) TangentNumbers.tangentNumberLit_2
  (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true) (@Eq.refl Bool Bool.true)

/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/Defs.lean -/
section CertificatePort142

/-!
# Enclosure definitions that need no `Mathlib`

The plain computable definitions the `Enclosure` certificate lemmas state their side conditions
with, kept free of `Mathlib` so that compiled checkers (the `NativeCode` library) can use exactly
the same functions the lemmas mention.

* `numPos`/`numNeg`: the natural parts of a signed numerator `±cn`;
* `recentreOk`: the side conditions of `Real.IsNear.recentre'`, as one Boolean.
-/
section

namespace Enclosure

/- The positive part of the signed numerator `±cn`: `cn` if nonnegative, else `0`. -/
def numPos (neg : Bool) (cn : Nat) : Nat := if neg then 0 else cn

/- The negative part of the signed numerator `±cn`: `cn` if negative, else `0`. -/
def numNeg (neg : Bool) (cn : Nat) : Nat := if neg then cn else 0

/- The six side conditions of `Real.IsNear.recentre'`, as one Boolean. Each `a ≤ b` is carried as
`Nat.sub a b`, zero exactly when it holds, and the six are summed and compared against zero, so the
whole check stays on `Nat.sub`/`add`/`mul`/`beq`. -/
def recentreOk (cn cd rn rd cn' cd' rn' rd' : Nat) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cd)
    (Nat.add (Nat.sub (nat_lit 1) cd')
    (Nat.add (Nat.sub (nat_lit 1) rd)
    (Nat.add (Nat.sub (nat_lit 1) rd')
    (Nat.add (Nat.sub (cn'.mul cd) (cn.mul cd'))
             (Nat.sub (((rn.mul (cd.mul cd')).add (((cn.mul cd').sub (cn'.mul cd)).mul rd)).mul rd')
                      (rn'.mul (rd.mul (cd.mul cd')))))))))
    (nat_lit 0)

end Enclosure

end

end CertificatePort142
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/Core.lean -/
section CertificatePort143


/-!
# Real interval enclosures: the `Real.IsNear` predicate

`Real.IsNear x neg cn cd rn rd` says `|x − ±cn/cd| ≤ rn/rd`: `x` within radius `rn/rd` of the signed
centre `±cn/cd`. Centre and radius are ratios of naturals with the sign a separate `Bool`.
-/
section


namespace Enclosure

/- `|x − ±cn/cd| ≤ rn/rd`: `x` is within radius `rn/rd` of the signed centre `sfrac neg cn cd`. -/
def Real.IsNear (x : ℝ) (neg : Bool) (cn cd rn rd : ℕ) : Prop :=
  |x - sfrac neg cn cd| ≤ (rn : ℝ) / rd

/- The lower endpoint of an `IsNear` enclosure: `sfrac neg cn cd − rn/rd ≤ x`. -/
theorem Real.IsNear.lower {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (h : Real.IsNear x neg cn cd rn rd) : sfrac neg cn cd - (rn : ℝ) / rd ≤ x := by
  have := (abs_le.mp h).1; linarith

/- The upper endpoint of an `IsNear` enclosure: `x ≤ sfrac neg cn cd + rn/rd`. -/
theorem Real.IsNear.upper {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (h : Real.IsNear x neg cn cd rn rd) : x ≤ sfrac neg cn cd + (rn : ℝ) / rd := by
  have := (abs_le.mp h).2; linarith

/- Build an `IsNear` enclosure from the two endpoint inequalities. -/
theorem Real.IsNear.mk' {x : ℝ} {neg : Bool} {cn cd rn rd : ℕ}
    (hlo : sfrac neg cn cd - (rn : ℝ) / rd ≤ x) (hhi : x ≤ sfrac neg cn cd + (rn : ℝ) / rd) :
    Real.IsNear x neg cn cd rn rd := abs_le.mpr ⟨by linarith, by linarith⟩

/-! ### Signed numerator as a difference of natural parts

`numPos`/`numNeg` (one always `0`) write `sfrac neg cn cd` as `(numPos − numNeg)/cd`. -/

/- `sfrac` as the difference of its natural parts over the denominator. -/
theorem sfrac_eq_parts (neg : Bool) (cn cd : ℕ) :
    sfrac neg cn cd = ((numPos neg cn : ℝ) - (numNeg neg cn : ℝ)) / cd := by
  cases neg <;> simp [sfrac, numPos, numNeg, neg_div, sub_zero, zero_sub]

/- The absolute value of a signed fraction is its (nonnegative) magnitude. -/
theorem abs_sfrac (neg : Bool) (cn cd : ℕ) : |sfrac neg cn cd| = (cn : ℝ) / cd := by
  rw [sfrac]
  cases neg <;> simp [abs_div, abs_of_nonneg]

/- The product of two signed fractions: signs `xor`, magnitudes multiply. -/
theorem sfrac_mul (nx ny : Bool) (cnx cdx cny cdy : ℕ) :
    sfrac nx cnx cdx * sfrac ny cny cdy = sfrac (Bool.xor nx ny) (cnx * cny) (cdx * cdy) := by
  cases nx <;> cases ny <;> simp [sfrac] <;> ring

/-! ### Constants and radius weakening -/

/- A signed rational encloses itself with radius `0`. -/
theorem Real.IsNear.const (neg : Bool) (cn cd : ℕ) :
    Real.IsNear (sfrac neg cn cd) neg cn cd (nat_lit 0) (nat_lit 1) := by
  simp [Real.IsNear]

/- Radius weakening: any enclosure stays valid with a larger radius `rn'/rd' ≥ rn/rd`. -/
theorem Real.IsNear.widen {x : ℝ} {n : Bool} {cn cd rn rd rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd) (hrd : Nat.ble 1 rd) (hrd' : Nat.ble 1 rd')
    (hle : Nat.ble (rn.mul rd') (rn'.mul rd)) :
    Real.IsNear x n cn cd rn' rd' := by
  simp only [Nat.ble_eq, Nat.mul_eq] at hle
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hrd'R : (0:ℝ) < rd' := pos_real_of_ble hrd'
  simp only [Real.IsNear] at h ⊢
  refine le_trans h ?_
  rw [div_le_div_iff₀ hrdR hrd'R]
  exact_mod_cast hle

end Enclosure

end

end CertificatePort143
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/Arith.lean -/
section CertificatePort144


/-!
# Real interval enclosures: arithmetic combinators

Addition, negation, subtraction and multiplication of `Real.IsNear` enclosures, their
literal-output (`*Lit`) forms with the sign-specialized variants, and `recentre`.
-/
section


namespace Enclosure

/-! ### Addition of enclosures -/

/- `x + y` is near `±cnR/(cdx·cdy)` with radius `(rnx·rdy + rny·rdx)/(rdx·rdy)`; the result
sign/magnitude is fixed by `hnum`. -/
theorem Real.IsNear.add {x y : ℝ} {nx ny nR : Bool} {cnx cdx rnx rdx cny cdy rny rdy cnR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg ny cny).mul cdx))
                    (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add
                          ((numPos ny cny).mul cdx))) :
    Real.IsNear (x + y) nR cnR (cdx.mul cdy) ((rnx.mul rdy).add (rny.mul rdx)) (rdx.mul rdy) := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hcdyR : (0:ℝ) < cdy := pos_real_of_ble hcdy
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hrdyR : (0:ℝ) < rdy := pos_real_of_ble hrdy
  have eR : (numPos nR cnR : ℝ) + (numNeg nx cnx : ℝ) * cdy + (numNeg ny cny : ℝ) * cdx
          = (numNeg nR cnR : ℝ) + (numPos nx cnx : ℝ) * cdy + (numPos ny cny : ℝ) * cdx := by
    have h' := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.add_eq, Nat.mul_eq] at h'
    exact_mod_cast h'
  have hc : sfrac nR cnR (cdx * cdy) = sfrac nx cnx cdx + sfrac ny cny cdy := by
    rw [sfrac_eq_parts nR cnR, sfrac_eq_parts nx cnx, sfrac_eq_parts ny cny,
      div_add_div _ _ (ne_of_gt hcdxR) (ne_of_gt hcdyR), Nat.cast_mul,
      div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (cdx : ℝ) * (cdy : ℝ) * eR
  have hrad : ((rnx * rdy + rny * rdx : ℕ) : ℝ) / ((rdx * rdy : ℕ) : ℝ)
            = (rnx : ℝ) / rdx + (rny : ℝ) / rdy := by
    rw [div_add_div _ _ (ne_of_gt hrdxR) (ne_of_gt hrdyR)]
    push_cast
    ring
  simp only [Real.IsNear] at hx hy ⊢
  rw [hc, hrad]
  calc |x + y - (sfrac nx cnx cdx + sfrac ny cny cdy)|
      = |(x - sfrac nx cnx cdx) + (y - sfrac ny cny cdy)| := by congr 1; ring
    _ ≤ |x - sfrac nx cnx cdx| + |y - sfrac ny cny cdy| := abs_add_le _ _
    _ ≤ (rnx : ℝ) / rdx + (rny : ℝ) / rdy := add_le_add hx hy

/-! ### Negation and subtraction -/

/- Negation. `−x` is near the sign-flipped centre with the same magnitude and radius. -/
theorem Real.IsNear.neg {x : ℝ} {nx : Bool} {cnx cdx rnx rdx : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) : Real.IsNear (-x) (!nx) cnx cdx rnx rdx := by
  simp only [Real.IsNear, sfrac_not] at hx ⊢
  have : -x - -sfrac nx cnx cdx = -(x - sfrac nx cnx cdx) := by ring
  rwa [this, abs_neg]

/- `x − y` (via `add ∘ neg`); same shape as `add`, with `hnum` flipping `y`'s sign. -/
theorem Real.IsNear.sub {x y : ℝ} {nx ny nR : Bool} {cnx cdx rnx rdx cny cdy rny rdy cnR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq
        (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg (!ny) cny).mul cdx))
        (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add ((numPos (!ny) cny).mul cdx))) :
    Real.IsNear (x - y) nR cnR (cdx.mul cdy) ((rnx.mul rdy).add (rny.mul rdx)) (rdx.mul rdy) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg hcdx hcdy hrdx hrdy hnum

/-! ### Multiplication of enclosures -/

/- The interval-multiplication error bound: `|xy − cx·cy| ≤ |cx|·ry + |cy|·rx + rx·ry`. -/
theorem abs_mul_sub {x y cx cy rx ry : ℝ} (hx : |x - cx| ≤ rx) (hy : |y - cy| ≤ ry) :
    |x * y - cx * cy| ≤ |cx| * ry + |cy| * rx + rx * ry := by
  have hrx : 0 ≤ rx := le_trans (abs_nonneg _) hx
  calc |x * y - cx * cy|
      = |cx * (y - cy) + cy * (x - cx) + (x - cx) * (y - cy)| := by congr 1; ring
    _ ≤ |cx * (y - cy) + cy * (x - cx)| + |(x - cx) * (y - cy)| := abs_add_le _ _
    _ ≤ (|cx * (y - cy)| + |cy * (x - cx)|) + |(x - cx) * (y - cy)| := by
        gcongr; exact abs_add_le _ _
    _ = |cx| * |y - cy| + |cy| * |x - cx| + |x - cx| * |y - cy| := by
        rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |cx| * ry + |cy| * rx + rx * ry := by gcongr

/- `x · y` is near `±(cnx·cny)/(cdx·cdy)` with the interval-product radius; the sign is `xor`. -/
theorem Real.IsNear.mul {x y : ℝ} {nx ny : Bool} {cnx cdx rnx rdx cny cdy rny rdy : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy)
    (hrdx : Nat.ble (nat_lit 1) rdx) (hrdy : Nat.ble (nat_lit 1) rdy) :
    Real.IsNear (x * y) (Bool.xor nx ny) (cnx.mul cny) (cdx.mul cdy)
      (((((cnx.mul rny).mul cdy).mul rdx).add (((cny.mul rnx).mul cdx).mul rdy)).add
        (((rnx.mul rny).mul cdx).mul cdy))
      (((cdx.mul cdy).mul rdx).mul rdy) := by
  simp only [Nat.mul_eq, Nat.add_eq]
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hcdyR : (0:ℝ) < cdy := pos_real_of_ble hcdy
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hrdyR : (0:ℝ) < rdy := pos_real_of_ble hrdy
  have hcdxN : 0 < cdx := pos_of_ble hcdx
  have hcdyN : 0 < cdy := pos_of_ble hcdy
  have hrdxN : 0 < rdx := pos_of_ble hrdx
  have hrdyN : 0 < rdy := pos_of_ble hrdy
  have hrad : (cnx : ℝ) / cdx * ((rny : ℝ) / rdy) + (cny : ℝ) / cdy * ((rnx : ℝ) / rdx)
              + (rnx : ℝ) / rdx * ((rny : ℝ) / rdy)
            = ((cnx * rny * cdy * rdx + cny * rnx * cdx * rdy + rnx * rny * cdx * cdy : ℕ) : ℝ)
              / ((cdx * cdy * rdx * rdy : ℕ) : ℝ) := by
    rw [eq_div_iff (by positivity)]
    push_cast
    field_simp
  simp only [Real.IsNear] at hx hy ⊢
  rw [← sfrac_mul]
  refine le_trans (abs_mul_sub hx hy) ?_
  rw [abs_sfrac, abs_sfrac, hrad]

/-! ### Combinators with literal outputs

Each `*Lit` combinator states its result centre/radius as single numeral literals, tied to the
symbolic result by a `Nat.beq` (centre) and a `Nat.ble` (radius). -/

private theorem ble_one_mul {a b : ℕ} (ha : Nat.ble (nat_lit 1) a
      = true) (hb : Nat.ble (nat_lit 1) b = true) :
    Nat.ble (nat_lit 1) (a.mul b) = true := by
  rw [Nat.ble_eq] at ha hb ⊢
  have h := Nat.mul_le_mul ha hb
  omega

/- Re-represent an enclosure's centre exactly (`cn/D = cn'/cd'`, cross-multiplied by `hc`) and
widen its radius (`Rn/Rd ≤ rn'/rd'`, by `hr`). The shared tail of the `*Lit` combinators. -/
theorem Real.IsNear.reprLit {x : ℝ} {n : Bool} {cn D Rn Rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn D Rn Rd)
    (hD : Nat.ble (nat_lit 1) D) (hRd : Nat.ble (nat_lit 1) Rd) (hcd' : Nat.ble (nat_lit 1)
          cd') (hrd' : Nat.ble (nat_lit 1) rd')
    (hc : Nat.beq (cn.mul cd') (cn'.mul D))
    (hr : Nat.ble (Rn.mul rd') (rn'.mul Rd)) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [Nat.ble_eq, Nat.mul_eq] at hr
  have hDr : (0:ℝ) < D := pos_real_of_ble hD
  have hRdr : (0:ℝ) < Rd := pos_real_of_ble hRd
  have hcd'r : (0:ℝ) < cd' := pos_real_of_ble hcd'
  have hrd'r : (0:ℝ) < rd' := pos_real_of_ble hrd'
  have hceq : (cn : ℝ) / D = (cn' : ℝ) / cd' := by
    have hc' := Nat.eq_of_beq_eq_true hc
    simp only [Nat.mul_eq] at hc'
    rw [div_eq_div_iff hDr.ne' hcd'r.ne']; exact_mod_cast hc'
  have hsfrac : sfrac n cn D = sfrac n cn' cd' := by simp only [sfrac, hceq]
  have hrle : (Rn : ℝ) / Rd ≤ (rn' : ℝ) / rd' := by
    rw [div_le_div_iff₀ hRdr hrd'r]; exact_mod_cast hr
  simp only [Real.IsNear] at h ⊢
  rw [← hsfrac]
  exact le_trans h hrle

/- `add` with literal outputs: centre `cnR'/cdR'` equal to the signed sum, radius `rnR'/rdR'`. -/
theorem Real.IsNear.addLit {x y : ℝ} {nx ny nR : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg ny cny).mul cdx))
                    (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add ((numPos ny cny).mul cdx)))
    (hcdR' : Nat.ble (nat_lit 1) cdR') (hrdR' : Nat.ble (nat_lit 1) rdR')
    (hc : Nat.beq (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)))
    (hr : Nat.ble (((rnx.mul rdy).add (rny.mul rdx)).mul rdR') (rnR'.mul (rdx.mul rdy))) :
    Real.IsNear (x + y) nR cnR' cdR' rnR' rdR' :=
  (hx.add hy hcdx hcdy hrdx hrdy hnum).reprLit
    (ble_one_mul hcdx hcdy) (ble_one_mul hrdx hrdy) hcdR' hrdR' hc hr

/- Subtraction with literal outputs (the mirror of `addLit`; `hnum` flips `y`'s sign). -/
theorem Real.IsNear.subLit {x y : ℝ} {nx ny nR : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hnum : Nat.beq
        (((numPos nR cnR).add ((numNeg nx cnx).mul cdy)).add ((numNeg (!ny) cny).mul cdx))
        (((numNeg nR cnR).add ((numPos nx cnx).mul cdy)).add ((numPos (!ny) cny).mul cdx)))
    (hcdR' : Nat.ble (nat_lit 1) cdR') (hrdR' : Nat.ble (nat_lit 1) rdR')
    (hc : Nat.beq (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)))
    (hr : Nat.ble (((rnx.mul rdy).add (rny.mul rdx)).mul rdR') (rnR'.mul (rdx.mul rdy))) :
    Real.IsNear (x - y) nR cnR' cdR' rnR' rdR' :=
  (hx.sub hy hcdx hcdy hrdx hrdy hnum).reprLit
    (ble_one_mul hcdx hcdy) (ble_one_mul hrdx hrdy) hcdR' hrdR' hc hr

/-! ### Sign-specialized `addLit`/`subLit` variants

One variant per input sign pair, baking the signs in so `hnum` is a plain `Nat.beq` on products. -/

private theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  simpa [Nat.beq_eq_true_eq] using h

/- The eight side conditions shared by every `addLit`/`subLit` sign variant, as one Boolean.
Each `a ≤ b` is carried as `Nat.sub a b`, each `a = b` as the pair of differences, and the sum is
compared against zero, so the check stays on `Nat.sub`/`add`/`mul`/`beq`. The per-variant `hnum`
stays a separate argument, since its shape depends on the signs. -/
def addLitOk (cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cdx)
    (Nat.add (Nat.sub (nat_lit 1) cdy)
    (Nat.add (Nat.sub (nat_lit 1) rdx)
    (Nat.add (Nat.sub (nat_lit 1) rdy)
    (Nat.add (Nat.sub (nat_lit 1) cdR')
    (Nat.add (Nat.sub (nat_lit 1) rdR')
    (Nat.add (Nat.sub (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)))
    (Nat.add (Nat.sub (cnR'.mul (cdx.mul cdy)) (cnR.mul cdR'))
             (Nat.sub (((rnx.mul rdy).add (rny.mul rdx)).mul rdR')
                      (rnR'.mul (rdx.mul rdy)))))))))))
    (nat_lit 0)

/- Unpack `addLitOk` into the eight conditions the sign variants take. -/
private theorem addLitOk_parts {cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' : ℕ}
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Nat.ble (nat_lit 1) cdx = true ∧ Nat.ble (nat_lit 1) cdy = true ∧
    Nat.ble (nat_lit 1) rdx = true ∧ Nat.ble (nat_lit 1) rdy = true ∧
    Nat.ble (nat_lit 1) cdR' = true ∧ Nat.ble (nat_lit 1) rdR' = true ∧
    Nat.beq (cnR.mul cdR') (cnR'.mul (cdx.mul cdy)) = true ∧
    Nat.ble (((rnx.mul rdy).add (rny.mul rdx)).mul rdR') (rnR'.mul (rdx.mul rdy)) = true := by
  simp only [addLitOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z6, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z7, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z8, z9⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6),
    beq_of_eq (Nat.le_antisymm (Nat.le_of_sub_eq_zero z7) (Nat.le_of_sub_eq_zero z8)),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z9)⟩

/- The eight side conditions shared by all four `mulLit` sign variants, as one Boolean, in the
same packed form as `addLitOk`. -/
def mulLitOk (cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) cdx)
    (Nat.add (Nat.sub (nat_lit 1) cdy)
    (Nat.add (Nat.sub (nat_lit 1) rdx)
    (Nat.add (Nat.sub (nat_lit 1) rdy)
    (Nat.add (Nat.sub (nat_lit 1) cdR)
    (Nat.add (Nat.sub (nat_lit 1) rdR)
    (Nat.add (Nat.sub ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)))
    (Nat.add (Nat.sub (cnR.mul (cdx.mul cdy)) ((cnx.mul cny).mul cdR))
             (Nat.sub ((((((cnx.mul rny).mul cdy).mul rdx).add
                         (((cny.mul rnx).mul cdx).mul rdy)).add
                         (((rnx.mul rny).mul cdx).mul cdy)).mul rdR)
                      (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy)))))))))))
    (nat_lit 0)

/- Unpack `mulLitOk` into the eight conditions the sign variants take. -/
private theorem mulLitOk_parts {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Nat.ble (nat_lit 1) cdx = true ∧ Nat.ble (nat_lit 1) cdy = true ∧
    Nat.ble (nat_lit 1) rdx = true ∧ Nat.ble (nat_lit 1) rdy = true ∧
    Nat.ble (nat_lit 1) cdR = true ∧ Nat.ble (nat_lit 1) rdR = true ∧
    Nat.beq ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)) = true ∧
    Nat.ble ((((((cnx.mul rny).mul cdy).mul rdx).add (((cny.mul rnx).mul cdx).mul rdy)).add
      (((rnx.mul rny).mul cdx).mul cdy)).mul rdR) (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy))
      = true := by
  simp only [mulLitOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z6, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z7, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z8, z9⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5), Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6),
    beq_of_eq (Nat.le_antisymm (Nat.le_of_sub_eq_zero z7) (Nat.le_of_sub_eq_zero z8)),
    Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z9)⟩

/- `x ≥ 0, y ≥ 0` (result sign `+`): `cnR = cnx·cdy + cny·cdx`. -/
theorem Real.IsNear.addLit_ff {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr

/- `x ≤ 0, y ≤ 0` (result sign `−`): `cnx·cdy + cny·cdx = cnR`. -/
theorem Real.IsNear.addLit_tt {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr

/- `x ≥ 0, y ≤ 0`, result `+`: `cnR + cny·cdx = cnx·cdy`. -/
theorem Real.IsNear.addLit_ft_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cny.mul cdx)) (cnx.mul cdy))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/- `x ≥ 0, y ≤ 0`, result `−`: `cny·cdx = cnR + cnx·cdy`. -/
theorem Real.IsNear.addLit_ft_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cny.mul cdx) (cnR.add (cnx.mul cdy)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/- `x ≤ 0, y ≥ 0`, result `+`: `cnR + cnx·cdy = cny·cdx`. -/
theorem Real.IsNear.addLit_tf_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cnx.mul cdy)) (cny.mul cdx))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/- `x ≤ 0, y ≥ 0`, result `−`: `cnx·cdy = cnR + cny·cdx`. -/
theorem Real.IsNear.addLit_tf_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cnx.mul cdy) (cnR.add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x + y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.addLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/- `x ≥ 0, y ≥ 0`, difference `+`: `cnR + cny·cdx = cnx·cdy`. -/
theorem Real.IsNear.subLit_ff_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cny.mul cdx)) (cnx.mul cdy))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/- `x ≥ 0, y ≥ 0`, difference `−`: `cny·cdx = cnR + cnx·cdy`. -/
theorem Real.IsNear.subLit_ff_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq (cny.mul cdx) (cnR.add (cnx.mul cdy)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/- `x ≥ 0, y ≤ 0` (so `x − y = x + |y|`, result `+`): `cnR = cnx·cdy + cny·cdx`. -/
theorem Real.IsNear.subLit_ft {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr

/- `x ≤ 0, y ≥ 0` (so `x − y = −(|x| + y)`, result `−`): `cnx·cdy + cny·cdx = cnR`. -/
theorem Real.IsNear.subLit_tf {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hnum : Nat.beq cnR ((cnx.mul cdy).add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq, h])) hcdR' hrdR' hc hr

/- `x ≤ 0, y ≤ 0`, difference `+` (`|y| ≥ |x|`): `cnR + cnx·cdy = cny·cdx`. -/
theorem Real.IsNear.subLit_tt_p {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cnR.add (cnx.mul cdy)) (cny.mul cdx))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) false cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/- `x ≤ 0, y ≤ 0`, difference `−` (`|x| ≥ |y|`): `cnx·cdy = cnR + cny·cdx`. -/
theorem Real.IsNear.subLit_tt_n {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cnR' cdR' rnR' rdR' : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hnum : Nat.beq (cnx.mul cdy) (cnR.add (cny.mul cdx)))
    (hs : addLitOk cdx rdx cdy rdy cnR cnR' cdR' rnx rny rnR' rdR' = true) :
    Real.IsNear (x - y) true cnR' cdR' rnR' rdR' := by
  obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR', hrdR', hc, hr⟩ := addLitOk_parts hs
  exact Real.IsNear.subLit hx hy hcdx hcdy hrdx hrdy (beq_of_eq (by
    have h := Nat.eq_of_beq_eq_true hnum
    simp only [Nat.mul_eq, Nat.add_eq] at h
    simp [numPos, numNeg, Nat.mul_eq, Nat.add_eq]
    omega)) hcdR' hrdR' hc hr

/- `mul` with literal outputs: centre `cnR/cdR` equal to the exact product (sign `xor`), radius
`rnR/rdR`. -/
theorem Real.IsNear.mulLit {x y : ℝ} {nx ny : Bool}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (hy : Real.IsNear y ny cny cdy rny rdy)
    (hcdx : Nat.ble (nat_lit 1) cdx) (hcdy : Nat.ble (nat_lit 1) cdy) (hrdx : Nat.ble (nat_lit 1)
          rdx) (hrdy : Nat.ble (nat_lit 1) rdy)
    (hcdR : Nat.ble (nat_lit 1) cdR) (hrdR : Nat.ble (nat_lit 1) rdR)
    (hc : Nat.beq ((cnx.mul cny).mul cdR) (cnR.mul (cdx.mul cdy)))
    (hr : Nat.ble (((((((cnx.mul rny).mul cdy).mul rdx).add
        (((cny.mul rnx).mul cdx).mul rdy)).add (((rnx.mul rny).mul cdx).mul cdy)).mul rdR))
      (rnR.mul (((cdx.mul cdy).mul rdx).mul rdy))) :
    Real.IsNear (x * y) (Bool.xor nx ny) cnR cdR rnR rdR :=
  (hx.mul hy hcdx hcdy hrdx hrdy).reprLit (ble_one_mul hcdx hcdy)
    (ble_one_mul (ble_one_mul (ble_one_mul hcdx hcdy) hrdx) hrdy) hcdR hrdR hc hr

/-! ### Sign-specialized `mulLit` variants

Four variants (one per input sign pair) baking the result sign in as a literal. -/

/- `x ≥ 0, y ≥ 0`: result sign `+`. -/
theorem Real.IsNear.mulLit_ff {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) false cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr

/- `x ≥ 0, y ≤ 0`: result sign `−`. -/
theorem Real.IsNear.mulLit_ft {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x false cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) true cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr

/- `x ≤ 0, y ≥ 0`: result sign `−`. -/
theorem Real.IsNear.mulLit_tf {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y false cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) true cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr

/- `x ≤ 0, y ≤ 0`: result sign `+`. -/
theorem Real.IsNear.mulLit_tt {x y : ℝ}
    {cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR : ℕ}
    (hx : Real.IsNear x true cnx cdx rnx rdx) (hy : Real.IsNear y true cny cdy rny rdy)
    (hs : mulLitOk cnx cdx rnx rdx cny cdy rny rdy cnR cdR rnR rdR = true) :
    Real.IsNear (x * y) false cnR cdR rnR rdR :=
  by obtain ⟨hcdx, hcdy, hrdx, hrdy, hcdR, hrdR, hc, hr⟩ := mulLitOk_parts hs
     exact Real.IsNear.mulLit hx hy hcdx hcdy hrdx hrdy hcdR hrdR hc hr

/- Round an enclosure's centre down to a coarser dyadic `cn'/cd' ≤ cn/cd` and inflate the radius by
the drop `δ = cn/cd − cn'/cd'`. -/
theorem Real.IsNear.recentre {x : ℝ} {n : Bool} {cn cd rn rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd)
    (hcd : Nat.ble (nat_lit 1) cd) (hcd' : Nat.ble (nat_lit 1) cd') (hrd : Nat.ble (nat_lit 1)
          rd) (hrd' : Nat.ble (nat_lit 1) rd')
    (hfloor : Nat.ble (cn'.mul cd) (cn.mul cd'))
    (hrad : Nat.ble (((rn.mul (cd.mul cd')).add (((cn.mul cd').sub (cn'.mul cd)).mul rd)).mul rd')
                    (rn'.mul (rd.mul (cd.mul cd')))) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hfloor hrad
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hcd'R : (0:ℝ) < cd' := pos_real_of_ble hcd'
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hrd'R : (0:ℝ) < rd' := pos_real_of_ble hrd'
  have hnn : (0:ℝ) ≤ (cn : ℝ) / cd - (cn' : ℝ) / cd' := by
    have : (cn' : ℝ) / cd' ≤ (cn : ℝ) / cd := by
      rw [div_le_div_iff₀ hcd'R hcdR]; exact_mod_cast hfloor
    linarith
  have hmagdiff : |sfrac n cn cd - sfrac n cn' cd'| = (cn : ℝ) / cd - (cn' : ℝ) / cd' := by
    have hsdiff : sfrac n cn cd - sfrac n cn' cd'
        = (if n then -1 else 1) * ((cn : ℝ) / cd - (cn' : ℝ) / cd') := by
      simp only [sfrac]; ring
    rw [hsdiff, abs_mul]; cases n <;> simp [abs_of_nonneg hnn]
  have hkey : (rn : ℝ) / rd + ((cn : ℝ) / cd - (cn' : ℝ) / cd') ≤ (rn' : ℝ) / rd' := by
    rw [div_sub_div _ _ (ne_of_gt hcdR) (ne_of_gt hcd'R),
      div_add_div _ _ (ne_of_gt hrdR) (by positivity), div_le_div_iff₀ (by positivity) hrd'R]
    have hcast : ((cn : ℝ) * cd' - cd * cn') = ((cn * cd' - cn' * cd : ℕ) : ℝ) := by
      rw [Nat.cast_sub hfloor]; push_cast; ring
    rw [hcast]
    have h2 : (((rn * (cd * cd') + (cn * cd' - cn' * cd) * rd) * rd' : ℕ) : ℝ)
            ≤ ((rn' * (rd * (cd * cd')) : ℕ) : ℝ) := by exact_mod_cast hrad
    push_cast at h2 ⊢
    nlinarith [h2]
  simp only [Real.IsNear] at h ⊢
  calc |x - sfrac n cn' cd'|
      ≤ |x - sfrac n cn cd| + |sfrac n cn cd - sfrac n cn' cd'| := abs_sub_le _ _ _
    _ ≤ (rn : ℝ) / rd + ((cn : ℝ) / cd - (cn' : ℝ) / cd') := by
      rw [hmagdiff]; exact add_le_add h le_rfl
    _ ≤ (rn' : ℝ) / rd' := hkey

/- `Real.IsNear.recentre` with its six side conditions behind `recentreOk`, so the statement the
kernel instantiates carries one short application rather than six arithmetic trees. -/
theorem Real.IsNear.recentre' {x : ℝ} {n : Bool} {cn cd rn rd cn' cd' rn' rd' : ℕ}
    (h : Real.IsNear x n cn cd rn rd)
    (hs : recentreOk cn cd rn rd cn' cd' rn' rd' = true) :
    Real.IsNear x n cn' cd' rn' rd' := by
  simp only [recentreOk, Nat.beq_eq, Nat.add_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, z6⟩ := Nat.add_eq_zero_iff.mp hs
  exact Real.IsNear.recentre h
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z1)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z2))
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z3)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z4))
    (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z5)) (Nat.ble_eq.mpr (Nat.le_of_sub_eq_zero z6))

end Enclosure

end

end CertificatePort144
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/Images.lean -/
section CertificatePort145


/-!
# Real interval enclosures: images under functions

Enclosure of `f x` from an enclosure of `x`: the Lipschitz image (`sin`, `cos`), the monotone
endpoint images (`sqrt`, `inv`), the two-sided sandwich `of_interval`, and the midpoint helper
`of_endpoints`.
-/
section


namespace Enclosure

/-! ### Function of an enclosure (Lipschitz image)

Enclose `x` about a rational centre `c`, certify `f` at `c`, and widen by the Lipschitz factor. -/

/- Image of an enclosure under a 1-Lipschitz `f`: from `x` near `c` (radius `ρn/ρd`) and a
certificate of `f c` (centre `q`, radius `rsn/rsd`), `f x` is near `q` with radius `ρ + r`. -/
theorem Real.IsNear.lipschitz_image {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y|)
    {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (f c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (f x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) := by
  subst hc
  simp only [Nat.mul_eq, Nat.add_eq]
  have hρdR : (0:ℝ) < ρd := pos_real_of_ble hρd
  have hrsdR : (0:ℝ) < rsd := pos_real_of_ble hrsd
  have hρdN : 0 < ρd := pos_of_ble hρd
  have hrsdN : 0 < rsd := pos_of_ble hrsd
  simp only [Real.IsNear] at hx hsc ⊢
  have hrad : ((rsn * ρd + ρn * rsd : ℕ) : ℝ) / ((rsd * ρd : ℕ) : ℝ)
            = (ρn : ℝ) / ρd + (rsn : ℝ) / rsd := by
    rw [div_eq_iff (by positivity)]; push_cast; field_simp; ring
  rw [hrad]
  calc |f x - sfrac sn scn scd|
      ≤ |f x - f (sfrac nc cn cd)| + |f (sfrac nc cn cd) - sfrac sn scn scd| :=
        abs_sub_le _ _ _
    _ ≤ |x - sfrac nc cn cd| + (rsn : ℝ) / rsd := add_le_add (hf _ _) hsc
    _ ≤ (ρn : ℝ) / ρd + (rsn : ℝ) / rsd := by linarith [hx]

/- `sin` of an enclosure: `lipschitz_image` at `Real.abs_sin_sub_sin_le`. -/
theorem Real.IsNear.sin_image {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (Real.sin c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (Real.sin x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) :=
  lipschitz_image (fun _ _ => Real.abs_sin_sub_sin_le _ _) hx hc hsc hρd hrsd

/- `cos` of an enclosure: `lipschitz_image` at `Real.abs_cos_sub_cos_le`. -/
theorem Real.IsNear.cos_image {x c : ℝ} {nc : Bool} {cn cd ρn ρd : ℕ}
    {sn : Bool} {scn scd rsn rsd : ℕ}
    (hx : Real.IsNear x nc cn cd ρn ρd)
    (hc : sfrac nc cn cd = c)
    (hsc : Real.IsNear (Real.cos c) sn scn scd rsn rsd)
    (hρd : Nat.ble 1 ρd) (hrsd : Nat.ble 1 rsd) :
    Real.IsNear (Real.cos x) sn scn scd ((rsn.mul ρd).add (ρn.mul rsd)) (rsd.mul ρd) :=
  lipschitz_image (fun _ _ => Real.abs_cos_sub_cos_le _ _) hx hc hsc hρd hrsd

/- Midpoint enclosure from rational endpoints: if `a/Q ≤ z ≤ b/Q` (`Q > 0`), then `z` is near the
midpoint `(a+b)/(2Q)` with radius `(b−a)/(2Q)`. Shared tail of `sqrt_image` and `inv_image`. -/
theorem Real.IsNear.of_endpoints {z : ℝ} {a b Q : ℕ} (hQ : Nat.ble 1 Q)
    (h1 : (a : ℝ) / Q ≤ z) (h2 : z ≤ (b : ℝ) / Q) :
    Real.IsNear z false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a) (Nat.mul (nat_lit 2) Q) := by
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hab : a ≤ b := by
    have hh : (a : ℝ) / Q ≤ (b : ℝ) / Q := le_trans h1 h2
    rw [div_le_div_iff₀ hQR hQR] at hh
    exact_mod_cast le_of_mul_le_mul_right hh hQR
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := Nat.cast_sub hab
  simp only [Nat.mul_eq, Nat.add_eq, Nat.sub_eq]
  have hc1 : ((a : ℝ) + b) / (2 * Q) - ((b : ℝ) - a) / (2 * Q) = (a : ℝ) / Q := by field_simp; ring
  have hc2 : ((a : ℝ) + b) / (2 * Q) + ((b : ℝ) - a) / (2 * Q) = (b : ℝ) / Q := by field_simp; ring
  rw [Real.IsNear, sfrac_false_div, abs_le]
  push_cast [hcast]
  exact ⟨by linarith [h1, hc1], by linarith [h2, hc2]⟩

/- `√` of a nonnegative enclosure `S ∈ [lo, hi]`: with square-to-verify bounds `a/Q ≤ √lo` and
`√hi ≤ b/Q` on the rational endpoints, monotonicity gives `√S ∈ [a/Q, b/Q]`, returned as the
midpoint `(a+b)/(2Q) ± (b−a)/(2Q)`. -/
theorem Real.IsNear.sqrt_image {S : ℝ} {cn cd rn rd a b Q : ℕ}
    (hS : Real.IsNear S false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hQ : Nat.ble 1 Q)
    (hge : Nat.ble (rn.mul cd) (cn.mul rd))
    (hlo : Nat.ble ((a.pow 2).mul (cd.mul rd)) (((cn.mul rd).sub (rn.mul cd)).mul (Q.pow 2)))
    (hhi : Nat.ble (((cn.mul rd).add (rn.mul cd)).mul (Q.pow 2)) ((b.pow 2).mul (cd.mul rd))) :
    Real.IsNear (Real.sqrt S) false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a)
      (Nat.mul (nat_lit 2) Q) := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.sub_eq] at hge hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hsub : ((cn * rd - rn * cd : ℕ) : ℝ) = (cn : ℝ) * rd - rn * cd := by
    rw [Nat.cast_sub hge]; push_cast; ring
  have hQ2 : (0:ℝ) < (Q : ℝ) ^ 2 := by positivity
  have hcr : (0:ℝ) < (cd : ℝ) * rd := by positivity
  have hlo' : ((a : ℝ) / Q) ^ 2 ≤ (cn : ℝ) / cd - (rn : ℝ) / rd := by
    rw [div_pow, div_sub_div _ _ (ne_of_gt hcdR) (ne_of_gt hrdR), div_le_div_iff₀ hQ2 hcr]
    have h : ((a ^ 2 * (cd * rd) : ℕ) : ℝ) ≤ (((cn * rd - rn * cd) * Q ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hlo
    push_cast [hsub] at h; nlinarith [h]
  have hhi' : (cn : ℝ) / cd + (rn : ℝ) / rd ≤ ((b : ℝ) / Q) ^ 2 := by
    rw [div_pow, div_add_div _ _ (ne_of_gt hcdR) (ne_of_gt hrdR), div_le_div_iff₀ hcr hQ2]
    have h : (((cn * rd + rn * cd) * Q ^ 2 : ℕ) : ℝ) ≤ ((b ^ 2 * (cd * rd) : ℕ) : ℝ) := by
      exact_mod_cast hhi
    push_cast at h; nlinarith [h]
  have hSlo : (cn : ℝ) / cd - (rn : ℝ) / rd ≤ S := by have h := hS.lower; rwa [sfrac_false_div] at h
  have hShi : S ≤ (cn : ℝ) / cd + (rn : ℝ) / rd := by have h := hS.upper; rwa [sfrac_false_div] at h
  have h1 : (a : ℝ) / Q ≤ Real.sqrt S := by
    calc (a : ℝ) / Q = Real.sqrt (((a : ℝ) / Q) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((cn : ℝ) / cd - (rn : ℝ) / rd) := Real.sqrt_le_sqrt hlo'
      _ ≤ Real.sqrt S := Real.sqrt_le_sqrt hSlo
  have h2 : Real.sqrt S ≤ (b : ℝ) / Q := by
    calc Real.sqrt S ≤ Real.sqrt ((cn : ℝ) / cd + (rn : ℝ) / rd) := Real.sqrt_le_sqrt hShi
      _ ≤ Real.sqrt (((b : ℝ) / Q) ^ 2) := Real.sqrt_le_sqrt hhi'
      _ = (b : ℝ) / Q := Real.sqrt_sq (by positivity)
  exact Real.IsNear.of_endpoints hQ h1 h2

/- Enclosure of `y` from a two-sided sandwich `y1 ≤ y ≤ y2` (enclosures of `y1`, `y2`) plus literal
result fields whose interval contains `[y1.lo, y2.hi]` (`hL`/`hH`). -/
theorem Real.IsNear.of_interval {y y1 y2 : ℝ} {n1 n2 nR : Bool}
    {c1 d1 r1 e1 c2 d2 r2 e2 cnR cdR rnR rdR : ℕ}
    (h1 : Real.IsNear y1 n1 c1 d1 r1 e1) (h2 : Real.IsNear y2 n2 c2 d2 r2 e2)
    (hlo : y1 ≤ y) (hhi : y ≤ y2)
    (hd1 : Nat.ble 1 d1) (he1 : Nat.ble 1 e1) (hd2 : Nat.ble 1 d2) (he2 : Nat.ble 1 e2)
    (hcdR : Nat.ble 1 cdR) (hrdR : Nat.ble 1 rdR)
    (hL : Nat.ble ((((numPos nR cnR).mul ((rdR.mul d1).mul e1)).add
              ((numNeg n1 c1).mul ((cdR.mul rdR).mul e1))).add
              (r1.mul ((cdR.mul rdR).mul d1)))
            ((((numPos n1 c1).mul ((cdR.mul rdR).mul e1)).add
              ((numNeg nR cnR).mul ((rdR.mul d1).mul e1))).add
              (rnR.mul ((cdR.mul d1).mul e1))))
    (hH : Nat.ble ((((numPos n2 c2).mul ((cdR.mul rdR).mul e2)).add
              ((numNeg nR cnR).mul ((rdR.mul d2).mul e2))).add
              (r2.mul ((cdR.mul rdR).mul d2)))
            ((((numPos nR cnR).mul ((rdR.mul d2).mul e2)).add
              ((numNeg n2 c2).mul ((cdR.mul rdR).mul e2))).add
              (rnR.mul ((cdR.mul d2).mul e2)))) :
    Real.IsNear y nR cnR cdR rnR rdR := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hL hH
  have hd1R : (0:ℝ) < d1 := pos_real_of_ble hd1
  have he1R : (0:ℝ) < e1 := pos_real_of_ble he1
  have hd2R : (0:ℝ) < d2 := pos_real_of_ble hd2
  have he2R : (0:ℝ) < e2 := pos_real_of_ble he2
  have hcdRR : (0:ℝ) < cdR := pos_real_of_ble hcdR
  have hrdRR : (0:ℝ) < rdR := pos_real_of_ble hrdR
  have hloR : sfrac nR cnR cdR - (rnR : ℝ) / rdR ≤ sfrac n1 c1 d1 - (r1 : ℝ) / e1 := by
    rw [sfrac_eq_parts nR cnR cdR, sfrac_eq_parts n1 c1 d1,
      div_sub_div _ _ hcdRR.ne' hrdRR.ne', div_sub_div _ _ hd1R.ne' he1R.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos nR cnR * (rdR * d1 * e1) + numNeg n1 c1 * (cdR * rdR * e1)
                + r1 * (cdR * rdR * d1) : ℕ) : ℝ)
            ≤ ((numPos n1 c1 * (cdR * rdR * e1) + numNeg nR cnR * (rdR * d1 * e1)
                + rnR * (cdR * d1 * e1) : ℕ) : ℝ) := by exact_mod_cast hL
    push_cast at hc ⊢; nlinarith [hc]
  have hhiR : sfrac n2 c2 d2 + (r2 : ℝ) / e2 ≤ sfrac nR cnR cdR + (rnR : ℝ) / rdR := by
    rw [sfrac_eq_parts nR cnR cdR, sfrac_eq_parts n2 c2 d2,
      div_add_div _ _ hd2R.ne' he2R.ne', div_add_div _ _ hcdRR.ne' hrdRR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos n2 c2 * (cdR * rdR * e2) + numNeg nR cnR * (rdR * d2 * e2)
                + r2 * (cdR * rdR * d2) : ℕ) : ℝ)
            ≤ ((numPos nR cnR * (rdR * d2 * e2) + numNeg n2 c2 * (cdR * rdR * e2)
                + rnR * (cdR * d2 * e2) : ℕ) : ℝ) := by exact_mod_cast hH
    push_cast at hc ⊢; nlinarith [hc]
  exact Real.IsNear.mk' (le_trans hloR (le_trans h1.lower hlo))
    (le_trans hhi (le_trans h2.upper hhiR))

/- Reciprocal of a strictly positive enclosure `x ∈ [lo, hi]` (`lo > 0`): with cross-multiplied
`Nat.ble` bounds `a/Q ≤ 1/hi` and `1/lo ≤ b/Q`, `x⁻¹ ∈ [a/Q, b/Q]`, returned in midpoint form. -/
theorem Real.IsNear.inv_image {x : ℝ} {cn cd rn rd a b Q : ℕ}
    (hx : Real.IsNear x false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hQ : Nat.ble 1 Q)
    (hpos : Nat.blt (rn.mul cd) (cn.mul rd))
    (hlo : Nat.ble (a.mul ((cn.mul rd).add (rn.mul cd))) (Q.mul (cd.mul rd)))
    (hhi : Nat.ble (Q.mul (cd.mul rd)) (b.mul ((cn.mul rd).sub (rn.mul cd)))) :
    Real.IsNear x⁻¹ false (a.add b) (Nat.mul (nat_lit 2) Q) (b.sub a)
      (Nat.mul (nat_lit 2) Q) := by
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hpos hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hQR : (0:ℝ) < Q := pos_real_of_ble hQ
  have hposn : rn * cd < cn * rd := hpos
  have hsub : ((cn * rd - rn * cd : ℕ) : ℝ) = (cn : ℝ) * rd - rn * cd := by
    rw [Nat.cast_sub hposn.le]; push_cast; ring
  have hloQ : (0:ℝ) < (cn : ℝ) / cd - (rn : ℝ) / rd := by
    rw [div_sub_div _ _ hcdR.ne' hrdR.ne', lt_div_iff₀ (by positivity)]
    have h := hposn
    have : ((rn * cd : ℕ) : ℝ) < ((cn * rd : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; nlinarith [this]
  have hSlo : (cn : ℝ) / cd - (rn : ℝ) / rd ≤ x := by
    have h := hx.lower; rwa [sfrac_false_div] at h
  have hShi : x ≤ (cn : ℝ) / cd + (rn : ℝ) / rd := by
    have h := hx.upper; rwa [sfrac_false_div] at h
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le hloQ hSlo
  have hdiffR : (0:ℝ) < (cn : ℝ) * rd - (cd : ℝ) * rn := by
    have h' : ((rn * cd : ℕ) : ℝ) < ((cn * rd : ℕ) : ℝ) := by exact_mod_cast hposn
    push_cast at h'; linarith
  have hsumR : (0:ℝ) < (cn : ℝ) * rd + (cd : ℝ) * rn := by
    have hcdrn : (0:ℝ) ≤ (cd : ℝ) * rn := by positivity
    linarith
  have h1 : (a : ℝ) / Q ≤ x⁻¹ := by
    have hstep : (a : ℝ) / Q ≤ ((cn : ℝ) / cd + (rn : ℝ) / rd)⁻¹ := by
      rw [div_add_div _ _ hcdR.ne' hrdR.ne', inv_div, div_le_div_iff₀ hQR hsumR]
      have h' : ((a * (cn * rd + rn * cd) : ℕ) : ℝ) ≤ ((Q * (cd * rd) : ℕ) : ℝ) := by
        exact_mod_cast hlo
      push_cast at h'; nlinarith [h']
    exact le_trans hstep (inv_anti₀ hx0 hShi)
  have h2 : x⁻¹ ≤ (b : ℝ) / Q := by
    have hstep : ((cn : ℝ) / cd - (rn : ℝ) / rd)⁻¹ ≤ (b : ℝ) / Q := by
      rw [div_sub_div _ _ hcdR.ne' hrdR.ne', inv_div, div_le_div_iff₀ hdiffR hQR]
      have h' : ((Q * (cd * rd) : ℕ) : ℝ) ≤ ((b * (cn * rd - rn * cd) : ℕ) : ℝ) := by
        exact_mod_cast hhi
      push_cast [hsub] at h'; nlinarith [h']
    exact le_trans (inv_anti₀ hloQ hSlo) hstep
  exact Real.IsNear.of_endpoints hQ h1 h2

end Enclosure

end

end CertificatePort145
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/Verify.lean -/
section CertificatePort146


/-!
# Real interval enclosures: the bound verifier and comparisons

The generic bound verifier `isNear_verify_le`, sign extraction (`pos_val`/`neg_val`), and the
certificate comparisons (`norm_gt_of_isNear`, `gt_of_isNear`).
-/
section


namespace Enclosure

/-! ### The generic bound verifier -/

/- Generic bound verifier: from an enclosure of `X` and the goal's own `q`, `eps`, conclude
`|X − q| ≤ eps`, since the enclosure interval sits inside `[q − eps, q + eps]` (`hlo`/`hhi`). -/
theorem isNear_verify_le (X q eps : ℝ) (cneg qneg : Bool) (cn cd rn rd qn qd en ed : ℕ)
    (hcert : Real.IsNear X cneg cn cd rn rd)
    (hq : q = sfrac qneg qn qd) (heps : eps = sfrac false en ed)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd) (hqd : Nat.ble 1 qd) (hed : Nat.ble 1 ed)
    (hlo : Nat.ble ((((numPos qneg qn).mul ((ed.mul cd).mul rd)).add
              ((numNeg cneg cn).mul ((qd.mul ed).mul rd))).add
              (rn.mul ((cd.mul qd).mul ed)))
            ((((numPos cneg cn).mul ((qd.mul ed).mul rd)).add
              ((numNeg qneg qn).mul ((ed.mul cd).mul rd))).add
              (en.mul ((qd.mul cd).mul rd))))
    (hhi : Nat.ble ((((numPos cneg cn).mul ((qd.mul ed).mul rd)).add
              ((numNeg qneg qn).mul ((ed.mul cd).mul rd))).add
              (rn.mul ((cd.mul qd).mul ed)))
            ((((numPos qneg qn).mul ((ed.mul cd).mul rd)).add
              ((numNeg cneg cn).mul ((qd.mul ed).mul rd))).add
              (en.mul ((qd.mul cd).mul rd)))) :
    |X - q| ≤ eps := by
  subst hq heps
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at hlo hhi
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hqdR : (0:ℝ) < qd := pos_real_of_ble hqd
  have hedR : (0:ℝ) < ed := pos_real_of_ble hed
  have heps : sfrac false en ed = (en : ℝ) / ed := by simp [sfrac]
  rw [Real.IsNear, abs_le] at hcert
  have hloR : sfrac qneg qn qd - (en : ℝ) / ed ≤ sfrac cneg cn cd - (rn : ℝ) / rd := by
    rw [sfrac_eq_parts qneg qn qd, sfrac_eq_parts cneg cn cd,
      div_sub_div _ _ hqdR.ne' hedR.ne', div_sub_div _ _ hcdR.ne' hrdR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos qneg qn * (ed * cd * rd) + numNeg cneg cn * (qd * ed * rd)
                + rn * (cd * qd * ed) : ℕ) : ℝ)
            ≤ ((numPos cneg cn * (qd * ed * rd) + numNeg qneg qn * (ed * cd * rd)
                + en * (qd * cd * rd) : ℕ) : ℝ) := by exact_mod_cast hlo
    push_cast at hc ⊢; nlinarith [hc]
  have hhiR : sfrac cneg cn cd + (rn : ℝ) / rd ≤ sfrac qneg qn qd + (en : ℝ) / ed := by
    rw [sfrac_eq_parts qneg qn qd, sfrac_eq_parts cneg cn cd,
      div_add_div _ _ hcdR.ne' hrdR.ne', div_add_div _ _ hqdR.ne' hedR.ne',
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hc : ((numPos cneg cn * (qd * ed * rd) + numNeg qneg qn * (ed * cd * rd)
                + rn * (cd * qd * ed) : ℕ) : ℝ)
            ≤ ((numPos qneg qn * (ed * cd * rd) + numNeg cneg cn * (qd * ed * rd)
                + en * (qd * cd * rd) : ℕ) : ℝ) := by exact_mod_cast hhi
    push_cast at hc ⊢; nlinarith [hc]
  rw [heps, abs_le]
  exact ⟨by linarith [hcert.1, hloR], by linarith [hcert.2, hhiR]⟩

/- Fast verifier for the common case where the goal's `q` equals the enclosure centre *as a
rational* (`qn/qd = cn/cd`, same sign, as on every `approx%`+`bound` path). Then
`|X − q| = |X − centre| ≤ rn/rd`, so the bound collapses to the centre check `qn·cd = cn·qd`
(one big multiply) plus `rn·ed ≤ en·rd`, avoiding `isNear_verify_le`'s four-denominator triple
products (the kernel bottleneck at high precision, where `cd`, `qd`, `ed`, `rd` are all
precision-sized). The goal's `q` may be a gcd-reduced literal (`ℚ` normalises), so this compares
by cross-multiplication rather than requiring `qn = cn`, `qd = cd` syntactically. -/
theorem isNear_verify_le_center (X q eps : ℝ) (neg : Bool) (cn cd rn rd qn qd en ed : ℕ)
    (hcert : Real.IsNear X neg cn cd rn rd)
    (hq : q = sfrac neg qn qd) (heps : eps = sfrac false en ed)
    (hcd : Nat.ble 1 cd) (hqd : Nat.ble 1 qd) (hrd : Nat.ble 1 rd) (hed : Nat.ble 1 ed)
    (hsame : (qn.mul cd).beq (cn.mul qd)) (hle : Nat.ble (rn.mul ed) (en.mul rd)) :
    |X - q| ≤ eps := by
  subst hq heps
  simp only [Nat.beq_eq, Nat.ble_eq, Nat.mul_eq] at hsame hle
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hqdR : (0:ℝ) < qd := pos_real_of_ble hqd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hedR : (0:ℝ) < ed := pos_real_of_ble hed
  have hqc : (qn : ℝ) / qd = (cn : ℝ) / cd := by
    rw [div_eq_div_iff hqdR.ne' hcdR.ne']; exact_mod_cast hsame
  have hqcenter : sfrac neg qn qd = sfrac neg cn cd := by unfold sfrac; rw [hqc]
  rw [hqcenter]
  have hcert' : |X - sfrac neg cn cd| ≤ (rn : ℝ) / rd := hcert
  refine hcert'.trans ?_
  rw [show sfrac false en ed = (en : ℝ) / ed from by simp [sfrac], div_le_div_iff₀ hrdR hedR]
  exact_mod_cast hle

/-! ### Sign and margin extraction (the certificate comparisons) -/

/- A negatively-signed enclosure whose radius stays below its centre magnitude pins `x < 0`. -/
theorem Real.IsNear.neg_val {x : ℝ} {cn cd rn rd : ℕ}
    (h : Real.IsNear x true cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd)
    (hlt : Nat.blt (rn.mul cd) (cn.mul rd)) : x < 0 := by
  simp only [Nat.blt_eq, Nat.mul_eq] at hlt
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hu := h.upper
  rw [sfrac_true_div, neg_div] at hu
  have hcross : (rn : ℝ) * cd < (cn : ℝ) * rd := by exact_mod_cast hlt
  have hlt' : (rn : ℝ) / rd < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ hrdR hcdR]
    linarith
  linarith

/- A positively-signed enclosure whose radius stays below its centre pins the sign: `0 < x`. -/
theorem Real.IsNear.pos_val {x : ℝ} {cn cd rn rd : ℕ}
    (h : Real.IsNear x false cn cd rn rd)
    (hcd : Nat.ble 1 cd) (hrd : Nat.ble 1 rd)
    (hlt : Nat.blt (rn.mul cd) (cn.mul rd)) : 0 < x := by
  simp only [Nat.blt_eq, Nat.mul_eq] at hlt
  have hcdR : (0:ℝ) < cd := pos_real_of_ble hcd
  have hrdR : (0:ℝ) < rd := pos_real_of_ble hrd
  have hl := h.lower
  rw [sfrac_false_div] at hl
  have hcross : (rn : ℝ) * cd < (cn : ℝ) * rd := by exact_mod_cast hlt
  have hlt' : (rn : ℝ) / rd < (cn : ℝ) / cd := by
    rw [div_lt_div_iff₀ hrdR hcdR]
    linarith
  linarith

/- `‖x‖ > e`: the magnitude lower bound of `x`'s enclosure exceeds the upper bound of `e`'s. -/
theorem norm_gt_of_isNear {x e : ℝ} {nx ne' : Bool} {cnx cdx rnx rdx cne cde rne rde : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (he : Real.IsNear e ne' cne cde rne rde)
    (hcdx : Nat.ble 1 cdx) (hrdx : Nat.ble 1 rdx) (hcde : Nat.ble 1 cde) (hrde : Nat.ble 1 rde)
    (h : Nat.blt ((((numPos ne' cne).mul (rde.mul (cdx.mul rdx))).add
            (rne.mul (cde.mul (cdx.mul rdx)))).add
            (rnx.mul (cde.mul (rde.mul cdx))))
          ((cnx.mul (cde.mul (rde.mul rdx))).add
            ((numNeg ne' cne).mul (rde.mul (cdx.mul rdx))))) :
    ‖x‖ > e := by
  simp only [Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at h
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hcdeR : (0:ℝ) < cde := pos_real_of_ble hcde
  have hrdeR : (0:ℝ) < rde := pos_real_of_ble hrde
  -- |x| ≥ cnx/cdx − rnx/rdx
  have habs : (cnx : ℝ) / cdx - (rnx : ℝ) / rdx ≤ |x| := by
    have h1 : |sfrac nx cnx cdx| - |x - sfrac nx cnx cdx| ≤ |x| := by
      have := abs_sub_abs_le_abs_sub (sfrac nx cnx cdx) x
      have habs2 : |sfrac nx cnx cdx - x| = |x - sfrac nx cnx cdx| := abs_sub_comm _ _
      linarith [this, habs2 ▸ this]
    rw [abs_sfrac] at h1
    have h2 : |x - sfrac nx cnx cdx| ≤ (rnx : ℝ) / rdx := hx
    linarith
  -- e ≤ sfrac ne' cne cde + rne/rde
  have hup := he.upper
  -- cross-multiplied comparison
  have hcR : ((numPos ne' cne * (rde * (cdx * rdx)) + rne * (cde * (cdx * rdx))
        + rnx * (cde * (rde * cdx)) : ℕ) : ℝ)
      < ((cnx * (cde * (rde * rdx)) + numNeg ne' cne * (rde * (cdx * rdx)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcR
  have hkey : sfrac ne' cne cde + (rne : ℝ) / rde < (cnx : ℝ) / cdx - (rnx : ℝ) / rdx := by
    rw [sfrac_eq_parts]
    rw [div_add_div _ _ hcdeR.ne' hrdeR.ne', div_sub_div _ _ hcdxR.ne' hrdxR.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcR]
  rw [Real.norm_eq_abs, gt_iff_lt]
  linarith

/- `x > e`: the lower bound of `x`'s enclosure exceeds the upper bound of `e`'s. -/
theorem gt_of_isNear {x e : ℝ} {nx ne' : Bool} {cnx cdx rnx rdx cne cde rne rde : ℕ}
    (hx : Real.IsNear x nx cnx cdx rnx rdx) (he : Real.IsNear e ne' cne cde rne rde)
    (hcdx : Nat.ble 1 cdx) (hrdx : Nat.ble 1 rdx) (hcde : Nat.ble 1 cde) (hrde : Nat.ble 1 rde)
    (h : Nat.blt ((((numPos ne' cne).mul (rde.mul (cdx.mul rdx))).add
            (rne.mul (cde.mul (cdx.mul rdx)))).add
          (((numNeg nx cnx).mul (rdx.mul (cde.mul rde))).add
            (rnx.mul (cdx.mul (cde.mul rde)))))
          (((numPos nx cnx).mul (rdx.mul (cde.mul rde))).add
            ((numNeg ne' cne).mul (rde.mul (cdx.mul rdx))))) :
    x > e := by
  simp only [Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at h
  have hcdxR : (0:ℝ) < cdx := pos_real_of_ble hcdx
  have hrdxR : (0:ℝ) < rdx := pos_real_of_ble hrdx
  have hcdeR : (0:ℝ) < cde := pos_real_of_ble hcde
  have hrdeR : (0:ℝ) < rde := pos_real_of_ble hrde
  have hlo : sfrac nx cnx cdx - (rnx : ℝ) / rdx ≤ x := by
    have h1 : |x - sfrac nx cnx cdx| ≤ (rnx : ℝ) / rdx := hx
    linarith [(abs_le.mp h1).1]
  have hup : e ≤ sfrac ne' cne cde + (rne : ℝ) / rde := he.upper
  have hcR : ((numPos ne' cne * (rde * (cdx * rdx)) + rne * (cde * (cdx * rdx))
        + (numNeg nx cnx * (rdx * (cde * rde)) + rnx * (cdx * (cde * rde))) : ℕ) : ℝ)
      < ((numPos nx cnx * (rdx * (cde * rde))
        + numNeg ne' cne * (rde * (cdx * rdx)) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcR
  have hkey : sfrac ne' cne cde + (rne : ℝ) / rde < sfrac nx cnx cdx - (rnx : ℝ) / rdx := by
    rw [sfrac_eq_parts, sfrac_eq_parts,
      div_add_div _ _ hcdeR.ne' hrdeR.ne', div_sub_div _ _ hcdxR.ne' hrdxR.ne',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcR]
  linarith

end Enclosure

end

end CertificatePort146
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/Sums.lean -/
section CertificatePort147


/-!
# Real interval enclosures: finite-sum helpers

`Finset.Ico`/`range` splitting lemmas and enclosure transport along equalities, used to assemble
an enclosure of a finite sum term by term.
-/
section


namespace Enclosure

/-! ### Transport and finite-sum helpers -/

/- Transport an enclosure along an equality of the enclosed real. -/
theorem Real.IsNear.of_eq {x y : ℝ} {n : Bool} {cn cd rn rd : ℕ}
    (he : x = y) (h : Real.IsNear y n cn cd rn rd) : Real.IsNear x n cn cd rn rd := by
  rw [he]; exact h

/- Split a `Finset.Ico` sum at a midpoint `m ∈ [a,b]` (both bounds as `Nat.ble` reflections). -/
theorem sum_Ico_consec_real (f : ℕ → ℝ) (a m b : ℕ)
    (hab : Nat.ble a m = true) (hmb : Nat.ble m b = true) :
    (∑ i ∈ Finset.Ico a b, f i) = (∑ i ∈ Finset.Ico a m, f i) + (∑ i ∈ Finset.Ico m b, f i) :=
  (Finset.sum_Ico_consecutive f (Nat.le_of_ble_eq_true hab) (Nat.le_of_ble_eq_true hmb)).symm

/- A width-one `Finset.Ico` sum (`b = a+1`) is the single term `f a`. -/
theorem sum_Ico_width_one_real (f : ℕ → ℝ) (a b : ℕ) (h : Nat.beq b (a.add 1) = true) :
    (∑ i ∈ Finset.Ico a b, f i) = f a := by
  have hb : b = a + 1 := Nat.eq_of_beq_eq_true h
  subst hb
  rw [Finset.sum_Ico_succ_top (Nat.le_refl a), Finset.Ico_self, Finset.sum_empty, zero_add]

/- An empty `Finset.Ico` sum (`a = b`) is `0`, enclosed with radius `0`. -/
theorem Real.IsNear.sum_Ico_empty (f : ℕ → ℝ) (a b : ℕ) (h : Nat.beq a b = true) :
    Real.IsNear (∑ i ∈ Finset.Ico a b, f i) false (nat_lit 0) (nat_lit 1) (nat_lit 0)
      (nat_lit 1) := by
  have hb : a = b := Nat.eq_of_beq_eq_true h
  subst hb
  rw [Finset.Ico_self, Finset.sum_empty]
  simp [Real.IsNear, sfrac]

/- A `Finset.range n` sum as a `Finset.Ico 0 n` sum. -/
theorem sum_range_eq_Ico_real (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i) = (∑ i ∈ Finset.Ico 0 n, f i) := by
  rw [Finset.range_eq_Ico]

end Enclosure

end

end CertificatePort147
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/BinarySplit/Reduce/Sin.lean -/
section CertificatePort149


/-!
# Range-reduction lemmas for `sin` at large arguments

* `sin` modulo `π/2`: the four quadrant identities `sin_quad0..3` and the reduction lemmas
  `sin_reduce0..3`, which delegate to the generic `reduce_*_val` chain.
* `sin` by the π-free triple angle `sin(3θ) = 3·sinθ − 4·sin³θ`: `sin_triple_step` and its
  dyadic/argument-shaped forms.
-/
section


namespace BSN
open Enclosure

-- Inside `BSN` a bare `open Real` would resolve to `BSN.Real` (the `Real.IsNear` layer),
-- so open the root namespace explicitly for `π` and the trigonometric lemmas.
open _root_.Real

/-! ### Rounding the reduced argument

The reduction leaves an argument `u/v` whose denominator carries the precision of the `π` constant
it used, far beyond what the answer needs. The series cost grows with `v`, so it is evaluated at a
coarser `u'/v'` instead and the difference is absorbed into the radius: `sin` and `cos` move by no
more than their argument does. -/

/- Side conditions of `cos_arg_round`/`sin_arg_round`: positive denominators, `u'/v' ≤ u/v` so the
`ℕ` subtraction is the true difference, and `|u/v − u'/v'| + 1/Dp ≤ 1/D` cleared of denominators. -/
def argRoundOk (u v u' v' Dp D : ℕ) : Bool :=
  Nat.beq
    (Nat.add (Nat.sub (nat_lit 1) v)
    (Nat.add (Nat.sub (nat_lit 1) v')
    (Nat.add (Nat.sub (nat_lit 1) Dp)
    (Nat.add (Nat.sub (nat_lit 1) D)
    (Nat.add (Nat.sub (u'.mul v) (u.mul v'))
             (Nat.sub (Nat.add (Nat.mul (D.mul Dp) (Nat.sub (u.mul v') (u'.mul v)))
                               (Nat.mul D (v.mul v')))
                      (Nat.mul Dp (v.mul v'))))))))
    (nat_lit 0)

/- Unpack `argRoundOk` into the six conditions. -/
private theorem argRoundOk_parts {u v u' v' Dp D : ℕ} (hs : argRoundOk u v u' v' Dp D = true) :
    1 ≤ v ∧ 1 ≤ v' ∧ 1 ≤ Dp ∧ 1 ≤ D ∧ u' * v ≤ u * v' ∧
      D * Dp * (u * v' - u' * v) + D * (v * v') ≤ Dp * (v * v') := by
  simp only [argRoundOk, Nat.beq_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at hs
  obtain ⟨z1, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z2, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z3, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z4, hs⟩ := Nat.add_eq_zero_iff.mp hs
  obtain ⟨z5, z6⟩ := Nat.add_eq_zero_iff.mp hs
  exact ⟨Nat.le_of_sub_eq_zero z1, Nat.le_of_sub_eq_zero z2, Nat.le_of_sub_eq_zero z3,
    Nat.le_of_sub_eq_zero z4, Nat.le_of_sub_eq_zero z5, Nat.le_of_sub_eq_zero z6⟩

/- The rounding step, shared by `cos_arg_round` and `sin_arg_round`: from the six unpacked
conditions, the coarse argument is within `1/D − 1/Dp` of the true one. -/
private theorem arg_round_bound {u v u' v' Dp D : ℕ}
    (hv : 1 ≤ v) (hv' : 1 ≤ v') (hDp : 1 ≤ Dp) (hD : 1 ≤ D)
    (hle : u' * v ≤ u * v')
    (hmain : D * Dp * (u * v' - u' * v) + D * (v * v') ≤ Dp * (v * v')) :
    |(u : ℝ) / v - (u' : ℝ) / v'| + 1 / Dp ≤ 1 / D := by
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hv'R : (0 : ℝ) < v' := by exact_mod_cast hv'
  have hDpR : (0 : ℝ) < Dp := by exact_mod_cast hDp
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hleR : ((u' : ℝ) * v) ≤ (u : ℝ) * v' := by exact_mod_cast hle
  have hnn : (0 : ℝ) ≤ (u : ℝ) * v' - (u' : ℝ) * v := by linarith
  have hsub : ((u * v' - u' * v : ℕ) : ℝ) = (u : ℝ) * v' - (u' : ℝ) * v := by
    have hle' : (u' * v : ℕ) ≤ (u * v' : ℕ) := hle
    push_cast [Nat.cast_sub hle']
    ring
  have hrw : (u : ℝ) / v - (u' : ℝ) / v' = ((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') := by
    field_simp
  have habs : |(u : ℝ) / v - (u' : ℝ) / v'| = ((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') := by
    rw [hrw]
    exact abs_of_nonneg (div_nonneg hnn (by positivity))
  have hmainR : (D : ℝ) * Dp * ((u : ℝ) * v' - (u' : ℝ) * v) + D * (v * v') ≤ Dp * (v * v') := by
    have hc : ((D * Dp * (u * v' - u' * v) + D * (v * v') : ℕ) : ℝ)
        ≤ ((Dp * (v * v') : ℕ) : ℝ) := by
      exact_mod_cast hmain
    push_cast [hsub] at hc
    linarith
  rw [← sub_nonneg, habs]
  have key : (1 : ℝ) / D - (((u : ℝ) * v' - (u' : ℝ) * v) / (v * v') + 1 / Dp)
      = ((Dp : ℝ) * (v * v') - ((D : ℝ) * Dp * ((u : ℝ) * v' - (u' : ℝ) * v) + D * (v * v')))
        / ((D : ℝ) * Dp * (v * v')) := by
    field_simp
  rw [key]
  exact div_nonneg (by linarith) (by positivity)

/- `cos` at a rounded argument: the series is evaluated at `u'/v'` and the difference from `u/v`
is absorbed into the radius. -/
theorem cos_arg_round {n : Bool} {cn cd : ℕ} (u v u' v' Dp D : ℕ)
    (h : Real.IsNear (Real.cos ((u' : ℝ) / v')) n cn cd 1 Dp)
    (hs : argRoundOk u v u' v' Dp D = true) :
    Real.IsNear (Real.cos ((u : ℝ) / v)) n cn cd 1 D := by
  obtain ⟨hv, hv', hDp, hD, hle, hmain⟩ := argRoundOk_parts hs
  have hb := arg_round_bound hv hv' hDp hD hle hmain
  have hlip : |Real.cos ((u : ℝ) / v) - Real.cos ((u' : ℝ) / v')| ≤ |(u : ℝ) / v - (u' : ℝ) / v'| :=
    Real.abs_cos_sub_cos_le _ _
  have h' : |Real.cos ((u' : ℝ) / v') - sfrac n cn cd| ≤ (1 : ℝ) / Dp := by
    have hh := h
    simp only [Real.IsNear] at hh
    push_cast at hh
    exact hh
  have htri := abs_sub_le (Real.cos ((u : ℝ) / v)) (Real.cos ((u' : ℝ) / v')) (sfrac n cn cd)
  have hres : |Real.cos ((u : ℝ) / v) - sfrac n cn cd| ≤ ((1 : ℕ) : ℝ) / ((D : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hres

/- `sin` at a rounded argument: the series is evaluated at `u'/v'` and the difference from `u/v`
is absorbed into the radius. -/
theorem sin_arg_round {n : Bool} {cn cd : ℕ} (u v u' v' Dp D : ℕ)
    (h : Real.IsNear (Real.sin ((u' : ℝ) / v')) n cn cd 1 Dp)
    (hs : argRoundOk u v u' v' Dp D = true) :
    Real.IsNear (Real.sin ((u : ℝ) / v)) n cn cd 1 D := by
  obtain ⟨hv, hv', hDp, hD, hle, hmain⟩ := argRoundOk_parts hs
  have hb := arg_round_bound hv hv' hDp hD hle hmain
  have hlip : |Real.sin ((u : ℝ) / v) - Real.sin ((u' : ℝ) / v')| ≤ |(u : ℝ) / v - (u' : ℝ) / v'| :=
    Real.abs_sin_sub_sin_le _ _
  have h' : |Real.sin ((u' : ℝ) / v') - sfrac n cn cd| ≤ (1 : ℝ) / Dp := by
    have hh := h
    simp only [Real.IsNear] at hh
    push_cast at hh
    exact hh
  have htri := abs_sub_le (Real.sin ((u : ℝ) / v)) (Real.sin ((u' : ℝ) / v')) (sfrac n cn cd)
  have hres : |Real.sin ((u : ℝ) / v) - sfrac n cn cd| ≤ ((1 : ℕ) : ℝ) / ((D : ℕ) : ℝ) := by
    push_cast
    linarith
  exact hres

/-! ### Quadrant identities (period-4 in the multiple of `π/2`) -/

/- `k ≡ 0 (mod 4)` quadrant: `sin (r + 4q·(π/2)) = sin r` (here `4q·(π/2) = q·2π`). -/
theorem sin_quad0 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ)) * (π / 2)) = Real.sin r := by
  have e : r + (4 * (q : ℝ)) * (π / 2) = r + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi]

/- `k ≡ 1 (mod 4)` quadrant: `sin (r + (4q+1)·(π/2)) = cos r`. -/
theorem sin_quad1 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 1) * (π / 2)) = Real.cos r := by
  have e : r + (4 * (q : ℝ) + 1) * (π / 2) = (r + π / 2) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi_div_two]

/- `k ≡ 2 (mod 4)` quadrant: `sin (r + (4q+2)·(π/2)) = −sin r`. -/
theorem sin_quad2 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 2) * (π / 2)) = -Real.sin r := by
  have e : r + (4 * (q : ℝ) + 2) * (π / 2) = (r + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi]

/- `k ≡ 3 (mod 4)` quadrant: `sin (r + (4q+3)·(π/2)) = −cos r`. -/
theorem sin_quad3 (r : ℝ) (q : ℤ) :
    Real.sin (r + (4 * (q : ℝ) + 3) * (π / 2)) = -Real.cos r := by
  have e : r + (4 * (q : ℝ) + 3) * (π / 2) = ((r + π / 2) + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, sin_add_int_mul_two_pi, sin_add_pi, sin_add_pi_div_two]

/-! ### `π/2`-interval helpers -/

/- From a `π` bound `|π − P| ≤ d`, halve it to a `π/2` bound `|π/2 − P/2| ≤ d/2`. -/
theorem sin_triple_step (θ q qnew : ℝ) (D Rho D' : ℝ)
    (hq1 : |q| ≤ 1)
    (hq : |Real.sin θ - q| ≤ 1 / D)
    (hround : |(3 * q - 4 * q ^ 3) - qnew| ≤ 1 / Rho)
    (hcomb : 15 * (1 / D) + 1 / Rho ≤ 1 / D') :
    |Real.sin (3 * θ) - qnew| ≤ 1 / D' := by
  rw [Real.sin_three_mul]
  have hs1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hfirst : |3 * Real.sin θ - 4 * Real.sin θ ^ 3 - (3 * q - 4 * q ^ 3)| ≤ 15 * (1 / D) := by
    have hfac : 3 * Real.sin θ - 4 * Real.sin θ ^ 3 - (3 * q - 4 * q ^ 3)
        = (Real.sin θ - q) * (3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)) := by ring
    rw [hfac, abs_mul]
    have hsum : |Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2| ≤ 3 := by
      calc |Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2|
          ≤ |Real.sin θ ^ 2| + |Real.sin θ * q| + |q ^ 2| :=
            (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
        _ ≤ 1 + 1 + 1 := by
            gcongr
            · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs1
            · rw [abs_mul]; exact mul_le_one₀ hs1 (abs_nonneg _) hq1
            · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hq1
        _ = 3 := by norm_num
    have hc : |3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)| ≤ 15 :=
      calc |3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)|
          ≤ |(3 : ℝ)| + |4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)| := abs_sub _ _
        _ = 3 + 4 * |Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2| := by
            rw [abs_mul]; norm_num
        _ ≤ 3 + 4 * 3 := by gcongr
        _ = 15 := by norm_num
    calc |Real.sin θ - q| * |3 - 4 * (Real.sin θ ^ 2 + Real.sin θ * q + q ^ 2)|
        ≤ (1 / D) * 15 := by
          apply mul_le_mul hq hc (abs_nonneg _)
          exact le_trans (abs_nonneg _) hq
      _ = 15 * (1 / D) := by ring
  calc |3 * Real.sin θ - 4 * Real.sin θ ^ 3 - qnew|
      ≤ |3 * Real.sin θ - 4 * Real.sin θ ^ 3 - (3 * q - 4 * q ^ 3)|
          + |(3 * q - 4 * q ^ 3) - qnew| := abs_sub_le _ _ _
    _ ≤ 15 * (1 / D) + 1 / Rho := add_le_add hfirst hround
    _ ≤ 1 / D' := hcomb

/- Triple-angle step, dyadic/ℕ form of `sin_triple_step`. Running value the signed centre `±cq/Q`,
next value `±cq'/Q'`; `hround1`/`hround2` are the floor characterisation
`s'·Q³ ≤ M·Q' < (s'+1)·Q³` with `M = 3sQ² − 4s³`. -/
theorem sin_triple_step_dyadic (nq : Bool) (cq Q : ℕ) (nq' : Bool) (cq' Q' D D' : ℕ) (θ : ℝ)
    (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q') (hD : Nat.ble 1 D) (hD' : Nat.ble 1 D')
    (hq1a : (numPos nq cq).ble ((numNeg nq cq).add Q))
    (hq1b : (numNeg nq cq).ble ((numPos nq cq).add Q))
    (hround1 : (((numPos nq' cq').mul (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')).ble
      ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))))
    (hround2 : ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))).blt
      ((((numPos nq' cq').mul (Q.pow 3)).add (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')))
    (hcomb : (((Nat.mul 15 Q').add D).mul D').ble (D.mul Q'))
    (hstep : Real.IsNear (Real.sin θ) nq cq Q 1 D) :
    Real.IsNear (Real.sin (3 * θ)) nq' cq' Q' 1 D' := by
  set mp := numPos nq cq with hmp_def
  set mn := numNeg nq cq with hmn_def
  set mp' := numPos nq' cq' with hmp'_def
  set mn' := numNeg nq' cq' with hmn'_def
  rw [Real.IsNear, Nat.cast_one, sfrac_eq_parts nq cq Q, ← hmp_def, ← hmn_def] at hstep
  rw [Real.IsNear, Nat.cast_one, sfrac_eq_parts nq' cq' Q', ← hmp'_def, ← hmn'_def]
  simp only [Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.pow_eq] at hq1a hq1b hround1 hround2 hcomb
  have hQr : (0 : ℝ) < Q := pos_real_of_ble hQ
  have hQ'r : (0 : ℝ) < Q' := pos_real_of_ble hQ'
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hD'r : (0 : ℝ) < D' := pos_real_of_ble hD'
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQr
  have hQ'ne : (Q' : ℝ) ≠ 0 := ne_of_gt hQ'r
  set q : ℝ := ((mp : ℝ) - mn) / Q with hq_def
  set qn : ℝ := ((mp' : ℝ) - mn') / Q' with hqn_def
  -- |q| ≤ 1
  have hq1 : |q| ≤ 1 := by
    rw [hq_def, abs_div, abs_of_pos hQr, div_le_one hQr, abs_le]
    refine ⟨?_, ?_⟩
    · have : (mn : ℝ) ≤ (mp : ℝ) + Q := by exact_mod_cast hq1b
      linarith
    · have : (mp : ℝ) ≤ (mn : ℝ) + Q := by exact_mod_cast hq1a
      linarith
  -- integer floor characterisation
  have C1z : ((mp' : ℤ) * Q ^ 3 + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q')
      ≤ ((3 * mp * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3) := by
    exact_mod_cast hround1
  have C2z : ((3 * (mp : ℤ) * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3)
      < ((mp' : ℤ) * Q ^ 3 + Q ^ 3 + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q') := by
    exact_mod_cast hround2
  set M : ℤ := 3 * ((mp : ℤ) - mn) * Q ^ 2 - 4 * ((mp : ℤ) - mn) ^ 3 with hM_def
  set s' : ℤ := (mp' : ℤ) - mn' with hs'_def
  have hN0 : (0 : ℤ) ≤ M * Q' - s' * Q ^ 3 := by
    have hexp : M * (Q' : ℤ) - s' * Q ^ 3
        = ((3 * (mp : ℤ) * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3)
          - ((mp' : ℤ) * Q ^ 3 + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q') := by
      rw [hM_def, hs'_def]; ring
    rw [hexp]; linarith [C1z]
  have hN1 : M * (Q' : ℤ) - s' * Q ^ 3 < Q ^ 3 := by
    have hexp : M * (Q' : ℤ) - s' * Q ^ 3 - Q ^ 3
        = ((3 * (mp : ℤ) * Q ^ 2 + 12 * mp ^ 2 * mn + 4 * mn ^ 3) * Q' + mn' * Q ^ 3)
          - ((mp' : ℤ) * Q ^ 3 + Q ^ 3
                + (3 * mn * Q ^ 2 + 4 * mp ^ 3 + 12 * mp * mn ^ 2) * Q') := by
      rw [hM_def, hs'_def]; ring
    linarith [C2z, hexp]
  -- |3q − 4q³ − qn| ≤ 1/Q'
  have hround : |(3 * q - 4 * q ^ 3) - qn| ≤ 1 / (Q' : ℝ) := by
    have hval : 3 * q - 4 * q ^ 3 - qn
        = ((M : ℝ) * Q' - (s' : ℝ) * Q ^ 3) / ((Q : ℝ) ^ 3 * Q') := by
      rw [hq_def, hqn_def, hM_def, hs'_def]
      push_cast
      field_simp
    rw [hval]
    have hden : (0 : ℝ) < (Q : ℝ) ^ 3 * Q' := by positivity
    have hN0r : (0 : ℝ) ≤ (M : ℝ) * Q' - (s' : ℝ) * Q ^ 3 := by exact_mod_cast hN0
    have hN1r : (M : ℝ) * Q' - (s' : ℝ) * Q ^ 3 < Q ^ 3 := by exact_mod_cast hN1
    rw [abs_of_nonneg (div_nonneg hN0r (le_of_lt hden)), div_le_div_iff₀ hden hQ'r, one_mul]
    have hmul : ((M : ℝ) * Q' - (s' : ℝ) * Q ^ 3) * Q' ≤ (Q : ℝ) ^ 3 * Q' :=
      mul_le_mul_of_nonneg_right (le_of_lt hN1r) (le_of_lt hQ'r)
    linarith [hmul]
  -- 15/D + 1/Q' ≤ 1/D'
  have hcombr : 15 * (1 / (D : ℝ)) + 1 / (Q' : ℝ) ≤ 1 / (D' : ℝ) := by
    have hlhs : 15 * (1 / (D : ℝ)) + 1 / (Q' : ℝ) = (15 * (Q' : ℝ) + D) / ((D : ℝ) * Q') := by
      field_simp
    rw [hlhs, div_le_div_iff₀ (mul_pos hDr hQ'r) hD'r, one_mul]
    have key : (15 * (Q' : ℝ) + D) * D' ≤ (D : ℝ) * Q' := by exact_mod_cast hcomb
    linarith [key]
  exact sin_triple_step θ q qn (D : ℝ) (Q' : ℝ) (D' : ℝ) hq1 hstep hround hcombr

/- Argument-shaped triple-angle step. With `dj1 = 3·dj`, an enclosure of `sin(↑a/↑dj1)` yields one
of `sin(↑a/↑dj)` (since `3·(a/dj1) = a/dj`). -/
theorem sin_triple_step_arg (a dj dj1 : ℕ) (nq : Bool) (cq Q : ℕ) (nq' : Bool) (cq' Q' D D' : ℕ)
    (hdj1 : dj1.beq (Nat.mul 3 dj))
    (hdj : Nat.ble 1 dj)
    (hQ : Nat.ble 1 Q) (hQ' : Nat.ble 1 Q') (hD : Nat.ble 1 D) (hD' : Nat.ble 1 D')
    (hq1a : (numPos nq cq).ble ((numNeg nq cq).add Q))
    (hq1b : (numNeg nq cq).ble ((numPos nq cq).add Q))
    (hround1 : (((numPos nq' cq').mul (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')).ble
      ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))))
    (hround2 : ((((((Nat.mul 3 (numPos nq cq)).mul (Q.pow 2)).add
        ((Nat.mul 12 ((numPos nq cq).pow 2)).mul (numNeg nq cq))).add
        (Nat.mul 4 ((numNeg nq cq).pow 3))).mul Q').add ((numNeg nq' cq').mul (Q.pow 3))).blt
      ((((numPos nq' cq').mul (Q.pow 3)).add (Q.pow 3)).add
        (((((Nat.mul 3 (numNeg nq cq)).mul (Q.pow 2)).add
          (Nat.mul 4 ((numPos nq cq).pow 3))).add
          ((Nat.mul 12 (numPos nq cq)).mul ((numNeg nq cq).pow 2))).mul Q')))
    (hcomb : (((Nat.mul 15 Q').add D).mul D').ble (D.mul Q'))
    (hstep : Real.IsNear (Real.sin ((a : ℝ) / (dj1 : ℝ))) nq cq Q 1 D) :
    Real.IsNear (Real.sin ((a : ℝ) / (dj : ℝ))) nq' cq' Q' 1 D' := by
  simp only [Nat.beq_eq, Nat.mul_eq] at hdj1
  subst hdj1
  have hdjpos : 0 < dj := pos_of_ble hdj
  have hdjr : (dj : ℝ) ≠ 0 := by exact_mod_cast hdjpos.ne'
  have h3 : (3 : ℝ) * ((a : ℝ) / ((3 * dj : ℕ) : ℝ)) = (a : ℝ) / (dj : ℝ) := by
    push_cast
    field_simp
  rw [Real.IsNear, ← h3, ← Real.IsNear]
  exact sin_triple_step_dyadic nq cq Q nq' cq' Q' D D' ((a : ℝ) / ((3 * dj : ℕ) : ℝ))
    hQ hQ' hD hD' hq1a hq1b hround1 hround2 hcomb hstep

/-! ### The value-generic reduction chain and the `sin`/`cos` quadrant lemmas

The interval + Lipschitz reduction chain over any real `F` with an identity `F = ε·g(x − k·π/2)`;
the `sin` and `cos` quadrant wrappers instantiate it. -/

/- Interval + Lipschitz reduction core: from `F = ε·g r`, `1`-Lipschitz `g` between `r` and the
rational centre `rc`, `|r − rc| ≤ B`, and `|g rc − q| ≤ inner`, conclude `|F − ε·q| ≤ B + inner`. -/
theorem reduce_core_val (F r rc q B inner Dinv : ℝ) (ε : ℝ) (g : ℝ → ℝ)
    (hε : |ε| = 1)
    (hquad : F = ε * g r)
    (hlip : |g r - g rc| ≤ |r - rc|)
    (hB : |r - rc| ≤ B)
    (hinner : |g rc - q| ≤ inner)
    (htot : B + inner ≤ Dinv) :
    |F - ε * q| ≤ Dinv := by
  have h1 : |F - ε * q| ≤ |g r - g rc| + |g rc - q| := by
    rw [hquad]
    calc |ε * g r - ε * q| = |ε| * |g r - q| := by rw [← mul_sub, abs_mul]
      _ = |g r - q| := by rw [hε, one_mul]
      _ ≤ |g r - g rc| + |g rc - q| := abs_sub_le _ _ _
  calc |F - ε * q| ≤ |g r - g rc| + |g rc - q| := h1
    _ ≤ B + inner := add_le_add (hlip.trans hB) hinner
    _ ≤ Dinv := htot

/- Reduction step: combine a `π` certificate `|π − Pr| ≤ 1/E` and the in-range certificate
`|g rcv − val| ≤ 1/Dp` into `|F − ε·val| ≤ 1/D`, for `rcv = x − k·(Pr/2)`. -/
theorem reduce_step_val (F x r rcv Pr val : ℝ) (k E Dp D : ℕ) (ε : ℝ) (g : ℝ → ℝ)
    (hε : |ε| = 1)
    (hquad : F = ε * g r)
    (hr : r = x - (k : ℝ) * (π / 2))
    (hlip : |g r - g rcv| ≤ |r - rcv|)
    (hrc : rcv = x - (k : ℝ) * (Pr / 2))
    (hpi : |Real.pi - Pr| ≤ 1 / (E : ℝ))
    (hinner : |g rcv - val| ≤ 1 / (Dp : ℝ))
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((k.mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble ((Nat.mul 2 E).mul Dp)) :
    |F - ε * val| ≤ 1 / (D : ℝ) := by
  simp only [Nat.ble_eq, Nat.add_eq, Nat.mul_eq] at htot
  have hEr : (0 : ℝ) < E := pos_real_of_ble hE
  have hDpr : (0 : ℝ) < Dp := pos_real_of_ble hDp
  have hDr : (0 : ℝ) < D := pos_real_of_ble hD
  have hB : |r - rcv| ≤ (k : ℝ) / (2 * E) := by
    rw [hr, hrc]
    have e : (x - (k : ℝ) * (π / 2)) - (x - (k : ℝ) * (Pr / 2)) = (k : ℝ) * (Pr / 2 - π / 2) := by
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    have hhalf : |Pr / 2 - π / 2| ≤ 1 / (2 * E) := by
      have e2 : Pr / 2 - π / 2 = -(Real.pi - Pr) / 2 := by ring
      rw [e2, abs_div, abs_neg, abs_two]
      calc |Real.pi - Pr| / 2 ≤ (1 / (E : ℝ)) / 2 := by gcongr
        _ = 1 / (2 * E) := by ring
    calc (k : ℝ) * |Pr / 2 - π / 2| ≤ (k : ℝ) * (1 / (2 * E)) := by gcongr
      _ = (k : ℝ) / (2 * E) := by ring
  have htotR : (k : ℝ) / (2 * E) + 1 / (Dp : ℝ) ≤ 1 / (D : ℝ) := by
    have hc : ((k * D * Dp + 2 * E * D : ℕ) : ℝ) ≤ ((2 * E * Dp : ℕ) : ℝ) := by exact_mod_cast htot
    push_cast at hc
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hc, hEr, hDpr, hDr]
  exact reduce_core_val F r rcv val ((k : ℝ) / (2 * E)) (1 / Dp) (1 / D) ε g hε hquad
    hlip hB hinner htotR

/- Master quadrant lemma over any real `F`: turn an in-range enclosure of `g rcv` at
`rcv = x − k·((Pc/PQ)/2)` into an enclosure of `F`. The `sin`/`cos` wrappers instantiate it. -/
theorem reduce_quad_val (F x rcv : ℝ) (g : ℝ → ℝ) (ε : ℝ) (Pc PQ : ℕ) (ineg oneg : Bool)
    (icn Qd k E Dp D : ℕ)
    (hε : |ε| = 1)
    (hquad : F = ε * g (x - (k : ℝ) * (π / 2)))
    (hlip : ∀ a b, |g a - g b| ≤ |a - b|)
    (hsign : sfrac oneg icn Qd = ε * sfrac ineg icn Qd)
    (hrc : rcv = x - (k : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (g rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((k.mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear F oneg icn Qd 1 D := by
  rw [Real.IsNear, sfrac_false_div, Nat.cast_one] at hpi
  rw [← sfrac_false_div Pc PQ] at hpi
  rw [Real.IsNear, Nat.cast_one] at hinner
  rw [Real.IsNear, Nat.cast_one, hsign]
  exact reduce_step_val F x (x - (k : ℝ) * (π / 2)) rcv (sfrac false Pc PQ)
    (sfrac ineg icn Qd) k E Dp D ε g hε hquad rfl (hlip _ _) hrc hpi hinner hE hDp hD htot

/- `k ≡ 0 (mod 4)` quadrant for `cos`: `cos (r + 4q·(π/2)) = cos r`. -/
theorem cos_quad0 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ)) * (π / 2)) = Real.cos r := by
  have e : r + (4 * (q : ℝ)) * (π / 2) = r + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi]

/- `k ≡ 1 (mod 4)` quadrant for `cos`: `cos (r + (4q+1)·(π/2)) = −sin r`. -/
theorem cos_quad1 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 1) * (π / 2)) = -Real.sin r := by
  have e : r + (4 * (q : ℝ) + 1) * (π / 2) = (r + π / 2) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi_div_two]

/- `k ≡ 2 (mod 4)` quadrant for `cos`: `cos (r + (4q+2)·(π/2)) = −cos r`. -/
theorem cos_quad2 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 2) * (π / 2)) = -Real.cos r := by
  have e : r + (4 * (q : ℝ) + 2) * (π / 2) = (r + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi]

/- `k ≡ 3 (mod 4)` quadrant for `cos`: `cos (r + (4q+3)·(π/2)) = sin r`. -/
theorem cos_quad3 (r : ℝ) (q : ℤ) :
    Real.cos (r + (4 * (q : ℝ) + 3) * (π / 2)) = Real.sin r := by
  have e : r + (4 * (q : ℝ) + 3) * (π / 2) = ((r + π / 2) + π) + (q : ℝ) * (2 * π) := by ring
  rw [e, cos_add_int_mul_two_pi, cos_add_pi, cos_add_pi_div_two, neg_neg]

/-! ### The `sin` and `cos` reduction lemmas -/

/- Quadrant `k ≡ 0`: in-range `g = sin`, sign `ε = +1`. -/
theorem sin_reduce0 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : ((((Nat.mul 4 qq).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.sin 1 Pc PQ ineg ineg icn Qd (4 * qq) E Dp D abs_one
    (by rw [one_mul, ← sin_quad0 (x - ((4 * qq : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le (one_mul _).symm hrc hpi hinner hE hDp hD htot

/- Quadrant `k ≡ 1`: in-range `g = cos`, sign `ε = +1`. -/
theorem sin_reduce1 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).succ).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.cos 1 Pc PQ ineg ineg icn Qd (4 * qq + 1) E Dp D abs_one
    (by rw [one_mul, ← sin_quad1 (x - ((4 * qq + 1 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le (one_mul _).symm hrc hpi hinner hE hDp hD htot

/- Quadrant `k ≡ 2`: in-range `g = sin`, sign `ε = −1` (the in-range centre's sign flips). -/
theorem sin_reduce2 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 2).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.sin (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 2) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← sin_quad2 (x - ((4 * qq + 2 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot

/- Quadrant `k ≡ 3`: in-range `g = cos`, sign `ε = −1` (the in-range centre's sign flips). -/
theorem sin_reduce3 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 3).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.sin x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.sin x) x rcv Real.cos (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 3) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← sin_quad3 (x - ((4 * qq + 3 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot

/- Quadrant `k ≡ 0` for `cos`: in-range `g = cos`, sign `ε = +1`. -/
theorem cos_reduce0 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : ((((Nat.mul 4 qq).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.cos 1 Pc PQ ineg ineg icn Qd (4 * qq) E Dp D abs_one
    (by rw [one_mul, ← cos_quad0 (x - ((4 * qq : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_cos_sub_cos_le (one_mul _).symm hrc hpi hinner hE hDp hD htot

/- Quadrant `k ≡ 1` for `cos`: in-range `g = sin`, sign `ε = −1`. -/
theorem cos_reduce1 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).succ).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.sin (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 1) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← cos_quad1 (x - ((4 * qq + 1 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 2; push_cast; ring)
    Real.abs_sin_sub_sin_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot

/- Quadrant `k ≡ 2` for `cos`: in-range `g = cos`, sign `ε = −1`. -/
theorem cos_reduce2 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.cos rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 2).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) (!ineg) icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.cos (-1) Pc PQ ineg (!ineg) icn Qd (4 * qq + 2) E Dp D
    ((abs_neg 1).trans abs_one)
    (by rw [neg_one_mul, ← cos_quad2 (x - ((4 * qq + 2 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 2; push_cast; ring)
    Real.abs_cos_sub_cos_le ((sfrac_not ineg icn Qd).trans (neg_one_mul _).symm)
    hrc hpi hinner hE hDp hD htot

/- Quadrant `k ≡ 3` for `cos`: in-range `g = sin`, sign `ε = +1`. -/
theorem cos_reduce3 (x rcv : ℝ) (Pc PQ : ℕ) (ineg : Bool) (icn Qd qq E Dp D : ℕ)
    (hrc : rcv = x - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2))
    (hpi : Real.IsNear Real.pi false Pc PQ 1 E)
    (hinner : Real.IsNear (Real.sin rcv) ineg icn Qd 1 Dp)
    (hE : Nat.ble 1 E) (hDp : Nat.ble 1 Dp) (hD : Nat.ble 1 D)
    (htot : (((((Nat.mul 4 qq).add 3).mul D).mul Dp).add ((Nat.mul 2 E).mul D)).ble
      ((Nat.mul 2 E).mul Dp)) :
    Real.IsNear (Real.cos x) ineg icn Qd 1 D :=
  reduce_quad_val (Real.cos x) x rcv Real.sin 1 Pc PQ ineg ineg icn Qd (4 * qq + 3) E Dp D
    abs_one
    (by rw [one_mul, ← cos_quad3 (x - ((4 * qq + 3 : ℕ) : ℝ) * (π / 2)) (qq : ℤ)]
        congr 1; push_cast; ring)
    Real.abs_sin_sub_sin_le (one_mul _).symm hrc hpi hinner hE hDp hD htot

/- The rational centre identity: with `v = 2·b·PQ` and the `ℕ` link `2·a·PQ = u + k·(b·Pc)`, the
rational `u/v` equals `a/b − k·(Pr/2)` for `Pr = sfrac false Pc PQ`. -/
theorem sin_reduce_arg_pos_rat (a b Pc PQ k u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add (k.mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ)) - (k : ℝ) * (sfrac false Pc PQ / 2) := by
  simp only [Nat.beq_eq, Nat.add_eq, Nat.mul_eq] at hlink hv
  subst hv
  rw [sfrac_false_div]
  have hQr : (0 : ℝ) < PQ := pos_real_of_ble hQ
  have hbr : (0 : ℝ) < b := pos_real_of_ble hb
  have hlinkR : (2 * a * PQ : ℝ) = (u + k * (b * Pc) : ℝ) := by exact_mod_cast hlink
  push_cast
  field_simp
  ring_nf
  linarith [hlinkR]

/-! ### Centre identities in each quadrant's own multiplier shape

`sin_reduce_arg_pos_rat` states the multiplier as a single `k`, while the quadrant lemmas state
it as `4·qq + j` for their own `j`. Supplying the former for the latter's hypothesis leaves the
kernel to reconcile the two shapes at every reduction. These four state the identity in the
shape each quadrant expects, so the hypothesis matches without reconciliation. -/

theorem sin_reduce_arg_pos_rat_q0 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.mul 4 qq).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ)) - ((4 * qq : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq) u v hlink hv hQ hb

theorem sin_reduce_arg_pos_rat_q1 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 1).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 1 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 1) u v hlink hv hQ hb

theorem sin_reduce_arg_pos_rat_q2 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 2).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 2 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 2) u v hlink hv hQ hb

theorem sin_reduce_arg_pos_rat_q3 (a b Pc PQ qq u v : ℕ)
    (hlink : ((Nat.mul 2 a).mul PQ).beq (u.add ((Nat.add (Nat.mul 4 qq) 3).mul (b.mul Pc))))
    (hv : ((Nat.mul 2 b).mul PQ).beq v) (hQ : Nat.ble 1 PQ) (hb : Nat.ble 1 b) :
    ((u : ℝ) / (v : ℝ)) = ((a : ℝ) / (b : ℝ))
      - ((4 * qq + 3 : ℕ) : ℝ) * (sfrac false Pc PQ / 2) := by
  simpa using sin_reduce_arg_pos_rat a b Pc PQ (4 * qq + 3) u v hlink hv hQ hb

end BSN

end

end CertificatePort149
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Enclosure/Complex.lean -/
section CertificatePort150


/-!
# Complex rectangle enclosures: the `Complex.IsNear` predicate

A complex `z` is enclosed by a rectangle: independent `IsNear` enclosures of `z.re` and `z.im`. All
arithmetic on `ℂ` reduces to the real combinators applied componentwise.
-/
section


namespace Enclosure

/- `z` lies in the rectangle whose real and imaginary sides are the two `IsNear` enclosures. -/
def Complex.IsNear (z : ℂ)
    (reNeg : Bool) (reCn reCd reRn reRd : ℕ)
    (imNeg : Bool) (imCn imCd imRn imRd : ℕ) : Prop :=
  Real.IsNear z.re reNeg reCn reCd reRn reRd ∧
  Real.IsNear z.im imNeg imCn imCd imRn imRd

/- Real-part accessor. -/
theorem Complex.IsNear.re_isNear {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Real.IsNear z.re reNeg reCn reCd reRn reRd := h.1

/- Imaginary-part accessor; see `Complex.IsNear.re_isNear`. -/
theorem Complex.IsNear.im_isNear {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Real.IsNear z.im imNeg imCn imCd imRn imRd := h.2

/- Build a rectangle enclosure of the explicit complex number `⟨re, im⟩` from independent
enclosures of its real and imaginary parts. -/
theorem Complex.IsNear.mk {re im : ℝ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear re reNeg reCn reCd reRn reRd)
    (him : Real.IsNear im imNeg imCn imCd imRn imRd) :
    Complex.IsNear ⟨re, im⟩ reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := ⟨hre, him⟩

/- Negation. `−z` flips the sign flag of each component; magnitudes and radii are unchanged. -/
theorem Complex.IsNear.neg {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (h : Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Complex.IsNear (-z) (!reNeg) reCn reCd reRn reRd (!imNeg) imCn imCd imRn imRd := by
  obtain ⟨hre, him⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Complex.neg_re]; exact hre.neg
  · rw [Complex.neg_im]; exact him.neg

/- Addition. From `IsNear` enclosures of the componentwise sums `z.re+w.re` and `z.im+w.im`,
conclude the rectangle enclosure of `z+w`. -/
theorem Complex.IsNear.add {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re + w.re) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.im + w.im) imN imCn imCd imRn imRd) :
    Complex.IsNear (z + w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.add_re]; exact hre
  · rw [Complex.add_im]; exact him

/- Subtraction. From `IsNear` enclosures of the componentwise differences `z.re−w.re` and
`z.im−w.im`, conclude the rectangle enclosure of `z−w`. -/
theorem Complex.IsNear.sub {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re - w.re) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.im - w.im) imN imCn imCd imRn imRd) :
    Complex.IsNear (z - w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.sub_re]; exact hre
  · rw [Complex.sub_im]; exact him

/- Multiplication. From `IsNear` enclosures of the two real combinations
`z.re·w.re − z.im·w.im` and `z.re·w.im + z.im·w.re`, conclude the rectangle enclosure of `z·w`. -/
theorem Complex.IsNear.mul {z w : ℂ}
    {reN : Bool} {reCn reCd reRn reRd : ℕ} {imN : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear (z.re * w.re - z.im * w.im) reN reCn reCd reRn reRd)
    (him : Real.IsNear (z.re * w.im + z.im * w.re) imN imCn imCd imRn imRd) :
    Complex.IsNear (z * w) reN reCn reCd reRn reRd imN imCn imCd imRn imRd := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re]; exact hre
  · rw [Complex.mul_im]; exact him

/-! ### Paired-input combine lemmas

The `*LitP` variants consume the paired proofs `h1`/`h2` directly, carrying both components'
literal-output conditions in one application. Sign conditions use the raw `Bool.rec` forms
`numPosC`/`numNegC`. -/

/- `numPos` in raw `Bool.rec` form (kernel fast path, no `cond`/`Bool.casesOn` wrappers): same
value. -/
def numPosC (neg : Bool) (cn : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) cn 0 neg

/- `numNeg` in raw `Bool.rec` form; see `numPosC`. -/
def numNegC (neg : Bool) (cn : ℕ) : ℕ := @Bool.rec (fun _ => ℕ) 0 cn neg

theorem numPosC_eq (neg : Bool) (cn : ℕ) : numPosC neg cn = numPos neg cn := by
  cases neg <;> rfl

theorem numNegC_eq (neg : Bool) (cn : ℕ) : numNegC neg cn = numNeg neg cn := by
  cases neg <;> rfl

/- Paired addition with literal outputs: `Real.IsNear.addLit` on both components, concluded
through `Complex.IsNear.add`. Suffix `r`/`i` = real/imaginary component. -/
theorem Complex.IsNear.addLitP {z w : ℂ}
    {nxr : Bool} {cnxr cdxr rnxr rdxr : ℕ} {nxi : Bool} {cnxi cdxi rnxi rdxi : ℕ}
    {nyr : Bool} {cnyr cdyr rnyr rdyr : ℕ} {nyi : Bool} {cnyi cdyi rnyi rdyi : ℕ}
    {nRr : Bool} {cnRr cnRr' cdRr' rnRr' rdRr' : ℕ}
    {nRi : Bool} {cnRi cnRi' cdRi' rnRi' rdRi' : ℕ}
    (h1 : Complex.IsNear z nxr cnxr cdxr rnxr rdxr nxi cnxi cdxi rnxi rdxi)
    (h2 : Complex.IsNear w nyr cnyr cdyr rnyr rdyr nyi cnyi cdyi rnyi rdyi)
    (hcdxr : Nat.ble (nat_lit 1) cdxr) (hcdyr : Nat.ble (nat_lit 1) cdyr)
    (hrdxr : Nat.ble (nat_lit 1) rdxr) (hrdyr : Nat.ble (nat_lit 1) rdyr)
    (hnumr : Nat.beq
      (((numPosC nRr cnRr).add ((numNegC nxr cnxr).mul cdyr)).add
        ((numNegC nyr cnyr).mul cdxr))
      (((numNegC nRr cnRr).add ((numPosC nxr cnxr).mul cdyr)).add
        ((numPosC nyr cnyr).mul cdxr)))
    (hcdRr' : Nat.ble (nat_lit 1) cdRr') (hrdRr' : Nat.ble (nat_lit 1) rdRr')
    (hcr : Nat.beq (cnRr.mul cdRr') (cnRr'.mul (cdxr.mul cdyr)))
    (hrr : Nat.ble (((rnxr.mul rdyr).add (rnyr.mul rdxr)).mul rdRr')
      (rnRr'.mul (rdxr.mul rdyr)))
    (hcdxi : Nat.ble (nat_lit 1) cdxi) (hcdyi : Nat.ble (nat_lit 1) cdyi)
    (hrdxi : Nat.ble (nat_lit 1) rdxi) (hrdyi : Nat.ble (nat_lit 1) rdyi)
    (hnumi : Nat.beq
      (((numPosC nRi cnRi).add ((numNegC nxi cnxi).mul cdyi)).add
        ((numNegC nyi cnyi).mul cdxi))
      (((numNegC nRi cnRi).add ((numPosC nxi cnxi).mul cdyi)).add
        ((numPosC nyi cnyi).mul cdxi)))
    (hcdRi' : Nat.ble (nat_lit 1) cdRi') (hrdRi' : Nat.ble (nat_lit 1) rdRi')
    (hci : Nat.beq (cnRi.mul cdRi') (cnRi'.mul (cdxi.mul cdyi)))
    (hri : Nat.ble (((rnxi.mul rdyi).add (rnyi.mul rdxi)).mul rdRi')
      (rnRi'.mul (rdxi.mul rdyi))) :
    Complex.IsNear (z + w) nRr cnRr' cdRr' rnRr' rdRr' nRi cnRi' cdRi' rnRi' rdRi' := by
  simp only [numPosC_eq, numNegC_eq] at hnumr hnumi
  exact Complex.IsNear.add
    (Real.IsNear.addLit h1.1 h2.1 hcdxr hcdyr hrdxr hrdyr hnumr hcdRr' hrdRr' hcr hrr)
    (Real.IsNear.addLit h1.2 h2.2 hcdxi hcdyi hrdxi hrdyi hnumi hcdRi' hrdRi' hci hri)

/- Paired subtraction with literal outputs; see `Complex.IsNear.addLitP`. -/
theorem Complex.IsNear.subLitP {z w : ℂ}
    {nxr : Bool} {cnxr cdxr rnxr rdxr : ℕ} {nxi : Bool} {cnxi cdxi rnxi rdxi : ℕ}
    {nyr : Bool} {cnyr cdyr rnyr rdyr : ℕ} {nyi : Bool} {cnyi cdyi rnyi rdyi : ℕ}
    {nRr : Bool} {cnRr cnRr' cdRr' rnRr' rdRr' : ℕ}
    {nRi : Bool} {cnRi cnRi' cdRi' rnRi' rdRi' : ℕ}
    (h1 : Complex.IsNear z nxr cnxr cdxr rnxr rdxr nxi cnxi cdxi rnxi rdxi)
    (h2 : Complex.IsNear w nyr cnyr cdyr rnyr rdyr nyi cnyi cdyi rnyi rdyi)
    (hcdxr : Nat.ble (nat_lit 1) cdxr) (hcdyr : Nat.ble (nat_lit 1) cdyr)
    (hrdxr : Nat.ble (nat_lit 1) rdxr) (hrdyr : Nat.ble (nat_lit 1) rdyr)
    (hnumr : Nat.beq
      (((numPosC nRr cnRr).add ((numNegC nxr cnxr).mul cdyr)).add
        ((numPosC nyr cnyr).mul cdxr))
      (((numNegC nRr cnRr).add ((numPosC nxr cnxr).mul cdyr)).add
        ((numNegC nyr cnyr).mul cdxr)))
    (hcdRr' : Nat.ble (nat_lit 1) cdRr') (hrdRr' : Nat.ble (nat_lit 1) rdRr')
    (hcr : Nat.beq (cnRr.mul cdRr') (cnRr'.mul (cdxr.mul cdyr)))
    (hrr : Nat.ble (((rnxr.mul rdyr).add (rnyr.mul rdxr)).mul rdRr')
      (rnRr'.mul (rdxr.mul rdyr)))
    (hcdxi : Nat.ble (nat_lit 1) cdxi) (hcdyi : Nat.ble (nat_lit 1) cdyi)
    (hrdxi : Nat.ble (nat_lit 1) rdxi) (hrdyi : Nat.ble (nat_lit 1) rdyi)
    (hnumi : Nat.beq
      (((numPosC nRi cnRi).add ((numNegC nxi cnxi).mul cdyi)).add
        ((numPosC nyi cnyi).mul cdxi))
      (((numNegC nRi cnRi).add ((numPosC nxi cnxi).mul cdyi)).add
        ((numNegC nyi cnyi).mul cdxi)))
    (hcdRi' : Nat.ble (nat_lit 1) cdRi') (hrdRi' : Nat.ble (nat_lit 1) rdRi')
    (hci : Nat.beq (cnRi.mul cdRi') (cnRi'.mul (cdxi.mul cdyi)))
    (hri : Nat.ble (((rnxi.mul rdyi).add (rnyi.mul rdxi)).mul rdRi')
      (rnRi'.mul (rdxi.mul rdyi))) :
    Complex.IsNear (z - w) nRr cnRr' cdRr' rnRr' rdRr' nRi cnRi' cdRi' rnRi' rdRi' := by
  simp only [numPosC_eq, numNegC_eq] at hnumr hnumi
  refine Complex.IsNear.sub
    (Real.IsNear.subLit h1.1 h2.1 hcdxr hcdyr hrdxr hrdyr ?_ hcdRr' hrdRr' hcr hrr)
    (Real.IsNear.subLit h1.2 h2.2 hcdxi hcdyi hrdxi hrdyi ?_ hcdRi' hrdRi' hci hri)
  · cases nyr <;> simpa [numPos, numNeg] using hnumr
  · cases nyi <;> simpa [numPos, numNeg] using hnumi

/- Rectangle recentre: `Real.IsNear.recentre` on both components in one application. -/
theorem Complex.IsNear.recentre2 {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {rCn' rCd' rRn' rRd' iCn' iCd' iRn' iRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hrcd : Nat.ble (nat_lit 1) rCd) (hrcd' : Nat.ble (nat_lit 1) rCd') (hrrd : Nat.ble
          (nat_lit 1) rRd)
    (hrrd' : Nat.ble (nat_lit 1) rRd')
    (hrfloor : Nat.ble (rCn'.mul rCd) (rCn.mul rCd'))
    (hrrad : Nat.ble
      (((rRn.mul (rCd.mul rCd')).add (((rCn.mul rCd').sub (rCn'.mul rCd)).mul rRd)).mul rRd')
      (rRn'.mul (rRd.mul (rCd.mul rCd'))))
    (hicd : Nat.ble (nat_lit 1) iCd) (hicd' : Nat.ble (nat_lit 1) iCd') (hird : Nat.ble
          (nat_lit 1) iRd)
    (hird' : Nat.ble (nat_lit 1) iRd')
    (hifloor : Nat.ble (iCn'.mul iCd) (iCn.mul iCd'))
    (hirad : Nat.ble
      (((iRn.mul (iCd.mul iCd')).add (((iCn.mul iCd').sub (iCn'.mul iCd)).mul iRd)).mul iRd')
      (iRn'.mul (iRd.mul (iCd.mul iCd')))) :
    Complex.IsNear z rN rCn' rCd' rRn' rRd' iN iCn' iCd' iRn' iRd' :=
  ⟨h.1.recentre hrcd hrcd' hrrd hrrd' hrfloor hrrad,
   h.2.recentre hicd hicd' hird hird' hifloor hirad⟩

/- One-sided rectangle recentre: round only the real component; imaginary passes through. -/
theorem Complex.IsNear.recentreRe {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {rCn' rCd' rRn' rRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hrcd : Nat.ble (nat_lit 1) rCd) (hrcd' : Nat.ble (nat_lit 1) rCd') (hrrd : Nat.ble
          (nat_lit 1) rRd)
    (hrrd' : Nat.ble (nat_lit 1) rRd')
    (hrfloor : Nat.ble (rCn'.mul rCd) (rCn.mul rCd'))
    (hrrad : Nat.ble
      (((rRn.mul (rCd.mul rCd')).add (((rCn.mul rCd').sub (rCn'.mul rCd)).mul rRd)).mul rRd')
      (rRn'.mul (rRd.mul (rCd.mul rCd')))) :
    Complex.IsNear z rN rCn' rCd' rRn' rRd' iN iCn iCd iRn iRd :=
  ⟨h.1.recentre hrcd hrcd' hrrd hrrd' hrfloor hrrad, h.2⟩

/- One-sided rectangle recentre for the IMAGINARY component; see `recentreRe`. -/
theorem Complex.IsNear.recentreIm {z : ℂ}
    {rN : Bool} {rCn rCd rRn rRd : ℕ} {iN : Bool} {iCn iCd iRn iRd : ℕ}
    {iCn' iCd' iRn' iRd' : ℕ}
    (h : Complex.IsNear z rN rCn rCd rRn rRd iN iCn iCd iRn iRd)
    (hicd : Nat.ble (nat_lit 1) iCd) (hicd' : Nat.ble (nat_lit 1) iCd') (hird : Nat.ble
          (nat_lit 1) iRd)
    (hird' : Nat.ble (nat_lit 1) iRd')
    (hifloor : Nat.ble (iCn'.mul iCd) (iCn.mul iCd'))
    (hirad : Nat.ble
      (((iRn.mul (iCd.mul iCd')).add (((iCn.mul iCd').sub (iCn'.mul iCd)).mul iRd)).mul iRd')
      (iRn'.mul (iRd.mul (iCd.mul iCd')))) :
    Complex.IsNear z rN rCn rCd rRn rRd iN iCn' iCd' iRn' iRd' :=
  ⟨h.1, h.2.recentre hicd hicd' hird hird' hifloor hirad⟩

/- Rectangle enclosure of `z` from enclosures of `z.re`, `z.im`; the projection form of `mk`. -/
theorem Complex.IsNear.of_parts {z : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (hre : Real.IsNear z.re reNeg reCn reCd reRn reRd)
    (him : Real.IsNear z.im imNeg imCn imCd imRn imRd) :
    Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := ⟨hre, him⟩

/- Transport a rectangle enclosure along an equality of the enclosed complex value. -/
theorem Complex.IsNear.of_eq {z w : ℂ}
    {reNeg : Bool} {reCn reCd reRn reRd : ℕ} {imNeg : Bool} {imCn imCd imRn imRd : ℕ}
    (he : z = w) (h : Complex.IsNear w reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd) :
    Complex.IsNear z reNeg reCn reCd reRn reRd imNeg imCn imCd imRn imRd := by
  rw [he]; exact h

/- The real part of a complex inverse as a product: `(z⁻¹).re = z.re · (normSq z)⁻¹`. -/
theorem Complex.inv_re_eq_mul (z : ℂ) : (z⁻¹).re = z.re * (Complex.normSq z)⁻¹ := by
  rw [Complex.inv_re, div_eq_mul_inv]

/- The imaginary part of a complex inverse as a product: `(z⁻¹).im = (−z.im) · (normSq z)⁻¹`. -/
theorem Complex.inv_im_eq_mul (z : ℂ) : (z⁻¹).im = -z.im * (Complex.normSq z)⁻¹ := by
  rw [Complex.inv_im, div_eq_mul_inv, neg_mul]

/- `normSq z = z.re·z.re + z.im·z.im`, the form the real combinators assemble. -/
theorem Complex.normSq_eq_mul_add_mul (z : ℂ) :
    Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z

/-! ### Complex finite-sum splitting (the mirror of the real lemmas in `Sums.lean`) -/

/- Split a complex `Finset.Ico` sum at a midpoint `m ∈ [a,b]`. -/
theorem Complex.arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  have h1 : -(Real.pi / 2) < z.arg := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz)
  have h2 : z.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [← Complex.tan_arg z, Real.arctan_tan h1 h2]

/- Real part of `Complex.log ⟨p/q, r/q⟩` as `½·log(N/M)` with `N = p²+r²`, `M = q²`. -/
theorem clog_re_eq (p r q N M : ℕ) (hq : Nat.ble (nat_lit 1) q = true)
    (hN : Nat.beq N ((p.mul p).add (r.mul r)) = true) (hM : Nat.beq M (q.mul q) = true) :
    (Complex.log ⟨sfrac false p q, sfrac false r q⟩).re
      = sfrac false (nat_lit 1) (nat_lit 2) * Real.log (sfrac false N M) := by
  obtain rfl := Nat.eq_of_beq_eq_true hN
  obtain rfl := Nat.eq_of_beq_eq_true hM
  have hqR : (0 : ℝ) < q := pos_real_of_ble hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  have hnorm : Complex.normSq ⟨sfrac false p q, sfrac false r q⟩
      = sfrac false ((p.mul p).add (r.mul r)) (q.mul q) := by
    rw [Complex.normSq_mk]
    simp only [sfrac_false_div, Nat.mul_eq, Nat.add_eq]
    push_cast
    field_simp
  rw [Complex.log_re, Complex.norm_def, hnorm, sfrac_false_div, sfrac_false_div,
    Real.log_sqrt (by positivity)]
  push_cast
  ring

/- Imaginary part of `Complex.log ⟨p/q, r/q⟩` (`p, q > 0`) as `arctan(r/p)` (the `q` cancels). -/
theorem clog_im_eq (p r q : ℕ) (hp : Nat.ble (nat_lit 1) p
      = true) (hq : Nat.ble (nat_lit 1) q = true) :
    (Complex.log ⟨sfrac false p q, sfrac false r q⟩).im = Real.arctan ((r : ℝ) / p) := by
  have hpR : (0 : ℝ) < p := pos_real_of_ble hp
  have hqR : (0 : ℝ) < q := pos_real_of_ble hq
  have hproj_re : (⟨sfrac false p q, sfrac false r q⟩ : ℂ).re = sfrac false p q := rfl
  have hproj_im : (⟨sfrac false p q, sfrac false r q⟩ : ℂ).im = sfrac false r q := rfl
  have hre : (0 : ℝ) < (⟨sfrac false p q, sfrac false r q⟩ : ℂ).re := by
    rw [hproj_re, sfrac_false_div]
    exact div_pos hpR hqR
  rw [Complex.log_im, Complex.arg_eq_arctan_of_re_pos hre, hproj_re, hproj_im,
    sfrac_false_div, sfrac_false_div, div_div_div_cancel_right₀ hqR.ne']

end Enclosure

end

end CertificatePort150
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/SpecialFunctions/GammaFactor.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/Complex/ArgVariation.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Theta.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Gamma/HalfPlane.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannXi.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Gamma/LogGammaBranch.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/SpecialFunctions/Arctan.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Summation/Basic.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Summation/Complex.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Gamma/Stirling.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Gamma/DigammaStirling.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Gamma/Growth.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Gamma/LogGammaStirling.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Gamma/LogGammaEM.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/EulerMaclaurin/Basic.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/EulerMaclaurin/Continuation.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Zeros/HardyZ.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/Calculus/IteratedDeriv.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/SpecialFunctions/Gaussian.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/Complex/SinExp.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Line.lean -/
section CertificatePort90
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The slanted Riemann–Siegel contour

The Riemann–Siegel kernel `Zeta.RiemannSiegel.kernel` is integrated along the line of slope one
`L(a)(w) = (a + w) + i w` through a point `a` of the real axis (`riemann_siegel.tex`,
`sec:rs_contour`). Two features of that contour drive everything downstream.

*Rotation.* Multiplying by `e^{iπ/4}` turns `L(a)` into the **vertical** line `Re z = a/√2`. That
is what lets the contour-shift argument use honest axis-parallel rectangles, and what puts the
contour in a half-plane on which Mathlib's principal branch of `x ↦ x^{-s}` may be used after
rotation.

*Half-integer crossings.* When `a` is a half-integer the denominator `2 sin(πx)` of the kernel is
bounded below by `√2` all along `L(a)`, uniformly in `w`: near the real axis because `a + w` stays
within `¼` of a half-integer, and away from it because `sinh` grows.

The uniform bound `√2` is all the order-zero theory uses, but the sharp first-order estimates need
the growth itself: away from the real axis the denominator is not merely bounded but exponentially
large, and that is the difference between an outer tail that is negligible and one that is not
(`riemann_siegel.tex`, `lem:rs_sin_lower_sharp`). That bound needs no hypothesis on `a`; unlike the
uniform one it is vacuous, rather than false, at `w = 0`.

## Main results

* `Zeta.RiemannSiegel.line`: the contour `L(a)`;
* `Zeta.RiemannSiegel.line_ne_zero`: `L(a)` misses the origin for `a ≠ 0`;
* `Zeta.RiemannSiegel.line_zero`: `L(0)(w) = √2 w e^{iπ/4}`, the two Hankel rays;
* `Zeta.RiemannSiegel.continuous_line`: `L(a)` is continuous;
* `Zeta.RiemannSiegel.re_exp_pi_div_four_mul_I_mul_line`,
  `Zeta.RiemannSiegel.re_exp_pi_div_four_mul_I_mul_ofReal`: `Re (e^{iπ/4} L(a)(w)) = a/√2`;
* `Zeta.RiemannSiegel.norm_line_ge`, `Zeta.RiemannSiegel.norm_line_le`:
  `a/√2 ≤ |L(a)(w)| ≤ a + 2|w|`;
* `Zeta.RiemannSiegel.norm_line_sub_ofReal_le`: `|L(a)(w) − p| ≤ |a − p| + √2 |w|` for real `p`;
* `Zeta.RiemannSiegel.norm_line_sub_ofReal_sq`, `Zeta.RiemannSiegel.norm_line_sub_ofReal_le'`,
  `Zeta.RiemannSiegel.norm_line_sub_ofReal_ge`: the same distance in terms of the centred
  parameter `w + (a − p)/2`, exactly and as two-sided bounds;
* `Zeta.RiemannSiegel.sinh_le_norm_sin_pi_mul_line`,
  `Zeta.RiemannSiegel.abs_sin_le_norm_sin_pi_mul_line`: the two coordinatewise lower bounds
  `|sin (π L(a)(w))| ≥ sinh (π|w|)` and `≥ |sin (π (a + w))|`, for arbitrary `a`;
* `Zeta.RiemannSiegel.norm_sin_pi_mul_line_ge`, `Zeta.RiemannSiegel.sin_pi_mul_line_ne_zero`:
  `|sin (π L(a)(w))| ≥ √2/2`, and in particular `sin (π L(a)(w)) ≠ 0`, for `a` a half-integer;
* `Zeta.RiemannSiegel.norm_sin_pi_mul_line_ge_min`: `|sin (π L(a)(w))| ≥ min (½, |L(a)(w)|)` for
  `0 ≤ a ≤ ½`, a bound that survives the degeneration `a → 0`;
* `Zeta.RiemannSiegel.mul_exp_le_norm_sin_pi_mul_line`: the exponential lower bound
  `|sin (π L(a)(w))| ≥ (99/200) e^{π|w|}` for `|w| ≥ 1`, for arbitrary `a`.
-/
section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/- The **slanted Riemann–Siegel contour** `L(a)(w) = (a + w) + i w`: the line of slope one
through `a`, traversed in the direction `1 + i`. -/
noncomputable def line (a w : ℝ) : ℂ := (a + w : ℝ) + (w : ℝ) * I

@[simp]
theorem line_re (a w : ℝ) : (line a w).re = a + w := by simp [line]

@[simp]
theorem line_im (a w : ℝ) : (line a w).im = w := by simp [line]

/- **The slanted contour misses the origin** as soon as it does not pass through it. -/
@[fun_prop]
theorem continuous_line (a : ℝ) : Continuous (line a) := by
  unfold line; fun_prop

/- **Rotating the slanted contour to a vertical line.** -/
end Zeta.RiemannSiegel

end

end CertificatePort90
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Gaussian.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Kernel.lean -/
section CertificatePort92
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The Riemann–Siegel kernel

The **Riemann–Siegel kernel** is
`G(x) = e^{iπx²} / (e^{iπx} − e^{−iπx}) = e^{iπx²} / (2i sin πx)`,
the integrand of the contour integral underlying the Riemann–Siegel formula (`riemann_siegel.tex`,
`sec:rs_kernel`). It is holomorphic off `ℤ` and has a simple pole at *every* integer with the
*same* residue `1/(2πi)`; that uniformity is what makes a contour shift across `1, …, ν` produce
the unweighted partial sum `∑_{n ≤ ν} n^{-s}`.

The quasi-periodicity `G(x + 1) − G(x) = e^{iπx(x+1)}` says the increment across one period is a
pure Gaussian.

## Main results

* `Zeta.RiemannSiegel.kernel`: the kernel `G`;
* `Zeta.RiemannSiegel.differentiableAt_kernel`: `G` is holomorphic off `ℤ`;
* `Zeta.RiemannSiegel.tendsto_sub_mul_kernel`: `G` has a simple pole of residue `1/(2πi)` at every
  integer;
* `Zeta.RiemannSiegel.kernel_neg`: `G` is odd;
* `Zeta.RiemannSiegel.kernel_eq_tsum_of_im_neg`, `Zeta.RiemannSiegel.kernel_eq_neg_tsum_of_im_pos`:
  the Gaussian expansions of `G` on the two open half-planes;
* `Zeta.RiemannSiegel.kernel_add_one`, `Zeta.RiemannSiegel.kernel_add_one_sub_kernel`: the
  quasi-periodicity of `G`.
-/
section


open Complex Filter Topology

open scoped Real

namespace Zeta.RiemannSiegel

/- The **Riemann–Siegel kernel** `G(x) = e^{iπx²} / (e^{iπx} − e^{−iπx})`. -/
noncomputable def kernel (x : ℂ) : ℂ :=
  exp (π * I * x ^ 2) / (exp (π * I * x) - exp (-(π * I * x)))

/- The Riemann–Siegel kernel in terms of the sine. -/
end Zeta.RiemannSiegel

end

end CertificatePort92
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/Complex/Arg.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Analysis/Complex/Cpow.lean -/
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Power.lean -/
section CertificatePort95
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The branch of `x ^ s` along the slanted Riemann–Siegel contour

The Riemann–Siegel integrand carries a factor `x ^ (-s)` which must be interpreted through the
branch of the logarithm that is real on `(0, ∞)` and continuous on the plane cut along the *upward*
imaginary ray `i[0, ∞)` (`riemann_siegel.tex`, `def:rs_power`). Mathlib's principal branch cuts
along the negative real axis instead, which the slanted contour `Zeta.RiemannSiegel.line` crosses,
so it cannot be used directly.

No bespoke branch theory is needed, however. Rotating by `e^{iπ/4}` carries the contour into the
open right half-plane (`Zeta.RiemannSiegel.re_exp_pi_div_four_mul_I_mul_line`), where the principal
branch is unproblematic, so the required branch is defined by rotating, taking mathlib's `cpow`, and
rotating back:
`x ^ s = e^{-iπs/4} (e^{iπ/4} x) ^ s`.

Holomorphy is therefore stated under membership of `Complex.slitPlane`, the hypothesis the
underlying `Complex.cpow` actually needs, rather than under `0 < Re (e^{iπ/4} x)`: the strict
inequality holds on `L(a)` for `a > 0` but degenerates to an equality on the contour `L(0)` through
the origin, along which the branch is nevertheless holomorphic away from `0`.

## Main results

* `Zeta.RiemannSiegel.slantArg`, `Zeta.RiemannSiegel.slantLog`,
  `Zeta.RiemannSiegel.slantCpow`: the branch of the argument, of the logarithm and of
  `x ↦ x ^ s` adapted to the contour;
* `Zeta.RiemannSiegel.slantCpow_eq_exp_mul_slantLog`: `x ^ s = e^{s Log x}`, for every `x ≠ 0`;
* `Zeta.RiemannSiegel.slantLog_eq_log`: on the right half-plane the branch agrees with mathlib's;
* `Zeta.RiemannSiegel.slantCpow_of_exp_pi_div_four_mul_I_mul_eq`: the branch in polar form,
  `x ^ u = ρ^u e^{i(φ - π/4)u}` when the rotation carries `x` to `ρ e^{iφ}`;
* `Zeta.RiemannSiegel.slantCpow_ofReal`: on `(0, ∞)` the branch agrees with mathlib's;
* `Zeta.RiemannSiegel.slantCpow_ofReal_mul_exp_pi_div_four_mul_I`,
  `Zeta.RiemannSiegel.slantCpow_neg_ofReal_mul_exp_pi_div_four_mul_I`: the branch on the two
  halves `ρ e^{iπ/4}` and `ρ e^{-3iπ/4}` of the contour through the origin;
* `Zeta.RiemannSiegel.differentiableAt_slantCpow`: the branch is holomorphic off the rotated branch
  cut;
* `Zeta.RiemannSiegel.norm_slantCpow`: `‖x ^ s‖ = ‖x‖ ^ Re s / exp (slantArg x * Im s)`;
* `Zeta.RiemannSiegel.slantArg_line`, `Zeta.RiemannSiegel.abs_slantArg_line_lt`: along the contour
  the argument is `arctan ((a + 2w)/a) - π/4`, and in particular bounded by `3π/4`;
* `Zeta.RiemannSiegel.slantArg_line_mul_im_le`: the resulting bound on the exponent of the modulus
  of the power.
-/
section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/- The **argument rotated through `π/4`**, `slantArg x = arg (e^{iπ/4} x) - π/4`. On the rotated
right half-plane `Re (e^{iπ/4} x) > 0` — which contains the whole contour
`Zeta.RiemannSiegel.line a` for `a > 0` — it is the branch of the argument that is continuous on
the plane cut along the upward imaginary ray `i[0, ∞)`. -/
noncomputable def slantArg (x : ℂ) : ℝ := (exp ((π / 4 : ℝ) * I) * x).arg - π / 4

/- The **branch of the logarithm** cut along the upward imaginary ray,
`Log x = log ‖x‖ + i arg_Ω x` with `arg_Ω = Zeta.RiemannSiegel.slantArg`. It is the branch that is
real on `(0, ∞)` and continuous on `ℂ \ i[0, ∞)`. -/
noncomputable def slantLog (x : ℂ) : ℂ := (Real.log ‖x‖ : ℂ) + (slantArg x : ℂ) * I

/- The **branch of `x ↦ x ^ s`** cut along the upward imaginary ray, `x ^ s = e^{-iπs/4}
(e^{iπ/4} x) ^ s` with Mathlib's principal `Complex.cpow` on the right. It agrees with the principal
branch on `(0, ∞)`, and on the rotated right half-plane it is the branch determined by
`Zeta.RiemannSiegel.slantArg`. -/
noncomputable def slantCpow (x s : ℂ) : ℂ :=
  exp (-((π / 4 : ℝ) * I * s)) * (exp ((π / 4 : ℝ) * I) * x) ^ s

/- **The slanted power is the exponential of the slanted logarithm**, `x ^ s = e^{s Log x}`. No
hypothesis beyond `x ≠ 0` is needed: the branch cut of the rotated variable is invisible to both
sides. -/
end Zeta.RiemannSiegel

end

end CertificatePort95
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Integral.lean -/
section CertificatePort96
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The Riemann–Siegel contour integral

The Riemann–Siegel formula rests on the contour integral `I(s, a) = ∫_{L(a)} x^{-s} G(x) dx` of the
kernel `Zeta.RiemannSiegel.kernel` against the branch `Zeta.RiemannSiegel.slantCpow` of
`x ↦ x^{-s}`, taken along the slanted line `Zeta.RiemannSiegel.line` (`riemann_siegel.tex`,
`def:rs_integral`).

The integral converges absolutely for every `s`, and for a very robust reason: the Gaussian factor
`e^{iπx²}` of the kernel contributes `e^{-2πw(a+w)}`, whose square-exponential decay beats both the
polynomial factor `‖x‖^{-Re s}` and the exponential factor `e^{slantArg x · Im s}` coming from the
power — the latter being bounded outright, since the argument along the contour never reaches
`±3π/4`. The crude constant obtained here is irrelevant: the sharp estimate on the critical line is
the business of `Zeta/RiemannSiegel/Bound.lean`.

## Main results

* `Zeta.RiemannSiegel.integrand`: the integrand `x ↦ x^{-s} G(x)`;
* `Zeta.RiemannSiegel.contourIntegrand`, `Zeta.RiemannSiegel.norm_contourIntegrand`,
  `Zeta.RiemannSiegel.norm_contourIntegrand_eq_exp`: its restriction
  `w ↦ L(a)(w)^{-s} G(L(a)(w))` to the contour, and two forms of the modulus of that;
* `Zeta.RiemannSiegel.continuous_contourIntegrand`: continuity along a contour missing the
  integers;
* `Zeta.RiemannSiegel.norm_contourIntegrand_le_exp`: a Gaussian majorant, uniform for `s` in a box;
* `Zeta.RiemannSiegel.integrable_contourIntegrand`,
  `Zeta.RiemannSiegel.integrable_contourIntegrand_of_le_half`: absolute convergence;
* `Zeta.RiemannSiegel.norm_kernel_line_le`: a Gaussian bound `‖G(L(a)(w))‖ = O(e^{-πw²})` for the
  kernel alone, with no power attached;
* `Zeta.RiemannSiegel.slantIntegral`: the integral of an arbitrary integrand along `L(a)`;
* `Zeta.RiemannSiegel.contourIntegral`: the contour integral `I(s, a)`.
-/
section


open Complex MeasureTheory

open scoped Real

namespace Complex

/- The modulus of a purely imaginary doubling: `‖2i z‖ = 2‖z‖`. -/
end Complex

namespace Zeta.RiemannSiegel

/- The **Riemann–Siegel integrand** `x ↦ x^{-s} G(x)`, in which the power is taken in the branch
`Zeta.RiemannSiegel.slantCpow` adapted to the contour. -/
noncomputable def integrand (s x : ℂ) : ℂ :=
  slantCpow x (-s) * kernel x

/- The **integrand of the Riemann–Siegel contour integral**, `w ↦ L(a)(w)^{-s} G(L(a)(w))`. -/
noncomputable def contourIntegrand (s : ℂ) (a w : ℝ) : ℂ :=
  integrand s (line a w)

/- The modulus of the integrand, with the kernel's denominator `2i sin (πx)` split off. -/
noncomputable def slantIntegral (f : ℂ → ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, f (line a w)

/- The **Riemann–Siegel contour integral** `I(s, a) = ∫_{L(a)} x^{-s} G(x) dx`, parametrised by
the slanted contour `Zeta.RiemannSiegel.line`, whose constant velocity is `1 + i`. -/
noncomputable def contourIntegral (s : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, contourIntegrand s a w

end Zeta.RiemannSiegel

end

end CertificatePort96
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Model.lean -/
section CertificatePort97
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The Riemann–Siegel model integral

Replacing the true integrand of `Zeta.RiemannSiegel.contourIntegral` by its Gaussian model at the
saddle leaves the **model integral**

`M(p) = ∫_{L(1/2)} e^{2πi(v − p)²} / (e^{iπv} − e^{−iπv}) dv`

(`riemann_siegel_first.tex`, `def:rsf_model`), which carries the whole of the first-order
correction to the Riemann–Siegel formula. The contour is the half-integer line `L(1/2)`, so the
denominator is bounded below by `Zeta.RiemannSiegel.norm_sin_pi_mul_line_ge` exactly as in the
order-zero chapter, and no new lower bound is needed. The contour parameter is carried along
nonetheless, because the unit shift of `ModelShift.lean` deforms `L(1/2)` out to `L(3/2)`.

The point of this file is the **half shift** `modelIntegral_add_half`, one of the two functional
equations that pin `M` algebraically — with no analytic continuation, no Liouville argument and no
growth estimate anywhere in the chapter.

## Main results

* `Zeta.RiemannSiegel.modelFun`, `Zeta.RiemannSiegel.modelIntegrand`,
  `Zeta.RiemannSiegel.modelIntegral`: the model integrand as a function of the complex variable, its
  restriction to `L(a)`, and the model integral `M(p) = modelIntegral p (1/2)`;
* `Zeta.RiemannSiegel.modelFun_add_one`: translation by one reverses the sign;
* `Zeta.RiemannSiegel.integrable_modelIntegrand`: absolute convergence, for every complex `p`;
* `Zeta.RiemannSiegel.norm_exp_two_pi_mul_I_mul_line_sub_sq`,
  `Zeta.RiemannSiegel.norm_exp_two_pi_mul_I_mul_line_sub_sq'`: the modulus of the model Gaussian
  along `L(½)`, with the square completed, and as a Gaussian in the distance to the centre;
* `Zeta.RiemannSiegel.norm_modelIntegral_le`: `|M(p)| ≤ e^{π(1/2 − p)²}/2` for real `p`;
* `Zeta.RiemannSiegel.modelIntegral_add_half`:
  `M(p + 1/2) = i e^{2πip} M(p) − i e^{iπ/8} e^{iπp}/√2`.
-/
section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/- The **Riemann–Siegel model integrand** `m_p(x) = e^{2πi(x − p)²} / (e^{iπx} − e^{−iπx})`, whose
denominator is that of the Riemann–Siegel kernel `Zeta.RiemannSiegel.kernel`. -/
noncomputable def modelFun (p x : ℂ) : ℂ :=
  exp (2 * π * I * (x - p) ^ 2) / (exp (π * I * x) - exp (-(π * I * x)))

/- The **integrand of the Riemann–Siegel model integral** along the contour `L(a)`. -/
noncomputable def modelIntegrand (p : ℂ) (a w : ℝ) : ℂ :=
  modelFun p (line a w)

/- The **Riemann–Siegel model integral** `M(p) = ∫_{L(1/2)} m_p(v) dv`, taken here along the
contour `L(a)`, whose constant velocity is `1 + i`. -/
noncomputable def modelIntegral (p : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, modelIntegrand p a w

end Zeta.RiemannSiegel

end

end CertificatePort97
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Moment.lean -/
section CertificatePort98
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The weighted moments of the Riemann–Siegel model integral

The sharp first-order estimate replaces the crude bound `|e^Δ − 1| ≤ …` of
`Zeta.RiemannSiegel.norm_integral_inner_le` by an exact evaluation of the `ζ`-linear part of
`e^Δ − 1`, whose coefficients are the **weighted model moments**

`N_n(p) = ∫_{L(1/2)} (v − p)^n e^{2πi(v − p)²} / (e^{iπv} − e^{−iπv}) dv`

(`riemann_siegel_first.tex`, `def:rsf_moment`), of which `N_0` is the model integral
`Zeta.RiemannSiegel.modelIntegral` itself.

The estimates of this file are stated uniformly in the centre `p`, through an upper bound `P` for
`‖p‖`: the majorant is then independent of `p` on any ball, which is what differentiation under
the integral sign in `p` needs.

## Main results

* `Zeta.RiemannSiegel.modelMomentIntegrand`, `Zeta.RiemannSiegel.modelMoment`: the weighted
  integrand along `L(a)` and its integral `N_n(p)`;
* `Zeta.RiemannSiegel.modelMoment_zero`: `N_0 = M`;
* `Zeta.RiemannSiegel.norm_modelMomentIntegrand_le`: a Gaussian majorant depending on `p` only
  through a bound `‖p‖ ≤ P`;
* `Zeta.RiemannSiegel.integrable_modelMomentIntegrand`: absolute convergence, for every complex
  `p` and every order `n`;
* `Zeta.RiemannSiegel.hasDerivAt_modelMoment`: the recursion `N_n' = −n N_{n−1} − 4πi N_{n+1}`;
* `Zeta.RiemannSiegel.iteratedDeriv_three_modelIntegral`: `M''' = 48π² N₁ + 64π³ i N₃`;
* `Zeta.RiemannSiegel.neg_half_modelMoment_one_sub_eq`: `−N₁/2 − (2πi/3) N₃ = −M'''/(96π²)`.
-/
section


open Complex MeasureTheory

open scoped Real

namespace Zeta.RiemannSiegel

/- The **integrand of the weighted Riemann–Siegel model moment** along the contour `L(a)`: the
model integrand `Zeta.RiemannSiegel.modelIntegrand` weighted by `(v − p)^n`. -/
noncomputable def modelMomentIntegrand (n : ℕ) (p : ℂ) (a w : ℝ) : ℂ :=
  (line a w - p) ^ n * modelIntegrand p a w

/- The **weighted Riemann–Siegel model moment**
`N_n(p) = ∫_{L(1/2)} (v − p)^n e^{2πi(v − p)²} / (e^{iπv} − e^{−iπv}) dv`, taken here along the
contour `L(a)`, whose constant velocity is `1 + i`. -/
noncomputable def modelMoment (n : ℕ) (p : ℂ) (a : ℝ) : ℂ :=
  (1 + I) * ∫ w : ℝ, modelMomentIntegrand n p a w

/- **The zeroth moment is the model integral.** -/
end Zeta.RiemannSiegel

end

end CertificatePort98
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/RiemannSiegel/Defs.lean -/
section CertificatePort99
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# The Riemann–Siegel approximant: definitions

The objects a Riemann–Siegel *certificate* is stated in terms of — the main sum at a prescribed
phase, the correction function `Ψ` and its linear coefficient `C₁`, and the packaged first-order
approximant `hardyZApproximantRS` with its error bound `hardyZErrorBoundRS` — separated from the
chapters that prove things about them.

The split is import hygiene. The proofs (`Zeta.RiemannSiegel.ZeroOrder`, `Correction`, `Linear`,
`FirstOrder`) deform contours and are phrased in `PrimeNumberTheoremAnd`'s rectangle-residue
apparatus, whereas the definitions need only `Zeta.RiemannSiegel.Model`/`Moment` and
`Zeta.Zeros.HardyZ`. Keeping the definitions on their own lets a certificate file, which only ever
*mentions* the approximant, stay clear of that apparatus; the analytic content
(`abs_hardyZRemainderRS_le`) is attached where the certificates are consumed.

## Main definitions

- `Zeta.RiemannSiegel.mainSumOfPhase`: `2 ∑_{n ≤ ν} n^{-1/2} cos(θ − t log n)`.
- `Zeta.RiemannSiegel.correction`, `Zeta.RiemannSiegel.correctionLinear`: `Ψ(p)` and `C₁(p)`.
- `hardyZApproximantRS`, `hardyZErrorBoundRS` (and the linear-free `…RS₀` variants): the
  approximant a certificate evaluates and the closed-form bound its margins are checked against.
-/
section


open Complex

open scoped Real

namespace Zeta.RiemannSiegel

/- The **Riemann–Siegel main sum at a prescribed phase** `θ`,
`S(θ, t, ν) = 2 ∑_{n = 1}^{ν} n^{-1/2} cos (θ − t log n)`. -/
noncomputable def mainSumOfPhase (θ t : ℝ) (ν : ℕ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ν, Real.cos (θ - t * Real.log n) / Real.sqrt n

/- The **Riemann–Siegel correction function** `Ψ(p) = 2 Re(e^{−iπ/8} M(p))`
(`riemann_siegel_first.tex`, `def:rsf_correction`). -/
noncomputable def correction (p : ℝ) : ℝ :=
  2 * (exp (-((π / 8 : ℝ) * I)) * modelIntegral (p : ℂ) (1 / 2)).re

/- The **first classical Riemann–Siegel coefficient** `C₁(p) = −Ψ'''(p)/(96π²)`
(`riemann_siegel_first.tex`, `def:rsf_c1`), in its moment form. -/
noncomputable def correctionLinear (p : ℝ) : ℝ :=
  2 * (exp (-((π / 8 : ℝ) * I)) *
    (-(1 / 2) * modelMoment 1 (p : ℂ) (1 / 2) - 2 * π * I / 3 * modelMoment 3 (p : ℂ) (1 / 2))).re

end Zeta.RiemannSiegel

open Zeta.RiemannSiegel

/- **The first-order Riemann–Siegel approximant for Hardy's `Z`**: the main sum at the order-`2`
Stirling phase and cutoff `ν = ⌊√T⌋`, corrected by `(-1)^ν T^{-1/4}(Ψ(p) + C₁(p)/√T)` at the
fractional part `p = √T - ν`. Unlike `hardyZApproximantEM` it takes no parameters: the cutoff and
the correction order are determined by `t` alone. -/
noncomputable abbrev hardyZApproximantRS (t : ℝ) : ℝ :=
  mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ⌊Real.sqrt (t / (2 * π))⌋₊
    - (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
        * (correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
          + correctionLinear (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)
              / Real.sqrt (t / (2 * π)))

/- **The error term of the first-order Riemann–Siegel approximant**, `Z(t) − Z̃^{RS}(t)`. It is
bounded by `abs_hardyZRemainderRS_le`. -/
noncomputable abbrev hardyZRemainderRS (t : ℝ) : ℝ := hardyZ t - hardyZApproximantRS t

/- **The first-order Riemann–Siegel error bound**, `25/4 · T^{-5/4} + T^{-15/4}/32` with
`T = t/2π`. A closed form in `t` alone: there is no parameter to tune and no free `ε`. -/
noncomputable abbrev hardyZErrorBoundRS (t : ℝ) : ℝ :=
  25 / 4 * (t / (2 * π)) ^ (-(5 / 4) : ℝ) + 1 / 32 * (t / (2 * π)) ^ (-(15 / 4) : ℝ)

/- **The first-order Riemann–Siegel approximant without the linear correction**: as
`hardyZApproximantRS`, but carrying only `Ψ(p)` and not `C₁(p)/√T`. Its error bound is
`hardyZErrorBoundRS₀`. -/
noncomputable abbrev hardyZApproximantRS₀ (t : ℝ) : ℝ :=
  mainSumOfPhase (riemannSiegelThetaApproximant 2 0 t) t ⌊Real.sqrt (t / (2 * π))⌋₊
    - (-1) ^ (⌊Real.sqrt (t / (2 * π))⌋₊ : ℕ) * (t / (2 * π)) ^ (-(1 / 4) : ℝ)
        * correction (Real.sqrt (t / (2 * π)) - ⌊Real.sqrt (t / (2 * π))⌋₊)

/- **The error term of the linear-free approximant**, `Z(t) − Z̃₀^{RS}(t)`. -/
noncomputable abbrev hardyZRemainderRS₀ (t : ℝ) : ℝ := hardyZ t - hardyZApproximantRS₀ t

/- **The error bound for the linear-free approximant**: `hardyZErrorBoundRS` plus the discarded
linear term's uniform size `(13/10)·T^{-3/4}`. -/
noncomputable abbrev hardyZErrorBoundRS₀ (t : ℝ) : ℝ :=
  hardyZErrorBoundRS t + 13 / 10 * (t / (2 * π)) ^ (-(3 / 4) : ℝ)

end

end CertificatePort99
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Zeros/Interval.lean -/
section CertificatePort100
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# Certified zero intervals

A `ZIntervalEM` is a closed interval carrying the Euler–Maclaurin data used to estimate Hardy's
`Z` at its endpoints; a `ZIntervalEM.Certificate` records that the two computed endpoint values
have opposite signs and exceed their error bounds, which forces a genuine sign change of `Z`.

A `CertifiedZeroIntervals` bundles a separated list of plain intervals together with the *fact*
that each brackets a `ζ`-zero, rather than the certificate that established it. That is the seam
between the approximation method and the counting argument: everything below this structure —
`height`, `zeros`, and the `N` bound — is method-agnostic, and each method supplies its own smart
constructor discharging `has_zero` from its own certificates. `ZIntervalRS` needs no per-endpoint
data at all, the Riemann–Siegel cutoff being determined by the height alone.

## Main definitions

- `ZIntervalEM`, `ZIntervalEM.Certificate`: one bracketed zero and its Euler–Maclaurin
  certificate; `ZIntervalRS`, the Riemann–Siegel counterpart.
- `CertifiedZeroIntervals`, `CertifiedZeroIntervals.height`, `CertifiedZeroIntervals.zeros`: a
  separated list of certified intervals, the largest right endpoint, and the bracketed zeros.

## Main results

- `riemannZeta.exists_zero_of_zIntervalEM_certificate`: a certified Euler–Maclaurin interval
  contains a `ζ`-zero on the critical line.

Two results one might expect here live elsewhere, for import hygiene: this file is imported by
every certificate batch, so it mentions the Riemann–Siegel approximant only through its
*definition* (`Zeta.RiemannSiegel.Defs`) and never touches the zero-counting function.
- `riemannZeta.exists_zero_of_zIntervalRS_certificate`, the Riemann–Siegel counterpart of the
  theorem above, is in `Zeta/Zeros/IntervalRS.lean`: it needs the first-order bound
  `abs_hardyZRemainderRS_le`, whose proof chapter is phrased in `PrimeNumberTheoremAnd`'s
  rectangle apparatus.
- `riemannZeta.le_N_of_certifiedZeroIntervals`, `C.intervals.length ≤ N(C.height)`, is in
  `Zeta/Zeros/Count.lean` with the rest of the counting side.
-/
section


namespace Zeta.Certificates

/- A closed nonempty interval along with the parameters needed to compute the Euler-Maclaurin
approximation of Hardy's Z-function at the endpoints. -/
structure ZIntervalEM extends NonemptyInterval ℝ where
  /- The Euler–Maclaurin cutoff used to estimate the lower `Z` value. -/
  fstCutoff : ℕ
  /- The Euler–Maclaurin cutoff used to estimate the upper `Z` value. -/
  sndCutoff : ℕ
  /- The number of Bernoulli terms used to estimate the lower `Z` value. -/
  fstBernoulli : ℕ
  /- The number of Bernoulli terms used to estimate the upper `Z` value. -/
  sndBernoulli : ℕ

/- A closed nonempty interval used to compute the Riemann-Siegel approximation of Hardy's `Z`. -/
abbrev ZIntervalRS := NonemptyInterval ℝ

/- The approximate value of the Hardy Z function at the left endpoint. -/
noncomputable abbrev ZIntervalEM.fstVal (I : ZIntervalEM) : ℝ :=
  hardyZApproximantEM I.fstBernoulli I.fstCutoff I.fst

/- The approximate value of the Hardy Z function at the right endpoint. -/
noncomputable abbrev ZIntervalEM.sndVal (I : ZIntervalEM) : ℝ :=
  hardyZApproximantEM I.sndBernoulli I.sndCutoff I.snd

/- The approximate value of the Hardy Z function at the left endpoint. -/
noncomputable abbrev ZIntervalRS.fstVal (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS I.fst

/- The approximate value of the Hardy Z function at the right endpoint. -/
noncomputable abbrev ZIntervalRS.sndVal (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS I.snd

/- The approximate value of the Hardy Z function at the left endpoint, without the first-order
correction `C₁`; see `ZIntervalRS.Certificate₀`. -/
noncomputable abbrev ZIntervalRS.fstVal₀ (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS₀ I.fst

/- The approximate value of the Hardy Z function at the right endpoint, without the first-order
correction `C₁`; see `ZIntervalRS.Certificate₀`. -/
noncomputable abbrev ZIntervalRS.sndVal₀ (I : ZIntervalRS) : ℝ :=
  hardyZApproximantRS₀ I.snd

/- A certificate that the interval `I` brackets a genuine zero of Hardy's `Z` function,
using Euler-Maclaurin approximation of the `Z`-function. This certifies that the interval
equivalently contains a zero of `ζ` on the critical line. -/
structure ZIntervalEM.Certificate (I : ZIntervalEM) where
  /- Required for the Riemann-Siegel theta function error bound. -/
  fst_nonneg : 0 ≤ I.fst
  /- Required for the log-Γ Stirling remainder error bound. -/
  fstBernoulli_pos : 0 < I.fstBernoulli
  /- Required for the zeta Euler-Maclaurin error bound. -/
  fstCutoff_pos : 0 < I.fstCutoff
  /- At least one Bernoulli term is used at the right endpoint; see `leftBernoulli_pos`. -/
  sndBernoulli_pos : 0 < I.sndBernoulli
  /- The right Euler–Maclaurin cutoff is positive; see `leftCutoff_pos`. -/
  sndCutoff_pos : 0 < I.sndCutoff
  /- The two computed endpoint values have opposite signs. -/
  is_sign_change : I.fstVal * I.sndVal < 0
  /- The computed left value exceeds its error bound, so the true `Z` shares its sign. -/
  fst_error : ‖I.fstVal‖ > hardyZErrorBoundEM I.fstBernoulli I.fstCutoff I.fst
  /- The computed right value exceeds its error bound, so the true `Z` shares its sign. -/
  snd_error : ‖I.sndVal‖ > hardyZErrorBoundEM I.sndBernoulli I.sndCutoff I.snd

/- A certificate that the interval `I` brackets a genuine zero of Hardy's `Z` function,
using Riemann-Siegel approximation of the `Z`-function. This certifies that the interval
equivalently contains a zero of `ζ` on the critical line. -/
structure ZIntervalRS.Certificate (I : ZIntervalRS) where
  /- Required for the first-order Riemann–Siegel error bound, which holds only for `t ≥ 32π`.
  The same bound at the right endpoint follows via `I.fst_le_snd`; see `le_snd`. -/
  le_fst : 32 * Real.pi ≤ I.fst
  /- The two computed endpoint values have opposite signs. -/
  is_sign_change : I.fstVal * I.sndVal < 0
  /- The computed left value exceeds its error bound, so the true `Z` shares its sign. -/
  fst_error : ‖I.fstVal‖ > hardyZErrorBoundRS I.fst
  /- The computed right value exceeds its error bound, so the true `Z` shares its sign. -/
  snd_error : ‖I.sndVal‖ > hardyZErrorBoundRS I.snd

namespace ZIntervalRS.Certificate

variable {I : ZIntervalRS}

/- The threshold `t ≥ 32π` also holds at the right endpoint. -/
theorem fst_nonneg (h : I.Certificate) : 0 ≤ I.fst :=
  le_trans (by positivity) h.le_fst

/- The left endpoint clears the Riemann–Siegel threshold in the `T = t/2π` normalisation, the
form `abs_hardyZRemainderRS_le` takes it in. -/
end ZIntervalRS.Certificate

/- A certificate as `ZIntervalRS.Certificate`, but against the linear-free approximant
`hardyZApproximantRS₀` and its larger error bound `hardyZErrorBoundRS₀`. It is cheaper to build,
since there is no `C₁` enclosure, and suffices wherever both endpoint values clear the extra
`13/10·T^{-3/4}`; close zero pairs still need the full `Certificate`. -/
structure ZIntervalRS.Certificate₀ (I : ZIntervalRS) where
  /- Required for the first-order Riemann–Siegel error bound; see `Certificate.le_fst`. -/
  le_fst : 32 * Real.pi ≤ I.fst
  /- The two computed endpoint values have opposite signs. -/
  is_sign_change : I.fstVal₀ * I.sndVal₀ < 0
  /- The computed left value exceeds its error bound, so the true `Z` shares its sign. -/
  fst_error : ‖I.fstVal₀‖ > hardyZErrorBoundRS₀ I.fst
  /- The computed right value exceeds its error bound, so the true `Z` shares its sign. -/
  snd_error : ‖I.sndVal₀‖ > hardyZErrorBoundRS₀ I.snd

namespace ZIntervalRS.Certificate₀

variable {I : ZIntervalRS}

/- The threshold `t ≥ 32π` also holds at the right endpoint. -/
theorem fst_nonneg (h : I.Certificate₀) : 0 ≤ I.fst :=
  le_trans (by positivity) h.le_fst

end ZIntervalRS.Certificate₀

/- What a Riemann–Siegel batch records per interval: either certificate. The metaprogram tries
the cheaper `Certificate₀` first and falls back to the full `Certificate`. -/
abbrev ZIntervalRS.Certified (I : ZIntervalRS) : Prop := I.Certificate ∨ I.Certificate₀

/- A list of certified zero intervals, ordered and pairwise disjoint. -/
structure CertifiedZeroIntervals where
  intervals : List (NonemptyInterval ℝ)
  fst_nonneg : ∀ I ∈ intervals, 0 ≤ I.fst
  has_zero : ∀ I ∈ intervals, ∃ t ∈ Set.Ioo I.fst I.snd, riemannZeta (1/2 + Complex.I * t) = 0
  disj : intervals.IsChain fun I J ↦ I.snd ≤ J.fst


/- The height of a certified list: the largest right endpoint (`0` if the list is empty). -/
@[simp]
noncomputable def CertifiedZeroIntervals.height (C : CertifiedZeroIntervals) : ℝ :=
  if h : C.intervals = [] then 0 else (C.intervals.maxOn (fun I ↦ I.snd) h).snd

/- Every interval of a certified list ends below its height. -/
end Zeta.Certificates

open Zeta.Certificates

/- A real number within `|b|` of `b` shares `b`'s (necessarily nonzero) sign. -/
namespace Zeta.Certificates

open Complex Set

/- The list of critical-line `ζ`-zeros bracketed by a certified list of intervals, one per
interval. -/
noncomputable def CertifiedZeroIntervals.zeros (C : CertifiedZeroIntervals) : List ℂ :=
  (C.intervals.pmap (fun I hI ↦ (C.has_zero I hI).choose) (by simp)).map
      fun t : ℝ ↦ 1/2 + I * t

/- An empty certified list brackets no zeros. -/
end Zeta.Certificates

end

end CertificatePort100
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/Gram/Block.lean -/
section CertificatePort101
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/


/-!
# Certified gram blocks

A `GramPoint` is an interval bracketing the `n`-th gram point (the solution of `θ(t) = n·π`),
together with the Stirling data used to estimate `θ` at its endpoints; its `Certificate` records
that the two computed values straddle `n·π` by more than their error bounds. A `GramBlock` pairs
two consecutive certified gram points with a list of zero intervals lying between them, and a
`CertifiedGramBlockSeq` chains such blocks; this is the input to Turing's method.

## Main definitions

- `GramPoint`, `GramPoint.fstVal`, `GramPoint.sndVal`, `GramPoint.Certificate`: a bracketed
  gram point, its two computed `θ`-values, and its certificate.
- `GramBlock`, `GramBlock.Certificate`: two consecutive gram points enclosing certified zeros.
- `CertifiedGramBlockSeq`, `CertifiedGramBlockSeq.minIdx`: a chain of certified gram blocks and
  the gram index at its head.

## Main results

- `GramPoint.certificate_theta_left_lt`, `GramPoint.certificate_theta_right_gt`: a certified gram
  point brackets `θ = n·π`.
- `CertifiedGramBlockSeq.getElem_left_idx`: the `j`-th block of a chain has left index
  `minIdx + j`.
-/
section


namespace Zeta.Certificates

open Real Set

/- An interval bracketing the `n`-th gram point (`θ(t) = n·π`), with the Stirling orders and
shifts used to estimate `θ` at its endpoints. -/
structure GramPoint extends NonemptyInterval ℝ where
  /- The gram index `n`. -/
  idx : ℕ
  /- The Stirling shift used to estimate `θ` at the left endpoint. -/
  fstCutoff : ℕ
  /- The number of Bernoulli terms used to estimate `θ` at the left endpoint. -/
  fstBernoulli : ℕ
  /- The Stirling shift used to estimate `θ` at the right endpoint. -/
  sndCutoff : ℕ
  /- The number of Bernoulli terms used to estimate `θ` at the right endpoint. -/
  sndBernoulli : ℕ

/- The approximate value of `θ` at the left endpoint. -/
noncomputable abbrev GramPoint.fstVal (G : GramPoint) : ℝ :=
  riemannSiegelThetaApproximant G.fstBernoulli G.fstCutoff G.fst

/- The approximate value of `θ` at the right endpoint. -/
noncomputable abbrev GramPoint.sndVal (G : GramPoint) : ℝ :=
  riemannSiegelThetaApproximant G.sndBernoulli G.sndCutoff G.snd

/- A certificate that the interval `G` brackets the gram point of index `G.idx`. -/
structure GramPoint.Certificate (G : GramPoint) where
  /- Required for the Riemann–Siegel theta error bound at the left endpoint. -/
  fst_nonneg : 0 ≤ G.fst
  /- Required for the Riemann–Siegel theta error bound at the right endpoint. -/
  snd_nonneg : 0 ≤ G.snd
  /- Required for the log-Γ Stirling remainder bound at the left endpoint. -/
  fstBernoulli_pos : 0 < G.fstBernoulli
  /- Required for the log-Γ Stirling remainder bound at the right endpoint. -/
  sndBernoulli_pos : 0 < G.sndBernoulli
  /- The computed left value falls short of `G.idx · π` by more than its error bound. -/
  fst_bound : G.idx * π - G.fstVal >
    riemannSiegelThetaStirlingErrorBound' G.fstBernoulli G.fstCutoff G.fst
  /- The computed right value exceeds `G.idx · π` by more than its error bound. -/
  snd_bound : G.sndVal - G.idx * π >
    riemannSiegelThetaStirlingErrorBound' G.sndBernoulli G.sndCutoff G.snd

/- Two consecutive gram points together with the zero intervals lying between them. -/
structure GramBlock where
  /- The gram point of index `n`. -/
  left : GramPoint
  /- The gram point of index `n + 1`. -/
  right : GramPoint
  /- The zero intervals carried by the block. -/
  zeros : List (NonemptyInterval ℝ)
  /- The two gram indices are consecutive. -/
  seq : left.idx + 1 = right.idx
  /- The left bracket ends at or before the right one begins. Each bracket is separately
  non-empty by `GramPoint.fst_le_snd`. -/
  separated : left.snd ≤ right.fst

/- A certificate that the gram pair `G` brackets the gram points `n·π` and `(n+1)·π` and
encloses a certified zero of Hardy's `Z` between them. -/
structure GramBlock.Certificate (G : GramBlock) where
  /- The left gram point is certified. -/
  left_certificate : G.left.Certificate
  /- The right gram point is certified. -/
  right_certificate : G.right.Certificate
  /- Every interval carried by the block brackets a `ζ`-zero. As in `CertifiedZeroIntervals`,
  the block records the *fact* rather than the certificate that established it, so a block may
  carry intervals certified by either approximation method. -/
  has_zero : ∀ z ∈ G.zeros, ∃ t ∈ Set.Ioo z.fst z.snd, riemannZeta (1 / 2 + Complex.I * t) = 0
  /- Some zero interval lies between the two gram brackets. -/
  contains_zero : ∃ z ∈ G.zeros, z.fst ∈ Icc G.left.snd G.right.fst ∧
    z.snd ∈ Icc G.left.snd G.right.fst

/- A chain of certified gram blocks with consecutive indices, spanning a range wide enough
(`wide`) and high enough (`high`) for Turing's method. -/
structure CertifiedGramBlockSeq where
  /- The blocks, in increasing order. -/
  blocks : List GramBlock
  /- Consecutive blocks share a gram index. -/
  seq : blocks.IsChain fun a b ↦ a.right.idx = b.left.idx
  /- Every block is certified. -/
  cert : ∀ b ∈ blocks, b.Certificate
  /- The chain is non-empty. -/
  non_empty : blocks ≠ []
  /- The span of the chain exceeds the Lehman bound on `|∫S|`. -/
  wide : (5 + (0.128 : ℝ) * ((blocks.getLast non_empty).right.snd / (2 * π)).log) <
    ((blocks.getLast non_empty).right.fst - (blocks.head non_empty).left.snd) / 2
  /- The chain sits above `168π`, as the Lehman bound requires. -/
  high : 168 * π < (blocks.head non_empty).left.fst

/- The gram index at the head of a certified chain. -/
abbrev CertifiedGramBlockSeq.minIdx (C : CertifiedGramBlockSeq) : ℕ :=
  (C.blocks.head C.non_empty).left.idx

/- At the left endpoint of a certified gram point, `θ` lies strictly below `G.idx · π`. -/
end Zeta.Certificates

end

end CertificatePort101
/- SOURCE quantitative_sources/compatible_checkout/smmercuri-zeta-3dab648/Zeta/EulerMaclaurin/ErrorBound.lean -/


