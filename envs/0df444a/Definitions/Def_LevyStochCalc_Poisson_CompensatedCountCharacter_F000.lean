-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedCountCharacter_F000
-- name    : LevyStochCalc_Poisson_CompensatedCountCharacter_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:16:10.565233+00:00
-- url     : https://prove2.me/theorems/37e8a9cc-1d00-458b-889c-42bcdd0b5e63
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedCountCharacter
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedCountCharacter. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_RandomMeasure_F000
import Definitions.Def_LevyStochCalc_Probability_PoissonMoments_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing of a compensated Poisson count with its character

For a count `N` of a Poisson random measure on a region `B` of finite intensity
`λ = ν̂(B)`, the compensated count `Ñ = N − λ` and a real frequency `s`, the character
`e^{isÑ}` pairs with the first two powers of the compensated count as

  `E[e^{isÑ} Ñ] = λ (e^{is} − 1) E[e^{isÑ}]`,
  `E[e^{isÑ} Ñ²] = (λ² (e^{is} − 1)² + λ e^{is}) E[e^{isÑ}]`.

Both follow from Poisson integration by parts `E[N g(N)] = λ E[g(N + 1)]` for complex weights
`g`, applied to `g(n) = e^{is(n − λ)}` and `g(n) = e^{is(n − λ)} (n − λ)`, together with the
shift `e^{is(n + 1 − λ)} = e^{is} e^{is(n − λ)}`.

## Main statements

* `LevyStochCalc.Poisson.integral_exp_I_mul_compensated_mul_compensated` —
  `E[e^{isÑ} Ñ] = λ (e^{is} − 1) E[e^{isÑ}]`.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensated_mul_compensated_sq` —
  `E[e^{isÑ} Ñ²] = (λ² (e^{is} − 1)² + λ e^{is}) E[e^{isÑ}]`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Nat

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Moments of a Poisson count against its character -/

/-- Poisson integration by parts with a complex weight: `E[N g(N)] = r E[g(N + 1)]` under
`poissonMeasure r`. -/
private theorem integral_natCast_mul_poissonMeasure (r : ℝ≥0) {g : ℕ → ℂ}
    (hg : Integrable (fun n : ℕ => (n : ℂ) * g n) (poissonMeasure r)) :
    ∫ n, (n : ℂ) * g n ∂poissonMeasure r = (r : ℂ) * ∫ n, g (n + 1) ∂poissonMeasure r := by
  have hsum := (hasSum_integral_poissonMeasure hg).summable
  rw [integral_poissonMeasure, integral_poissonMeasure, hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, smul_zero, zero_add]
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [Complex.real_smul, Complex.real_smul]
  have hfac : ((m + 1)! : ℝ) = ((m : ℝ) + 1) * m ! := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h0 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have h1 : ((m ! : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast [hfac, pow_succ]
  field_simp
/-- A function of a count of a Poisson random measure on a region of finite intensity
integrates against its Poisson law. -/
private theorem integral_comp_count (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) {F : ℝ≥0∞ → ℂ}
    (hF : Measurable F) :
    ∫ ω, F (N.N ω B) ∂P = ∫ n : ℕ, F n ∂poissonMeasure (referenceIntensity ν B).toNNReal := by
  rw [← integral_map (N.measurable_eval hB).aemeasurable hF.aestronglyMeasurable,
    N.poisson_law hB hfin, poissonMeasureENN,
    integral_map (by fun_prop) hF.aestronglyMeasurable]
/-- Integrability of a function of a Poisson count bounded by a power of the shifted count. -/
private theorem integrable_poissonMeasure_of_le (r : ℝ≥0) (k : ℕ) {g : ℕ → ℂ}
    (hg : ∀ n : ℕ, ‖g n‖ ≤ ((n : ℝ) + r) ^ k) : Integrable g (poissonMeasure r) := by
  have h := Probability.integrable_eval_poissonMeasure r ((Polynomial.X + Polynomial.C (r : ℝ)) ^ k)
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C] at h
  exact Integrable.mono' h (by fun_prop) (Eventually.of_forall hg)
/-- The first two moments of a centred Poisson count against its character. For `N` with law
`poissonMeasure r` and `λ = r`, writing `b(n) = e^{i s (n − λ)}`,
`E[b(N) (N − λ)] = λ (e^{is} − 1) E[b(N)]` and
`E[b(N) (N − λ)²] = (λ² (e^{is} − 1)² + λ e^{is}) E[b(N)]`. -/
private theorem integral_exp_mul_centred_poissonMeasure (r : ℝ≥0) (s : ℝ) :
    (∫ n : ℕ, Complex.exp (Complex.I * ((s * ((n : ℝ) - r) : ℝ) : ℂ))
        * (((n : ℝ) - r : ℝ) : ℂ) ∂poissonMeasure r
      = (r : ℂ) * (Complex.exp (Complex.I * s) - 1)
        * ∫ n : ℕ, Complex.exp (Complex.I * ((s * ((n : ℝ) - r) : ℝ) : ℂ)) ∂poissonMeasure r)
    ∧ (∫ n : ℕ, Complex.exp (Complex.I * ((s * ((n : ℝ) - r) : ℝ) : ℂ))
        * (((n : ℝ) - r : ℝ) : ℂ) ^ 2 ∂poissonMeasure r
      = ((r : ℂ) ^ 2 * (Complex.exp (Complex.I * s) - 1) ^ 2
          + (r : ℂ) * Complex.exp (Complex.I * s))
        * ∫ n : ℕ, Complex.exp (Complex.I * ((s * ((n : ℝ) - r) : ℝ) : ℂ)) ∂poissonMeasure r) := by
  set b : ℕ → ℂ := fun n => Complex.exp (Complex.I * ((s * ((n : ℝ) - r) : ℝ) : ℂ)) with hb
  set z : ℂ := Complex.exp (Complex.I * s) with hz
  have hbn : ∀ n : ℕ, ‖b n‖ = 1 := fun n => by rw [hb, Complex.norm_exp_I_mul_ofReal]
  have hshift : ∀ n : ℕ, b (n + 1) = z * b n := fun n => by
    rw [hb, hz, ← Complex.exp_add]
    push_cast
    ring_nf
  have hr0 : (0 : ℝ) ≤ r := r.2
  have habs : ∀ n : ℕ, |(n : ℝ) - r| ≤ (n : ℝ) + r := fun n =>
    abs_le.2 ⟨by linarith [n.cast_nonneg (α := ℝ)], by linarith⟩
  have hnorm1 : ∀ n : ℕ, ‖(((n : ℝ) - r : ℝ) : ℂ)‖ ≤ (n : ℝ) + r := fun n => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact habs n
  have hn1 : ∀ n : ℕ, ‖((n : ℂ))‖ ≤ (n : ℝ) + r := fun n => by
    rw [Complex.norm_natCast]; linarith
  have i0 : Integrable b (poissonMeasure r) :=
    integrable_poissonMeasure_of_le r 0 fun n => by rw [hbn, pow_zero]
  have i1 : Integrable (fun n : ℕ => b n * (((n : ℝ) - r : ℝ) : ℂ)) (poissonMeasure r) :=
    integrable_poissonMeasure_of_le r 1 fun n => by
      rw [norm_mul, hbn, one_mul, pow_one]; exact hnorm1 n
  have i2 : Integrable (fun n : ℕ => b n * (((n : ℝ) - r : ℝ) : ℂ) ^ 2) (poissonMeasure r) :=
    integrable_poissonMeasure_of_le r 2 fun n => by
      rw [norm_mul, hbn, one_mul, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm1 n) 2
  have j1 : Integrable (fun n : ℕ => (n : ℂ) * b n) (poissonMeasure r) :=
    integrable_poissonMeasure_of_le r 1 fun n => by
      rw [norm_mul, hbn, mul_one, pow_one]; exact hn1 n
  have j2 : Integrable (fun n : ℕ => (n : ℂ) * (b n * (((n : ℝ) - r : ℝ) : ℂ)))
      (poissonMeasure r) :=
    integrable_poissonMeasure_of_le r 2 fun n => by
      rw [norm_mul, norm_mul, hbn, one_mul, sq]
      exact mul_le_mul (hn1 n) (hnorm1 n) (norm_nonneg _) (by positivity)
  set B0 := ∫ n : ℕ, b n ∂poissonMeasure r with hB0
  have hB1 : ∫ n : ℕ, b n * (((n : ℝ) - r : ℝ) : ℂ) ∂poissonMeasure r
      = (r : ℂ) * (z - 1) * B0 := by
    have hsplit : (fun n : ℕ => b n * (((n : ℝ) - r : ℝ) : ℂ))
        = fun n : ℕ => (n : ℂ) * b n - (r : ℂ) * b n := by
      funext n; push_cast; ring
    rw [hsplit, integral_sub j1 (i0.const_mul _), integral_const_mul,
      integral_natCast_mul_poissonMeasure r j1]
    simp_rw [hshift]
    rw [integral_const_mul]
    ring
  refine ⟨hB1, ?_⟩
  have hsplit : (fun n : ℕ => b n * (((n : ℝ) - r : ℝ) : ℂ) ^ 2)
      = fun n : ℕ => (n : ℂ) * (b n * (((n : ℝ) - r : ℝ) : ℂ))
        - (r : ℂ) * (b n * (((n : ℝ) - r : ℝ) : ℂ)) := by
    funext n; push_cast; ring
  have hshift2 : ∀ n : ℕ, b (n + 1) * ((((n + 1 : ℕ) : ℝ) - r : ℝ) : ℂ)
      = z * (b n * (((n : ℝ) - r : ℝ) : ℂ)) + z * b n := fun n => by
    rw [hshift]; push_cast; ring
  rw [hsplit, integral_sub j2 (i1.const_mul _), integral_const_mul,
    integral_natCast_mul_poissonMeasure r j2]
  simp_rw [hshift2]
  rw [integral_add (i1.const_mul _) (i0.const_mul _), integral_const_mul, integral_const_mul,
    hB1]
  ring
/-- The pairing of the character of a compensated count with a power of the compensated count,
as an integral against the Poisson law of the count. -/
private theorem integral_exp_mul_compensated_pow_eq (N : PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (s : ℝ)
    (i : ℕ) :
    ∫ ω, Complex.exp (Complex.I * ((s * N.compensated B ω : ℝ) : ℂ))
        * ((N.compensated B ω : ℝ) : ℂ) ^ i ∂P
      = ∫ n : ℕ, Complex.exp (Complex.I * ((s * ((n : ℝ) - (referenceIntensity ν B).toNNReal) :
          ℝ) : ℂ)) * (((n : ℝ) - (referenceIntensity ν B).toNNReal : ℝ) : ℂ) ^ i
        ∂poissonMeasure (referenceIntensity ν B).toNNReal := by
  have hF : Measurable fun x : ℝ≥0∞ =>
      Complex.exp (Complex.I * ((s * (x.toReal - (referenceIntensity ν B).toNNReal) : ℝ) : ℂ))
        * (((x.toReal - (referenceIntensity ν B).toNNReal : ℝ)) : ℂ) ^ i := by fun_prop
  have h := integral_comp_count N hB hfin hF
  simp only [ENNReal.toReal_natCast] at h
  rw [← h]
  rfl
/-- **The first-order pairing of a compensated count with its character.** For a region `B` of
finite intensity `λ` and the compensated count `Ñ = Ñ(B)`,
`E[e^{isÑ} Ñ] = λ (e^{is} − 1) E[e^{isÑ}]`. -/
theorem integral_exp_I_mul_compensated_mul_compensated (N : PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (s : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((s * N.compensated B ω : ℝ) : ℂ))
        * (N.compensated B ω : ℂ) ∂P
      = ((referenceIntensity ν B).toReal : ℂ) * (Complex.exp (Complex.I * s) - 1)
        * ∫ ω, Complex.exp (Complex.I * ((s * N.compensated B ω : ℝ) : ℂ)) ∂P := by
  have h1 := integral_exp_mul_compensated_pow_eq N hB hfin s 1
  have h0 := integral_exp_mul_compensated_pow_eq N hB hfin s 0
  simp only [pow_one, pow_zero, mul_one] at h1 h0
  rw [h1, h0]
  exact (integral_exp_mul_centred_poissonMeasure _ s).1
/-- **The second-order pairing of a compensated count with its character.** For a region `B` of
finite intensity `λ` and the compensated count `Ñ = Ñ(B)`,
`E[e^{isÑ} Ñ²] = (λ² (e^{is} − 1)² + λ e^{is}) E[e^{isÑ}]`. -/
theorem integral_exp_I_mul_compensated_mul_compensated_sq (N : PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (s : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((s * N.compensated B ω : ℝ) : ℂ))
        * (N.compensated B ω : ℂ) ^ 2 ∂P
      = (((referenceIntensity ν B).toReal : ℂ) ^ 2 * (Complex.exp (Complex.I * s) - 1) ^ 2
          + ((referenceIntensity ν B).toReal : ℂ) * Complex.exp (Complex.I * s))
        * ∫ ω, Complex.exp (Complex.I * ((s * N.compensated B ω : ℝ) : ℂ)) ∂P := by
  have h0 := integral_exp_mul_compensated_pow_eq N hB hfin s 0
  simp only [pow_zero, mul_one] at h0
  rw [integral_exp_mul_compensated_pow_eq N hB hfin s 2, h0]
  exact (integral_exp_mul_centred_poissonMeasure _ s).2
end LevyStochCalc.Poisson


