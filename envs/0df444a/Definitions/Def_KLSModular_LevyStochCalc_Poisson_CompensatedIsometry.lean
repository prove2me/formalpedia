-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
-- name    : KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:46:42.510558+00:00
-- url     : https://prove2.me/theorems/4240c0de-7cd4-4cfd-b0f6-ca08dd14100d
-- title:
--   Poisson moment and compensated-mass identities
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. The bundle establishes the Poisson series identities for the first and second moments, yielding mean $r$, second moment $r^2+r$, and variance $r$ for `poissonMeasure r`. For a finite-intensity measurable $B$, `compensated_mean_zero` and `compensated_second_moment` state respectively that $\mathbb E[\widetilde N(B)]=0$ and $\mathbb E[\widetilde N(B)^2]=\widehat\nu(B).\mathrm{toReal}$; `compensated_sq_integrable` gives integrability of the square. The remaining declarations are summability and integrability auxiliaries for these identities.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Poisson.CompensatedSimple
--   import LevyStochCalc.Poisson.Filtered
--   import Mathlib.Probability.Independence.Integration
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private lemma poisson_term_succ_eq (r : ℝ) (n : ℕ) :
--       r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ)
--       = r * (r ^ n / (n.factorial : ℝ)) := by
--     have hn : (n.factorial : ℝ) ≠ 0 :=
--       Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
--     have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
--       Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
--     rw [Nat.factorial_succ, pow_succ]
--     push_cast
--     field_simp
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Poisson/CompensatedSimple`](https://prove2.me/theorems/e31661e6-5ece-4a83-a5a6-f85de245dba0), [`LevyStochCalc/Poisson/Filtered`](https://prove2.me/theorems/08066098-c121-481f-8591-4482fa5ae649).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Poisson/CompensatedIsometry.lean) · `LevyStochCalc.Poisson.CompensatedIsometry` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Poisson/CompensatedIsometry.lean#L45-L495 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Poisson.CompensatedIsometry`, definition bundle `KLSModular_LevyStochCalc_Poisson_CompensatedIsometry`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedSimple
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_Filtered
import Mathlib.Probability.Independence.Integration

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Poisson/CompensatedIsometry.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Poisson
namespace Compensated
universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
 lemma poisson_term_succ_eq (r : ℝ) (n : ℕ) :
    r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ)
    = r * (r ^ n / (n.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Series identity for Poisson mean.** `∑' n, r^n / n! · n = r · exp(r)`. -/
 lemma tsum_pow_div_factorial_mul_nat (r : ℝ) :
    ∑' n : ℕ, r ^ n / (n.factorial : ℝ) * (n : ℝ) = r * Real.exp r := by
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ))
            = fun n => r * (r ^ n / (n.factorial : ℝ)) from
      funext (LevyStochCalc.Poisson.Compensated.poisson_term_succ_eq r)]
    exact (Real.summable_pow_div_factorial r).mul_left r
  rw [tsum_eq_zero_add' h_summable_succ]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Nat.cast_zero, mul_zero, zero_add]
  simp_rw [LevyStochCalc.Poisson.Compensated.poisson_term_succ_eq r]
  rw [tsum_mul_left]
  congr 1
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Mean of `poissonMeasure r` is `r`.** Derived from `integral_poissonMeasure`
+ the series identity `∑' n, r^n / n! · n = r · exp(r)`. -/
 lemma poissonMeasure_integral_id (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r) = (r : ℝ) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  have h_smul_eq : ∀ n : ℕ,
      (Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ)) • ((n : ℝ))
      = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
    intro n
    change Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
        = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ))
    ring
  simp_rw [h_smul_eq]
  rw [tsum_mul_left]
  rw [LevyStochCalc.Poisson.Compensated.tsum_pow_div_factorial_mul_nat]
  rw [show Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) * Real.exp (↑r))
        = (↑r : ℝ) * (Real.exp (-(↑r : ℝ)) * Real.exp (↑r)) from by ring]
  rw [← Real.exp_add]
  rw [show (-(↑r : ℝ) + (↑r : ℝ)) = 0 from by ring]
  rw [Real.exp_zero, mul_one]
/-- **Summability of `r^n / n! · n` for r ≥ 0.** Used for integrability of `(n : ℝ)`
w.r.t. `poissonMeasure r`. -/
lemma summable_pow_div_factorial_mul_nat (r : ℝ) :
    Summable fun n : ℕ => r ^ n / (n.factorial : ℝ) * (n : ℝ) := by
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ))
            = fun n => r * (r ^ n / (n.factorial : ℝ)) from
      funext (LevyStochCalc.Poisson.Compensated.poisson_term_succ_eq r)]
    exact (Real.summable_pow_div_factorial r).mul_left r
  exact (summable_nat_add_iff 1).mp h_summable_succ
set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Compensated-Poisson mean is zero.** For a measurable set `B` with finite
intensity, `∫ ω, Ñ(B, ω) ∂P = 0`. Follows from `E[N(B)] = ν̂(B)` (Poisson mean,
proved via `poissonMeasure_integral_id`). -/
lemma compensated_mean_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫ ω, N.compensated B ω ∂P = 0 := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  -- compensated B ω = (·.toReal - c) ∘ (N.N · B)
  have h_compensated_eq : (fun ω => N.compensated B ω) =
      (fun x : ℝ≥0∞ => x.toReal - c) ∘ (fun ω => N.N ω B) := by
    funext ω
    rfl
  rw [h_compensated_eq]
  -- Pushforward via integral_map
  rw [show (∫ ω, ((fun x : ℝ≥0∞ => x.toReal - c) ∘ (fun ω => N.N ω B)) ω ∂P)
      = ∫ x, (x.toReal - c) ∂(P.map (fun ω => N.N ω B)) from
    (MeasureTheory.integral_map h_NB_meas.aemeasurable
      (ENNReal.measurable_toReal.sub_const _).aestronglyMeasurable).symm]
  -- Apply poisson_law
  rw [N.poisson_law hB h_finite]
  -- Unfold poissonMeasureENN
  change ∫ x, (x.toReal - c) ∂((ProbabilityTheory.poissonMeasure r).map
    (fun n : ℕ => (n : ℝ≥0∞))) = 0
  rw [MeasureTheory.integral_map measurable_from_nat.aemeasurable
    (ENNReal.measurable_toReal.sub_const _).aestronglyMeasurable]
  -- Simplify the cast (n : ℝ≥0∞).toReal = (n : ℝ)
  have h_phi_cast : ∀ n : ℕ, ((n : ℝ≥0∞)).toReal - c = (n : ℝ) - c := by
    intro n
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp]
  simp_rw [h_phi_cast]
  -- Now goal: ∫ n, (n : ℝ) - c ∂(poissonMeasure r) = 0
  -- Establish integrability of (n : ℝ) w.r.t. poissonMeasure r
  have h_int_id : MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
    rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
      rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
    simp_rw [h_norm]
    have h_eq : ∀ n : ℕ,
        Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
        = Real.exp (-(↑r : ℝ))
          * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
      intro n; ring
    simp_rw [h_eq]
    exact (summable_pow_div_factorial_mul_nat (↑r)).mul_left _
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => c) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  rw [MeasureTheory.integral_sub h_int_id h_int_const]
  rw [LevyStochCalc.Poisson.Compensated.poissonMeasure_integral_id, MeasureTheory.integral_const]
  -- Goal: (↑r : ℝ) - (Measure.real (poissonMeasure r) Set.univ) • c = 0
  rw [show ((ProbabilityTheory.poissonMeasure r).real Set.univ : ℝ) = 1 from by
    rw [MeasureTheory.measureReal_def]
    simp [MeasureTheory.measure_univ]]
  rw [← h_c_eq_r]
  simp
/-- **Per-term reduction for `n²`:** `r^(n+1) / (n+1)! · (n+1)² = r · (n+1) · (r^n / n!)`. -/
 lemma poisson_term_succ_sq_eq (r : ℝ) (n : ℕ) :
    r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
    = r * ((n + 1 : ℕ) : ℝ) * (r ^ n / (n.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
/-- **Summability of `r^n / n! · n²`** for any real `r`. -/
 lemma summable_pow_div_factorial_mul_nat_sq (r : ℝ) :
    Summable fun n : ℕ => r ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2 := by
  have h_split : ∀ n : ℕ,
      r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
      = r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
        + r * (r ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [LevyStochCalc.Poisson.Compensated.poisson_term_succ_sq_eq r]
    push_cast
    ring
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2)
            = fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
              + r * (r ^ n / (n.factorial : ℝ)) from
      funext h_split]
    refine Summable.add ?_ ?_
    · have h_eq : (fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)))
              = fun n : ℕ => r * (r ^ n / (n.factorial : ℝ) * (n : ℝ)) := by
        funext n; ring
      rw [h_eq]
      exact (summable_pow_div_factorial_mul_nat r).mul_left r
    · exact (Real.summable_pow_div_factorial r).mul_left r
  exact (summable_nat_add_iff 1).mp h_summable_succ
set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Series identity:** `∑' n, r^n / n! · n² = (r² + r) · exp(r)`. -/
 lemma tsum_pow_div_factorial_mul_nat_sq (r : ℝ) :
    ∑' n : ℕ, r ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2 = (r ^ 2 + r) * Real.exp r := by
  have h_split : ∀ n : ℕ,
      r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
      = r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
        + r * (r ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [LevyStochCalc.Poisson.Compensated.poisson_term_succ_sq_eq r]
    push_cast
    ring
  have h_summable_n : Summable fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)) := by
    have h_eq : (fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)))
            = fun n : ℕ => r * (r ^ n / (n.factorial : ℝ) * (n : ℝ)) := by
      funext n; ring
    rw [h_eq]
    exact (summable_pow_div_factorial_mul_nat r).mul_left r
  have h_summable_const : Summable fun n : ℕ => r * (r ^ n / (n.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial r).mul_left r
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2)
            = fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
              + r * (r ^ n / (n.factorial : ℝ)) from
      funext h_split]
    exact h_summable_n.add h_summable_const
  rw [tsum_eq_zero_add' h_summable_succ]
  -- 0 term: r^0/0! * 0² = 0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_add]
  simp_rw [h_split]
  rw [Summable.tsum_add h_summable_n h_summable_const]
  -- Goal: (∑' n, r * n * (r^n/n!)) + (∑' n, r * (r^n/n!)) = (r² + r) * exp(r)
  rw [show (fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)))
          = fun n : ℕ => r * (r ^ n / (n.factorial : ℝ) * (n : ℝ)) from by
    funext n; ring]
  rw [tsum_mul_left, LevyStochCalc.Poisson.Compensated.tsum_pow_div_factorial_mul_nat]
  rw [tsum_mul_left]
  have h_exp : ∑' n : ℕ, r ^ n / (n.factorial : ℝ) = Real.exp r := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [h_exp]
  ring
set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Second moment of `poissonMeasure r`:** `∫ n, (n : ℝ)² ∂poissonMeasure r = r² + r`. -/
 lemma poissonMeasure_integral_id_sq (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (r : ℝ) ^ 2 + (r : ℝ) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  have h_smul_eq : ∀ n : ℕ,
      (Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ)) • ((n : ℝ) ^ 2)
      = Real.exp (-(↑r : ℝ))
        * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ) ^ 2) := by
    intro n
    change Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ) ^ 2
        = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ) ^ 2)
    ring
  simp_rw [h_smul_eq]
  rw [tsum_mul_left]
  rw [LevyStochCalc.Poisson.Compensated.tsum_pow_div_factorial_mul_nat_sq]
  rw [show Real.exp (-(↑r : ℝ)) * (((↑r : ℝ) ^ 2 + (↑r : ℝ)) * Real.exp (↑r))
        = ((↑r : ℝ) ^ 2 + (↑r : ℝ))
          * (Real.exp (-(↑r : ℝ)) * Real.exp (↑r)) from by ring]
  rw [← Real.exp_add]
  rw [show (-(↑r : ℝ) + (↑r : ℝ)) = 0 from by ring]
  rw [Real.exp_zero, mul_one]
/-- Integrability of `(n : ℝ)` w.r.t. `poissonMeasure r`. -/
 lemma integrable_id_poissonMeasure (r : ℝ≥0) :
    MeasureTheory.Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
  simp_rw [h_norm]
  have h_eq : ∀ n : ℕ,
      Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
      = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
    intro n; ring
  simp_rw [h_eq]
  exact (summable_pow_div_factorial_mul_nat (↑r)).mul_left _
/-- Integrability of `(n : ℝ)²` w.r.t. `poissonMeasure r`. -/
 lemma integrable_id_sq_poissonMeasure (r : ℝ≥0) :
    MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h_norm : ∀ n : ℕ, ‖((n : ℝ) ^ 2)‖ = (n : ℝ) ^ 2 := fun n => by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg _)
  simp_rw [h_norm]
  have h_eq : ∀ n : ℕ,
      Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)^2
      = Real.exp (-(↑r : ℝ))
        * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)^2) := by
    intro n; ring
  simp_rw [h_eq]
  exact (LevyStochCalc.Poisson.Compensated.summable_pow_div_factorial_mul_nat_sq (↑r)).mul_left _
set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Variance of `poissonMeasure r`:** `∫ n, ((n:ℝ) − r)² ∂poissonMeasure r = r`.
Mean `r`, second moment `r²+r`, variance `(r²+r) − r² = r`. -/
 lemma poissonMeasure_variance (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) - (r : ℝ)) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (r : ℝ) := by
  have h_int_n := LevyStochCalc.Poisson.Compensated.integrable_id_poissonMeasure r
  have h_int_nsq := LevyStochCalc.Poisson.Compensated.integrable_id_sq_poissonMeasure r
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => (r : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  have h_int_2rn : MeasureTheory.Integrable
      (fun n : ℕ => 2 * (r : ℝ) * (n : ℝ)) (ProbabilityTheory.poissonMeasure r) :=
    h_int_n.const_mul (2 * (r : ℝ))
  -- Expand (n - r)² = n² - 2rn + r², explicitly stated as ((n² - 2rn) + r²) for additivity.
  have h_expand : ∀ n : ℕ, ((n : ℝ) - (r : ℝ)) ^ 2
      = ((n : ℝ) ^ 2 - 2 * (r : ℝ) * (n : ℝ)) + (r : ℝ) ^ 2 := by
    intro n; ring
  simp_rw [h_expand]
  -- Use integral linearity step-by-step. To avoid Pi.sub_apply matching issues,
  -- compute each integral as a have-hypothesis and combine via calc.
  have h_e_nsq : ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (↑r : ℝ) ^ 2 + (↑r : ℝ) := LevyStochCalc.Poisson.Compensated.poissonMeasure_integral_id_sq r
  have h_e_2rn : ∫ n : ℕ, 2 * (↑r : ℝ) * (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r)
      = 2 * (↑r : ℝ) * (↑r : ℝ) := by
    rw [MeasureTheory.integral_const_mul]
    rw [LevyStochCalc.Poisson.Compensated.poissonMeasure_integral_id]
  have h_e_csq :
      ∫ _ : ℕ, (↑r : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r) = (↑r : ℝ) ^ 2 := by
    rw [MeasureTheory.integral_const]
    rw [show (ProbabilityTheory.poissonMeasure r).real Set.univ = 1 from by
      rw [MeasureTheory.measureReal_def]; simp [MeasureTheory.measure_univ]]
    rw [one_smul]
  -- ∫ ((n² - 2rn) + r²) = ∫ (n² - 2rn) + ∫ r²
  rw [show
      ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ)) + (↑r : ℝ) ^ 2
        ∂(ProbabilityTheory.poissonMeasure r)
      = ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ))
          ∂(ProbabilityTheory.poissonMeasure r)
        + ∫ _ : ℕ, (↑r : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r) from
    MeasureTheory.integral_add (h_int_nsq.sub h_int_2rn) h_int_const]
  -- ∫ (n² - 2rn) = ∫ n² - ∫ 2rn
  rw [show
      ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ))
        ∂(ProbabilityTheory.poissonMeasure r)
      = ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
        - ∫ n : ℕ, 2 * (↑r : ℝ) * (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r) from
    MeasureTheory.integral_sub h_int_nsq h_int_2rn]
  rw [h_e_nsq, h_e_2rn, h_e_csq]
  ring
set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
lemma compensated_second_moment
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫ ω, (N.compensated B ω)^2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν B).toReal := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_meas_phi : Measurable (fun x : ℝ≥0∞ => (x.toReal - c)^2) :=
    (ENNReal.measurable_toReal.sub_const _).pow_const 2
  -- (Ñ(B,ω))² = ((·).toReal - c)² ∘ (N.N · B)
  have h_compensated_sq_eq : (fun ω => (N.compensated B ω)^2) =
      (fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B) := by
    funext ω; rfl
  rw [h_compensated_sq_eq]
  rw [show (∫ ω, ((fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B)) ω ∂P)
      = ∫ x, (x.toReal - c)^2 ∂(P.map (fun ω => N.N ω B)) from
    (MeasureTheory.integral_map h_NB_meas.aemeasurable
      h_meas_phi.aestronglyMeasurable).symm]
  rw [N.poisson_law hB h_finite]
  change ∫ x, (x.toReal - c)^2 ∂((ProbabilityTheory.poissonMeasure r).map
    (fun n : ℕ => (n : ℝ≥0∞))) = c
  rw [MeasureTheory.integral_map measurable_from_nat.aemeasurable
    h_meas_phi.aestronglyMeasurable]
  have h_phi_cast :
      ∀ n : ℕ, (((n : ℝ≥0∞)).toReal - c) ^ 2 = ((n : ℝ) - (r : ℝ)) ^ 2 := by
    intro n
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp, h_c_eq_r]
  simp_rw [h_phi_cast]
  rw [LevyStochCalc.Poisson.Compensated.poissonMeasure_variance r]
  exact h_c_eq_r.symm
/-- **Integrability of `(N.compensated B)²` w.r.t. P.** Follows from pushforward
through `poisson_law` + integrability of `(n − r)²` w.r.t. `poissonMeasure r`. -/
lemma compensated_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => (N.compensated B ω)^2) P := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_meas_phi_sq : Measurable (fun x : ℝ≥0∞ => (x.toReal - c)^2) :=
    (ENNReal.measurable_toReal.sub_const _).pow_const 2
  -- (compensated B)² = ((·).toReal - c)² ∘ (N.N · B). Lift through pushforwards.
  rw [show (fun ω => (N.compensated B ω)^2) =
      (fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B) from rfl]
  -- Step 1: convert Integrable (g ∘ f) P → Integrable g (P.map f) via the iff.
  rw [← MeasureTheory.integrable_map_measure (μ := P) (f := fun ω => N.N ω B)
      h_meas_phi_sq.aestronglyMeasurable h_NB_meas.aemeasurable]
  -- Step 2: replace P.map with poissonMeasureENN via poisson_law.
  rw [N.poisson_law hB h_finite]
  -- Step 3: unfold poissonMeasureENN = (poissonMeasure r).map Nat.cast.
  change MeasureTheory.Integrable (fun x : ℝ≥0∞ => (x.toReal - c)^2)
    ((ProbabilityTheory.poissonMeasure r).map (fun n : ℕ => (n : ℝ≥0∞)))
  -- Step 4: convert Integrable g (μ.map f) → Integrable (g ∘ f) μ.
  rw [MeasureTheory.integrable_map_measure
      (μ := ProbabilityTheory.poissonMeasure r) (f := fun n : ℕ => (n : ℝ≥0∞))
      h_meas_phi_sq.aestronglyMeasurable measurable_from_nat.aemeasurable]
  -- Now goal: Integrable ((fun x => (x.toReal - c)^2) ∘ Nat.cast) (poissonMeasure r)
  -- Simplify (↑n : ℝ≥0∞).toReal = (n : ℝ); use c = (r : ℝ).
  have h_simp : ((fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun n : ℕ => (n : ℝ≥0∞)))
              = fun n : ℕ => ((n : ℝ) - (r : ℝ))^2 := by
    funext n
    change (((n : ℝ≥0∞)).toReal - c)^2 = ((n : ℝ) - (r : ℝ))^2
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp, h_c_eq_r]
  rw [h_simp]
  -- Expand (n - r)² = (n² - 2rn) + r².
  have h_eq : (fun n : ℕ => ((n : ℝ) - (r : ℝ))^2)
            = fun n : ℕ => (((n : ℝ)^2) - (2 * (r : ℝ) * (n : ℝ))) + (r : ℝ)^2 := by
    funext n; ring
  rw [h_eq]
  have h_int_n := LevyStochCalc.Poisson.Compensated.integrable_id_poissonMeasure r
  have h_int_nsq := LevyStochCalc.Poisson.Compensated.integrable_id_sq_poissonMeasure r
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => (r : ℝ)^2) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  have h_int_2rn : MeasureTheory.Integrable
      (fun n : ℕ => 2 * (r : ℝ) * (n : ℝ)) (ProbabilityTheory.poissonMeasure r) :=
    h_int_n.const_mul (2 * (r : ℝ))
  exact (h_int_nsq.sub h_int_2rn).add h_int_const
end Compensated
end Poisson
end LevyStochCalc


