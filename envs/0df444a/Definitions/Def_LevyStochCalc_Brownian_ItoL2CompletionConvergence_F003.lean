-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003
-- name    : LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:37:35.978058+00:00
-- url     : https://prove2.me/theorems/cb5ba46a-ef87-4c68-87c4-3db4f3195278
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionConvergence
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionConvergence. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: `L¹`/`L²` convergence and adapted approximation

Transfer of the martingale property along `L¹`-limits, criteria for `L¹`
convergence of squares from `L²` bounds, the endpoint `L²` bound for differences of
simple integrals, and the existence of an adapted `SimplePredictable` integrand
within a prescribed `L²([0, T] × Ω)` tolerance of a progressively measurable
square-integrable integrand, together with the norm and increment identities they
use.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- `simpleIntegral W H t = 0` for `t ≤ 0` (all increments `W_t − W_t` vanish). -/
lemma simpleIntegral_eq_zero_of_nonpos
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {t : ℝ} (ht : t ≤ 0) (ω : Ω) :
    simpleIntegral W H t ω = 0 := by
  unfold simpleIntegral
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hp1 : 0 ≤ H.partition i.succ := by
    have := H.partition_strictMono.monotone (Fin.zero_le i.succ)
    rwa [H.partition_zero] at this
  have hp2 : 0 ≤ H.partition i.castSucc := by
    have := H.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [H.partition_zero] at this
  rw [min_eq_right (ht.trans hp1), min_eq_right (ht.trans hp2), sub_self, mul_zero]
/-- `∫⁻ ‖g‖₊² = ofReal (∫ g²)` for `g ∈ L²`. -/
lemma lintegral_nnnorm_sq_eq_ofReal_integral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : MeasureTheory.MemLp g 2 P) :
    ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (g ω) ^ 2 ∂P) := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
  refine lintegral_congr (fun ω => ?_)
  rw [show (‖g ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖g ω‖ from (ofReal_norm _).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
/-- `∫ (W_b − W_a)² = b − a` for `0 ≤ a < b`. -/
lemma brownian_incr_sq_integral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P = b - a := by
  have h_meas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [show (∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P)
        = ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => W.W b ω - W.W a ω)) from
      (MeasureTheory.integral_map h_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ 2) _)).symm,
    W.increment_gaussian ha hab]
  exact LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨b - a, by linarith⟩
end LevyStochCalc.Brownian.Ito


