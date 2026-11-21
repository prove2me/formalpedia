-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000
-- name    : LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:34:43.456154+00:00
-- url     : https://prove2.me/theorems/4f4b3484-5c72-4885-a195-008a98ce762c
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

/-- **L²-convergence ⇒ L¹-convergence** (probability measure). The `L¹` seminorm
is dominated by the `L²` seminorm when `μ` is a probability measure, so an
`L²`-null sequence is `L¹`-null. Bridges the `L²`-Cauchy approximating sequence
(`cauchySeq_simpleIntegralLp_brownian`) to the `L¹` hypothesis of
`martingale_of_tendsto_eLpNorm_one`. -/
lemma tendsto_eLpNorm_one_of_eLpNorm_two
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {g : ℕ → Ω → ℝ} (hg : ∀ n, MeasureTheory.AEStronglyMeasurable (g n) μ)
    (h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (g n) 2 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (g n) 1 μ)
      Filter.atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun _ => bot_le)
    (fun n => MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hg n))
/-- **L² Hölder product.** `‖f·g‖₁ ≤ ‖f‖₂·‖g‖₂` (Cauchy–Schwarz). The
conjunct-2 (quadratic-variation) limit needs `aₙ²→a²` in `L¹` from `aₙ→a` in
`L²`, via `aₙ²−a² = (aₙ−a)(aₙ+a)` and this bound. -/
lemma eLpNorm_one_mul_le {μ : MeasureTheory.Measure Ω} {f g : Ω → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    MeasureTheory.eLpNorm (f * g) 1 μ
      ≤ MeasureTheory.eLpNorm f 2 μ * MeasureTheory.eLpNorm g 2 μ := by
  have hpq : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
  calc ∫⁻ x, ‖(f * g) x‖ₑ ∂μ
      = ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ := by
        refine lintegral_congr (fun x => ?_); rw [Pi.mul_apply, enorm_mul]
    _ ≤ (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
        * (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.enorm hg.enorm
    _ = MeasureTheory.eLpNorm f 2 μ * MeasureTheory.eLpNorm g 2 μ := by
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
            MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
        norm_num
end LevyStochCalc.Brownian.Ito


