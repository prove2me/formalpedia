-- Prove2me | Definitions.Def_SourceProof_6be12e51c788a72f4de041a3
-- name    : SourceProof_6be12e51c788a72f4de041a3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:01:06.024212+00:00
-- url     : https://prove2.me/theorems/9d888490-f21f-49e8-9a39-30ba2813c862
-- title:
--   LevyStochCalc source module: SourceProof_6be12e51c788a72f4de041a3
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_eLpNorm_one_sq_sub` comes from the `LevyStochCalc.Brownian.ItoL2CompletionConvergence` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000

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


theorem _root_.Prove2MeSourceProof.h_6be12e51c788a72f4de041a3
    {μ : MeasureTheory.Measure Ω} {ι : Type*} {l : Filter ι} {a : ι → Ω → ℝ} {b : Ω → ℝ}
    (ha : ∀ n, AEMeasurable (a n) μ) (hb : AEMeasurable b μ)
    (hbfin : MeasureTheory.eLpNorm b 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ)
      l (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ)
      l (nhds 0) := by
  have hbound : ∀ n, MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ
      ≤ MeasureTheory.eLpNorm (a n - b) 2 μ
        * (MeasureTheory.eLpNorm (a n - b) 2 μ + 2 * MeasureTheory.eLpNorm b 2 μ) := by
    intro n
    have hfac : (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) = (a n - b) * (a n + b) := by
      funext ω; simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]; ring
    rw [hfac]
    refine le_trans (LevyStochCalc.Brownian.Ito.eLpNorm_one_mul_le ((ha n).sub hb) ((ha n).add hb)) ?_
    gcongr
    calc MeasureTheory.eLpNorm (a n + b) 2 μ
        = MeasureTheory.eLpNorm ((a n - b) + (2 : ℝ) • b) 2 μ := by
          congr 1; funext ω; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
            smul_eq_mul]; ring
      _ ≤ MeasureTheory.eLpNorm (a n - b) 2 μ + MeasureTheory.eLpNorm ((2 : ℝ) • b) 2 μ :=
          MeasureTheory.eLpNorm_add_le ((ha n).sub hb).aestronglyMeasurable
            (hb.aestronglyMeasurable.const_smul (2 : ℝ)) (by norm_num)
      _ ≤ MeasureTheory.eLpNorm (a n - b) 2 μ + 2 * MeasureTheory.eLpNorm b 2 μ := by
          gcongr
          refine le_trans MeasureTheory.eLpNorm_const_smul_le (le_of_eq ?_)
          rw [show ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) from by simp [Real.enorm_eq_ofReal_abs]]
  have htend_bound : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ
        * (MeasureTheory.eLpNorm (a n - b) 2 μ + 2 * MeasureTheory.eLpNorm b 2 μ))
      l (nhds 0) := by
    have h1 := htend.add (tendsto_const_nhds (x := 2 * MeasureTheory.eLpNorm b 2 μ))
    have h2C : (2 : ℝ≥0∞) * MeasureTheory.eLpNorm b 2 μ ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hbfin
    have := ENNReal.Tendsto.mul htend (Or.inr (by simpa using h2C)) h1
      (Or.inr (by norm_num))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend_bound
    (fun _ => bot_le) hbound
end LevyStochCalc.Brownian.Ito


