-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionCompensator_F000
-- name    : LevyStochCalc_Brownian_ItoL2CompletionCompensator_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:04:34.378594+00:00
-- url     : https://prove2.me/theorems/e3f7b260-4038-4737-ad21-0840661c7dc0
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionCompensator
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionCompensator. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the compensated square of a simple integral

Weighted off-diagonal vanishing for products of Brownian increments, the clamped
expansion of the square of a difference of simple integrals, and the martingale
property of the compensated square
`(simpleIntegral W H t)² − ∫_{[0, t]} (H.eval u)² du` with respect to the
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- `∫ (W_b − W_a) = 0` for `0 ≤ a < b`. -/
lemma brownian_incr_mean
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ∂P = 0 := by
  have h_meas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [show (∫ ω, (W.W b ω - W.W a ω) ∂P)
        = ∫ x : ℝ, x ∂(P.map (fun ω => W.W b ω - W.W a ω)) from
      (MeasureTheory.integral_map h_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x) _)).symm,
    W.increment_gaussian ha hab]
  exact ProbabilityTheory.integral_id_gaussianReal
/-- **Off-diagonal building block.** For a bounded `ℱ_a`-measurable factor `g`,
`∫ g · (W_b − W_a) = 0` — the increment is centred and independent of `g`. -/
lemma integral_factor_increment_eq_zero
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a)
      (hab : a < b)
    {g : Ω → ℝ}
    (hg_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g) :
    ∫ ω, g ω * (W.W b ω - W.W a ω) ∂P = 0 := by
  set ΔW : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔW
  have hΔW_meas : Measurable ΔW := (W.measurable_eval b).sub (W.measurable_eval a)
  have hg_m : Measurable g :=
    (hg_meas.mono (ℱ.le a)).measurable
  have h_indep_F := hℱ.indep ha hab
  have hg_comap_le : MeasurableSpace.comap g inferInstance ≤ ℱ a :=
    hg_meas.measurable.comap_le
  have h_indep_g_ΔW : ProbabilityTheory.IndepFun g ΔW P := by
    rw [ProbabilityTheory.IndepFun_iff]; intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F
    exact h_indep_F u v (hg_comap_le u hu) hv
  rw [show (fun ω => g ω * (W.W b ω - W.W a ω)) = g * ΔW from rfl,
    h_indep_g_ΔW.integral_mul_eq_mul_integral hg_m.aestronglyMeasurable
      hΔW_meas.aestronglyMeasurable,
    brownian_incr_mean W ha hab, mul_zero]
end LevyStochCalc.Brownian.Ito


