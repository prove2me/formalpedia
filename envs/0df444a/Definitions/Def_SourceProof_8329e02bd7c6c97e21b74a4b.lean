-- Prove2me | Definitions.Def_SourceProof_8329e02bd7c6c97e21b74a4b
-- name    : SourceProof_8329e02bd7c6c97e21b74a4b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:02:06.577837+00:00
-- url     : https://prove2.me/theorems/341c201b-83b6-46a3-9ec6-de084f1a3cfc
-- title:
--   LevyStochCalc source module: SourceProof_8329e02bd7c6c97e21b74a4b
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_factor_increment_sq` comes from the `LevyStochCalc.Brownian.ItoL2CompletionConvergence` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F003

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


theorem _root_.Prove2MeSourceProof.h_8329e02bd7c6c97e21b74a4b
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a)
      (hab : a < b)
    {g : Ω → ℝ}
    (hg_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g) :
    ∫ ω, g ω * (W.W b ω - W.W a ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * (b - a) := by
  set ΔW : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔW
  have hΔW_meas : Measurable ΔW := (W.measurable_eval b).sub (W.measurable_eval a)
  have hg_m : Measurable g :=
    (hg_meas.mono (ℱ.le a)).measurable
  -- IndepFun g ΔW
  have h_indep_F := hℱ.indep ha hab
  have hg_comap_le : MeasurableSpace.comap g inferInstance ≤ ℱ a :=
    hg_meas.measurable.comap_le
  have h_indep_g_ΔW : ProbabilityTheory.IndepFun g ΔW P := by
    rw [ProbabilityTheory.IndepFun_iff]; intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F
    exact h_indep_F u v (hg_comap_le u hu) hv
  have h_indep_g_ΔWsq : ProbabilityTheory.IndepFun g (fun ω => (ΔW ω) ^ 2) P := by
    have := h_indep_g_ΔW.comp measurable_id (measurable_id.pow_const 2)
    simpa [Function.comp_def] using this
  rw [show (fun ω => g ω * (W.W b ω - W.W a ω) ^ 2) = g * (fun ω => (ΔW ω) ^ 2) from rfl,
    h_indep_g_ΔWsq.integral_mul_eq_mul_integral hg_m.aestronglyMeasurable
    ((hΔW_meas.pow_const 2).aestronglyMeasurable), LevyStochCalc.Brownian.Ito.brownian_incr_sq_integral W ha hab]
end LevyStochCalc.Brownian.Ito


