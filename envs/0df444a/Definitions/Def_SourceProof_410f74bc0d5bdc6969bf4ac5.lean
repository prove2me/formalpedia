-- Prove2me | Definitions.Def_SourceProof_410f74bc0d5bdc6969bf4ac5
-- name    : SourceProof_410f74bc0d5bdc6969bf4ac5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:58:51.112507+00:00
-- url     : https://prove2.me/theorems/f71a1662-36bb-4536-9da9-a970e9a7398e
-- title:
--   LevyStochCalc source module: SourceProof_410f74bc0d5bdc6969bf4ac5
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_sq_increment_eq_of_martingale` comes from the `LevyStochCalc.Brownian.ItoL2CompletionConvergence` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_410f74bc0d5bdc6969bf4ac5
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    ∫ ω, (M t ω - M s ω) ^ 2 ∂P
      = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by
  have hm : ℱ s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hcr : MeasureTheory.Integrable (fun ω => M s ω * M t ω) P :=
    hMs.integrable_mul hMt
  -- cross term: `∫ M s · M t = ∫ (M s)²` via pull-out + martingale identity.
  have h_cross : ∫ ω, M s ω * M t ω ∂P = ∫ ω, (M s ω) ^ 2 ∂P := by
    have h_pull : P[(fun ω => M s ω * M t ω) | ℱ s]
        =ᵐ[P] fun ω => M s ω * P[M t | ℱ s] ω := by
      have := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := ℱ s) (hmart.stronglyAdapted s) hcr (hmart.integrable t)
      exact this
    calc ∫ ω, M s ω * M t ω ∂P
        = ∫ ω, P[(fun ω => M s ω * M t ω) | ℱ s] ω ∂P :=
          (MeasureTheory.integral_condExp hm).symm
      _ = ∫ ω, M s ω * P[M t | ℱ s] ω ∂P := integral_congr_ae h_pull
      _ = ∫ ω, M s ω * M s ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hmart.condExp_ae_eq hst] with ω hω using by rw [hω]
      _ = ∫ ω, (M s ω) ^ 2 ∂P := by simp_rw [pow_two]
  have hMt2 : MeasureTheory.Integrable (fun ω => (M t ω) ^ 2) P := hMt.integrable_sq
  have hMs2 : MeasureTheory.Integrable (fun ω => (M s ω) ^ 2) P := hMs.integrable_sq
  calc ∫ ω, (M t ω - M s ω) ^ 2 ∂P
      = ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_)); ring
    _ = (∫ ω, (M t ω) ^ 2 ∂P) - 2 * (∫ ω, M s ω * M t ω ∂P) + ∫ ω, (M s ω) ^ 2 ∂P := by
        have e1 : ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P
            = (∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P) + ∫ ω, (M s ω) ^ 2 ∂P :=
          integral_add (hMt2.sub (hcr.const_mul 2)) hMs2
        have e2 : ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P
            = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, 2 * (M s ω * M t ω) ∂P :=
          integral_sub hMt2 (hcr.const_mul 2)
        have e3 : ∫ ω, 2 * (M s ω * M t ω) ∂P = 2 * ∫ ω, M s ω * M t ω ∂P :=
          integral_const_mul 2 _
        rw [e1, e2, e3]
    _ = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by rw [h_cross]; ring
end LevyStochCalc.Brownian.Ito


