-- Prove2me | Definitions.Def_SourceProof_824bcd558fff0b7dee883334
-- name    : SourceProof_824bcd558fff0b7dee883334
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:40:44.387479+00:00
-- url     : https://prove2.me/theorems/8dc01190-9fe0-427d-8689-671043317973
-- title:
--   LevyStochCalc source module: SourceProof_824bcd558fff0b7dee883334
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.le_clipTime_iff` comes from the `LevyStochCalc.Brownian.VectorItoStopped` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a vector Itô process

Cutting the coefficients of a vector Itô process off at a stopping time of finite range leaves a
vector Itô process, whose version is the original one evaluated at the clipped time.

## Main statements

* `LevyStochCalc.Brownian.Ito.clipTime` — the horizon clipped at a stopping time.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip` — the Itô integral of a
  stopped integrand is the integral evaluated at the clipped horizon.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` — the stopped version.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Clip

variable {Ω : Type u}

variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}

theorem _root_.Prove2MeSourceProof.h_824bcd558fff0b7dee883334 {s : ℝ} (hs : s ≤ t) :
    ((s : ℝ) : WithTop ℝ) ≤ τ ω ↔ s ≤ clipTime τ t ω := by
  by_cases hle : ((t : ℝ) : WithTop ℝ) ≤ τ ω
  · rw [LevyStochCalc.Brownian.Ito.clipTime_of_le hle]
    refine ⟨fun _ => hs, fun _ => le_trans (by exact_mod_cast hs) hle⟩
  · have hne : τ ω ≠ ⊤ := by
      intro hcon
      exact hle (by rw [hcon]; exact le_top)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    have hrt : r < t := by
      by_contra hcon
      exact hle (by rw [← hr]; exact_mod_cast le_of_not_gt hcon)
    rw [LevyStochCalc.Brownian.Ito.clipTime_eq_min hr.symm, min_eq_right hrt.le, ← hr]
    exact WithTop.coe_le_coe
end Clip

section StoppedIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsBrownianFiltration W ℱ) (τ : Ω → WithTop ℝ)

end StoppedIntegral

section StoppedDrift

variable {Ω : Type u}

end StoppedDrift

section StoppedVersion

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

end StoppedVersion

end LevyStochCalc.Brownian.Ito


