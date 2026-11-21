-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F000
-- name    : LevyStochCalc_Brownian_VectorItoStopped_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:38:05.370942+00:00
-- url     : https://prove2.me/theorems/45a16441-33ee-4395-bb2f-398e1444583c
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoStopped
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoStopped. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F001
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000

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

/-- The horizon `t` clipped at a stopping time: `t` itself where the time has not been reached,
and the time's value otherwise. -/
noncomputable def clipTime (τ : Ω → WithTop ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if ((t : ℝ) : WithTop ℝ) ≤ τ ω then t else (τ ω).untopD t
variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}

theorem clipTime_of_le (h : ((t : ℝ) : WithTop ℝ) ≤ τ ω) : clipTime τ t ω = t := if_pos h
theorem clipTime_eq_self_of_top (h : τ ω = ⊤) : clipTime τ t ω = t :=
  clipTime_of_le (by rw [h]; exact le_top)
theorem clipTime_eq_min {r : ℝ} (h : τ ω = ((r : ℝ) : WithTop ℝ)) :
    clipTime τ t ω = min t r := by
  rw [clipTime, h]
  by_cases hle : t ≤ r
  · rw [if_pos (by exact_mod_cast hle), min_eq_left hle]
  · rw [if_neg (by exact_mod_cast hle), min_eq_right (le_of_not_ge hle)]
    simp
theorem clipTime_le_self (τ : Ω → WithTop ℝ) (t : ℝ) (ω : Ω) : clipTime τ t ω ≤ t := by
  by_cases hle : ((t : ℝ) : WithTop ℝ) ≤ τ ω
  · exact le_of_eq (clipTime_of_le hle)
  · have hne : τ ω ≠ ⊤ := by
      intro hcon
      exact hle (by rw [hcon]; exact le_top)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [clipTime_eq_min hr.symm]
    exact min_le_left _ _
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


