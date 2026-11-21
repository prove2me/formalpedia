-- Prove2me | Definitions.Def_SourceProof_3148dc49c4c32cf6b40c23ee
-- name    : SourceProof_3148dc49c4c32cf6b40c23ee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:05:07.689028+00:00
-- url     : https://prove2.me/theorems/7cc35b4b-5287-49cd-b51f-3e50ecd48573
-- title:
--   LevyStochCalc source module: SourceProof_3148dc49c4c32cf6b40c23ee
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.abs_clamp_sub_le` comes from the `LevyStochCalc.Brownian.ItoFourthMomentLintegral` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentPartialSums_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Fourth moment of the `L²` Itô integral

Truncation of a simple integrand and the `lintegral` form of the fourth-moment bound. Clamping
the coefficients to `[-C, C]` (`SimplePredictable.truncate`) moves a value no further from a
target already in `[-C, C]`, so a truncated approximant is still an approximant; the bound for
the simple integrands then passes to the `L²` Itô integral of any integrand bounded by `C` by
Fatou along an almost-everywhere convergent subsequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_3148dc49c4c32cf6b40c23ee {C x y : ℝ} (hC : 0 ≤ C) (hy : |y| ≤ C) :
    |max (-C) (min C x) - y| ≤ |x - y| := by
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  rcases le_or_gt x (-C) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ C), max_eq_left hx,
      abs_of_nonpos (by linarith : -C - y ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · rcases le_or_gt x C with hx' | hx'
    · rw [min_eq_right hx', max_eq_right (by linarith : -C ≤ x)]
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -C ≤ C),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ C - y),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
      linarith
section LintegralForm

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end LintegralForm

end LevyStochCalc.Brownian.Ito


