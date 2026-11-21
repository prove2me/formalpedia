-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityLimit_F002
-- name    : LevyStochCalc_Poisson_CompensatedDensityLimit_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:57:39.277656+00:00
-- url     : https://prove2.me/theorems/337cb27e-c5c0-4af7-82d5-38504d671cfa
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cross-resolution Cauchy estimate and the `L²` limit

The isometry for the difference of two step integrals at different dyadic resolutions, the
resulting Cauchy estimate for the Euler sums of a bounded predictable integrand, and the limit
in `L²(P)` it produces. Closing bricks on the regularity of monotone `ℝ≥0∞`-valued functions of
time and the right-continuity of the intensity of shrinking time-mark boxes support the path
regularity of that limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- `eLpNorm g 2 μ ^ (2:ℝ) = ∫⁻ ‖g‖₊²`. -/
lemma eLpNorm_two_rpow_eq_lintegral_sq {P : Measure Ω} (g : Ω → ℝ) :
    MeasureTheory.eLpNorm g 2 P ^ (2 : ℝ) = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := P) (p := (2 : ℝ≥0))
    (f := g) (by norm_num)
  rw [show ((2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
    show ((2 : ℝ≥0) : ℝ) = (2 : ℝ) from by norm_num] at h
  rw [h]; refine lintegral_congr (fun ω => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
/-! ### Path regularity bricks (toward the càdlàg conjunct of #6)

The compensated step integral is càdlàg in `t`: the compensator part is continuous,
and the count part is a Stieltjes function of `t` (monotone, right-continuous with
left limits via measure continuity). These bricks give the right-continuity and
left-limit existence of monotone `ℝ≥0∞`-valued functions, the substrate for the
Doob `L²` càdlàg modification. -/

end LevyStochCalc.Poisson.Compensated


