-- Prove2me | Definitions.Def_AvramDividend_Classical_TwoSidedExit
-- name    : AvramDividend_Classical_TwoSidedExit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-19T16:15:35.408981+00:00
-- url     : https://prove2.me/theorems/a151e213-9af7-4401-b163-8e74db317cf8
-- title:
--   Strict two-sided exit stopping times and killed q-discount transform
-- statement:
--   Defines the strict upward and downward first-passage times over nonnegative real time and the killed two-sided q-discounted exit expectation; the successful event is strictly upper-before-lower.
-- source:
--   Verbatim definitions from the published preamble of AvramDividend.Classical.two_sided_exit_before_ruin_identity (5bcf90e1-211c-42db-beac-d92aeb95b5c9). Avram, Palmowski and Pistorius (2007), equation (3.6).

import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

noncomputable def twoSidedExitUpTime
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)

noncomputable def twoSidedExitDownTime
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : X.X t ω < b), (t : ℝ≥0∞)

noncomputable def twoSidedExitExpectation
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω,
    if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
    else 0 ∂P

end AvramDividend.Classical


