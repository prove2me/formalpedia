-- Prove2me | Definitions.Def_AvramDividend_Classical_TwoSidedExitPassage
-- name    : AvramDividend_Classical_TwoSidedExitPassage
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-24T22:50:46.91597+00:00
-- url     : https://prove2.me/theorems/ff9ae739-e742-42f6-8bd5-c0f153a6de03
-- title:
--   Two-sided first-passage times and killed discounted up-exit expectation
-- statement:
--   For a spectrally negative Levy process X: the upward first-passage time of a level b, the downward first-passage time of a level b, and the killed discounted up-exit expectation, i.e. the integral over paths of exp(-q tau_up) on the event that upward passage of a-x precedes downward passage of -x, and 0 otherwise.
-- source:
--   Verbatim extraction of the three inline passage-time definitions from the authoritative preamble of AvramDividend.Classical.two_sided_exit_before_ruin_identity (5bcf90e1), published as an importable module so proof candidates can reference the exact target-level constants (lint-submit raw_target_parse_error remediation).

import Mathlib
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


