-- Prove2me | Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
-- name    : AvramDividend_Classical_TwoSidedExitCorrected
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-07T21:13:09.255576+00:00
-- url     : https://prove2.me/theorems/e8e42ce5-03a3-4ff7-bd29-3067a57464c0
-- title:
--   Corrected two-sided exit times and killed discount expectation
-- source:
--   Avram, Palmowski and Pistorius (2007), equation (3.6), with the upward-before-ruin success event made explicit so infinite passage times contribute zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}

noncomputable def twoSidedExitUpTimeCorrected
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)

noncomputable def twoSidedExitDownTimeCorrected
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : X.X t ω < b), (t : ℝ≥0∞)

noncomputable def twoSidedExitExpectationCorrected
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω,
    if twoSidedExitUpTimeCorrected X (a - x) ω <
        twoSidedExitDownTimeCorrected X (-x) ω then
      ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTimeCorrected X (a - x) ω))))
    else 0 ∂P

end AvramDividend.Classical


