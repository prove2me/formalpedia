-- Prove2me | Definitions.Def_Freiman_perronArithmetic
-- name    : Freiman_perronArithmetic
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:44:32.314725+00:00
-- url     : https://prove2.me/theorems/eaeca3b7-3903-4d89-91ef-1f35faef4fd6
-- title:
--   Arithmetic witnesses used by Perron’s comparison
-- statement:
--   The nearest-integer numerator is chosen by rounding down q ξ+1/2. Its rational quotient has Mathlib’s reduced positive denominator. These are witnesses used in the report’s reduction of a nearest rational approximation; they do not replace integerDistance or approximationValue.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §§1.1–1.3

import Definitions.Def_Freiman_continuants
import Definitions.Def_Freiman_lagrangeSpectrum

namespace Freiman

noncomputable def nearestNumerator (ξ : ℝ) (q : ℕ) : ℤ :=
  Int.floor ((q : ℝ) * ξ + 1 / 2)
noncomputable def reducedApproximation (ξ : ℝ) (q : ℕ) : ℚ :=
  (nearestNumerator ξ q : ℚ) / (q : ℚ)
noncomputable def reducedApproximationDenominator (ξ : ℝ) (q : ℕ) : ℕ :=
  (reducedApproximation ξ q).den

end Freiman


