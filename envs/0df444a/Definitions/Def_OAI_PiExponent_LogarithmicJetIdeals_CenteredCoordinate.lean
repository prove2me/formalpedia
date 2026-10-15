-- Prove2me | Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_CenteredCoordinate
-- name    : OAI_PiExponent_LogarithmicJetIdeals_CenteredCoordinate
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-15T06:06:24.242984+00:00
-- url     : https://prove2.me/theorems/51533597-9fbd-46b2-b2b6-0fef7168710c
-- title:
--   Centered polynomial coordinates for logarithmic jets
-- statement:
--   Defines polynomial coordinates whose logarithmic jets have zero constant terms and identity linear coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Equiv

namespace OAI.PiExponent.LogarithmicJetIdeals

noncomputable def centeredCoordinate {m : Nat} (center : Fin m → Complex) :
    Fin (m + 1) → MvPolynomial (Fin (m + 1)) Complex :=
  Fin.cases (MvPolynomial.X 0 - MvPolynomial.C 1)
    (fun i => MvPolynomial.X i.succ - MvPolynomial.C (center i) -
      (MvPolynomial.X 0 - MvPolynomial.C 1))

end OAI.PiExponent.LogarithmicJetIdeals


