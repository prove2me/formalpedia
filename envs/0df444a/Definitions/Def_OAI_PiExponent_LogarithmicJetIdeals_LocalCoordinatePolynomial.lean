-- Prove2me | Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
-- name    : OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-14T13:45:28.049975+00:00
-- url     : https://prove2.me/theorems/507bedd6-c55c-4b6a-ad24-4114a8ef3357
-- title:
--   Polynomial expressed in truncated logarithmic coordinates
-- statement:
--   Substitutes $1+Y_0$ for the zeroth variable and $c_i+Y_{i+1}$ plus the degree-<$T_i$ truncated logarithm in $Y_0$ for each remaining variable, expressing the polynomial in the local jet coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

namespace OAI.PiExponent.LogarithmicJetIdeals

noncomputable def localCoordinatePolynomial {m : ℕ} (c : Fin m → ℂ)
    (T : Fin m → ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval
    (Fin.cases (1 + MvPolynomial.X 0)
      (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
        Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
          (InterpolationMatrix.truncatedLog (T i)))
    ) P

end OAI.PiExponent.LogarithmicJetIdeals


