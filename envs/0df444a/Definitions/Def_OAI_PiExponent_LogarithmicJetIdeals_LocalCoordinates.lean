-- Prove2me | Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
-- name    : OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-15T21:17:15.933467+00:00
-- url     : https://prove2.me/theorems/26447bed-5667-4343-b98b-20c5b5d85e67
-- title:
--   Polynomial in inverse local jet coordinates
-- statement:
--   Substitutes 1+X_0 for the zeroth variable and c_i+X_{i+1}+trunc_{T_i}(log)(X_0) for each successor variable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

namespace OAI.PiExponent.LogarithmicJetIdeals

noncomputable def localCoordinatePolynomial {m : ℕ} (c : Fin m → ℂ)
    (T : Fin m → ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ :=
  let coordinates : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ :=
    Fin.cases (1 + MvPolynomial.X 0) (fun i : Fin m =>
      MvPolynomial.C (c i) + MvPolynomial.X i.succ +
        Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
          (InterpolationMatrix.truncatedLog (T i)))
  MvPolynomial.aeval coordinates P

end OAI.PiExponent.LogarithmicJetIdeals


