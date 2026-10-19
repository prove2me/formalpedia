-- Prove2me | Definitions.Def_OAI_PiExponent_PolynomialLogarithmicJets
-- name    : OAI_PiExponent_PolynomialLogarithmicJets
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T21:57:25.638412+00:00
-- url     : https://prove2.me/theorems/597301e2-27e4-472a-9cb3-836d7af34f99
-- title:
--   Polynomial substitution for truncated logarithmic jets
-- statement:
--   Substitute X₀ by 1+X₀ and each remaining variable by its center plus its jet variable plus the truncated logarithm in X₀. This polynomial substitution sends the corresponding local jet coordinates to the ordinary polynomial variables.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

namespace OAI.PiExponent.LogarithmicJetIdeals

/-- Polynomial substitution inverse to the triangular logarithmic jet coordinates. -/
noncomputable def polynomialJet {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + MvPolynomial.X 0)
    (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
      Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0)
        (InterpolationMatrix.truncatedLog (T i))))

end OAI.PiExponent.LogarithmicJetIdeals


