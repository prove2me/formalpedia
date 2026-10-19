-- Prove2me | Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_FiniteLogPullback
-- name    : OAI_PiExponent_AdmissibleFormalInterpolation_FiniteLogPullback
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T12:06:48.714382+00:00
-- url     : https://prove2.me/theorems/dbe01ed9-2a4c-48af-bbf1-f92bbd68813a
-- title:
--   Finite logarithm polynomial pullback
-- statement:
--   The polynomial algebra endomorphism fixes the first variable and subtracts the logarithm's Taylor polynomial of degrees strictly below the cutoff from every later variable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators

namespace OAI.PiExponent.AdmissibleFormalInterpolation

noncomputable def finiteLogPullback {m : ℕ} (T : ℕ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ]
      MvPolynomial (Fin (m + 1)) ℂ :=
  let correction : MvPolynomial (Fin (m + 1)) ℂ :=
    ∑ k ∈ Finset.range T,
      (if k = 0 then 0 else
        (((-1 : ℂ) ^ (k + 1)) / (k : ℂ)) •
          (MvPolynomial.X 0 - 1) ^ k)
  MvPolynomial.aeval
    (Fin.cases (MvPolynomial.X 0)
      (fun i => MvPolynomial.X i.succ - correction))

end OAI.PiExponent.AdmissibleFormalInterpolation


