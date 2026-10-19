-- Prove2me | Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
-- name    : OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T12:30:35.736719+00:00
-- url     : https://prove2.me/theorems/6da7f046-f93c-4567-a6e8-826e1dc35a28
-- title:
--   Polynomial formal jet with truncated logarithms
-- statement:
--   Polynomial evaluation into multivariate formal power series, sending the zeroth variable to one plus the zeroth formal variable, and every remaining variable to its center plus its formal variable plus the lifted logarithm truncated strictly below its specified order.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

namespace OAI.PiExponent.AdmissibleFormalInterpolation

/-- The formal jet obtained by using the logarithm truncated strictly below each specified order. -/
noncomputable def truncatedFormalJet {m : ℕ} (T : Fin m → ℕ)
    (c : Fin m → ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
    (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
      liftLogSeries m (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ)))

end OAI.PiExponent.AdmissibleFormalInterpolation


