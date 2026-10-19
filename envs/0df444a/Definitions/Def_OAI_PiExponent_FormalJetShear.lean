-- Prove2me | Definitions.Def_OAI_PiExponent_FormalJetShear
-- name    : OAI_PiExponent_FormalJetShear
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T11:57:57.466376+00:00
-- url     : https://prove2.me/theorems/a2f2d70b-4535-4231-a5ac-40ea1b97c9a5
-- title:
--   Formal univariate shears and their finite packet coefficient matrices
-- statement:
--   Given univariate formal series δᵢ, define the polynomial-to-series substitution
--
--   $$X_0\mapsto X_0,\qquad X_{i+1}\mapsto X_{i+1}+\delta_i(X_0).$$
--
--   For a finite exponent set S and K packets, its finite packet coefficient matrix has entry equal to the target monomial coefficient of the substituted source monomial when packet indices agree, and zero otherwise. These definitions apply to arbitrary finite exponent sets and arbitrary complex formal series.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

namespace OAI.PiExponent.AdmissibleFormalInterpolation

/-- The polynomial-to-series shear fixing the zeroth variable and adding a
univariate series in that variable to each remaining variable. -/
noncomputable def formalShear {m : ℕ} (delta : Fin m → PowerSeries ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (MvPowerSeries.X 0)
    (fun i => MvPowerSeries.X i.succ + liftLogSeries m (delta i)))

/-- The finite coefficient matrix of a shear, acting separately on each packet.
The set of retained exponents need not be closed under taking divisors. -/
noncomputable def finitePacketShearMatrix {m : ℕ} (K : ℕ)
    (S : Finset (Fin (m + 1) → ℕ)) (delta : Fin m → PowerSeries ℂ) :
    Matrix (Fin K × ↥S) (Fin K × ↥S) ℂ :=
  fun rho sigma =>
    if rho.1 = sigma.1 then
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
        (formalShear delta
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector sigma.2.val) 1))
    else 0

end OAI.PiExponent.AdmissibleFormalInterpolation


