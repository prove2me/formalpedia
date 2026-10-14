-- Prove2me | Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
-- name    : OAI_PiExponent_TruncatedPolynomialJets
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-13T05:04:28.141426+00:00
-- url     : https://prove2.me/theorems/846319f2-d18e-43cb-b5ff-1dc12efe5317
-- title:
--   Polynomial jets and coefficient packets for the truncated logarithm
-- statement:
--   The polynomial jet substitutes 1+X₀ for the first variable and cᵢ+Xᵢ₊₁ plus the truncated logarithm for each remaining variable. Its packet collects the resulting coefficients at centers jr and the target row indices.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

noncomputable section

namespace OAI.PiExponent.FormalInterpolation

def truncatedPolynomialJet {m : Nat} (c : Fin m → Complex) (T : Fin m → Nat) :
    MvPolynomial (Fin (m + 1)) Complex →ₐ[Complex]
      MvPolynomial (Fin (m + 1)) Complex :=
  MvPolynomial.aeval (Fin.cases (1 + MvPolynomial.X 0)
    (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
      Polynomial.aeval (MvPolynomial.X 0) (InterpolationMatrix.truncatedLog (T i))))

def truncatedPolynomialPacket {m : Nat} (K : Nat) (v0 theta : Real)
    (w : Fin m → Real) (H : Real) (r : Fin m → Complex) (T : Fin m → Nat)
    (P : MvPolynomial (Fin (m + 1)) Complex) :
    InterpolationMatrix.Row K v0 theta w H → Complex :=
  fun rho => (truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T P).coeff
    (InterpolationMatrix.exponentVector rho.2.val)

end OAI.PiExponent.FormalInterpolation


