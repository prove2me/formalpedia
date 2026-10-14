-- Prove2me | Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
-- name    : OAI_PiExponent_AdmissibleFormalInterpolation
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-12T19:56:45.624987+00:00
-- url     : https://prove2.me/theorems/76461acd-f087-4501-9f56-60f650a27e6e
-- title:
--   Weighted polynomial and formal logarithmic packet interface
-- statement:
--   Lift the one-variable formal logarithm into multivariate power series, substitute Z₀ = 1+t and Zᵢ₊₁ = cᵢ+Yᵢ+log(1+t), restrict input polynomials by the original column weights, and extract coefficients indexed by the original strict weighted row domain at centers j·r.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

namespace OAI.PiExponent.AdmissibleFormalInterpolation

noncomputable def liftLogSeries (m : ℕ) :
    PowerSeries ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ :=
  (MvPowerSeries.finSuccEquiv ℂ m).symm.toRingHom.comp
    (PowerSeries.map MvPowerSeries.C)

noncomputable def formalJet {m : ℕ} (c : Fin m → ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
    (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
      liftLogSeries m (PowerSeries.log ℂ)))

def WeightedPolynomial {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  {P : MvPolynomial (Fin (m + 1)) ℂ //
    ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : ℝ) ≤ H}

noncomputable def packetMap {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ)
    (P : WeightedPolynomial w0 w H) :
    InterpolationMatrix.Row K v0 theta w H → ℂ :=
  fun rho => MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
    (formalJet (fun i => (rho.1.val : ℂ) * r i) P.val)

end OAI.PiExponent.AdmissibleFormalInterpolation


