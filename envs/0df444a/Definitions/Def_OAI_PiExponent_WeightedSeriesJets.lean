-- Prove2me | Definitions.Def_OAI_PiExponent_WeightedSeriesJets
-- name    : OAI_PiExponent_WeightedSeriesJets
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T12:30:39.911117+00:00
-- url     : https://prove2.me/theorems/1c4cca5e-9ff0-433c-b3a9-d239014cd5d8
-- title:
--   Formal series substitutions and weighted jet coefficients
-- statement:
--   Generalize formalJet by substituting an arbitrary univariate series F_i in each nonzero coordinate, then retain coefficients in the strict weighted simplex. Taking every F_i to be the formal logarithm recovers the coefficients used by packetMap.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

noncomputable def OAI.PiExponent.AdmissibleFormalInterpolation.seriesJet
    {m : ℕ} (c : Fin m → ℂ) (F : Fin m → PowerSeries ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
    (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
      OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries m (F i)))

noncomputable def OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (c : Fin m → ℂ) (F : Fin m → PowerSeries ℂ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    (↥(OAI.PiExponent.strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ :=
  fun b => MvPowerSeries.coeff
    (OAI.PiExponent.InterpolationMatrix.exponentVector b.val)
    (OAI.PiExponent.AdmissibleFormalInterpolation.seriesJet c F P)


