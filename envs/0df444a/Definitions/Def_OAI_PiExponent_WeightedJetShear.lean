-- Prove2me | Definitions.Def_OAI_PiExponent_WeightedJetShear
-- name    : OAI_PiExponent_WeightedJetShear
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T16:43:14.75209+00:00
-- url     : https://prove2.me/theorems/a8cff28b-2e59-4676-8e6d-d75f9936b092
-- title:
--   Polynomial shears and their finite weighted coefficient operators
-- statement:
--   The polynomial algebra homomorphism seriesShear fixes X0 and sends each X_(i+1) to X_(i+1) plus the lift of D_i in coordinate zero. The complex linear map weightedShear is its explicit finite coefficient matrix on the strict weighted simplex: its entry at output b and input a is the coefficient of b in the sheared monomial X^a. These definitions require no filtration assumptions; the child theorems impose the hypotheses needed for cancellation and compatibility with series jets.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedSeriesJets

open OAI.PiExponent
open scoped BigOperators

namespace OAI.PiExponent.AdmissibleFormalInterpolation

/-- Polynomial substitution fixing coordinate zero and translating the other coordinates. -/
noncomputable def seriesShear {m : ℕ} (D : Fin m → PowerSeries ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (MvPowerSeries.X 0)
    (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i)))

/-- The finite matrix of a shear on coefficients strictly below the weighted cutoff. -/
noncomputable def weightedShear {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (D : Fin m → PowerSeries ℂ) :
    ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) →ₗ[ℂ]
      ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) := by
  classical
  exact
    { toFun := fun x b =>
        ∑ a : ↥(strictWeightedSimplex (Fin.cases v0 u) H),
          x a * MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
            (seriesShear D
              (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) 1))
      map_add' := by
        intro x y
        funext b
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro z x
        funext b
        simp [smul_eq_mul, Finset.mul_sum, mul_assoc] }

end OAI.PiExponent.AdmissibleFormalInterpolation


