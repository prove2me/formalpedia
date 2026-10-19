-- Prove2me | Definitions.Def_OAI_PiExponent_ColumnCombination
-- name    : OAI_PiExponent_ColumnCombination
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-16T12:47:09.08478+00:00
-- url     : https://prove2.me/theorems/69eaf5a8-8873-4b92-a681-458f7a1472ba
-- title:
--   Finite polynomial combination of interpolation columns
-- statement:
--   The first definition turns a column’s function-valued exponent into the finitely supported exponent used by `MvPolynomial.monomial`. The second forms the finite sum of those monomials weighted by the supplied coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedSeriesJets

open scoped BigOperators

namespace OAI.PiExponent.AdmissibleFormalInterpolation

noncomputable def columnMonomial {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (c : InterpolationMatrix.Column w0 w H) : MvPolynomial (Fin (m + 1)) ℂ :=
  MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) 1

noncomputable def columnCombination {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (x : InterpolationMatrix.Column w0 w H → ℂ) : MvPolynomial (Fin (m + 1)) ℂ := by
  classical
  exact ∑ c : InterpolationMatrix.Column w0 w H, MvPolynomial.C (x c) * columnMonomial w0 w H c

end OAI.PiExponent.AdmissibleFormalInterpolation


