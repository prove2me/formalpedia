-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
-- name    : KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:54:05.422992+00:00
-- url     : https://prove2.me/theorems/feae233d-d547-4d24-bbcb-d30b77cdbfdc
-- title:
--   Coordinate operator matrices and tensor energy form
-- statement:
--   `stdMatrix H` is the matrix of a continuous operator $H$ on $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$ in the standard basis, with entries $\langle e_i,H e_k\rangle$. `energyForm A T` is the coordinate expression $\sum_{J,J'}T_JT_{J'}\prod_s\langle e_{J_s},A^{-1}e_{J'_s}\rangle$, where `Ring.inverse A` is the operator-algebra inverse and $T$ has order $r$. It represents the quadratic form induced by applying the inverse of $A$ in every tensor slot.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L19-L27 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
open Matrix
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace CoordinateTensor
variable {n r : ℕ}
/-- The matrix of an operator on `ℝⁿ` in the standard basis: `(stdMatrix H) i k = ⟪e_i, H e_k⟫`. -/
def stdMatrix (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
/-- The energy form `F(A, T) = ⟨T, (A⁻¹)^{⊗r} T⟩ = Σ_{J,J'} T_J T_{J'} Π_s ⟪e_{J_s}, A⁻¹ e_{J'_s}⟫` of BKL
arXiv:2610.05474v1, p. 22 (`A⁻¹ = Ring.inverse A`, the canonical inverse of the operator algebra). -/
def energyForm (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (T : (Fin r → Fin n) → ℝ) : ℝ :=
  ∑ J : Fin r → Fin n, ∑ J' : Fin r → Fin n, T J * T J' *
    ∏ s, ⟪EuclideanSpace.basisFun (Fin n) ℝ (J s), Ring.inverse A (EuclideanSpace.basisFun (Fin n) ℝ (J' s))⟫
end CoordinateTensor
end Analysis
end FunctionalInequalities


