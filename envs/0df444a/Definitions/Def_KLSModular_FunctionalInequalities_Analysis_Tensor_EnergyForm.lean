-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm
-- name    : KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:02:03.246342+00:00
-- url     : https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e
-- title:
--   Coordinate operator matrices and tensor energy form
-- statement:
--   `stdMatrix H` is the matrix of a continuous operator $H$ on $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$ in the standard basis, with entries $\langle e_i,H e_k\rangle$. `energyForm A T` is the coordinate expression $\sum_{J,J'}T_JT_{J'}\prod_s\langle e_{J_s},A^{-1}e_{J'_s}\rangle$, where `Ring.inverse A` is the operator-algebra inverse and $T$ has order $r$. It represents the quadratic form induced by applying the inverse of $A$ in every tensor slot.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Tensor.SlotAction
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def stdMatrix (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
--     Matrix.of fun i k => ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Tensor/SlotAction`](https://prove2.me/theorems/ac2f7bbd-0bd0-4fc4-b26d-e658d94082e4).
--
--   Theorems in source order:
--
--   - [`contDiffAt_energyForm`](https://prove2.me/theorems/3ecc6a67-dc0c-4de0-aced-f227c0a5133b)
--   - [`sum_mul_prod_delta_erase`](https://prove2.me/theorems/3d2d4761-884a-4e2c-9099-8cbf58b20f0b)
--   - [`slot_derivative_sum`](https://prove2.me/theorems/da9c4569-cbdb-4d97-92a7-3f4b97b10178)
--   - [`hasDerivAt_energyForm_line`](https://prove2.me/theorems/7d3fc6e6-7635-41c8-9e97-877316e76ce3)
--   - [`sum_mul_prod_delta_erase_erase`](https://prove2.me/theorems/76502fa4-2d8b-4cb4-b4ba-234b9fc000dc)
--   - [`fderiv_fderiv_apply_eq_deriv_deriv_line`](https://prove2.me/theorems/91499aa3-4a30-4b4f-af4c-05085add7997)
--   - [`slot_sum_two`](https://prove2.me/theorems/e0d1f1e6-4957-4586-aef5-50f1a34f8224)
--   - [`two_slot_sum`](https://prove2.me/theorems/a6830ee8-1fb6-478d-9a58-968e1fda2c6d)
--   - [`deriv_deriv_energyForm_line`](https://prove2.me/theorems/8ec8d6e9-231a-4f63-b067-a5beeb835aaf)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean) · `FunctionalInequalities.Analysis.Tensor.EnergyForm` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L19-L27 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction

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


