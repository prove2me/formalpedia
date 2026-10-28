-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
-- name    : KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:08:26.06124+00:00
-- url     : https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34
-- title:
--   Coordinate trace and Hilbert–Schmidt square norm
-- statement:
--   `stdTrace M` is the trace of a continuous operator $M$ on $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$ computed in the standard basis: $\sum_i\langle e_i,Me_i\rangle$. `hsNormSq M` is the squared Hilbert–Schmidt norm $\sum_i\sum_j\langle e_i,Me_j\rangle^2$. Both are real-valued finite sums and require no positivity or symmetry assumption on $M$.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib
--   import Mathlib.Analysis.InnerProductSpace.Trace
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def stdTrace (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
--     ∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, M (EuclideanSpace.basisFun (Fin n) ℝ i)⟫
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`norm_apply_sq_le_hsNormSq_mul`](https://prove2.me/theorems/3aa78c22-bf8d-4c99-aea7-40e318280ade)
--   - [`opNorm_sq_le_hsNormSq`](https://prove2.me/theorems/4e1eeade-d7a1-4e5a-8b0a-e8fcba8ae762)
--   - [`sum_inner_apply_le_sqrt_hsNormSq_mul`](https://prove2.me/theorems/9a0d0118-09fb-42ba-8956-a35ad70bd1c0)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean) · `FunctionalInequalities.Analysis.Operator.HilbertSchmidt` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean#L54-L60 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.HilbertSchmidt`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt`; the repository is private at upload time).

import Mathlib
import Mathlib.Analysis.InnerProductSpace.Trace

noncomputable section
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
variable {n : ℕ}
/-- The coordinate trace `tr M = Σ_i ⟪e_i, M e_i⟫` of an operator on `ℝⁿ`. -/
def stdTrace (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, M (EuclideanSpace.basisFun (Fin n) ℝ i)⟫
/-- The squared Hilbert–Schmidt norm `‖M‖²_HS = Σ_{i,j} ⟪e_i, M e_j⟫²`. -/
def hsNormSq (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ∑ j, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, M (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ ^ 2
end Analysis
end FunctionalInequalities


