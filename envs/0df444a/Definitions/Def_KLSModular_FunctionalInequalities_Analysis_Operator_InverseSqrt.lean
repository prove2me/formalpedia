-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
-- name    : KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:22:33.577817+00:00
-- url     : https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533
-- title:
--   Basis-defined principal inverse square roots
-- statement:
--   `inverseSqrtIn b A` pulls back the canonical continuous-functional-calculus square root of the inverse matrix of $A$ in the orthonormal basis $b$. `inverseSqrt A` uses the standard orthonormal basis of the finite-dimensional real inner-product space; these declarations define the operators but do not themselves state the positivity, inverse, uniqueness, or basis-independence properties described in the module documentation.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Operator.Coordinates
--   import FunctionalInequalities.Analysis.Operator.Positive
--   import Mathlib.Analysis.Calculus.ContDiff.RCLike
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def inverseSqrtIn (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) : E →L[ℝ] E :=
--     operatorOfMatrix b (CFC.sqrt ((operatorMatrix b A)⁻¹))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/Operator/Positive`](https://prove2.me/theorems/24c7879d-566d-4210-a63a-42bb869e1bbc).
--
--   Theorems in source order:
--
--   - [`inverseSqrt_mul_mul_inverseSqrt`](https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a)
--   - [`locallyLipschitz_matrixEntries_sqrt`](https://prove2.me/theorems/5c4697cb-4b3d-46a3-98ab-b78c98b3d26d)
--   - [`locallyLipschitz_inverseSqrt_of_contDiff_ringInverse`](https://prove2.me/theorems/23b7714a-0376-441c-80ce-52e55886211f)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Operator/InverseSqrt.lean) · `FunctionalInequalities.Analysis.Operator.InverseSqrt` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/InverseSqrt.lean#L30-L109 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.InverseSqrt`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Positive
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open scoped MatrixOrder RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The principal (positive) inverse square root of `A` computed in the orthonormal basis `b`: the canonical
matrix `CFC.sqrt` of `(operatorMatrix b A)⁻¹`, pulled back to an operator. -/
def inverseSqrtIn (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  operatorOfMatrix b (CFC.sqrt ((operatorMatrix b A)⁻¹))
/-- The principal inverse square root `A^{-1/2}` (in the standard orthonormal basis; basis independent for
positive units). -/
def inverseSqrt (A : E →L[ℝ] E) : E →L[ℝ] E :=
  inverseSqrtIn (stdOrthonormalBasis ℝ E) A
end Analysis
end FunctionalInequalities


