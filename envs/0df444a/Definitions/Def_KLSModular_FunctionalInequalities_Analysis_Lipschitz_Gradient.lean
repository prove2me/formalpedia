-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Lipschitz_Gradient
-- name    : KLSModular_FunctionalInequalities_Analysis_Lipschitz_Gradient
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:17:15.224855+00:00
-- url     : https://prove2.me/theorems/c121ae0a-019e-498c-bab1-b5d194574dc8
-- title:
--   Gradient and Lipschitz derivative estimates
-- statement:
--   For a real-valued function on a complete real inner-product space, `norm_gradient_eq_norm_fderiv` identifies the norm of the gradient with the operator norm of the Fréchet derivative, and `norm_gradient_le_of_lipschitz` bounds it by a Lipschitz constant when the function is `LipschitzWith`. The theorem `gradient_eq_of_hasFDerivAt` identifies the gradient at a point with the inverse Riesz image of a specified continuous linear derivative.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Calculus.Gradient.Basic
--   import Mathlib.Analysis.Calculus.ContDiff.RCLike
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   import Mathlib.Analysis.Calculus.MeanValue
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   theorem norm_gradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
--       ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
--     LinearIsometryEquiv.norm_map _ _
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`exists_lipschitzWith_neg_add_comp_gradient`](https://prove2.me/theorems/e0b4ed2f-da69-4e68-a1df-7fa0bdfaa735)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Lipschitz/Gradient.lean) · `FunctionalInequalities.Analysis.Lipschitz.Gradient` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Lipschitz/Gradient.lean#L50-L60 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Lipschitz.Gradient`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Lipschitz_Gradient`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
noncomputable section
open Filter Topology
open scoped ContDiff ENNReal
namespace FunctionalInequalities
namespace Energy
namespace Euclidean
namespace LipschitzApproximation
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
theorem norm_gradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  LinearIsometryEquiv.norm_map _ _
theorem norm_gradient_le_of_lipschitz {K : NNReal} {f : E → ℝ} (hf : LipschitzWith K f) (x : E) :
    ‖gradient f x‖ ≤ K := by
  rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hf
theorem gradient_eq_of_hasFDerivAt {f : E → ℝ} {L : E →L[ℝ] ℝ} {x : E} (h : HasFDerivAt f L x) :
    gradient f x = (InnerProductSpace.toDual ℝ E).symm L :=
  (hasFDerivAt_iff_hasGradientAt.mp h).gradient
end Gradient
end LipschitzApproximation
end Euclidean
end Energy
end FunctionalInequalities


