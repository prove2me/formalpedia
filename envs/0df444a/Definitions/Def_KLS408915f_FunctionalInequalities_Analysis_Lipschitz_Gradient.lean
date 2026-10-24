-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
-- name    : KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:00:16.548147+00:00
-- url     : https://prove2.me/theorems/806c1f73-853c-4fc5-a178-f8a1cd7dc699
-- title:
--   Gradient and Lipschitz derivative estimates
-- statement:
--   For a real-valued function on a complete real inner-product space, `norm_gradient_eq_norm_fderiv` identifies the norm of the gradient with the operator norm of the Fréchet derivative, and `norm_gradient_le_of_lipschitz` bounds it by a Lipschitz constant when the function is `LipschitzWith`. The theorem `gradient_eq_of_hasFDerivAt` identifies the gradient at a point with the inverse Riesz image of a specified continuous linear derivative.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Lipschitz/Gradient.lean#L50-L60 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Lipschitz.Gradient`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2

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


