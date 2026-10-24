-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
-- name    : KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:02:16.823529+00:00
-- url     : https://prove2.me/theorems/ead6ee46-c4d0-4359-889f-836e4f68782a
-- title:
--   Coordinate coefficients of multilinear maps
-- statement:
--   Given an orthonormal basis $b$ of an $n$-dimensional real inner-product space $E$ and a continuous real $k$-linear map $\Phi$, `coordTensor b Φ` is the element of `Coord n k` whose coordinate at $(i_1,\ldots,i_k)$ is $\Phi(b(i_1),\ldots,b(i_k))$. It packages the coefficient array of the multilinear map in the chosen basis; no additional equality or norm theorem is declared in this bundle.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coefficients.lean#L25-L29 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coefficients`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic

noncomputable section
open Finset
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The coefficient array `(Φ (b i₁, …, b i_k))_i` of a real `k`-linear map in an orthonormal
basis `b`. -/
def coordTensor {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) : Coord n k :=
  WithLp.toLp 2 fun i => Φ (fun j => b (i j))
end Tensor
end Analysis
end FunctionalInequalities


