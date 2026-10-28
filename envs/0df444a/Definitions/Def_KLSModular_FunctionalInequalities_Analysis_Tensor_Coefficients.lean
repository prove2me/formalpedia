-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients
-- name    : KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:19:51.423638+00:00
-- url     : https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f
-- title:
--   Coordinate coefficients of multilinear maps
-- statement:
--   Given an orthonormal basis $b$ of an $n$-dimensional real inner-product space $E$ and a continuous real $k$-linear map $\Phi$, `coordTensor b Φ` is the element of `Coord n k` whose coordinate at $(i_1,\ldots,i_k)$ is $\Phi(b(i_1),\ldots,b(i_k))$. It packages the coefficient array of the multilinear map in the chosen basis; no additional equality or norm theorem is declared in this bundle.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Tensor.Coordinate
--   import FunctionalInequalities.Analysis.Tensor.Multilinear
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def coordTensor {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
--       (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) : Coord n k :=
--     WithLp.toLp 2 fun i => Φ (fun j => b (i j))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`Analysis/Tensor/Multilinear`](https://prove2.me/theorems/95acd8c3-b570-4032-a49b-c00dac41b021).
--
--   Theorems in source order:
--
--   - [`apply_eq_sum_coordTensor`](https://prove2.me/theorems/8f695d42-8d17-42ff-8947-34303d3bbf9f)
--   - [`norm_coordTensor_le`](https://prove2.me/theorems/fe64a874-0aad-495c-87d8-2d0977852b27)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Coefficients.lean) · `FunctionalInequalities.Analysis.Tensor.Coefficients` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coefficients.lean#L25-L29 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coefficients`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Multilinear

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


