-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:05:51.334012+00:00
-- url     : https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b
-- title:
--   Symmetric average in Euclidean space
-- statement:
--   For $g:\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin} n)\to\mathbb{R}$ and $h,y$ in that space, `n9_average g h y` is the symmetric average $\frac12\bigl(g(y+h)+g(y-h)\bigr)$. It is a private helper in the touching-test and viscosity-inequality development.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import Mathlib.Analysis.Calculus.DerivativeTest
--   import FunctionalInequalities.Analysis.Convex.Alexandrov
--   import FunctionalInequalities.Analysis.Convex.SecondOrder
--   import FunctionalInequalities.Analysis.Matrix.LogDet
--   import Mathlib.Analysis.Calculus.BumpFunction.Convolution
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private def n9_average {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
--       (h y : EuclideanSpace ℝ (Fin n)) : ℝ :=
--     (1 / 2 : ℝ) * (g (y + h) + g (y - h))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905), [`Analysis/Convex/SecondOrder`](https://prove2.me/theorems/25ef7ab1-0f22-4192-9c58-d196bc21f161), [`Analysis/Matrix/LogDet`](https://prove2.me/theorems/4063692a-a203-477a-8815-ef391dc73f51).
--
--   Theorems in source order:
--
--   - [`directional_second_deriv_nonneg`](https://prove2.me/theorems/86f74169-4ea8-4fc0-a5ef-90fee5ab8c8b)
--   - [`posSemidef_hessianMatrix_of_upper_touch`](https://prove2.me/theorems/c0934c18-f16d-42fc-a97b-28fa4ccb6c6d)
--   - [`hessianMatrix_quadratic`](https://prove2.me/theorems/c1a646b2-00af-48f5-80d5-4c01f3dab8bd)
--   - [`local_taylor_two`](https://prove2.me/theorems/4b2efc81-f85a-4a3c-aec5-38e536f55203)
--   - [`le_det_hessianMatrix_of_upper_touch`](https://prove2.me/theorems/6c79ec26-adc7-48d0-89d1-5a5ef657b31d)
--   - [`det_hessianMatrix_le_of_lower_touch`](https://prove2.me/theorems/0a6a663c-c593-49af-8752-569576e141d5)
--   - [`hessianMatrix_quadraticAt`](https://prove2.me/theorems/facc6c9b-040a-4551-a141-72b34dae970f)
--   - [`posDef_and_det_eq_of_quadratic_expansion`](https://prove2.me/theorems/fdeb8c35-d7cf-4a28-9642-da29fd09799b)
--   - [`expansion_secondDifference`](https://prove2.me/theorems/546aab2f-04b5-4802-87d1-3ee07a4c5efe)
--   - [`convolution_hessian_integral`](https://prove2.me/theorems/71cd5614-d749-4ac1-8ee0-bcd17a10ea5c)
--   - [`trace_integral_bound`](https://prove2.me/theorems/d9cb05da-6288-4525-adcd-78dfcf3313ac)
--   - [`posDef_and_convolution_le_log_det_hessianMatrix`](https://prove2.me/theorems/6d69beca-a1f9-48e2-959c-68716a21a551)
--   - [`ae_exists_quadraticAt_expansion`](https://prove2.me/theorems/995efd14-b691-40e5-adc5-c0effdf385d3)
--   - [`exists_penalized_maximum_with_comparison`](https://prove2.me/theorems/511a8bb6-640f-477b-98fa-7c8e07f3450e)
--   - [`ae_hessian_increment_le_generator`](https://prove2.me/theorems/8a32f083-457a-427c-a413-4a9bda9a98fb)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean) · `FunctionalInequalities.Analysis.Convex.Viscosity` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1473-L1475 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Mathlib.Analysis.Calculus.DerivativeTest
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_LogDet
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT17BMaximumWithComparison
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities
namespace Analysis
 def n9_average {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (h y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 2 : ℝ) * (g (y + h) + g (y - h))
end Analysis
end FunctionalInequalities
end LT17BMaximumWithComparison


