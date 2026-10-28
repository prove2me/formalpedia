-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:23:35.615248+00:00
-- url     : https://prove2.me/theorems/b6210dc1-894e-490a-a262-24735151f6b5
-- title:
--   BKL Taylor-criterion constant
-- statement:
--   The definition `taylorCriterionConstant` is the real constant $100c^2$, where $c = 2^{20}\max(1,3)^2 = 9\cdot 2^{20}$. Thus its value is the explicit universal constant $100\bigl(2^{20}\max(1,3)^2\bigr)^2$ used for the Taylor-coefficient criterion.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.PoissonIterate.Defect
--   import FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.ApproximateEigenfunction
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Curvature
--   import FunctionalInequalities.KLS.LogConcave.Regular.Basic
--   import FunctionalInequalities.Analysis.DyadicSummation
--   import FunctionalInequalities.Analysis.Tensor.BasisChange
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def taylorCriterionConstant : ℝ := 100 * (2 ^ 20 * max 1 3 ^ 2) ^ 2
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/PoissonIterate/Defect`](https://prove2.me/theorems/d0aba350-4ee9-4d0f-afbf-76da9501de4e), [`KLS/BKL/PoissonIterate/TaylorRecursion`](https://prove2.me/theorems/bcd328b5-2d4f-467f-9a61-fa515af4f15b), [`KLS/LogConcave/HeatSemigroup/ApproximateEigenfunction`](https://prove2.me/theorems/c5bf48cd-81f9-4528-8e4e-dd3378a514bf), [`KLS/LogConcave/HeatSemigroup/Curvature`](https://prove2.me/theorems/cf9c6f61-3825-46e6-acd2-1e708f058970), [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342), [`Analysis/DyadicSummation`](https://prove2.me/theorems/358bf73c-21aa-4831-bfb4-1bf819949889), [`Analysis/Tensor/BasisChange`](https://prove2.me/theorems/89846a1e-d28c-484e-94fe-f976ef7e2382).
--
--   Theorems in source order:
--
--   - [`recursion`](https://prove2.me/theorems/29ed27ac-971d-48f4-ba7a-bfb704866cf8)
--   - [`le_of_iterate_bounds`](https://prove2.me/theorems/f80538b2-5d61-41ae-9ced-cdc9bb4e7bf2)
--   - [`norm_taylorField_sq_le`](https://prove2.me/theorems/658d541a-caf2-439c-ac49-7e33a7865643)
--   - [`taylorCriterion`](https://prove2.me/theorems/02b2baa1-1cb3-4817-9e35-5dc605a75700)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean) · `FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Criterion.lean#L367-L369 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Criterion`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Criterion`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Defect
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_ApproximateEigenfunction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Curvature
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_DyadicSummation
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_BasisChange

noncomputable section
open MeasureTheory Filter Topology Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace PoissonIterate
/-- The universal constant of BKL Theorem 3.1 obtained in the operator route: `K = 100 c²` with
`c = 2^20 max(1, 3)² = 9 · 2^20`, the constant of Lemma 3.8 (route statement `J1`) at `β = 3`. -/
def taylorCriterionConstant : ℝ := 100 * (2 ^ 20 * max 1 3 ^ 2) ^ 2
end PoissonIterate
end LogConcave
end KLS
end FunctionalInequalities


