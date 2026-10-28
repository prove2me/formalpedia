-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:22:23.587985+00:00
-- url     : https://prove2.me/theorems/bcd328b5-2d4f-467f-9a61-fa515af4f15b
-- title:
--   Coordinate-tensor relabelling
-- statement:
--   The private definition `recast` relabels the index positions of a coordinate tensor when natural numbers $N$ and $N'$ are identified by an equality $h : N = N'$. For a tensor $A : \mathrm{Coord}(n,N)$, it produces an element of $\mathrm{Coord}(n,N')$ by precomposing $A$ with `Fin.cast h` and representing the resulting function in the $L^2$ space using `WithLp.toLp 2`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor
--   import FunctionalInequalities.KLS.BKL.PoissonIterate.Symmetry
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private def recast {N' : ℕ} (h : N = N') (A : Coord n N) : Coord n N' :=
--     WithLp.toLp 2 fun J => A (J ∘ Fin.cast h)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/PoissonIterate/Taylor`](https://prove2.me/theorems/4a314a0c-259a-4368-99cf-b24123869fe0), [`KLS/BKL/PoissonIterate/Symmetry`](https://prove2.me/theorems/39390486-c6df-45a6-82e9-cb779c8b05f8).
--
--   Theorems in source order:
--
--   - [`norm_symmetrize_taylorField_grad0_iter_sq_le`](https://prove2.me/theorems/de3c1c47-ae18-4799-bd2e-86a2b7358227)
--   - [`norm_taylorField_grad0_iter_sq_le`](https://prove2.me/theorems/d70ec743-efb5-4716-8d35-79b1b1891737)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/TaylorRecursion.lean) · `FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/TaylorRecursion.lean#L163-L165 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.TaylorRecursion`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_TaylorRecursion`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Symmetry

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ContDiff
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace PoissonIterate
section Coordinates
variable {n N : ℕ}
/-- Relabelling the index positions of a coordinate tensor along `N = N'`. -/
 def recast {N' : ℕ} (h : N = N') (A : Coord n N) : Coord n N' :=
  WithLp.toLp 2 fun J => A (J ∘ Fin.cast h)
end Coordinates
end PoissonIterate
end LogConcave
end KLS
end FunctionalInequalities


