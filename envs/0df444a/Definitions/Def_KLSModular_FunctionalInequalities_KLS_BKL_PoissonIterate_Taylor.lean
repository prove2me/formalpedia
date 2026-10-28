-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:17:10.981725+00:00
-- url     : https://prove2.me/theorems/4a314a0c-259a-4368-99cf-b24123869fe0
-- title:
--   Extension of a permutation on tensor slots
-- statement:
--   For permutations $τ$ of the first $q$ positions and natural numbers $q,r$, `extendPerm τ` is the permutation of `Fin (q+r)` that acts by $τ$ on the first $q$ slots and by the identity on the remaining $r$ slots. It is a private indexing helper for the Taylor-field and Poisson-iterate identities described in the module.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.PoissonIterate.Domain
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Tilt
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Temperate
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private def extendPerm {q r : ℕ} (τ : Equiv.Perm (Fin q)) : Equiv.Perm (Fin (q + r)) :=
--     finSumFinEquiv.permCongr (Equiv.Perm.sumCongr τ 1)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/PoissonIterate/Domain`](https://prove2.me/theorems/26613bf5-8972-4fc0-832a-ace98ef2407a), [`KLS/LogConcave/HeatSemigroup/Tilt`](https://prove2.me/theorems/c32ba817-f9ca-4787-8cee-e05ffed04129), [`KLS/LogConcave/HeatSemigroup/Temperate`](https://prove2.me/theorems/1eb5f917-f4b3-485c-b451-be82d396cded).
--
--   Theorems in source order:
--
--   - [`taylorTensor_center`](https://prove2.me/theorems/2224e876-b11e-4fc6-980d-876a9062141d)
--   - [`symmetrize_apply_comp_cast`](https://prove2.me/theorems/f3dc6e21-450b-4d16-aab4-8e4451661aaa)
--   - [`taylorTensor_gen_apply`](https://prove2.me/theorems/f4cc32ce-29c2-4586-b75f-f09fd183f1c1)
--   - [`symmetrize_taylorField_grad0_step`](https://prove2.me/theorems/1a522d0e-cd67-4d05-8329-16d2b2b836aa)
--   - [`meanGradSq_eq_norm_taylorField_one_genField`](https://prove2.me/theorems/bb480bc9-8569-44a2-a555-12d3a5f1d619)
--   - [`sum_mean_partialDeriv_sq_le`](https://prove2.me/theorems/be8a1565-79a5-4823-bee4-b6c4a9957d96)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean) · `FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L141-L143 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Tilt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Temperate

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace PoissonIterate
section Slots
/-- A permutation of the first `q` of `q + r` positions, extended by the identity. -/
 def extendPerm {q r : ℕ} (τ : Equiv.Perm (Fin q)) : Equiv.Perm (Fin (q + r)) :=
  finSumFinEquiv.permCongr (Equiv.Perm.sumCongr τ 1)
end Slots
end PoissonIterate
end LogConcave
end KLS
end FunctionalInequalities


