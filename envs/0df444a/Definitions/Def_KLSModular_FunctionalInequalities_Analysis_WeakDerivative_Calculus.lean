-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
-- name    : KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:20:24.064252+00:00
-- url     : https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5
-- title:
--   Import context: Analysis/WeakDerivative/Calculus
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.WeakDerivative.Calculus` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.WeakDerivative.Approximation`, `FunctionalInequalities.Analysis.Cutoff.SmoothBall`, `FunctionalInequalities.Analysis.WeakDerivative.Basic`, `FunctionalInequalities.Analysis.WeakDerivative.Mollification`, and `FunctionalInequalities.Analysis.Cutoff.Profile`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.WeakDerivative.Approximation
--   import FunctionalInequalities.Analysis.Cutoff.SmoothBall
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.Analysis.WeakDerivative.Mollification
--   import FunctionalInequalities.Analysis.Cutoff.Profile
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/WeakDerivative/Approximation`](https://prove2.me/theorems/55bb7a47-4741-4de8-91f0-25080da6fa69), [`Analysis/Cutoff/SmoothBall`](https://prove2.me/theorems/e579c572-cae8-4aab-bbfa-980860e9fc63), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`Analysis/WeakDerivative/Mollification`](https://prove2.me/theorems/480cb5f8-8cac-4e12-bd32-870acaf66221), [`Analysis/Cutoff/Profile`](https://prove2.me/theorems/2770d0f0-88ba-4965-8db8-6b9999985219).
--
--   Theorems in source order:
--
--   - [`HasWeakDerivAlong.mul_of_memLp_two`](https://prove2.me/theorems/194c1651-5c29-4beb-84c6-06fd15f07790)
--   - [`memLp_mul_of_hasCompactSupport`](https://prove2.me/theorems/b04b1dc7-d732-49ae-8bbb-620873456903)
--   - [`HasWeakDerivAlong.mul_of_locally_memLp_two`](https://prove2.me/theorems/4c31865f-283b-4c42-8cee-41884d14d427)
--   - [`hasWeakDerivAlong_finsetSum_mul`](https://prove2.me/theorems/2618f40b-2846-4d7d-9e77-e6c773de9cee)
--   - [`hasWeakDerivAlong_finsetProd_of_locally_memLp_two`](https://prove2.me/theorems/9810d657-43d4-4de0-a307-1f01259642ca)
--   - [`hasWeakDerivAlong_exp_neg_of_lipschitz`](https://prove2.me/theorems/bacd1f1f-068d-4e42-88a3-d15ac6d6ee33)
--   - [`HasWeakDerivAlong.mul_of_locally_bounded`](https://prove2.me/theorems/1133273b-c737-4c38-bf2a-2953cd23a941)
--   - [`integral_weakDeriv_mul_eq_swap`](https://prove2.me/theorems/61cf322f-0c0f-4f7d-8765-ac88a842a6c5)
--   - [`compact_bounded_test_domination`](https://prove2.me/theorems/598f7c40-05a7-49e8-94fe-b29d9620425b)
--   - [`integral_flux_eq_neg_forcing_of_bounded_weak_test`](https://prove2.me/theorems/a62894bf-0470-4e04-8a24-6f8073da24d8)
--   - [`HasWeakDerivAlong.compact_mul_data`](https://prove2.me/theorems/14d1dc0b-7afe-403f-ae05-0178b771addc)
--   - [`integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test`](https://prove2.me/theorems/68f53a73-98d0-4677-9ebd-c4a0016296fd)
--   - [`integral_eq_zero_of_integrable_weak_derivative`](https://prove2.me/theorems/4bbf5126-d256-459b-9474-606b9a141762)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean) · `FunctionalInequalities.Analysis.WeakDerivative.Calculus` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1-L2345 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Approximation
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Mollification
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile


