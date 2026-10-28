-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Standardization
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Standardization
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:09:45.694042+00:00
-- url     : https://prove2.me/theorems/4671fb2f-bcb0-4175-82a9-3d629303664a
-- title:
--   Import context: KLS/BKL/Posterior/Standardization
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.BKL.Posterior.Standardization` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Probability.Posterior.CompactDomain`, `FunctionalInequalities.KLS.IsotropicSupport`, `FunctionalInequalities.Probability.Posterior.Generator`, `FunctionalInequalities.KLS.LogConcave.Density.ConcaveTilt`, `FunctionalInequalities.Analysis.Operator.InverseSqrt`, `FunctionalInequalities.Probability.Posterior.JointRegularity`, `FunctionalInequalities.Probability.Transport`, `FunctionalInequalities.KLS.LogConcave.Isotropic`, `FunctionalInequalities.Probability.IntrinsicTranslation`, `FunctionalInequalities.Probability.Covariance.CauchySchwarz`, `FunctionalInequalities.Probability.CoordinateThirdMoment`, and `FunctionalInequalities.KLS.BKL.Posterior.Covariance`. It also directly imports the external prerequisite modules `Mathlib.Probability.Moments.Covariance` and `Mathlib.Probability.Moments.Variance`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Posterior.CompactDomain
--   import FunctionalInequalities.KLS.IsotropicSupport
--   import FunctionalInequalities.Probability.Posterior.Generator
--   import FunctionalInequalities.KLS.LogConcave.Density.ConcaveTilt
--   import FunctionalInequalities.Analysis.Operator.InverseSqrt
--   import FunctionalInequalities.Probability.Posterior.JointRegularity
--   import FunctionalInequalities.Probability.Transport
--   import FunctionalInequalities.KLS.LogConcave.Isotropic
--   import FunctionalInequalities.Probability.IntrinsicTranslation
--   import FunctionalInequalities.Probability.Covariance.CauchySchwarz
--   import FunctionalInequalities.Probability.CoordinateThirdMoment
--   import Mathlib.Probability.Moments.Covariance
--   import Mathlib.Probability.Moments.Variance
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda), [`KLS/IsotropicSupport`](https://prove2.me/theorems/0df82d3b-ac5a-45d7-a562-335edb194007), [`Probability/Posterior/Generator`](https://prove2.me/theorems/f83f846f-96fd-4858-aa50-76e79f5d2363), [`KLS/LogConcave/Density/ConcaveTilt`](https://prove2.me/theorems/7ed5056e-c3f4-4ab8-9bf8-55101609725f), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533), [`Probability/Posterior/JointRegularity`](https://prove2.me/theorems/38b44b15-e229-4b35-89b9-63261754a611), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564), [`KLS/LogConcave/Isotropic`](https://prove2.me/theorems/35471368-b77f-4600-8554-699e6845e252), [`Probability/IntrinsicTranslation`](https://prove2.me/theorems/b9ce8338-e7be-450b-86d4-c0e89470d643), [`Probability/Covariance/CauchySchwarz`](https://prove2.me/theorems/609822dd-0643-4f61-936f-db8283b6fe24), [`Probability/CoordinateThirdMoment`](https://prove2.me/theorems/51f9be5c-10cc-4c23-abf8-08bfdd24cc62), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa).
--
--   Theorems in source order:
--
--   - [`Isotropic.exists_inverseSqrt_equiv_isotropic_standardized`](https://prove2.me/theorems/590c5914-bf1c-477c-b78a-cf7e5e57e017)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Posterior/Standardization.lean) · `FunctionalInequalities.KLS.BKL.Posterior.Standardization` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Posterior/Standardization.lean#L1-L116 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.BKL.Posterior.Standardization`, import-context bundle `KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Standardization`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_IsotropicSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_ConcaveTilt
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_JointRegularity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_IntrinsicTranslation
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_CauchySchwarz
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_CoordinateThirdMoment
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance


