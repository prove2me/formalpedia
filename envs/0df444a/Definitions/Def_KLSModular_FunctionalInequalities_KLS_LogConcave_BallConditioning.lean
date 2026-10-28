-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:53:28.818956+00:00
-- url     : https://prove2.me/theorems/2fa3d0ff-8849-4ff0-b13d-3697177849fc
-- title:
--   Import context: KLS/LogConcave/BallConditioning
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.BallConditioning` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.Regular.Affine`, `FunctionalInequalities.KLS.Isotropic`, and `FunctionalInequalities.Analysis.Operator.InverseSqrt`. It also directly imports the external prerequisite modules `Mathlib.Probability.ConditionalProbability` and `Mathlib.Topology.UniformSpace.HeineCantor`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Regular.Affine
--   import Mathlib.Probability.ConditionalProbability
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.Analysis.Operator.InverseSqrt
--   import Mathlib.Topology.UniformSpace.HeineCantor
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Regular/Affine`](https://prove2.me/theorems/29516924-6815-4c08-8c28-b0309812c8d6), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533).
--
--   Theorems in source order:
--
--   - [`exists_regularClass_of_cond_closedBall_map`](https://prove2.me/theorems/09f327ff-9750-431b-aefd-04c440b44d3b)
--   - [`covariance_tendsto_one`](https://prove2.me/theorems/931a2bcc-f8c0-48ee-8d9a-a38753c18c36)
--   - [`whitening_sequence`](https://prove2.me/theorems/4f39d579-4312-46d4-8a78-c4f9ba76eab9)
--   - [`exists_whitening_tendsto_moments`](https://prove2.me/theorems/e2bcc388-90fd-4d11-8bef-4995ad9590a2)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean) · `FunctionalInequalities.KLS.LogConcave.BallConditioning` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean#L1-L530 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.BallConditioning`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_BallConditioning`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Affine
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt
import Mathlib.Topology.UniformSpace.HeineCantor


