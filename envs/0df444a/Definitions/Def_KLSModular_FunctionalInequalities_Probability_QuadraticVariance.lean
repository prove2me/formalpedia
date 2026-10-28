-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticVariance
-- name    : KLSModular_FunctionalInequalities_Probability_QuadraticVariance
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:05:26.921568+00:00
-- url     : https://prove2.me/theorems/8f374ce2-317b-44db-96d6-94eef9130b1f
-- title:
--   Import context: Probability/QuadraticVariance
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.QuadraticVariance` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Matrix.Sign`, `FunctionalInequalities.L2.MeanVariance`, `FunctionalInequalities.Probability.ProductVariance`, and `FunctionalInequalities.Probability.Moments`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Matrix.Sign
--   import FunctionalInequalities.L2.MeanVariance
--   import FunctionalInequalities.Probability.ProductVariance
--   import FunctionalInequalities.Probability.Moments
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Matrix/Sign`](https://prove2.me/theorems/2761ff4f-5f84-494d-b685-5a11640444c8), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`Probability/ProductVariance`](https://prove2.me/theorems/65fe02bc-71f6-4e5c-8ecc-75b243fe19fa), [`Probability/Moments`](https://prove2.me/theorems/b17c0176-d838-4b45-bc76-c9e62313e1ce).
--
--   Theorems in source order:
--
--   - [`tendsto_variance_quadratic_matrix_forms`](https://prove2.me/theorems/6bac75bd-e0cf-4ff6-8155-e85bb3d798fc)
--   - [`quadratic_variance_le_centered_noise_convolution`](https://prove2.me/theorems/36dbece0-39c9-42e4-832b-b29a213eec41)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/QuadraticVariance.lean) · `FunctionalInequalities.Probability.QuadraticVariance` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/QuadraticVariance.lean#L1-L163 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.QuadraticVariance`, import-context bundle `KLSModular_FunctionalInequalities_Probability_QuadraticVariance`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ProductVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Moments


