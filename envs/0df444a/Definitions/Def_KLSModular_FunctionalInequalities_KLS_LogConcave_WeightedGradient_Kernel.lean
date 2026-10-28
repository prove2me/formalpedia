-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:16:32.104103+00:00
-- url     : https://prove2.me/theorems/53a4cc1e-e3fe-4459-bbf4-e862b9c35c22
-- title:
--   Import context: KLS/LogConcave/WeightedGradient/Kernel
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier`, `FunctionalInequalities.Energy.Euclidean.WeakDerivative`, `FunctionalInequalities.L2.MeanVariance`, `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, and `FunctionalInequalities.Energy.Euclidean.ZeroGradient`. It also directly imports the external prerequisite module `Mathlib.MeasureTheory.Measure.Tilted`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Multiplier
--   import FunctionalInequalities.Energy.Euclidean.WeakDerivative
--   import FunctionalInequalities.L2.MeanVariance
--   import FunctionalInequalities.KLS.LogConcave.Density.Tilted
--   import FunctionalInequalities.Energy.Euclidean.ZeroGradient
--   import Mathlib.MeasureTheory.Measure.Tilted
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/WeightedGradient/Multiplier`](https://prove2.me/theorems/5b6390bb-3865-4ef0-88d2-fa41db26a901), [`Energy/Euclidean/WeakDerivative`](https://prove2.me/theorems/c4b37c13-923e-4442-bcbf-73e18432fd7e), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38), [`Energy/Euclidean/ZeroGradient`](https://prove2.me/theorems/52f28c92-8879-4a35-be78-f95c88a2a467).
--
--   Theorems in source order:
--
--   - [`integral_eq_integral_mul_exp`](https://prove2.me/theorems/e50ba0fe-194c-4fab-a951-2f7b7b282f0a)
--   - [`restrict_le_smul_of_eq_tilted`](https://prove2.me/theorems/7744a7a5-331d-4220-a88d-91325cd3a0c8)
--   - [`tendsto_integral_mul_of_tendsto`](https://prove2.me/theorems/0ead0018-76f8-4e4a-918c-0de12ef6b171)
--   - [`tendsto_integral_mul_inner_of_tendsto`](https://prove2.me/theorems/af848101-2a6e-4098-8b0e-6563207a68d5)
--   - [`integral_mul_fderiv_eq_neg_integral_mul_inner`](https://prove2.me/theorems/7c322f0f-17ab-4ef7-afc1-582bee9c53ac)
--   - [`integral_mul_fderiv_eq_zero_of_closedWeightedOperator_eq_zero`](https://prove2.me/theorems/b4c17c79-99e5-4160-b388-7eeda9e935f3)
--   - [`eq_const_mean_of_closedWeightedOperator_eq_zero`](https://prove2.me/theorems/1a8d321f-1b90-4644-b319-efb67dd1e6ce)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean) · `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L1-L472 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Multiplier
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient
import Mathlib.MeasureTheory.Measure.Tilted


