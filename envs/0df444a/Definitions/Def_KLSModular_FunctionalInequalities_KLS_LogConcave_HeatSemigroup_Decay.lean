-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Decay
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Decay
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:24:47.586993+00:00
-- url     : https://prove2.me/theorems/87f7a5e4-b54d-4085-b6b9-cd0350aac65d
-- title:
--   Import context: KLS/LogConcave/HeatSemigroup/Decay
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Decay` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Markov`, `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Domain`, `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Poincare`, `FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative`, and `FunctionalInequalities.L2.MeanVariance`. It also directly imports the external prerequisite module `Mathlib.Analysis.Calculus.Deriv.MeanValue`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Markov
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Domain
--   import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Poincare
--   import FunctionalInequalities.Analysis.Semigroup.Generated.TimeDerivative
--   import FunctionalInequalities.L2.MeanVariance
--   import Mathlib.Analysis.Calculus.Deriv.MeanValue
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/HeatSemigroup/Markov`](https://prove2.me/theorems/73466029-c8a0-4ff1-b09b-fd66281b152c), [`KLS/LogConcave/HeatSemigroup/Domain`](https://prove2.me/theorems/c32bf6a0-da1f-4bb9-8595-564187dbc939), [`KLS/LogConcave/WeightedGradient/Poincare`](https://prove2.me/theorems/80fd6f93-3b94-490a-9376-d2fdf9e800cd), [`Analysis/Semigroup/Generated/TimeDerivative`](https://prove2.me/theorems/b3d8e0b7-8cea-4a59-87d9-a8d37efcca52), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Decay.lean) · `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Decay` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Decay.lean#L1-L220 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Decay`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Decay`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Poincare
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_TimeDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Mathlib.Analysis.Calculus.Deriv.MeanValue


