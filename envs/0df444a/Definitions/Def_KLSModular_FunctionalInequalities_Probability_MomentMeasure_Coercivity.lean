-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity
-- name    : KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:59:01.269986+00:00
-- url     : https://prove2.me/theorems/a4ce5d12-c4a7-484f-afc3-169e6c7d1a5c
-- title:
--   Import context: Probability/MomentMeasure/Coercivity
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.MomentMeasure.Coercivity` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Convex.AffineMaximum`, `FunctionalInequalities.Probability.ConvexSupport`, `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, and `FunctionalInequalities.Probability.MomentMeasure.Affine`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Measure.Haar.NormedSpace` and `Mathlib.MeasureTheory.Integral.Lebesgue.Map`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.AffineMaximum
--   import FunctionalInequalities.Probability.ConvexSupport
--   import FunctionalInequalities.Probability.MomentMeasure.ConjugateMass
--   import FunctionalInequalities.Probability.MomentMeasure.Affine
--   import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
--   import Mathlib.MeasureTheory.Integral.Lebesgue.Map
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/AffineMaximum`](https://prove2.me/theorems/6ce50813-8eec-46a5-abb0-e806e1385307), [`Probability/ConvexSupport`](https://prove2.me/theorems/883cc35c-d1e7-4fcf-9935-3f624629687e), [`Probability/MomentMeasure/ConjugateMass`](https://prove2.me/theorems/c85f19a1-3736-404d-9ea6-0652c177907f), [`Probability/MomentMeasure/Affine`](https://prove2.me/theorems/763df6ce-b81b-47cb-8b6b-d4d0c79b4571).
--
--   Theorems in source order:
--
--   - [`exists_uniform_legendre_lower`](https://prove2.me/theorems/a15b2ea9-f03f-4130-82da-67d156766d05)
--   - [`density_scaled_le_exp`](https://prove2.me/theorems/19c43856-85c8-4cf6-9dbe-f234f3ec52f0)
--   - [`exists_uniform_mass_bound`](https://prove2.me/theorems/c940a54c-60e4-4d0d-a533-f6c9ae3a6309)
--   - [`exists_coercivity_of_centered_probability`](https://prove2.me/theorems/d7af9f42-295e-4d56-b5f8-6a8b48b31bf2)
--   - [`exists_bound_of_log_lower`](https://prove2.me/theorems/98239541-fa41-45b3-93db-26285bcefb48)
--   - [`exists_integral_bound_of_eventual_functional_lower`](https://prove2.me/theorems/ec1ab899-a2cd-4af7-a22e-cf39c5c47111)
--   - [`real_coercivity_le_uniform`](https://prove2.me/theorems/4b9111c6-9576-4b77-b712-57c19eb68875)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean) · `FunctionalInequalities.Probability.MomentMeasure.Coercivity` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L1-L325 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, import-context bundle `KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Affine
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Map


