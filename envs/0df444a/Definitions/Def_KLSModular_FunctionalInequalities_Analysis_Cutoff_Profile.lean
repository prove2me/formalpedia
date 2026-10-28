-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile
-- name    : KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:18:04.527869+00:00
-- url     : https://prove2.me/theorems/2770d0f0-88ba-4965-8db8-6b9999985219
-- title:
--   Import context: Analysis/Cutoff/Profile
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Cutoff.Profile` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   It also directly imports the external prerequisite modules `Mathlib.Analysis.SpecialFunctions.SmoothTransition`, `Mathlib.Analysis.Calculus.ContDiff.Deriv`, `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`, `Mathlib.Analysis.Calculus.BumpFunction.InnerProduct`, `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`, and `Mathlib.Analysis.SpecialFunctions.Log.Deriv`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.SpecialFunctions.SmoothTransition
--   import Mathlib.Analysis.Calculus.ContDiff.Deriv
--   import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
--   import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
--   import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
--   import Mathlib.Analysis.SpecialFunctions.Log.Deriv
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`smoothTransition_two_sub_cutoff`](https://prove2.me/theorems/107a6021-a617-4338-a167-9789f56e48be)
--   - [`exists_majorant_abs_deriv_deriv_smoothTransition_two_sub`](https://prove2.me/theorems/75594fe5-03f9-45fd-97be-284edaa2d948)
--   - [`inv_mul_intervalIntegral_div_three_cutoff`](https://prove2.me/theorems/84c111d5-1c7e-41d4-975d-61430e96ccc6)
--   - [`deriv_comp_sub_div_and_deriv_deriv`](https://prove2.me/theorems/41078cd2-f599-4095-aec6-d7ad2870689d)
--   - [`monotoneOn_and_tendsto_smoothTransition_two_sub_div`](https://prove2.me/theorems/07c7bff6-a883-4a34-a1d3-2095c97849b8)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean) · `FunctionalInequalities.Analysis.Cutoff.Profile` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L1-L566 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Cutoff.Profile`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv


