-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic
-- name    : KLSModular_FunctionalInequalities_Analysis_Mollification_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:14:37.471442+00:00
-- url     : https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d
-- title:
--   Import context: Analysis/Mollification/Basic
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Analysis.Mollification.Basic` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite module is `FunctionalInequalities.Analysis.BakryEmery.Calculus`. It also directly imports the external prerequisite modules `Mathlib.Analysis.Calculus.BumpFunction.Convolution`, `Mathlib.Analysis.Calculus.ContDiff.Convolution`, `Mathlib.MeasureTheory.Function.ContinuousMapDense`, `Mathlib.MeasureTheory.Function.L2Space`, `Mathlib.Analysis.Calculus.LineDeriv.Basic`, `Mathlib.Analysis.Calculus.Rademacher`, `Mathlib.Analysis.Convex.Integral`, and `Mathlib.MeasureTheory.SpecificCodomains.Pi`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import Mathlib.Analysis.Calculus.BumpFunction.Convolution
--   import Mathlib.Analysis.Calculus.ContDiff.Convolution
--   import Mathlib.MeasureTheory.Function.ContinuousMapDense
--   import Mathlib.MeasureTheory.Function.L2Space
--   import Mathlib.Analysis.Calculus.LineDeriv.Basic
--   import Mathlib.Analysis.Calculus.Rademacher
--   import Mathlib.Analysis.Convex.Integral
--   import Mathlib.MeasureTheory.SpecificCodomains.Pi
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a).
--
--   Theorems in source order:
--
--   - [`enorm_convolution_sq_le`](https://prove2.me/theorems/8688d530-bfa5-4460-868a-07eb55a8b66f)
--   - [`lintegral_enorm_convolution_sq_le`](https://prove2.me/theorems/63807bea-13bd-4a60-93ed-c5b5453cd20a)
--   - [`tendsto_eLpNorm_convolution_sub_of_continuous`](https://prove2.me/theorems/a7a4227b-bc74-47d0-aecc-a60ae8cbf721)
--   - [`tendsto_eLpNorm_convolution_sub`](https://prove2.me/theorems/3e5007ce-6906-4a04-82a9-55a0bdd821b3)
--   - [`integral_inner_convolution_eq`](https://prove2.me/theorems/fd3d77b4-2913-4723-a4fd-5a1404fbf923)
--   - [`gradient_convolution`](https://prove2.me/theorems/fe7a116d-bd27-498e-9e9e-354056906010)
--   - [`laplacian_convolution`](https://prove2.me/theorems/0855ca87-12f0-432a-bb25-ce692eba493f)
--   - [`integral_fderiv_kernel_eq`](https://prove2.me/theorems/8b5ca05b-ad73-4f24-8770-85db445dfaf1)
--   - [`hasFDerivAt_convolution_normed_of_lipschitz`](https://prove2.me/theorems/9ccb4a93-a981-4edd-a672-af4d66944fff)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean) · `FunctionalInequalities.Analysis.Mollification.Basic` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L1-L706 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Analysis.Mollification.Basic`, import-context bundle `KLSModular_FunctionalInequalities_Analysis_Mollification_Basic`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.SpecificCodomains.Pi


