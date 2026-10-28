-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_HessianKernel
-- name    : KLSModular_FunctionalInequalities_Probability_Stein_HessianKernel
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:26:31.598162+00:00
-- url     : https://prove2.me/theorems/ca510456-989b-410d-a253-55ac463b3962
-- title:
--   Import context: Probability/Stein/HessianKernel
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.Stein.HessianKernel` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Probability.Stein.Kernel`, `FunctionalInequalities.Analysis.BakryEmery.Calculus`, `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, and `FunctionalInequalities.Analysis.Operator.Coordinates`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Constructions.Polish.Basic` and `Mathlib.MeasureTheory.SpecificCodomains.WithLp`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.Stein.Kernel
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
--   import Mathlib.MeasureTheory.Constructions.Polish.Basic
--   import Mathlib.MeasureTheory.SpecificCodomains.WithLp
--   import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
--   import FunctionalInequalities.Analysis.Operator.Coordinates
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e), [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a), [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Stein/HessianKernel.lean) · `FunctionalInequalities.Probability.Stein.HessianKernel` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Stein/HessianKernel.lean#L1-L203 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.Stein.HessianKernel`, import-context bundle `KLSModular_FunctionalInequalities_Probability_Stein_HessianKernel`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates


