-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_Potential
-- name    : KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_Potential
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:12:42.092014+00:00
-- url     : https://prove2.me/theorems/76e138af-1ba7-464e-acf1-d307e8ead30a
-- title:
--   Import context: KLS/CEK/MomentRegularity/Potential
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.CEK.MomentRegularity.Potential` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, `FunctionalInequalities.Analysis.Convex.Alexandrov`, `FunctionalInequalities.Analysis.Convex.Caffarelli`, `FunctionalInequalities.Analysis.Convex.GradientLipschitz`, `FunctionalInequalities.Analysis.Convex.HessianRegularity`, `FunctionalInequalities.Analysis.Convex.Subgradient`, `FunctionalInequalities.Analysis.Convex.Viscosity`, `FunctionalInequalities.KLS.CEK.MomentMap`, `FunctionalInequalities.KLS.Isotropic`, and `FunctionalInequalities.Probability.Stein.HessianKernel`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
--   import FunctionalInequalities.Analysis.Convex.Alexandrov
--   import FunctionalInequalities.Analysis.Convex.Caffarelli
--   import FunctionalInequalities.Analysis.Convex.GradientLipschitz
--   import FunctionalInequalities.Analysis.Convex.HessianRegularity
--   import FunctionalInequalities.Analysis.Convex.Subgradient
--   import FunctionalInequalities.Analysis.Convex.Viscosity
--   import FunctionalInequalities.KLS.CEK.MomentMap
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.Probability.Stein.HessianKernel
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799), [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905), [`Analysis/Convex/Caffarelli`](https://prove2.me/theorems/9215c92e-8aaf-4fc3-85d3-101608b4064d), [`Analysis/Convex/GradientLipschitz`](https://prove2.me/theorems/b5069800-f62d-405b-8e8b-6b9408cea016), [`Analysis/Convex/HessianRegularity`](https://prove2.me/theorems/3de085c3-1487-424e-b91c-badb9e79b607), [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7), [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b), [`KLS/CEK/MomentMap`](https://prove2.me/theorems/a13c53cf-ecfe-4a6a-bd4e-0464d3687bba), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Probability/Stein/HessianKernel`](https://prove2.me/theorems/ca510456-989b-410d-a253-55ac463b3962).
--
--   Theorems in source order:
--
--   - [`exists_regular_moment_potential`](https://prove2.me/theorems/d91fde05-8ec1-4655-bc90-ed2dd99d4bf3)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Potential.lean) · `FunctionalInequalities.KLS.CEK.MomentRegularity.Potential` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/Potential.lean#L1-L324 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.CEK.MomentRegularity.Potential`, import-context bundle `KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_Potential`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_GradientLipschitz
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_HessianRegularity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentMap
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_HessianKernel


