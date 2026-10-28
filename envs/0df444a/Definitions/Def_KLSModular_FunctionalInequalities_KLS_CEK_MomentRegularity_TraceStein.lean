-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_TraceStein
-- name    : KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_TraceStein
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:24:27.146591+00:00
-- url     : https://prove2.me/theorems/612796d4-e184-478b-b16b-8d3f0b72bbf4
-- title:
--   Import context: KLS/CEK/MomentRegularity/TraceStein
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.CEK.MomentRegularity.TraceStein` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic`, `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian`, `FunctionalInequalities.Analysis.BakryEmery.MongeAmpere`, `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, `FunctionalInequalities.Analysis.Cutoff.Conservativity`, `FunctionalInequalities.Analysis.Matrix.Integral`, `FunctionalInequalities.Analysis.Matrix.Positivity`, `FunctionalInequalities.Analysis.Matrix.TraceGram`, `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, `FunctionalInequalities.Analysis.Matrix.WeakTrace`, `FunctionalInequalities.Analysis.WeakDerivative.Basic`, `FunctionalInequalities.KLS.Isotropic`, `FunctionalInequalities.KLS.LogConcave.HessianStein`, `FunctionalInequalities.KLS.LogConcave.HessianTrace`, and `FunctionalInequalities.KLS.CEK.MomentRegularity.Cutoff`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
--   import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian
--   import FunctionalInequalities.Analysis.BakryEmery.MongeAmpere
--   import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
--   import FunctionalInequalities.Analysis.Cutoff.Conservativity
--   import FunctionalInequalities.Analysis.Matrix.Integral
--   import FunctionalInequalities.Analysis.Matrix.Positivity
--   import FunctionalInequalities.Analysis.Matrix.TraceGram
--   import FunctionalInequalities.Analysis.Matrix.WeakDerivative
--   import FunctionalInequalities.Analysis.Matrix.WeakTrace
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.KLS.LogConcave.HessianStein
--   import FunctionalInequalities.KLS.LogConcave.HessianTrace
--   import FunctionalInequalities.KLS.CEK.MomentRegularity.Cutoff
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/IntegrationByParts/InverseHessian/Basic`](https://prove2.me/theorems/b8e832e5-3953-4fab-bf6b-4ce0c2f4bdfe), [`Analysis/BakryEmery/IntegrationByParts/LipschitzHessian`](https://prove2.me/theorems/a33bc411-81aa-4352-b34a-c6253ee0ed0a), [`Analysis/BakryEmery/MongeAmpere`](https://prove2.me/theorems/2b5c2043-7539-4080-9bb7-264ef25c0839), [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799), [`Analysis/Cutoff/Conservativity`](https://prove2.me/theorems/57f06eeb-f3c4-4cb8-a756-eddd5e871527), [`Analysis/Matrix/Integral`](https://prove2.me/theorems/09aa8c12-3230-447e-89a1-dc642659f2aa), [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c), [`Analysis/Matrix/TraceGram`](https://prove2.me/theorems/d77e66c8-d9dd-4a0b-bdab-7928904ca310), [`Analysis/Matrix/WeakDerivative`](https://prove2.me/theorems/3dfbda94-4a39-4ea5-9eac-fd198567c681), [`Analysis/Matrix/WeakTrace`](https://prove2.me/theorems/4921a24d-b044-4852-b95d-96829251045f), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/LogConcave/HessianStein`](https://prove2.me/theorems/72cb6534-e95d-45a6-ad0a-93acef4b771e), [`KLS/LogConcave/HessianTrace`](https://prove2.me/theorems/a007d6bd-8267-4526-a1ec-a10003542850), [`KLS/CEK/MomentRegularity/Cutoff`](https://prove2.me/theorems/75cc6def-529a-4f83-991b-244816282c31).
--
--   Theorems in source order:
--
--   - [`actual_source_weak_trace_conservativity_data`](https://prove2.me/theorems/c4a0bba5-191f-4457-aaab-30694404cab9)
--   - [`exists_regular_moment_weak_trace_energy`](https://prove2.me/theorems/8b9295d3-a838-466e-8d9d-2a61f4269613)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/TraceStein.lean) · `FunctionalInequalities.KLS.CEK.MomentRegularity.TraceStein` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/TraceStein.lean#L1-L2486 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.CEK.MomentRegularity.TraceStein`, import-context bundle `KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_TraceStein`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_LipschitzHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Conservativity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Integral
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_TraceGram
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakTrace
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HessianStein
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HessianTrace
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_Cutoff


