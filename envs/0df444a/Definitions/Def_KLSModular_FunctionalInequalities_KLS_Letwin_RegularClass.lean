-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_Letwin_RegularClass
-- name    : KLSModular_FunctionalInequalities_KLS_Letwin_RegularClass
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:29:53.404331+00:00
-- url     : https://prove2.me/theorems/cc1d2885-a1ae-49de-9545-d4de41532f3e
-- title:
--   Import context: KLS/Letwin/RegularClass
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.Letwin.RegularClass` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Analysis.Operator.HilbertSchmidt`, `FunctionalInequalities.KLS.CEK.MomentRegularity.TraceStein`, `FunctionalInequalities.KLS.IsotropicSupport`, `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.QuadraticVariance`, `FunctionalInequalities.Probability.Stein.QuadraticAction`, `FunctionalInequalities.Analysis.BakryEmery.Calculus`, `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, `FunctionalInequalities.Analysis.Matrix.Sign`, `FunctionalInequalities.Analysis.Operator.Coordinates`, `FunctionalInequalities.Probability.Stein.Kernel`, `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, `FunctionalInequalities.Analysis.WeakDerivative.Basic`, `FunctionalInequalities.Probability.LogConcave`, `FunctionalInequalities.KLS.Isotropic`, `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic`, `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, `FunctionalInequalities.Probability.AffineSupport`, `FunctionalInequalities.Probability.QuadraticVariance`, and `FunctionalInequalities.Probability.Transport`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Operator.HilbertSchmidt
--   import FunctionalInequalities.KLS.CEK.MomentRegularity.TraceStein
--   import FunctionalInequalities.KLS.IsotropicSupport
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.QuadraticVariance
--   import FunctionalInequalities.Probability.Stein.QuadraticAction
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
--   import FunctionalInequalities.Analysis.Matrix.Sign
--   import FunctionalInequalities.Analysis.Operator.Coordinates
--   import FunctionalInequalities.Probability.Stein.Kernel
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
--   import FunctionalInequalities.Analysis.WeakDerivative.Basic
--   import FunctionalInequalities.Probability.LogConcave
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
--   import FunctionalInequalities.KLS.LogConcave.Density.Tilted
--   import FunctionalInequalities.Probability.AffineSupport
--   import FunctionalInequalities.Probability.QuadraticVariance
--   import FunctionalInequalities.Probability.Transport
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Operator/HilbertSchmidt`](https://prove2.me/theorems/06361c00-f2b7-428f-bab2-caf9f49e2f34), [`KLS/CEK/MomentRegularity/TraceStein`](https://prove2.me/theorems/612796d4-e184-478b-b16b-8d3f0b72bbf4), [`KLS/IsotropicSupport`](https://prove2.me/theorems/0df82d3b-ac5a-45d7-a562-335edb194007), [`KLS/LogConcave/Density/GaussianSmoothing/QuadraticVariance`](https://prove2.me/theorems/032e441a-7b5c-4cf8-9242-29a059b98a48), [`Probability/Stein/QuadraticAction`](https://prove2.me/theorems/0e4b9766-8959-44c6-bfc8-ee388e8834ba), [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Analysis/Matrix/Sign`](https://prove2.me/theorems/2761ff4f-5f84-494d-b685-5a11640444c8), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799), [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8), [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81), [`Probability/QuadraticVariance`](https://prove2.me/theorems/8f374ce2-317b-44db-96d6-94eef9130b1f), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564).
--
--   Theorems in source order:
--
--   - [`regularClass_matrix_variance_le_eight`](https://prove2.me/theorems/cfd65a50-1952-469e-9117-ba413e5f75de)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/Letwin/RegularClass.lean) · `FunctionalInequalities.KLS.Letwin.RegularClass` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/Letwin/RegularClass.lean#L1-L219 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.Letwin.RegularClass`, import-context bundle `KLSModular_FunctionalInequalities_KLS_Letwin_RegularClass`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentRegularity_TraceStein
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_IsotropicSupport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_QuadraticVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_QuadraticAction
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Sign
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticVariance
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport


