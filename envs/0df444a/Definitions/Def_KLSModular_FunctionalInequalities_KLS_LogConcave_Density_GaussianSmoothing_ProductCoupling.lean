-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_ProductCoupling
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_ProductCoupling
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:02:25.174453+00:00
-- url     : https://prove2.me/theorems/ec60ae0c-90e6-43f3-859c-75d3c6dd9a5f
-- title:
--   Import context: KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.ProductCoupling` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.LinearImage`, `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments`, `FunctionalInequalities.KLS.LogConcave.HessianStein`, `FunctionalInequalities.Analysis.BakryEmery.Calculus`, `FunctionalInequalities.Energy.WeightedGradient.Core`, `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic`, `FunctionalInequalities.L2.Pairing`, `FunctionalInequalities.Probability.Stein.Kernel`, `FunctionalInequalities.Probability.Stein.SourceDualBound`, `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, and `FunctionalInequalities.Probability.Stein.HessianKernel`. It also directly imports the external prerequisite modules `Mathlib.MeasureTheory.Measure.RegularityCompacts` and `Mathlib.Topology.UniformSpace.Uniformizable`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.LinearImage
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Moments
--   import FunctionalInequalities.KLS.LogConcave.HessianStein
--   import Mathlib.MeasureTheory.Measure.RegularityCompacts
--   import Mathlib.Topology.UniformSpace.Uniformizable
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import FunctionalInequalities.Energy.WeightedGradient.Core
--   import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Basic
--   import FunctionalInequalities.L2.Pairing
--   import FunctionalInequalities.Probability.Stein.Kernel
--   import FunctionalInequalities.Probability.Stein.SourceDualBound
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.BakryEmery.WeakHessian
--   import FunctionalInequalities.Probability.Stein.HessianKernel
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Density/GaussianSmoothing/LinearImage`](https://prove2.me/theorems/65252c7c-8be3-4f9a-a8e7-be00ac3deb3b), [`KLS/LogConcave/Density/GaussianSmoothing/Moments`](https://prove2.me/theorems/0e6ed451-9a11-44a3-926c-c84236dabdf8), [`KLS/LogConcave/HessianStein`](https://prove2.me/theorems/72cb6534-e95d-45a6-ad0a-93acef4b771e), [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a), [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f), [`KLS/LogConcave/Density/GaussianSmoothing/Basic`](https://prove2.me/theorems/a2d7963c-80d1-434f-9795-020109b07575), [`L2/Pairing`](https://prove2.me/theorems/a600d495-e861-43ba-9e2e-1a9a446c488b), [`Probability/Stein/Kernel`](https://prove2.me/theorems/6af08ed6-46c1-440c-8a8d-7c243989192e), [`Probability/Stein/SourceDualBound`](https://prove2.me/theorems/205ca023-4637-4c3c-8da3-5cd441798375), [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/BakryEmery/WeakHessian`](https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799), [`Probability/Stein/HessianKernel`](https://prove2.me/theorems/ca510456-989b-410d-a253-55ac463b3962).
--
--   Theorems in source order:
--
--   - [`gaussian_product_source_stein_pairings_integrable`](https://prove2.me/theorems/baf328a1-6649-44a0-8197-8f43bfab886c)
--   - [`gaussian_product_source_stein_identity`](https://prove2.me/theorems/23d8691b-4721-4fa3-a71c-9a8a4ef02ab4)
--   - [`gaussian_product_compact_dual_bound`](https://prove2.me/theorems/c7109f6d-dfe4-4a98-a566-2c5d13265636)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling.lean) · `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.ProductCoupling` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/ProductCoupling.lean#L1-L280 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.ProductCoupling`, import-context bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_ProductCoupling`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_LinearImage
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Moments
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HessianStein
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Core
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_L2_Pairing
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_SourceDualBound
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Stein_HessianKernel


