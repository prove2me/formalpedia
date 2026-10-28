-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
-- name    : KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:16:53.299+00:00
-- url     : https://prove2.me/theorems/541d8ad1-e32c-4fe3-bcf1-975d2f57d4f0
-- title:
--   Import context: Probability/Covariance/Intrinsic
-- statement:
--   This bundle retains the import context of the source module `FunctionalInequalities.Probability.Covariance.Intrinsic` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `FunctionalInequalities.Probability.AffineSupport` and `FunctionalInequalities.Probability.Covariance.Basic`. It also directly imports the external prerequisite modules `Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional`, `Mathlib.Analysis.InnerProductSpace.Adjoint`, and `Mathlib.Analysis.Convex.Integral`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.AffineSupport
--   import FunctionalInequalities.Probability.Covariance.Basic
--   import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
--   import Mathlib.Analysis.InnerProductSpace.Adjoint
--   import Mathlib.Analysis.Convex.Integral
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81), [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc).
--
--   Theorems in source order:
--
--   - [`bilin_intrinsic`](https://prove2.me/theorems/1674ab9b-187e-47f3-8b54-7cbcd2655548)
--   - [`operator_coe_intrinsic`](https://prove2.me/theorems/fe1dea64-17ba-41d3-baa5-d22dd2d8805b)
--   - [`opNorm_operator_intrinsic`](https://prove2.me/theorems/71d571ba-6243-45a4-9ba5-f31b579fb453)
--   - [`intrinsic_operator_inner_self_pos`](https://prove2.me/theorems/af1259be-6217-4dce-8a0d-ab64ed2f22cf)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean) · `FunctionalInequalities.Probability.Covariance.Intrinsic` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L1-L225 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `FunctionalInequalities.Probability.Covariance.Intrinsic`, import-context bundle `KLSModular_FunctionalInequalities_Probability_Covariance_Intrinsic`). The line range identifies the complete original source module; this bundle preserves only its direct import context.

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Convex.Integral


