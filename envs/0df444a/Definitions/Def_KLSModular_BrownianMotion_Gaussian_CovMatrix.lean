-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Gaussian_CovMatrix
-- name    : KLSModular_BrownianMotion_Gaussian_CovMatrix
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:36:23.944539+00:00
-- url     : https://prove2.me/theorems/d80696ff-da68-4d43-8075-a81458b3bcd2
-- title:
--   Import context: BrownianMotion/Gaussian/CovMatrix
-- statement:
--   This bundle retains the import context of the source module `BrownianMotion.Gaussian.CovMatrix` in the modular KLS dependency graph. It adds no new mathematical declarations. Substantive statements and proofs are represented by separate theorem nodes.
--
--   Its direct project prerequisite modules are `BrownianMotion.Auxiliary.ContinuousBilinForm` and `BrownianMotion.Auxiliary.MeasureTheory`. It also directly imports the external prerequisite modules `Mathlib.Probability.Distributions.Gaussian.Fernique` and `Mathlib.Probability.Moments.CovarianceBilin`.
--
--   **Original module imports**
--
--   ```lean
--   public import BrownianMotion.Auxiliary.ContinuousBilinForm
--   public import BrownianMotion.Auxiliary.MeasureTheory
--   public import Mathlib.Probability.Distributions.Gaussian.Fernique
--   public import Mathlib.Probability.Moments.CovarianceBilin
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`BrownianMotion/Auxiliary/ContinuousBilinForm`](https://prove2.me/theorems/e3948a8c-94ac-4ee4-a766-f60b69242641), [`BrownianMotion/Auxiliary/MeasureTheory`](https://prove2.me/theorems/3312c2d9-e816-4bec-9802-c908ff00df00).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Gaussian/CovMatrix.lean) · `BrownianMotion.Gaussian.CovMatrix` · Frozen source `408915f`.
-- source:
--   Frozen KLS source: https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Gaussian/CovMatrix.lean#L1-L106 (commit 408915fd28eb892a7093fa5df6f6c2699e9de144, module `BrownianMotion.Gaussian.CovMatrix`, import-context bundle `KLSModular_BrownianMotion_Gaussian_CovMatrix`). The line range identifies the complete original source module; this bundle preserves only its direct import context. Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0); upstream source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Gaussian/CovMatrix.lean. Original vendor notices are retained in the generated Lean text.

import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_ContinuousBilinForm
import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_MeasureTheory
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilin

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Gaussian/CovMatrix.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)


