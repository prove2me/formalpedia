-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoVersionExists
-- name    : KLSModular_LevyStochCalc_Brownian_ItoVersionExists
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:14:39.976228+00:00
-- url     : https://prove2.me/theorems/2434b28d-1785-47cb-b2ca-447e98cb1dc2
-- title:
--   Dyadic approximation from below
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `dyadicApprox n u` is $\lfloor u2^n\rfloor_+/2^n$, the nonnegative-floor dyadic approximation from below to the real number $u$ at level $n$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoProcessVersion
--   import LevyStochCalc.Brownian.ItoQuadVarSum
--   import LevyStochCalc.Brownian.AugmentedFiltration
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def dyadicApprox (n : ℕ) (u : ℝ) : ℝ := (⌊u * 2 ^ n⌋₊ : ℝ) / 2 ^ n
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoProcessVersion`](https://prove2.me/theorems/a2bb5700-14ce-4159-98b0-8e856a34c49b), [`LevyStochCalc/Brownian/ItoQuadVarSum`](https://prove2.me/theorems/1add907f-537c-4a62-9c27-fe90c9b4a510), [`LevyStochCalc/Brownian/AugmentedFiltration`](https://prove2.me/theorems/3cbf8b32-8c2c-4826-b624-2939bc0b44c4).
--
--   Theorems in source order:
--
--   - [`exists_continuousAdapted_modification`](https://prove2.me/theorems/f0d85cba-26cf-42ee-a24a-f69b68bf4f0b)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoVersionExists.lean) · `LevyStochCalc.Brownian.ItoVersionExists` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoVersionExists.lean#L69-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoVersionExists`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoVersionExists`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoProcessVersion
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_AugmentedFiltration

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoVersionExists.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The `n`-th dyadic approximation from below of a nonnegative real. -/
noncomputable def dyadicApprox (n : ℕ) (u : ℝ) : ℝ := (⌊u * 2 ^ n⌋₊ : ℝ) / 2 ^ n
end Ito
end Brownian
end LevyStochCalc


