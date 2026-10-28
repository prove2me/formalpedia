-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
-- name    : KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentRestrict
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:05:31.695636+00:00
-- url     : https://prove2.me/theorems/6729fab9-4d54-4cac-a286-3a20b472164d
-- title:
--   Generalized interval-step integrand
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For $0\le a<b$, `stepIocGen Ω ha hab` is the simple predictable integrand representing $1_{(a,b]}$: it uses `stepIoc` when $a>0$ and `stepIoc₀` when $a=0$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoFourthMoment
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def stepIocGen (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       SimplePredictable Ω b :=
--     if h : 0 < a then stepIoc Ω h hab else stepIoc₀ Ω (lt_of_le_of_lt ha hab)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoFourthMoment`](https://prove2.me/theorems/bcb038e3-f0ed-457a-b5d3-77a5f1cbd884).
--
--   Theorems in source order:
--
--   - [`SimplePredictable.abs_eval_le`](https://prove2.me/theorems/1cd600b6-5e8b-4337-a77d-6ea63c207357)
--   - [`SimplePredictable.varClock_le_Ioc`](https://prove2.me/theorems/439559a5-0cc2-4a3a-a3c2-a6d24460420f)
--   - [`SimplePredictable.exists_restrict_Ioc`](https://prove2.me/theorems/5e9d641c-78ce-4154-aba8-1c8bbbf578e0)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean) · `LevyStochCalc.Brownian.ItoIncrementMomentRestrict` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean#L137-L140 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoIncrementMomentRestrict`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentRestrict`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The simple integrand `1_{(a, b]}` for `0 ≤ a < b`. -/
noncomputable def stepIocGen (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    SimplePredictable Ω b :=
  if h : 0 < a then stepIoc Ω h hab else stepIoc₀ Ω (lt_of_le_of_lt ha hab)
end Ito
end Brownian
end LevyStochCalc


