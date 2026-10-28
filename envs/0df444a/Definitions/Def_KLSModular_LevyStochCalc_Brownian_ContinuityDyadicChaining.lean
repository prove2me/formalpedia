-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining
-- name    : KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:37:11.9607+00:00
-- url     : https://prove2.me/theorems/70739fec-fa14-48e1-8f11-3b0c245eb2b3
-- title:
--   Dyadic rationals and dyadic truncation
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. The set `dyadicRationals` consists of real numbers of the form k · 2^(−n), with k ∈ ℤ and n ∈ ℕ. The noncomputable function `dyadicTrunc` maps x ∈ ℝ to floor(x · 2ⁿ) divided by 2ⁿ, the level-n dyadic approximation from below. This bundle contains these definitions only; the surrounding module documents their use in deterministic Hölder chaining.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.Construction
--   import Mathlib.Probability.Process.Kolmogorov
--   import Mathlib.Probability.Distributions.Gaussian.Fernique
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def dyadicRationals : Set ℝ :=
--     {x : ℝ | ∃ k : ℤ, ∃ n : ℕ, x = (k : ℝ) * (2 : ℝ)^(-n : ℤ)}
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Theorems in source order:
--
--   - [`dense_dyadicRationals`](https://prove2.me/theorems/85782cfc-fe1d-4e3d-b7b8-39bea04a659f)
--   - [`dyadicTrunc_succ_step`](https://prove2.me/theorems/f1f03a2a-9f1b-43c6-84e0-395a9ea8ebbc)
--   - [`dyadicTrunc_telescope`](https://prove2.me/theorems/d83ab303-32f8-4188-92ae-deae609712a4)
--   - [`dyadicTrunc_near_step`](https://prove2.me/theorems/cc514a95-7843-459b-984c-57d63cd24e90)
--   - [`dyadicTrunc_eventually_eq`](https://prove2.me/theorems/3e1785d0-d93f-4be2-b07c-69e9627ca49e)
--   - [`exists_dyadic_scale`](https://prove2.me/theorems/1d383b87-9bce-4bea-947b-c6594626f115)
--   - [`rpow_half_pow_le`](https://prove2.me/theorems/4d94cc63-e21d-4250-be10-7ae322e82378)
--   - [`kc_exponent_identity`](https://prove2.me/theorems/015b3d90-70b0-4878-af84-3becbce9c7eb)
--   - [`dyadic_holder_chaining`](https://prove2.me/theorems/749988d9-89e5-4fb5-9831-f2ad8915a549)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean) · `LevyStochCalc.Brownian.ContinuityDyadicChaining` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ContinuityDyadicChaining.lean#L103-L185 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ContinuityDyadicChaining`, definition bundle `KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace LevyStochCalc
namespace Brownian
namespace Continuity
/-- The set of dyadic rationals: `D := {k * 2^{-n} : k ∈ ℤ, n ∈ ℕ}`. Dense in ℝ. -/
def dyadicRationals : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, ∃ n : ℕ, x = (k : ℝ) * (2 : ℝ)^(-n : ℤ)}
/-- Level-`n` dyadic truncation `⌊x·2ⁿ⌋ / 2ⁿ` — the largest level-`n` dyadic
`≤ x`. -/
noncomputable def dyadicTrunc (n : ℕ) (x : ℝ) : ℝ := (⌊x * 2 ^ n⌋ : ℝ) / 2 ^ n
end Continuity
end Brownian
end LevyStochCalc


