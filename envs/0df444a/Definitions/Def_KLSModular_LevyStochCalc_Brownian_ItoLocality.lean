-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLocality
-- name    : KLSModular_LevyStochCalc_Brownian_ItoLocality
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:06:53.845616+00:00
-- url     : https://prove2.me/theorems/24c85544-31a3-4ffd-a08e-f5b9ac9b8eba
-- title:
--   Grid stopping times for Itô-integral locality
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For a stopping time $\tau:\Omega\to\mathbb R\cup\{\infty\}$, `stepStop τ c` is the two-valued stopping time that is $\infty$ when $c\le\tau$ and $c$ otherwise. `gridPt t n k` is $kt/n$, `gridStopAux τ t n` recursively takes the minimum of the relevant `stepStop` values, and `gridStop τ t n` is the resulting stopping time at the first grid point strictly beyond $\tau$ among the grid points indexed through $n$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.ItoOptionalStopping
--   import LevyStochCalc.Brownian.ItoIncrement
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def stepStop (c : ℝ) : Ω → WithTop ℝ :=
--     fun ω => if (c : WithTop ℝ) ≤ τ ω then ⊤ else (c : WithTop ℝ)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/ItoOptionalStopping`](https://prove2.me/theorems/1d25c358-1966-4cac-ba37-96d7bf5aaf7d), [`LevyStochCalc/Brownian/ItoIncrement`](https://prove2.me/theorems/0dacfd17-a335-4bce-a734-7c09a89723d3).
--
--   Theorems in source order:
--
--   - [`gridStopAux_le_iff`](https://prove2.me/theorems/6f0d962f-df1d-4b16-a483-6c727c1385c0)
--   - [`eventually_gridStop_lt`](https://prove2.me/theorems/e741dfe5-2d5c-477d-97d6-46f4687f6103)
--   - [`stochasticIntegralBrownian_stopped_eq_of_le`](https://prove2.me/theorems/dc8b0d30-1ce9-485a-bc89-a30aad33e6df)
--   - [`stochasticIntegralBrownian_congr_of_pos`](https://prove2.me/theorems/7c8a7f3d-a1b5-4c44-b668-4100f7891904)
--   - [`stochasticIntegralBrownian_congr_of_le`](https://prove2.me/theorems/b2a61bae-ccc8-42f5-8c56-486156033a8c)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoLocality.lean) · `LevyStochCalc.Brownian.ItoLocality` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoLocality.lean#L40-L171 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoLocality`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoLocality`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoOptionalStopping
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrement

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)
section GridStop
/-- The two-valued stopping time that stops at `c`, unless `τ` has already reached `c`. -/
noncomputable def stepStop (c : ℝ) : Ω → WithTop ℝ :=
  fun ω => if (c : WithTop ℝ) ≤ τ ω then ⊤ else (c : WithTop ℝ)
/-- A point of the uniform grid on `[0, t]` with `n` steps. -/
noncomputable def gridPt (t : ℝ) (n k : ℕ) : ℝ := (k : ℝ) * t / (n : ℝ)
/-- The stopping time that stops at the first grid point strictly beyond `τ`, among the first
`k + 1` points. -/
noncomputable def gridStopAux (t : ℝ) (n : ℕ) : ℕ → Ω → WithTop ℝ
  | 0 => stepStop τ (gridPt t n 0)
  | (k + 1) => fun ω => min (stepStop τ (gridPt t n (k + 1)) ω) (gridStopAux t n k ω)
/-- The stopping time that stops at the first point of the uniform grid on `[0, t]` with `n`
steps that lies strictly beyond `τ`. -/
noncomputable def gridStop (t : ℝ) (n : ℕ) : Ω → WithTop ℝ := gridStopAux τ t n n
end GridStop
end Ito
end Brownian
end LevyStochCalc


