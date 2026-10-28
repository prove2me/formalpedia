-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoTruncate
-- name    : KLSModular_LevyStochCalc_Brownian_ItoTruncate
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:17:28.86781+00:00
-- url     : https://prove2.me/theorems/7275d4a0-b19e-41be-9f18-49283c27276a
-- title:
--   Real clamp and its basic properties
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `clampAt j x` is $\max(-j,\min(j,x))$; for $j\ge0$ it fixes zero and satisfies $|\operatorname{clampAt}(j,x)|\le j$, while `continuous_clampAt` states continuity as a function of $x$.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.VectorItoVersionExists
--   import LevyStochCalc.Brownian.ItoLinear
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def clampAt (j x : ℝ) : ℝ := max (-j) (min j x)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/VectorItoVersionExists`](https://prove2.me/theorems/efbe558e-34b1-48bc-972e-346434525ee9), [`LevyStochCalc/Brownian/ItoLinear`](https://prove2.me/theorems/0a2c3dbb-5791-49a2-875b-20068ab8311a).
--
--   Theorems in source order:
--
--   - [`tendsto_energy_clampAt_sub`](https://prove2.me/theorems/554d2154-b037-4ba4-9d29-93ade89b3950)
--   - [`sq_enorm_finsetSum_le`](https://prove2.me/theorems/cf9da524-3235-4f23-9dbe-288975948e0e)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoTruncate.lean) · `LevyStochCalc.Brownian.ItoTruncate` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoTruncate.lean#L30-L48 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoTruncate`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoTruncate`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoVersionExists
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoTruncate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
open MeasureTheory
open scoped NNReal ENNReal Topology
section Clamp
/-- The clamp of a real number to `[-j, j]`. -/
noncomputable def clampAt (j x : ℝ) : ℝ := max (-j) (min j x)
theorem clampAt_zero {j : ℝ} (hj : 0 ≤ j) : clampAt j 0 = 0 := by
  unfold clampAt
  rw [min_eq_right hj, max_eq_right (by linarith : -j ≤ (0 : ℝ))]
theorem continuous_clampAt (j : ℝ) : Continuous (clampAt j) := by
  unfold clampAt
  fun_prop
theorem abs_clampAt_le {j : ℝ} (hj : 0 ≤ j) (x : ℝ) : |clampAt j x| ≤ j := by
  unfold clampAt
  rcases le_or_gt x (-j) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ j), max_eq_left hx, abs_neg, abs_of_nonneg hj]
  · rcases le_or_gt x j with hx' | hx'
    · rw [min_eq_right hx', max_eq_right hx.le, abs_le]
      exact ⟨hx.le, hx'⟩
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -j ≤ j), abs_of_nonneg hj]
end Clamp
end LevyStochCalc


