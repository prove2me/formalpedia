-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_SmoothCutoff
-- name    : KLSModular_LevyStochCalc_Brownian_SmoothCutoff
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:55:56.210478+00:00
-- url     : https://prove2.me/theorems/85fcd788-0ea4-412f-b77d-911eacf30754
-- title:
--   Smooth one-dimensional and box cutoffs
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `smoothCut k t` is a smooth transition-based cutoff, equal to $1$ on the intended inner interval and vanishing outside the intended outer interval as specified by the source conventions. `boxCut k z` multiplies `smoothCut k (z i)` over all $i:\mathrm{Fin}\,n$.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.SpecialFunctions.SmoothTransition
--   import Mathlib.Analysis.Calculus.FDeriv.Const
--   import Mathlib.Analysis.Calculus.ContDiff.Operations
--   import Mathlib.Topology.UniformSpace.HeineCantor
--   import Mathlib.Analysis.Normed.Group.Constructions
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def smoothCut (k t : ℝ) : ℝ :=
--     Real.smoothTransition ((4 * k ^ 2 - t ^ 2) * 4 / (7 * k ^ 2))
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/SmoothCutoff.lean) · `LevyStochCalc.Brownian.SmoothCutoff` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/SmoothCutoff.lean#L37-L62 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.SmoothCutoff`, definition bundle `KLSModular_LevyStochCalc_Brownian_SmoothCutoff`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/SmoothCutoff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
open scoped Topology
section OneDim
/-- A smooth one-dimensional cutoff: `1` on `[-3k/2, 3k/2]` and `0` off `(-2k, 2k)`. -/
noncomputable def smoothCut (k t : ℝ) : ℝ :=
  Real.smoothTransition ((4 * k ^ 2 - t ^ 2) * 4 / (7 * k ^ 2))
end OneDim
section Box
variable {n : ℕ}
/-- The product of the one-dimensional cutoffs over the coordinates. -/
noncomputable def boxCut (k : ℝ) (z : Fin n → ℝ) : ℝ := ∏ i, smoothCut k (z i)
end Box
end LevyStochCalc


