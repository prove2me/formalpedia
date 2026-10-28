-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal
-- name    : KLSModular_LevyStochCalc_Ito_PicardGlobal
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T18:36:40.453587+00:00
-- url     : https://prove2.me/theorems/c943d813-0c09-4024-8228-fab73533b083
-- title:
--   Global patching of finite-window paths
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc). `globalPatch Y` selects from a family of path maps $Y:\mathbb{N}\to\mathbb{R}\to\Omega\to(\mathrm{Fin}\,n\to\mathbb{R})$ the member indexed by the nonnegative ceiling $\lceil t\rceil_+$ at time $t$. It is the stated gluing operation for finite-window solutions, but this bundle contains only the definition and no theorem asserting consistency or that the patched map solves the global equation.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Ito.PicardWindow
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   noncomputable def globalPatch (Y : ℕ → ℝ → Ω → (Fin n → ℝ)) : ℝ → Ω → (Fin n → ℝ) :=
--     fun t ω => Y ⌈t⌉₊ t ω
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Ito/PicardWindow`](https://prove2.me/theorems/def3f42b-8053-4f4f-a322-473715ac993f).
--
--   Theorems in source order:
--
--   - [`ae_all_eq_of_rightCont`](https://prove2.me/theorems/439cca99-ccce-4335-8a27-57cecb8617ae)
--   - [`progressivelyMeasurable_globalPatch`](https://prove2.me/theorems/d7b4eeb7-145e-4369-9114-1296769d3100)
--   - [`ae_all_windows_agree`](https://prove2.me/theorems/28b35a3b-dd08-4022-854c-84cd03274ea9)
--   - [`cadlag_globalPatch`](https://prove2.me/theorems/3d125985-be22-4ea3-8cfc-9c8457d42cde)
--   - [`solvesOn_globalPatch`](https://prove2.me/theorems/2037a307-1801-4e9b-8f73-f67d1076a421)
--   - [`exists_globalSolution`](https://prove2.me/theorems/90eec698-1731-47a5-9f64-89ce1ff7ee42)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardGlobal.lean) · `LevyStochCalc.Ito.PicardGlobal` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardGlobal.lean#L86-L88 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardGlobal`, definition bundle `KLSModular_LevyStochCalc_Ito_PicardGlobal`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardWindow

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Ito
namespace Picard
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
/-- Glue a family of window solutions, using on `[0, t]` the member whose horizon covers `t`. -/
noncomputable def globalPatch (Y : ℕ → ℝ → Ω → (Fin n → ℝ)) : ℝ → Ω → (Fin n → ℝ) :=
  fun t ω => Y ⌈t⌉₊ t ω
end Picard
end Ito
end LevyStochCalc


