-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime
-- name    : KLSModular_LevyStochCalc_Probability_ExitTime
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:56:35.117994+00:00
-- url     : https://prove2.me/theorems/afef0596-dfb2-4d26-a303-b02e54dda356
-- title:
--   Exit sets, exit times, and rational grid points
-- statement:
--   Vendored from the upstream `LevyStochCalc` library at https://github.com/cgarryZA/LevyStochCalc, commit `984dbf0b790031eac05d56fe5a84b65e15e1e932` (Apache-2.0). For a path $t \mapsto X(\omega,t)$ in a normed additive group and level $k \in \mathbb{R}$, `exitSet X k ω` is the set of times $t \ge 0$ at which $\|X(\omega,t)\| \ge k$; `exitTime X k ω` is its infimum when nonempty, represented in $\mathbb{R} \cup \{\top\}$, and is $\top$ when the set is empty. `gridPt t n` enumerates the rationals using a fixed countable enumeration and clamps each value to $[0,t]$ by taking `max 0 (min t ·)`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Probability.Process.Stopping
--   import Mathlib.Data.Rat.Denumerable
--   import Mathlib.Topology.Order.Compact
--   import Mathlib.Topology.Order.Monotone
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def exitSet (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : Set ℝ := {t : ℝ | 0 ≤ t ∧ k ≤ ‖X ω t‖}
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`exitTime_le_iff`](https://prove2.me/theorems/ebd33cab-b36e-4b04-9cc1-92d3a27975cf)
--   - [`abs_clamp_sub_le`](https://prove2.me/theorems/dd3d7b99-46be-440b-a1a2-c53a92717bb6)
--   - [`exitTime_le_iff_forall`](https://prove2.me/theorems/71a39608-01e8-49d1-87e7-278e30c25025)
--   - [`norm_le_of_le_exitTime`](https://prove2.me/theorems/657fcfbb-b024-4d35-9d2d-20d9b2769cee)
--   - [`exists_lt_exitTime`](https://prove2.me/theorems/49d175b4-5189-43f1-894f-62a131c2b9d1)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Probability/ExitTime.lean) · `LevyStochCalc.Probability.ExitTime` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L29-L40 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, definition bundle `KLSModular_LevyStochCalc_Probability_ExitTime`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Probability.Process.Stopping
import Mathlib.Data.Rat.Denumerable
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Monotone

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/ExitTime.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
namespace LevyStochCalc
namespace Probability
universe u v
variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]
/-- The nonnegative times at which the path `X ω` has norm at least `k`. -/
def exitSet (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : Set ℝ := {t : ℝ | 0 ≤ t ∧ k ≤ ‖X ω t‖}
open scoped Classical in
/-- The first nonnegative time at which the path `X ω` has norm at least `k`, and `⊤` when the
path never reaches that norm. -/
noncomputable def exitTime (X : Ω → ℝ → E) (k : ℝ) (ω : Ω) : WithTop ℝ :=
  if (exitSet X k ω).Nonempty then ((sInf (exitSet X k ω) : ℝ) : WithTop ℝ) else ⊤
/-- The `n`-th rational, clamped to `[0, t]`. -/
noncomputable def gridPt (t : ℝ) (n : ℕ) : ℝ :=
  max 0 (min t (((Denumerable.eqv ℚ).symm n : ℚ) : ℝ))
end Probability
end LevyStochCalc


