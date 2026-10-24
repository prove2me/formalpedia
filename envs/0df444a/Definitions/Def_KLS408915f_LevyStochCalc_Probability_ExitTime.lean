-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Probability_ExitTime
-- name    : KLS408915f_LevyStochCalc_Probability_ExitTime
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T11:27:02.762946+00:00
-- url     : https://prove2.me/theorems/2512307e-613e-47a5-bcc9-ffc1400ad226
-- title:
--   Exit sets, exit times, and rational grid points
-- statement:
--   Vendored from the upstream `LevyStochCalc` library at https://github.com/cgarryZA/LevyStochCalc, commit `984dbf0b790031eac05d56fe5a84b65e15e1e932` (Apache-2.0). For a path $t \mapsto X(\omega,t)$ in a normed additive group and level $k \in \mathbb{R}$, `exitSet X k ω` is the set of times $t \ge 0$ at which $\|X(\omega,t)\| \ge k$; `exitTime X k ω` is its infimum when nonempty, represented in $\mathbb{R} \cup \{\top\}$, and is $\top$ when the set is empty. `gridPt t n` enumerates the rationals using a fixed countable enumeration and clamps each value to $[0,t]$ by taking `max 0 (min t ·)`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/ExitTime.lean#L29-L40 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.ExitTime`, definition bundle `KLS408915f_LevyStochCalc_Probability_ExitTime`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Data.Rat.Denumerable
import Mathlib.Probability.Process.Stopping
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


