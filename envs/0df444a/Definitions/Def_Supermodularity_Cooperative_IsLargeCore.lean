-- Prove2me | Definitions.Def_Supermodularity_Cooperative_IsLargeCore
-- name    : Supermodularity_Cooperative_IsLargeCore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:00:23.784696+00:00
-- url     : https://prove2.me/theorems/28011452-bd94-4c53-a78a-8624fcab06b5
-- title:
--   Section 5.1 - a large core
-- statement:
--   The core of a (sub)game on coalition $U$ is **large** (p. 209) if every acceptable payoff vector
--   $y''$ on $U$ (i.e. $f(S) \le \sum_{i \in S} y''_i$ for every $S \subseteq U$) is dominated on $U$,
--   coordinatewise, by some payoff vector $y' \in \mathrm{Core}(U,f)$: $y'_i \le y''_i$ for every
--   $i \in U$.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 209, Section 5.1

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core

namespace Supermodularity.Cooperative

/-- `IsLargeCore U f` says the core of the (sub)game on coalition `U` is large
(Topkis p. 209): every payoff vector `y''` that is acceptable on `U`
(`f S ≤ ∑_{i∈S} y'' i` for every `S ⊆ U`) is dominated on `U`, coordinatewise, by
some payoff vector `y'` in `Core U f`. -/
def IsLargeCore {n : ℕ} (U : Finset (Fin n)) (f : Finset (Fin n) → ℝ) : Prop :=
  ∀ y'' : Fin n → ℝ, (∀ S ⊆ U, f S ≤ ∑ i ∈ S, y'' i) →
    ∃ y' ∈ Core U f, ∀ i ∈ U, y' i ≤ y'' i

end Supermodularity.Cooperative


