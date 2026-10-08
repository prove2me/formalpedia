-- Prove2me | Definitions.Def_YoungConventions_AdaptivePlay_shortestPathLength
-- name    : YoungConventions_AdaptivePlay_shortestPathLength
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:00:54.803986+00:00
-- url     : https://prove2.me/theorems/20efe7a9-6135-467c-bf35-47842918368b
-- title:
--   $L(s)$, the length of a shortest best-reply path to a strict Nash equilibrium (§4, p. 64)
-- statement:
--   For a strategy tuple $s$ of a weakly acyclic game, $L(s)$ is the length of a shortest directed path in the best-reply graph from $s$ to a strict Nash equilibrium:
--   $$L(s) = \min\{\, n \in \mathbb N : \text{there is a best-reply path of length } n \text{ from } s \text{ to a strict pure Nash equilibrium} \,\}.$$
--
--   **Formalization Note** The minimum is `sInf` on $\mathbb N$. In a weakly acyclic game the set is nonempty for every $s$ (every sink is a strict Nash equilibrium), so the value is the true minimum; Lean's convention $\inf \emptyset = 0$ is never reached in the setting where the paper and the theorems use $L(s)$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsPathToStrictNash

namespace YoungConventions.AdaptivePlay

/-- **`L(s)`, the length of a shortest best-reply path to a strict Nash equilibrium** (Young 1993,
*The Evolution of Conventions*, Econometrica 61:57–84, §4, p. 64, PDF p. 9): "For each
strategy-tuple `s`, let `L(s)` be the length of a shortest directed path in the best reply graph
from `s` to a strict Nash equilibrium."

`shortestPathLength u s` is the least `n` such that a directed path of `n` edges leads from `s` to a
strict pure Nash equilibrium.

**Formalization Note.** Defined as `sInf` of a set of natural numbers. In a weakly acyclic game
(the only setting in which the paper and the theorems of this mission use `L(s)`) the set is
nonempty for every `s` (a sink is a strict Nash equilibrium), so the value is the true minimum; the
convention `sInf ∅ = 0` of Lean is never reached under that hypothesis. -/
noncomputable def shortestPathLength {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : ℕ :=
  sInf {n : ℕ | IsPathToStrictNash u s n}

end YoungConventions.AdaptivePlay


