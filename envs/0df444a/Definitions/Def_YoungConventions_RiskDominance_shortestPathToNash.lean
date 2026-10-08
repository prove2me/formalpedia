-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_shortestPathToNash
-- name    : YoungConventions_RiskDominance_shortestPathToNash
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:33.928967+00:00
-- url     : https://prove2.me/theorems/4885e928-4934-4174-9f92-8459aba4b721
-- title:
--   $L(s)$: shortest best-reply path to a strict equilibrium
-- statement:
--   For a strategy-tuple $s$, $L(s)$ is the length of a shortest directed path in the best-reply graph from $s$ to a strict Nash equilibrium:
--   $$L(s)=\min\{n : \text{there is a best-reply path of length } n \text{ from } s \text{ to a strict pure Nash equilibrium}\}.$$
--
--   **Formalization Note** The minimum is the infimum on $\mathbb N$. In a weakly acyclic game the set is nonempty for every $s$; in the $2\times2$ games of this mission it is nonempty as well, so the convention $\inf\emptyset=0$ is not used.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64

import Mathlib
import Definitions.Def_YoungConventions_RiskDominance_BestReplyPath
import Definitions.Def_YoungConventions_AdaptivePlay_IsStrictNash

namespace YoungConventions.RiskDominance

/-- **`L(s)`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §4, p. 64 (PDF p. 9): "For each strategy-tuple `s`, let `L(s)` be the length
of a shortest directed path in the best reply graph from `s` to a strict Nash equilibrium".

**Formalization Note.** `sInf` on `ℕ`. In a weakly acyclic game the set is nonempty for every `s`
(every sink is a strict Nash equilibrium, p. 64), so the junk value `sInf ∅ = 0` is not used there;
in the `2 × 2` games of this mission it is nonempty as well. -/
noncomputable def shortestPathToNash {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (u : ι → ((i : ι) → S i) → ℝ) (s : (i : ι) → S i) : ℕ :=
  sInf {n : ℕ | ∃ s', YoungConventions.AdaptivePlay.IsStrictNash u s' ∧ BestReplyPath u n s s'}

end YoungConventions.RiskDominance


