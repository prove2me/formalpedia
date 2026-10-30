-- Prove2me | Definitions.Def_FMMM_TSM_IsMaxTwoMatching
-- name    : FMMM_TSM_IsMaxTwoMatching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:15:11.225725+00:00
-- url     : https://prove2.me/theorems/72eb0e26-757c-48a8-8036-e61494973eb1
-- title:
--   Maximum 2-matching: the integral max flow $E_f$ of $G_f$
-- statement:
--   A set $F \subseteq E$ is a **maximum 2-matching** of $E$ if it is a 2-matching (every ad and every impression type has at most two incident edges of $F$) and no 2-matching of $E$ has more edges.
--
--   By the correspondence between integral flows of the boosted flow graph $G_f$ and 2-matchings, the maximum 2-matchings are exactly the edge sets $E_f$ of integral maximum flows of $G_f$: "We find a max-flow in this graph from $s$ to $t$. Since all the capacities are integers, we may assume that the resulting flow is integral. Let $E_f$ be the set of edges $(a, i) \subseteq E$ with non-zero flow on them." It is the offline object from which the two suggested matchings algorithm builds its two matchings.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.1, p. 6 (max-flow in G_f, integral flow, E_f)

import Mathlib
import Definitions.Def_FMMM_TSM_IsTwoMatching

namespace FMMM.TSM

/-- **Integral maximum flow of the boosted flow graph `G_f` (maximum 2-matching).**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.1, p. 6: "We find a max-flow in this graph from s to t. Since all the
capacities are integers, we may assume that the resulting flow is integral [18]. Let E_f be the set
of edges (a, i) ⊆ E with non-zero flow on them, which must be unit flow."

`IsMaxTwoMatching E F` says that `F` is a 2-matching of `E` (`IsTwoMatching E F`) of maximum
cardinality among all 2-matchings of `E`.

**Formalization Note.** Integral flows of `G_f` correspond to 2-matchings `F` with flow value
`|F|` (see `IsTwoMatching`), so the integral maximum flows are exactly the maximum 2-matchings and
`E_f = F`. -/
def IsMaxTwoMatching {A J : Type} [DecidableEq A] [DecidableEq J] (E F : Finset (A × J)) : Prop :=
  IsTwoMatching E F ∧ ∀ F' : Finset (A × J), IsTwoMatching E F' → F'.card ≤ F.card

end FMMM.TSM


