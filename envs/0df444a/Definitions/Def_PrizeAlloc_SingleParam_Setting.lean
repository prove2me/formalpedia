-- Prove2me | Definitions.Def_PrizeAlloc_SingleParam_Setting
-- name    : PrizeAlloc_SingleParam_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:23.705992+00:00
-- url     : https://prove2.me/theorems/b81bc4f5-8715-49ac-87e7-a8fcb933f6ff
-- title:
--   p. 16 — local consistency
-- statement:
--   Local consistency (p. 16), the axiom of Theorem 2 that is specific to this mission. The model (competitions, rankings, subrankings, prize allocation rules) and the axioms anonymity, order preservation, endowment monotonicity, endowment continuity and winner strict endowment monotonicity are the shared definitions `PrizeAlloc.Interval.Setting` and `PrizeAlloc.Interval.Companions`.
--
--   A prize allocation rule $\varphi$ is **locally consistent** if for each competition $(N,\mathcal R,E)$, each $S\subseteq N$ with $|\mathcal R(i)-\mathcal R(j)|\le|S|-1$ for all $i,j\in S$ (a block of consecutive positions) and each $i\in S$,
--   $$\varphi_i(N,\mathcal R,E)=\varphi_i\Big(S,\mathcal R_S,\sum_{j\in S}\varphi_j(N,\mathcal R,E)\Big).$$
--
--   **Formalization Note** A pair $(N,\mathcal R)$ is a duplicate-free nonempty list `l` of elements of $U$, best competitor first; $\mathcal R(i)$ is `pos l i` (1-based) and $\mathcal R_S$ is the sublist of `l` of the entries in $S$. The axiom quantifies only over rankings, $E\ge 0$ and $S\subseteq N$. The condition $|\mathcal R(i)-\mathcal R(j)|\le|S|-1$ is written $\mathcal R(i)\le\mathcal R(j)+(|S|-1)$ for all ordered pairs, which covers both signs; for $S=\emptyset$ the axiom is vacuous.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, p. 16, Axiom: local consistency

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Companions
import Definitions.Def_PrizeAlloc_Interval_Setting

namespace PrizeAlloc.SingleParam

variable {U : Type*} [DecidableEq U]

/-- Local consistency (p. 16): for every subset `S ⊆ N` with `|R(i) − R(j)| ≤ |S| − 1` for all
`i, j ∈ S` (a block of consecutive positions), every `i ∈ S` receives in the reduced competition
`(S, R_S, ∑_{j ∈ S} φ_j(N, R, E))` the same prize as in `(N, R, E)`. -/
def LocallyConsistent (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ l E, PrizeAlloc.Interval.IsRanking l → 0 ≤ E → ∀ S : Finset U, S ⊆ l.toFinset →
    (∀ i ∈ S, ∀ j ∈ S, PrizeAlloc.Interval.pos l i ≤ PrizeAlloc.Interval.pos l j + (S.card - 1)) →
    ∀ i ∈ S, φ l E i = φ (PrizeAlloc.Interval.sub l S) (∑ j ∈ S, φ l E j) i

end PrizeAlloc.SingleParam


