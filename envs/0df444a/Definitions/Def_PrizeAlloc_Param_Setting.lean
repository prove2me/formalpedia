-- Prove2me | Definitions.Def_PrizeAlloc_Param_Setting
-- name    : PrizeAlloc_Param_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:28.587868+00:00
-- url     : https://prove2.me/theorems/e1ca7753-ce81-4b1b-9bc9-e43b7bf973f1
-- title:
--   pp. 8–10, 14, 15, 20 — competitions, subrankings, prize allocation rules and the axioms
-- statement:
--   Let $U$ be a countable set of potential competitors. A **competition** $(N,\mathcal R,E)$ consists of a finite nonempty set $N\subseteq U$, a **ranking** $\mathcal R:N\to\{1,\dots,|N|\}$ (a bijection; $i$ is ranked above $j$ when $\mathcal R(i)<\mathcal R(j)$), and a **prize endowment** $E\ge 0$. For $S\subseteq N$ the **subranking** $\mathcal R_S:S\to\{1,\dots,|S|\}$ orders $S$ as $\mathcal R$ does.
--
--   A **prize allocation rule** $\varphi$ assigns to every competition a vector $\varphi(N,\mathcal R,E)\in\mathbb R_+^N$ with
--
--   $$\sum_{i\in N}\varphi_i(N,\mathcal R,E)=E.$$
--
--   The axioms used in this mission are, for all competitions in the domain:
--
--   1. **Anonymity**: $\varphi_i(N,\mathcal R,E)=\varphi_j(N',\mathcal R',E)$ whenever $|N|=|N'|$ and $\mathcal R(i)=\mathcal R'(j)$.
--   2. **Order preservation**: $\mathcal R(i)<\mathcal R(j)$ implies $\varphi_i(N,\mathcal R,E)\ge\varphi_j(N,\mathcal R,E)$.
--   3. **Endowment monotonicity**: $E<E'$ implies $\varphi_i(N,\mathcal R,E)\le\varphi_i(N,\mathcal R,E')$ for every $i$.
--   4. **Endowment continuity**: $E\mapsto\varphi_i(N,\mathcal R,E)$ is continuous on $\mathbb R_+$ for every $i$.
--   5. **Winner strict endowment monotonicity**: endowment monotonicity, and in addition $E<E'$ implies $\varphi_i(N,\mathcal R,E)<\varphi_i(N,\mathcal R,E')$ when $\mathcal R(i)=1$.
--   6. **Top consistency**: for every nonempty $S\subseteq N$ with $\mathcal R(i)\le|S|$ for each $i\in S$ (that is, $S$ is the top segment of the ranking) and every $i\in S$,
--   $$\varphi_i(N,\mathcal R,E)=\varphi_i\Big(S,\mathcal R_S,\sum_{j\in S}\varphi_j(N,\mathcal R,E)\Big).$$
--   7. **Endowment additivity**: $\varphi_i(N,\mathcal R,E+E')=\varphi_i(N,\mathcal R,E)+\varphi_i(N,\mathcal R,E')$ for $E,E'\ge 0$.
--   8. **Scale invariance**: $\varphi_i(N,\mathcal R,E)=E\,\varphi_i(N,\mathcal R,1)$ for $E\ge 0$.
--
--   These are the objects of Theorem 3 and Corollary 8 of the paper; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** A pair $(N,\mathcal R)$ is a duplicate-free nonempty list $l$ of elements of $U$, best competitor first: $N$ is the set of entries of $l$, $|N|$ its length, and $\mathcal R(i)$ is `pos l i`, the 1-based index of $i$ in $l$. $N$ is nonempty because no allocation of $E>0$ to an empty set exists. The subranking $\mathcal R_S$ is the sublist of entries in $S$. A rule is a function $\varphi(l,E,i)\in\mathbb R$; its values off the domain (lists that are not rankings, $E<0$, $i\notin l$) are irrelevant, and every axiom quantifies only over rankings, $E\ge 0$ and competitors in the ranking. Top consistency requires $S$ nonempty, which is automatic for the conclusion ($\forall i\in S$). The page's convergence $\varphi(N,\mathcal R,E)\to\varphi(N,\mathcal R,E')$ in $\mathbb R^N$ is coordinatewise continuity.
-- source:
--   Dietzenbacher and Kondratev, Fair and Consistent Prize Allocation in Competitions, arXiv:2008.08985v2, pp. 8–10 (§2.1 model, anonymity, order preservation, endowment monotonicity, endowment continuity, subranking), p. 14 (winner strict endowment monotonicity), p. 15 (endowment additivity, scale invariance), p. 20 (top consistency)

import Mathlib
import Definitions.Def_PrizeAlloc_Interval_Companions
import Definitions.Def_PrizeAlloc_Interval_Setting

namespace PrizeAlloc.Param

variable {U : Type*} [DecidableEq U]

/-- Top consistency (p. 20): consistency for the subsets `S` with `R(i) ≤ |S|` for each `i ∈ S`,
i.e. the top `|S|` positions. -/
def TopConsistent (φ : List U → ℝ → U → ℝ) : Prop :=
  ∀ l E, PrizeAlloc.Interval.IsRanking l → 0 ≤ E → ∀ S : Finset U, S ⊆ l.toFinset → S.Nonempty →
    (∀ i ∈ S, PrizeAlloc.Interval.pos l i ≤ S.card) →
    ∀ i ∈ S, φ l E i = φ (PrizeAlloc.Interval.sub l S) (∑ j ∈ S, φ l E j) i

end PrizeAlloc.Param


