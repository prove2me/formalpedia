-- Prove2me | Definitions.Def_JohnsonApprox_SubsetSum_Supplement_NCPrime
-- name    : JohnsonApprox_SubsetSum_Supplement_NCPrime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:26:06.880589+00:00
-- url     : https://prove2.me/theorems/3f06f695-211a-423a-8a0f-0810fd25b9f9
-- title:
--   NODE COVER as SET COVERING I: the restrictions NC′(k) and the no-parallel-arcs condition (Section 5, p. 269)
-- statement:
--   This definition sets up the problem $\mathrm{NC}'(k)$ of Johnson (1974), node cover in graphs in which every node is incident to exactly $k$ arcs, inside the paper's own SET COVERING I framework. The paper says:
--
--   > NC is equivalent to SC with inputs F restricted so that every point in $\bigcup_{S\in F} S$ is in precisely two sets of F, for in this case the points may be made to correspond to arcs of a graph and the sets to nodes. However, if we still further restrict the inputs, and let SC′(k) and NC′(k) be the problems where *exactly* k elements are in each set of the input family F, …
--
--   An input of SET COVERING I is a finite family $S_i$, $i \in \iota$, of finite sets, with ground set $T = \bigcup_i S_i$. Read as a graph, the indices $i$ are the **nodes**, the points of $T$ are the **arcs**, and $S_i$ is the set of arcs at node $i$.
--
--   1. **Every point in precisely two sets.** For every $a \in T$,
--   $$\#\{\, i \in \iota : a \in S_i \,\} = 2 .$$
--   Then each arc has exactly two distinct endpoints, so the family is the arc–node incidence of a graph without loops.
--   2. **$\mathrm{NC}'(k)$.** The family satisfies (1) and $|S_i| = k$ for every $i$: every node is incident to exactly $k$ arcs.
--   3. **No parallel arcs.** For distinct $i \ne j$, $|S_i \cap S_j| \le 1$: two nodes are joined by at most one arc. Together with (1), this makes the encoded graph a simple graph.
--
--   The measure, the optimum $F^*$ and algorithm C1 are those of SET COVERING I. A node cover $N' \subseteq N$ is exactly a subfamily covering $T$, and $m(N') = |N'|$. These predicates are what Theorem 5 is stated over.
--
--   **Formalization Note** The family is `S : ι → Finset α` over a `Fintype` index type, as in the published `JohnsonApprox.SetCover.Problem`. "Precisely two sets" counts indices, so the two endpoints of an arc are two nodes even when their arc sets coincide (a single arc between two degree-1 nodes). Condition (1) alone still admits parallel arcs; `NoParallelArcs` is a separate predicate so that existence statements can demand a genuine simple graph, while upper bounds can quantify over all of `InNCPrime k`.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 269, Section 5 (NODE COVER, NC(k), NC′(k))

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem

namespace JohnsonApprox.SubsetSum.Supplement

/-!
NODE COVER as a restriction of SET COVERING I (Johnson 1974, p. 269).

"NC is equivalent to SC with inputs F restricted so that every point in ⋃_{S∈F} S is in precisely
two sets of F, for in this case the points may be made to correspond to arcs of a graph and the
sets to nodes." `NC′(k)` further requires "exactly k elements … in each set of the input family F".

An input is an indexed family `S : ι → Finset α` of the published SET COVERING I definition:
indices are nodes, points are arcs, and `S i` is the set of arcs at node `i`.
-/

variable {ι α : Type} [Fintype ι] [DecidableEq α]

/-- Every point of `T = ⋃_i S_i` lies in precisely two sets of the family, counted by index:
`#{i | a ∈ S_i} = 2`. Such a family is the arc–node incidence of a graph without loops. -/
def EveryPointInTwo (S : ι → Finset α) : Prop :=
  ∀ a ∈ JohnsonApprox.SetCover.ground S, (Finset.univ.filter (fun i => a ∈ S i)).card = 2

/-- `S` is an input of `NC′(k)`: every point is in precisely two sets and every set has exactly
`k` elements (every node is incident to exactly `k` arcs). -/
def InNCPrime (k : ℕ) (S : ι → Finset α) : Prop :=
  EveryPointInTwo S ∧ ∀ i, (S i).card = k

/-- No two distinct nodes share more than one arc: the encoded graph has no parallel arcs. -/
def NoParallelArcs (S : ι → Finset α) : Prop :=
  ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1

end JohnsonApprox.SubsetSum.Supplement


