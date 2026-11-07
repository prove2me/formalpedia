-- Prove2me | Definitions.Def_MulticastPoS_IsGrouping
-- name    : MulticastPoS_IsGrouping
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:35.058203+00:00
-- url     : https://prove2.me/theorems/4648a3b0-efaf-49d0-b028-79eec856934c
-- title:
--   Guarantees of the grouping with parameter $Q$
-- statement:
--   Let $Q\ge 1$ and let $S$ be a subgraph of $G$. A partition $\pi$ of the players into groups, an optional residual group $g_0$ and subgraphs $(R_g)$ form a **grouping with parameter $Q$ on $S$** if
--
--   1. every nonresidual group satisfies $Q\le |g|<2Q$;
--   2. the residual group $g_0$, if present, is one of the groups, has $|g_0|<Q$, and $t\in V(R_{g_0})$;
--   3. every $R_g$ is a connected subgraph of $S$ with $\ell(g)=\{s_i : i\in g\}\subseteq V(R_g)$;
--   4. $E(R_g)\cap E(R_h)=\emptyset$ for distinct groups $g\ne h$.
--
--   These are the properties of the grouping procedure listed in Lemma 4.1; Sections 4.2 and 5 use only them.
--
--   **Formalization Note** A subgraph $R_g$ consisting of one vertex and no edges is allowed (a group completed at one vertex).
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 4.1 and Lemma 4.1, pp.7–8

import Mathlib
import Definitions.Def_MulticastPoS_nonresidual

namespace MulticastPoS

/-- The guarantees of the grouping procedure with parameter `Q` on a tree `S` (Huang–Yuan, *An
O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games*, STOC
2027 submission manuscript (sha256 dd0e08d0…f6d4), Section 4.1 and Lemma 4.1, pp.7–8): `π`
partitions the players (source occurrences) into groups, `g₀` is the residual group if there is
one, and `R g` is the connected subgraph associated with group `g`, such that

1. every nonresidual group has `Q ≤ |g| < 2Q`;
2. the residual group, if present, is a group with `|g₀| < Q` and `t ∈ V(R_{g₀})`;
3. every `R g` is a connected subgraph of `S` with `ℓ(g) ⊆ V(R g)`;
4. `E(R g) ∩ E(R h) = ∅` for distinct groups `g ≠ h`.

**Formalization Note** Groups are `Finset`s of players and `ℓ(g) = {s i : i ∈ g}`. A subgraph
`R g` with a single vertex and no edge is allowed (a group completed at one vertex). -/
def IsGrouping {V ι : Type*} [Fintype ι] [DecidableEq ι] {G : SimpleGraph V} (t : V)
    (s : ι → V) (Q : ℕ) (S : G.Subgraph) (π : Finpartition (Finset.univ : Finset ι))
    (g₀ : Option (Finset ι)) (R : Finset ι → G.Subgraph) : Prop :=
  (∀ g ∈ nonresidual π g₀, Q ≤ g.card ∧ g.card < 2 * Q) ∧
  (∀ g, g₀ = some g → g ∈ π.parts ∧ g.card < Q ∧ t ∈ (R g).verts) ∧
  (∀ g ∈ π.parts, R g ≤ S ∧ (R g).Connected ∧ ∀ i ∈ g, s i ∈ (R g).verts) ∧
  (∀ g ∈ π.parts, ∀ h ∈ π.parts, g ≠ h → Disjoint (R g).edgeSet (R h).edgeSet)

end MulticastPoS


