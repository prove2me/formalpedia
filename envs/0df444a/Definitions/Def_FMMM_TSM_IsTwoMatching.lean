-- Prove2me | Definitions.Def_FMMM_TSM_IsTwoMatching
-- name    : FMMM_TSM_IsTwoMatching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:35.197989+00:00
-- url     : https://prove2.me/theorems/2f616a26-9b3e-41d9-aaa2-7303413e892c
-- title:
--   2-matchings: integral flows of the boosted flow graph $G_f$
-- statement:
--   Let $G = (A, J, E)$ be a bipartite graph with ads $A$ and impression types $J$. The **boosted flow graph** $G_f$ has a source $s$ with an edge of capacity $2$ to every ad, the edges $(a, j) \in E$ directed from $A$ to $J$ with capacity $1$, and an edge of capacity $2$ from every impression type to a sink $t$.
--
--   A set $F \subseteq E$ is a **2-matching** of $E$ if every ad and every impression type is incident to at most two edges of $F$.
--
--   The integral $s$–$t$ flows of $G_f$ are exactly the 2-matchings: the unit-flow edges of an integral flow form a 2-matching $F = E_f$, every 2-matching arises this way, and the flow value is $|F|$.
--
--   **Formalization Note** The flow is represented by its support $E_f$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.1, p. 6 (boosted flow graph G_f, capacities 2, 1, 2)

import Mathlib

namespace FMMM.TSM

/-- **Integral flows of the boosted flow graph `G_f` (2-matchings).**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.1, p. 6: the boosted flow graph `G_f` has a source `s` with edges of
capacity 2 to every ad, the edges `(a, i) ∈ E` with capacity 1, and edges of capacity 2 from every
impression type to the sink `t`.

`IsTwoMatching E F` says `F ⊆ E` and every ad and every impression type is incident to at most two
edges of `F`.

**Formalization Note.** An integral `s`–`t` flow of `G_f` is determined by its set `E_f` of
unit-flow edges `(a, i)`; the sets that arise are exactly the subsets of `E` in which every vertex
has degree at most 2, and the flow value is `|E_f|`. So an integral flow is encoded by its support
`F = E_f`. -/
def IsTwoMatching {A J : Type} [DecidableEq A] [DecidableEq J] (E F : Finset (A × J)) : Prop :=
  F ⊆ E ∧ (∀ a : A, (F.filter (fun e => e.1 = a)).card ≤ 2) ∧
    ∀ j : J, (F.filter (fun e => e.2 = j)).card ≤ 2

end FMMM.TSM


