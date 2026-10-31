-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_IsTJoin
-- name    : CombOpt_TJoin_Graph_IsTJoin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:21.478286+00:00
-- url     : https://prove2.me/theorems/08a2e35c-a71e-468f-98dd-54a37aacd4b1
-- title:
--   $T$-join
-- statement:
--   Let $G=(V,E)$ be a graph and $T\subseteq V$. A set $J\subseteq E$ is a **$T$-join** of $G$ if
--
--   $$|J\cap\delta(v)|\equiv|T\cap\{v\}|\pmod 2\qquad\text{for all } v\in V,$$
--
--   that is, the nodes of odd degree in the subgraph $(V,J)$ are exactly the elements of $T$. Examples: for $T=\emptyset$ the $T$-joins are the even edge sets; for $T=\{r,s\}$ every $T$-join contains an $(r,s)$-path; for $T$ the set of odd-degree nodes the $T$-joins are the postman sets.
--
--   **Formalization Note** The book introduces $T$-joins for $|T|$ even; the predicate is defined for every $T$, and every theorem of the mission assumes $|T|$ even. Loops lie in no $\delta(v)$ and never affect the parity.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, p. 167 (PDF p. 175)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut

namespace CombOpt.TJoin

/-- **T-join.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 167 (PDF p. 175): "Let G = (V, E) be a graph, and let T ⊆ V such that |T| is
even. A T-join of G is a set J of edges such that |J ∩ δ(v)| ≡ |T ∩ {v}| (mod 2), for all
v ∈ V."

`G.IsTJoin T J` holds when, at every node `v`, the number of edges of `J` in the star `δ(v)` has
the parity of `|T ∩ {v}|`.

**Formalization Note.** The predicate is defined for every `T`; the book introduces it under
the standing assumption `|T|` even, and every theorem of this mission carries `Even T.card`.
Loops are in no `δ(v)`, so they never affect the parity, as in the book. -/
def Graph.IsTJoin {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (T : Finset V) (J : Finset E) : Prop :=
  ∀ v : V, (J ∩ G.cut {v}).card ≡ (T ∩ {v}).card [MOD 2]

end CombOpt.TJoin


