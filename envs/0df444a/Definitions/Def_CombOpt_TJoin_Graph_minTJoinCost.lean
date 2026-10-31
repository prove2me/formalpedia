-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_minTJoinCost
-- name    : CombOpt_TJoin_Graph_minTJoinCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:11.30583+00:00
-- url     : https://prove2.me/theorems/145d31b5-a4ef-4e9c-b253-3a9fd503f418
-- title:
--   Minimum cost of a $T$-join
-- statement:
--   For a graph $G=(V,E)$, $T\subseteq V$ and costs $c\in\mathbb R^E$, the **minimum cost of a $T$-join** is
--
--   $$\min\{c(J):\ J \text{ a } T\text{-join of } G\},\qquad c(J)=\sum_{e\in J}c_e,$$
--
--   the optimal value of the Optimal $T$-Join Problem.
--
--   **Formalization Note** The value is taken in the extended reals $\overline{\mathbb R}$ as an infimum over the finitely many edge sets: it is the real minimum when a $T$-join exists and $+\infty$ when none exists.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.4, Optimal T-Join Problem, p. 168 (PDF p. 176)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph
import Definitions.Def_CombOpt_TJoin_Graph_cut
import Definitions.Def_CombOpt_TJoin_Graph_IsTJoin

namespace CombOpt.TJoin

/-- **The minimum cost of a T-join.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 168 (PDF p. 176), Optimal T-Join Problem: "Given: A graph G = (V, E), a set
T ⊆ V such that |T| is even, and a cost vector c ∈ R^E. Objective: Find a T-join J of G such
that c(J) is minimum."

`G.minTJoinCost T c` is the infimum, in `EReal`, of `c(J) = ∑_{e ∈ J} c e` over all T-joins `J`.

**Formalization Note.** There are finitely many edge sets, so when a T-join exists the infimum
is a minimum and is a real number; when none exists the infimum of the empty family is `⊤`. -/
noncomputable def Graph.minTJoinCost {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (T : Finset V) (c : E → ℝ) : EReal :=
  ⨅ (J : Finset E) (_ : G.IsTJoin T J), ((∑ e ∈ J, c e : ℝ) : EReal)

end CombOpt.TJoin


