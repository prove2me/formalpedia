-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_IsGreedyOutput
-- name    : CombOpt_MatroidPolytope_IsGreedyOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:52.799155+00:00
-- url     : https://prove2.me/theorems/20041f16-d854-4000-a771-e9cd67075cb1
-- title:
--   A set returned by the Greedy Algorithm
-- statement:
--   A set $J\subseteq S$ is an **output of the Greedy Algorithm** for $\mathcal I$ and $c$ if it is reached from $\emptyset$ by finitely many iterations of the algorithm and the while condition fails at $J$: there is no $e\notin J$ with $c_e>0$ and $J\cup\{e\}\in\mathcal I$.
--
--   Every run of the algorithm stops (each iteration adds a new element of the finite set $S$) at such a set; when ties occur, different runs may stop at different sets.
--
--   **Formalization Note** Reachability is the reflexive–transitive closure of the one-iteration relation `GreedyStep`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, p. 274 (PDF p. 281), the box "Greedy Algorithm"

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_GreedyStep

namespace CombOpt.MatroidPolytope

/-- **A set the Greedy Algorithm can return.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, p. 274 (PDF p. 281), the box *Greedy Algorithm*: start from `J = ∅`, repeat the
while loop, and stop when there is no `e ∉ J` with `c_e > 0` and `J ∪ {e} ∈ I`.

`IsGreedyOutput I c J` says that `J` is reached from `∅` by finitely many iterations
(`GreedyStep`) and that the loop condition fails at `J`, so the algorithm stops with `J`.

**Formalization Note.** Because ties are broken arbitrarily, several sets may be outputs of the
algorithm for the same `c`; each run of the algorithm ends at one of them. -/
def IsGreedyOutput {α : Type*} [DecidableEq α] (I : Finset α → Prop) (c : α → ℝ)
    (J : Finset α) : Prop :=
  Relation.ReflTransGen (GreedyStep I c) ∅ J ∧ ¬ ∃ e : α, e ∉ J ∧ 0 < c e ∧ I (insert e J)

end CombOpt.MatroidPolytope


