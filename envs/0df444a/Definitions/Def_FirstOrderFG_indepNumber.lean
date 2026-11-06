-- Prove2me | Definitions.Def_FirstOrderFG_indepNumber
-- name    : FirstOrderFG_indepNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:31.911384+00:00
-- url     : https://prove2.me/theorems/ea0f80e6-fa5e-4a58-8e8a-5ad6414fc28d
-- title:
--   Independence number $\alpha$ of a directed graph
-- statement:
--   Let $G=(V,E)$ be a directed graph on a finite vertex set. A set $S\subseteq V$ is **independent** if no edge joins two distinct vertices of $S$ in either direction. The **independence number** is
--   $$
--   \alpha(G)=\max\{|S|:\ S\subseteq V\text{ independent}\}.
--   $$
--   Self-loops play no role. It is the graph quantity governing the first-order regret of the paper.
--
--   **Formalization Note** Independence is the published predicate `FirstPriceLearning.GraphFeedback.IsIndependentSet` (no edge $a\to b$ for distinct $a,b\in S$; ordered pairs cover both directions). The maximum is a `Finset.sup` over the finite family of independent subsets.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib
import Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph

namespace FirstOrderFG

open Classical in
/-- **The independence number `α`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3: "Denote by `α` the independence number of
`G`, defined as the largest cardinality of a vertex set with no edge between any two distinct
vertices in either direction."

`indepNumber E` is the largest cardinality of a finite vertex set `S` that is independent in the
sense of `FirstPriceLearning.GraphFeedback.IsIndependentSet` (no edge `a → b` between distinct
`a, b ∈ S`; quantifying over ordered pairs covers both directions; self-loops are ignored).

**Formalization Note.** The maximum is a `Finset.sup` over the (finite) family of independent
subsets of the finite vertex type, so it is a genuine maximum (the empty set is independent). -/
noncomputable def indepNumber {V : Type} [Fintype V] (E : V → V → Prop) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter
    (fun S => FirstPriceLearning.GraphFeedback.IsIndependentSet E S)).sup Finset.card

end FirstOrderFG


