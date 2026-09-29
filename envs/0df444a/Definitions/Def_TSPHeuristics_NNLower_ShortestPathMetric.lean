-- Prove2me | Definitions.Def_TSPHeuristics_NNLower_ShortestPathMetric
-- name    : TSPHeuristics_NNLower_ShortestPathMetric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:23:08.340266+00:00
-- url     : https://prove2.me/theorems/8eac16e3-ac0e-4e1a-9ff0-61b6a103ddbf
-- title:
--   Shortest-path distance in an undirected weighted graph given by an edge list
-- statement:
--   Let $E$ be a finite list of weighted edges $(a,b,w)$ on the node set $\mathbb N$; each edge joins $a$ and $b$ and has weight $w\in\mathbb R$, and an edge may be traversed in either direction. A **walk** from $x$ to $y$ is a sequence of edges leading from $x$ to $y$; its weight is the sum of the weights of its edges, and the empty walk from $x$ to $x$ has weight $0$. The **shortest-path distance** is
--   $$\delta_E(x,y)=\inf\{\,c : \text{some walk from } x \text{ to } y \text{ in } E \text{ has weight } c\,\}.$$
--   When all weights are nonnegative and $x$, $y$ are joined by some walk, this is the length of a minimal path from $x$ to $y$, the quantity the paper writes $\overline{XY}$ and uses to define $\bar G_i$ (pp. 568–569).
--
--   **Formalization Note** Walks are an inductive predicate `WalkCost E x y c`. The infimum is the real `sInf`; if no walk exists the set is empty and the value is $0$. All graphs this is applied to in this mission ($F_i$, $G_i$) are connected with positive weights, so the infimum is a minimum.
-- source:
--   Rosenkrantz, Stearns, Lewis, An Analysis of Several Heuristics for the Traveling Salesman Problem, SIAM J. Comput. 6(3), 1977, https://doi.org/10.1137/0206041, p. 568 ("d(a, b) is the length of the minimal path from a to b in G_i"), p. 569 ("the length of the shortest path between X and Y in F_{i+1}")

import Mathlib

namespace TSPHeuristics.NNLower

/-- `WalkCost E x y c`: in the undirected weighted (multi)graph whose edges are the triples
`(a, b, w) ∈ E` (an edge between nodes `a` and `b` of weight `w`), there is a walk from `x` to `y`
of total weight `c`. The empty walk from `x` to `x` has weight `0`; an edge may be traversed in
either direction. -/
inductive WalkCost (E : List (ℕ × ℕ × ℝ)) : ℕ → ℕ → ℝ → Prop
  | nil (x : ℕ) : WalkCost E x x 0
  | cons {x y z : ℕ} {w c : ℝ} (he : (x, y, w) ∈ E ∨ (y, x, w) ∈ E) (h : WalkCost E y z c) :
      WalkCost E x z (w + c)

/-- The shortest-path distance between `x` and `y` in the weighted graph `E`: the infimum of the
weights of all walks from `x` to `y`. For nonnegative weights and `x`, `y` in the same connected
component this is the length of a minimal path. (If no walk exists the set is empty and the real
`sInf` is `0`; the graphs this is applied to are connected.) -/
noncomputable def spDist (E : List (ℕ × ℕ × ℝ)) (x y : ℕ) : ℝ :=
  sInf {c : ℝ | WalkCost E x y c}

end TSPHeuristics.NNLower


