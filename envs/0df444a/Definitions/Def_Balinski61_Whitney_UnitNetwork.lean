-- Prove2me | Definitions.Def_Balinski61_Whitney_UnitNetwork
-- name    : Balinski61_Whitney_UnitNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:44:00.651466+00:00
-- url     : https://prove2.me/theorems/a2d70863-3b79-48d3-8fff-ceed700be604
-- title:
--   The capacities of Whitney's proof: 1 on points, n + 1 on lines, 1 on the line p_s p_k (p. 434)
-- statement:
--   In the proof of Whitney's theorem (p. 434), Balinski turns a graph $G$ with two points $p_s, p_k$ and an integer $n \ge 0$ into a network:
--
--   1. every point other than $p_s$ and $p_k$ gets capacity $1$;
--   2. every line gets capacity $n+1$, except the line joining $p_s$ and $p_k$ (if it exists), which gets capacity $1$.
--
--   The paper assigns no capacity to $p_s$ and $p_k$; here they receive capacity $n+1$:
--   $$
--   c(x) = \begin{cases} n+1, & x \in \{p_s,p_k\},\\ 1, & \text{otherwise,}\end{cases}
--   \qquad
--   c(e) = \begin{cases} 1, & e = \{p_s,p_k\},\\ n+1, & \text{otherwise.}\end{cases}
--   $$
--
--   With these capacities an integral flow of value at least $n$ is the same thing as $n$ internally disjoint paths from $p_s$ to $p_k$.
--
--   **Formalization Note** The choice $n+1$ at the source and sink fills a gap the paper leaves open; any value $\ge n$ gives the same statements in this mission. The capacity of the pair $\{p_s,p_k\}$ is $1$ whether or not it is a line of $G$; when it is not a line, the value is never used.
-- source:
--   Balinski, On the graph structure of convex polyhedra in n-space, Pacific J. Math. 11 (1961), p. 434, proof of WHITNEY'S THEOREM: the capacity assignment

import Mathlib

namespace Balinski61.Whitney

variable {V : Type*} [DecidableEq V]

/-- Point capacities of the network of the proof of WHITNEY'S THEOREM (p. 434): capacity `1` at
every point other than the source `ps` and the sink `pk`. The paper assigns no capacity to `ps`
and `pk`; here they receive `n + 1`, the line capacity (any value `≥ n` serves the proof). -/
def unitCapV (ps pk : V) (n : ℕ) (x : V) : ℝ :=
  if x = ps ∨ x = pk then (n : ℝ) + 1 else 1

/-- Line capacities of the network of the proof of WHITNEY'S THEOREM (p. 434): capacity `n + 1`
on every line, except the line joining `ps` and `pk` (if such a line exists), which gets `1`. -/
def unitCapE (ps pk : V) (n : ℕ) (e : Sym2 V) : ℝ :=
  if e = s(ps, pk) then 1 else (n : ℝ) + 1

end Balinski61.Whitney


