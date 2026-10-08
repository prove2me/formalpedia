-- Prove2me | Definitions.Def_SteinbergFalse_Counterexample_NoFourFiveCycle
-- name    : SteinbergFalse_Counterexample_NoFourFiveCycle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:30.86426+00:00
-- url     : https://prove2.me/theorems/aa89d679-dc69-4577-b7ab-5faa9767cdd5
-- title:
--   Graphs with no cycles of length four or five
-- statement:
--   Let $H$ be a simple graph on a vertex set $V$. A **cycle** of length $k$ in $H$ is a closed walk $v_0 v_1 \dots v_{k-1} v_0$ with $k \ge 3$ that uses no edge twice and whose vertices $v_0, \dots, v_{k-1}$ are pairwise distinct. We say that $H$ has **no cycles of length four or five** if every cycle of $H$ has length different from $4$ and from $5$:
--
--   $$
--   \text{for every cycle } C \text{ of } H:\qquad |C| \ne 4 \ \text{ and } \ |C| \ne 5 .
--   $$
--
--   This is the hypothesis of Steinberg's Conjecture (1976): every planar graph with no cycles of length four or five is 3-colorable. Triangles and cycles of length six or more are allowed.
--
--   **Formalization Note** A cycle is a Mathlib walk `p : H.Walk v v` with `p.IsCycle` (a closed trail of length at least three whose only repeated vertex is its common start and end); its length is `p.length`, the number of edges. Closed walks in general are not used: every edge yields a closed walk of length four, so "no closed walk of length four" would exclude every graph with an edge.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 1, Abstract and §1 (statement of Steinberg's Conjecture); p. 2, Lemma 1

import Mathlib

namespace SteinbergFalse.Counterexample

/-- A simple graph `H` has **no cycles of length four or five** if every cycle of `H`
(a closed walk `p` with `p.IsCycle`: a closed trail of length at least three whose only
repeated vertex is its start and end) has length different from `4` and from `5`. -/
def NoFourFiveCycle {V : Type*} (H : SimpleGraph V) : Prop :=
  ∀ (v : V) (p : H.Walk v v), p.IsCycle → p.length ≠ 4 ∧ p.length ≠ 5

end SteinbergFalse.Counterexample


