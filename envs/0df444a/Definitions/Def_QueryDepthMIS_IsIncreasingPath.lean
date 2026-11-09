-- Prove2me | Definitions.Def_QueryDepthMIS_IsIncreasingPath
-- name    : QueryDepthMIS_IsIncreasingPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:25.655219+00:00
-- url     : https://prove2.me/theorems/8c51831d-0f47-4185-8ab5-4caa006e7d25
-- title:
--   Increasing path with respect to a ranking
-- statement:
--   Let $G$ be a graph on $V$ and $r : V \to \mathbb N$ a ranking. An **increasing path** is a nonempty sequence of vertices $(v_1, \dots, v_L)$ with $v_i v_{i+1} \in E$ for $1 \le i < L$ and
--   $$
--   r(v_1) < r(v_2) < \cdots < r(v_L).
--   $$
--   Its length is its number of vertices $L$. The ranking is a parameter so that the notion applies to subgraphs with the inherited order.
--
--   **Formalization Note** The vertices are distinct because the ranks strictly increase (rankings from a permutation are injective).
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.4, p.8

import Mathlib

set_option autoImplicit false

namespace QueryDepthMIS

/-- Increasing path (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.4, p.8): "An increasing path with respect to π is a path
(v₁, v₂, …, v_L) such that rank(v₁) < rank(v₂) < ⋯ < rank(v_L)."

A nonempty list of vertices in which consecutive vertices are adjacent and the ranks `r` strictly
increase. The rank function `r` is a parameter, so that the notion applies to a subgraph with the
inherited order.

**Formalization Note** Distinctness of the vertices (a path) follows from the strict increase of
ranks when `r` is injective, as it is for every `rank ω`. The length of the path is the number of
its vertices (§2.1, p.7), `l.length`. -/
def IsIncreasingPath {V : Type*} (G : SimpleGraph V) (r : V → ℕ) (l : List V) : Prop :=
  l ≠ [] ∧ l.IsChain (fun a b => G.Adj a b ∧ r a < r b)

instance {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℕ) (l : List V) :
    Decidable (IsIncreasingPath G r l) := by
  unfold IsIncreasingPath; infer_instance

end QueryDepthMIS


