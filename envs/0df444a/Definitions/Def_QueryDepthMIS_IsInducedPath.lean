-- Prove2me | Definitions.Def_QueryDepthMIS_IsInducedPath
-- name    : QueryDepthMIS_IsInducedPath
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:36.621477+00:00
-- url     : https://prove2.me/theorems/76884485-4d0e-4156-99e3-f602125d1974
-- title:
--   Induced path
-- statement:
--   A sequence $(v_1, \dots, v_L)$ of vertices forms an **induced path** if
--
--   1. $v_i v_{i+1} \in E$ for $1 \le i < L$, and
--   2. $v_i v_j \notin E$ whenever $1 \le i \le j \le L$ and $j \ne i + 1$.
--
--   For three vertices it says $v_1 \sim v_2 \sim v_3$ and $v_1 \not\sim v_3$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.8, p.9

import Mathlib

set_option autoImplicit false

namespace QueryDepthMIS

/-- Induced path (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.8, p.9): "A sequence of positions p₁, p₂, …, p_L is said
to form an induced path if both of the following hold: • (π(p_i), π(p_{i+1})) ∈ E for
1 ≤ i < L, and • (π(p_i), π(p_j)) ∉ E for j ≠ i + 1, 1 ≤ i ≤ j ≤ L."

Stated for the list of vertices `[π(p₁), …, π(p_L)]`, 0-based. -/
def IsInducedPath {V : Type*} (G : SimpleGraph V) (l : List V) : Prop :=
  l.IsChain G.Adj ∧
    ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≤ j → j ≠ i + 1 →
      ¬ G.Adj l[i] l[j]

end QueryDepthMIS


