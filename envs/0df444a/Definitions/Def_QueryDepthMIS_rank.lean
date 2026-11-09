-- Prove2me | Definitions.Def_QueryDepthMIS_rank
-- name    : QueryDepthMIS_rank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:08.61345+00:00
-- url     : https://prove2.me/theorems/7006a750-8454-4d4f-8734-0cc6b6ae6ecc
-- title:
--   Rank of a vertex: $\operatorname{rank}(v) = \pi^{-1}(v) \in [1, n]$
-- statement:
--   For an ordering $\omega$ of $V$ (the permutation $\pi = \omega^{-1}$), the **rank** of a vertex $v$ is its position in $\pi$,
--   $$
--   \operatorname{rank}(v) = \pi^{-1}(v) = \omega(v) + 1 \in \{1, \dots, n\}.
--   $$
--   Positions are 1-based, as in the paper, so that bounds such as $p < \beta n$, $[\tau] = \{1, \dots, \tau\}$ and $\max P_1 + 1$ read literally. "The vertex at position $p$" is the vertex of rank $p$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.1, p.8

import Mathlib
import Definitions.Def_QueryDepthMIS_Perm

set_option autoImplicit false

namespace QueryDepthMIS

/-- The rank of a vertex (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Definition 2.1, p.8): "The rank of a vertex v, denoted by
rank(v), is its position in π, that is, π⁻¹(v)." Positions are 1-based, `rank ω v ∈ [1, n]`.

**Formalization Note** `rank ω v = ω v + 1`, so that every printed inequality between positions
(`p < βn`, `[τ] = {1, …, τ}`, `max P₁ + 1`) transfers literally. "The vertex at position `p`" is
phrased as "the vertex `v` with `rank ω v = p`". -/
def rank {V : Type*} [Fintype V] (ω : Perm V) (v : V) : ℕ := (ω v : ℕ) + 1

end QueryDepthMIS


