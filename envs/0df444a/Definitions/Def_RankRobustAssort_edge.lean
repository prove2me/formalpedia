-- Prove2me | Definitions.Def_RankRobustAssort_edge
-- name    : RankRobustAssort_edge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:35.587956+00:00
-- url     : https://prove2.me/theorems/9044c533-3684-46c6-9457-e6049a252b3e
-- title:
--   Directed edges of the graph $\mathcal G_{i_1\cdots i_M}$
-- statement:
--   For a tuple $(i_1,\dots,i_M)$ the directed graph $\mathcal G_{i_1\cdots i_M}$ has vertex set $\mathcal N_0$ and a directed edge $(i,i_m)$ **from $i$ to $i_m$** for each past assortment $m\in\mathcal M$ and each product $i\in S_m\setminus\{i_m\}$.
--
--   The edges point from each product of a past assortment towards the product of that assortment that the tuple declares most preferred.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Appendix B.2, p.ec14

import Mathlib
import Definitions.Def_RankRobustAssort_Problem

namespace RankRobustAssort

/-- The directed edges of the graph `𝒢_{i₁⋯i_M}` on the vertex set `𝒩₀`: there is an edge
`(a, i_m)` from vertex `a` to vertex `i_m` for each past assortment `m ∈ ℳ` and each product
`a ∈ S_m \ {i_m}`.

Sturt, arXiv:2112.05010v4, Appendix B.2, p.ec14.

Formalization Note: the tuple is `t : Fin M → Fin (n+1)`; `edge P t a b` holds iff some `m` has
`a ∈ S_m`, `a ≠ t m` and `b = t m`. Edges point *towards* the product preferred in `S_m`. -/
def edge {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1)) (a b : Fin (n + 1)) : Prop :=
  ∃ m, a ∈ P.S m ∧ a ≠ t m ∧ b = t m

end RankRobustAssort


