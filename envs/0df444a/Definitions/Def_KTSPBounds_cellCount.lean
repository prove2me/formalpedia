-- Prove2me | Definitions.Def_KTSPBounds_cellCount
-- name    : KTSPBounds_cellCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:09.375669+00:00
-- url     : https://prove2.me/theorems/d57aaa26-3d41-40cf-9c0f-66f8b6fef67f
-- title:
--   The cell occupancy counts $X_i$
-- statement:
--   Given $n$ draws $y_1,\dots,y_n$ with values in $P$ cells, $X_i$ is the number of draws that land in cell $i$:
--
--   $$
--   X_i = \#\{ j \le n : y_j = i \}.
--   $$
--
--   For independent identically distributed draws, $(X_1,\dots,X_P)$ has a multinomial distribution.
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, §3.2, p.12

import Mathlib

namespace KTSPBounds

/-- The occupancy count `X_i` of cell `i` (p.12), Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1: the number of draws
`j` among `y 0, …, y (n-1)` that fall in cell `i`. -/
def cellCount {n P : ℕ} (y : Fin n → Fin P) (i : Fin P) : ℕ :=
  (Finset.univ.filter fun j => y j = i).card

end KTSPBounds


