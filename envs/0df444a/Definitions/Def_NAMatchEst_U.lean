-- Prove2me | Definitions.Def_NAMatchEst_U
-- name    : NAMatchEst_U
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:54:04.391194+00:00
-- url     : https://prove2.me/theorems/1928b42b-390e-458b-a153-efba16d22f1f
-- title:
--   The low-degree set $U=V\setminus V_1$
-- statement:
--   The low-degree set $U:=V\setminus V_1$ of display (3): the vertices of degree less than $\Delta$. For $u\in U$ the first $\Delta$ positions of the adjacency list reveal all of $N(u)$.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, display (3), p.19 (PDF 23)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_V1

namespace NAMatchEst

/-- The low-degree set `U := V \ V₁` of display (3): the vertices of degree less than `∆`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.19 (PDF 23), display (3). -/
noncomputable def U {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) : Finset (Fin n) :=
  Finset.univ \ V1 G α k

end NAMatchEst


