-- Prove2me | Definitions.Def_NAMatchEst_V1
-- name    : NAMatchEst_V1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:52:50.240199+00:00
-- url     : https://prove2.me/theorems/ca7b6043-8ff5-4250-8a3a-479419418e6e
-- title:
--   The first layer $V_1=\{v:\deg(v)\ge\Delta\}$
-- statement:
--   The **first layer** of display (3): $V_1:=\{v\in V:\deg(v)\ge\Delta\}$, the vertices of degree at least the cutoff $\Delta=\lfloor 2k/\alpha\rfloor$.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, display (3), p.19 (PDF 23)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_Delta

namespace NAMatchEst

/-- The first layer `V₁ := {v ∈ V : deg(v) ⩾ ∆}` of display (3).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.2, p.19 (PDF 23), display (3).

**Formalization Note** `deg(v)` is the length of the adjacency list of `v`. -/
noncomputable def V1 {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => Delta k α ≤ (G.adj v).length

end NAMatchEst


