-- Prove2me | Definitions.Def_NAMatchEst_RH
-- name    : NAMatchEst_RH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:54:48.050723+00:00
-- url     : https://prove2.me/theorems/14627c01-40aa-4129-ae19-6782b28aeac3
-- title:
--   Residual total $R_H=\sum_{u\in U}d_{\bar H}(u)$
-- statement:
--   For a set $H\subseteq V$, the **residual total** of display (8) is
--
--   $$
--   R_H:=\sum_{u\in U} d_{\bar H}(u).
--   $$
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.3, display (8), p.21 (PDF 25)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_U
import Definitions.Def_NAMatchEst_dHbar

namespace NAMatchEst

/-- The residual total `R_H := Σ_{u ∈ U} d_{H̄}(u)` (display (8)).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.3, p.21 (PDF 25), display (8). -/
noncomputable def RH {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (H : Finset (Fin n)) : ℕ :=
  ∑ u ∈ U G α k, dHbar G H u

end NAMatchEst


