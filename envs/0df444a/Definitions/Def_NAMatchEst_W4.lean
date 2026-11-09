-- Prove2me | Definitions.Def_NAMatchEst_W4
-- name    : NAMatchEst_W4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:55:07.93869+00:00
-- url     : https://prove2.me/theorems/187da283-1244-4ae9-991a-e8e87b2345be
-- title:
--   $W_4=\{u\in U:d_{\bar H}(u)<4\alpha\}$
-- statement:
--   For a set $H\subseteq V$, $W_4:=\{u\in U: d_{\bar H}(u)<4\alpha\}$ (display (17)). It is used only in the analysis of the certified-edge test.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.5, display (17), p.24 (PDF 28)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_U
import Definitions.Def_NAMatchEst_dHbar

namespace NAMatchEst

/-- `W₄ := {u ∈ U : d_{H̄}(u) < 4α}` (display (17)).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.5, p.24 (PDF 28): "We therefore define W4 := {u ∈ U : d_H̄(u) < 4α}. (17)" -/
noncomputable def W4 {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (H : Finset (Fin n)) :
    Finset (Fin n) :=
  open Classical in (U G α k).filter fun u => (dHbar G H u : ℝ) < 4 * α

end NAMatchEst


