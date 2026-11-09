-- Prove2me | Definitions.Def_NAMatchEst_W3
-- name    : NAMatchEst_W3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:54:51.130177+00:00
-- url     : https://prove2.me/theorems/62f0d5d5-5bcb-4316-862b-fc38f6f7756b
-- title:
--   $W_3=\{u\in U:d_{\bar H}(u)<\alpha\}$
-- statement:
--   For a set $H\subseteq V$, $W_3:=\{u\in U: d_{\bar H}(u)<\alpha\}$ (display (11)): the low-degree vertices with fewer than $\alpha$ neighbours outside $H$.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.3, display (11), p.22 (PDF 26)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_U
import Definitions.Def_NAMatchEst_dHbar

namespace NAMatchEst

/-- `W₃ := {u ∈ U : d_{H̄}(u) < α}` (display (11)).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.3, p.22 (PDF 26): "Define W3 := {u ∈ U : d_H̄(u) < α}. (11)" -/
noncomputable def W3 {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (H : Finset (Fin n)) :
    Finset (Fin n) :=
  open Classical in (U G α k).filter fun u => (dHbar G H u : ℝ) < α

end NAMatchEst


