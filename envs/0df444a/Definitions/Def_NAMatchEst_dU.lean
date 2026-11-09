-- Prove2me | Definitions.Def_NAMatchEst_dU
-- name    : NAMatchEst_dU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:54:57.278278+00:00
-- url     : https://prove2.me/theorems/c6d73afa-a796-4fc2-8247-df68c1b9c2c9
-- title:
--   $d_U(v)=|N(v)\cap U|$
-- statement:
--   For a vertex $v$, $d_U(v):=|N(v)\cap U|$ is the number of neighbours of $v$ in the low-degree set $U$ (display (6)).
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.3, display (6), p.20 (PDF 24)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_U

namespace NAMatchEst

/-- `d_U(v) := |N(v) ∩ U|`, the number of neighbours of `v` in `U` (display (6)).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.3, p.20 (PDF 24): "For each v ∈ V, define dU(v) := |N(v) ∩ U|, V^H_1 := {v ∈ V1 :
dU(v) ⩾ 512α²}. (6)" -/
noncomputable def dU {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) (v : Fin n) : ℕ :=
  ((G.adj v).toFinset ∩ U G α k).card

end NAMatchEst


