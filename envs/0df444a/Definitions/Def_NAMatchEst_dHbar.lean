-- Prove2me | Definitions.Def_NAMatchEst_dHbar
-- name    : NAMatchEst_dHbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:03.787168+00:00
-- url     : https://prove2.me/theorems/a5920046-2fab-4000-9028-40aca689961b
-- title:
--   Residual degree $d_{\bar H}(v)=|N(v)\setminus H|$
-- statement:
--   For a set $H\subseteq V$ write $\bar H:=V\setminus H$. The **residual degree** of a vertex $v$ is $d_{\bar H}(v):=|N(v)\setminus H|$, the number of neighbours of $v$ outside $H$ (display (8)).
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.3, display (8), p.21 (PDF 25)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList

namespace NAMatchEst

/-- The residual degree `d_{H̄}(v) := |N(v) \ H|`, the number of neighbours of `v` outside `H`
(display (8)).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.3, p.21 (PDF 25): "For any H ⊆ V, write H̄ := V \ H and define d_H̄(v) := |N(v) \ H|,
RH := Σ_{u∈U} d_H̄(u). (8)" -/
def dHbar {n : ℕ} (G : AdjList n) (H : Finset (Fin n)) (v : Fin n) : ℕ :=
  ((G.adj v).toFinset \ H).card

end NAMatchEst


