-- Prove2me | Definitions.Def_NAMatchEst_V1H
-- name    : NAMatchEst_V1H
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:56:17.922362+00:00
-- url     : https://prove2.me/theorems/4df31655-8927-4f8f-beda-d7e63b73a1ff
-- title:
--   The heavy first-layer set $V_1^H$
-- statement:
--   $$
--   V_1^H:=\{v\in V_1: d_U(v)\ge 512\alpha^2\},
--   $$
--
--   the first-layer vertices with many neighbours in $U$ (display (6)). The tests need a set $H$ with $V_1^H\subseteq H\subseteq V_1$.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.3, display (6), p.20 (PDF 24)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_dU

namespace NAMatchEst

/-- `V₁^H := {v ∈ V₁ : d_U(v) ⩾ 512α²}`, the first-layer vertices with many neighbours in `U`
(display (6)).

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.3, p.20 (PDF 24), display (6). -/
noncomputable def V1H {n : ℕ} (G : AdjList n) (α : ℝ) (k : ℕ) : Finset (Fin n) :=
  open Classical in (V1 G α k).filter fun v => 512 * α ^ 2 ≤ (dU G α k v : ℝ)

end NAMatchEst


