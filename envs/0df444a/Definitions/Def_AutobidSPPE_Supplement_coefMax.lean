-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_coefMax
-- name    : AutobidSPPE_Supplement_coefMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:43:43.566625+00:00
-- url     : https://prove2.me/theorems/ea689ab3-611d-44b8-851a-48c2ca6aaf84
-- title:
--   Maximal spending coefficient $C_i=\max_S c_i(S)$
-- statement:
--   $$
--   C_i=\max_{S\subseteq[n]\setminus\{i\}}c_i(S),
--   $$
--   the largest spending bidder $i$ can face conditional on participating; a budget $\rho_i\ge C_i$ makes its response identically one. Theorem 3.18 assumes $\rho_j\ge C_j$ for all but at most one bidder.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §3.13, p.40

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_coefT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `Cᵢ = max_{S ⊆ [n]∖{i}} cᵢ(S)` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), §3.13, p.40). -/
noncomputable def coefMax {n : ℕ} (vbar : Fin n → ℝ) (i : Fin n) : ℝ :=
  (Finset.univ.erase i).powerset.sup' (Finset.powerset_nonempty _) (coefT vbar i)

end AutobidSPPE.Supplement


