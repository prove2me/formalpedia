-- Prove2me | Definitions.Def_DRSub4633_Supplement_sStar
-- name    : DRSub4633_Supplement_sStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:32:01.077534+00:00
-- url     : https://prove2.me/theorems/1c6ad659-e186-476d-8cef-1e533f893612
-- title:
--   $s_\star=1-b_\star$, Eq. (136)
-- statement:
--   The threshold $s_\star=1-b_\star=1-\sqrt3/2$. Below or at it, the map $h_\star$ uses its exponential branch.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Appendix B.1, Eq. (136), p.53

import Mathlib
import Definitions.Def_DRSub4633_Supplement_bStar

namespace DRSub4633.Supplement

/-- **`s⋆ = 1 − b⋆`, Eq. (136).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Appendix B.1, Eq. (136), p.53: "`s⋆ = 1 − b⋆`". -/
noncomputable def sStar : ℝ := 1 - bStar

end DRSub4633.Supplement


