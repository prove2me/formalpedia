-- Prove2me | Definitions.Def_DRSub4633_Supplement_bStar
-- name    : DRSub4633_Supplement_bStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:31:30.206514+00:00
-- url     : https://prove2.me/theorems/ad3fd492-73f1-409c-9011-5658f6721c32
-- title:
--   $b_\star=\sqrt3/2$, Eq. (136)
-- statement:
--   The constant
--   $$b_\star=\frac{\sqrt3}{2}.$$
--   It is the positive solution of $1+t+1/(4t)=(1+t)/t$ and fixes the sharp recovery map $h_\star$ of Appendix B.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Appendix B.1, Eq. (136), p.53

import Mathlib

namespace DRSub4633.Supplement

/-- **`b⋆ = √3/2`, Eq. (136).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Appendix B.1, Eq. (136), p.53: "`b⋆ = √3/2`". -/
noncomputable def bStar : ℝ := Real.sqrt 3 / 2

end DRSub4633.Supplement


