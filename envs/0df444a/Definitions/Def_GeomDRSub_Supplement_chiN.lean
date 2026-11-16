-- Prove2me | Definitions.Def_GeomDRSub_Supplement_chiN
-- name    : GeomDRSub_Supplement_chiN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:47:23.961581+00:00
-- url     : https://prove2.me/theorems/ff997b1f-278f-4076-a447-a065837cd68a
-- title:
--   $\chi_n=1-(1-r_n)^n$
-- statement:
--   $\chi_n=1-(1-r_n)^n$ (Eq. (149)).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 6.2, p.38, Eq. (149)

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_rN

namespace GeomDRSub.Supplement

/-- **`χ_n = 1 − (1 − r_n)^n`**, Eq. (149). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 6.2, p.38. -/
noncomputable def chiN (n : ℕ) : ℝ :=
  1 - (1 - rN n) ^ n

end GeomDRSub.Supplement


