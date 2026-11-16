-- Prove2me | Definitions.Def_GeomDRSub_Supplement_rN
-- name    : GeomDRSub_Supplement_rN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:46:22.101947+00:00
-- url     : https://prove2.me/theorems/fc8b8538-4e72-42f8-ad8f-dc3bbea6c474
-- title:
--   $r_n=1/(2n)$
-- statement:
--   For an integer $n\ge2$, $r_n=\dfrac1{2n}$ (Eq. (145)).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 6.2, p.37, Eq. (145)

import Mathlib

namespace GeomDRSub.Supplement

/-- **`r_n = 1/(2n)`**, Eq. (145). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 6.2, p.37. -/
noncomputable def rN (n : ℕ) : ℝ :=
  1 / (2 * n)

end GeomDRSub.Supplement


