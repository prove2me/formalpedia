-- Prove2me | Definitions.Def_GeomDRSub_Supplement_ellN
-- name    : GeomDRSub_Supplement_ellN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:47:57.18881+00:00
-- url     : https://prove2.me/theorems/1196bd13-25b7-4190-a005-c0ebb72f2ba7
-- title:
--   $\ell_n=n(1-r_n)^{n-1}$
-- statement:
--   For $n\ge2$, $\ell_n=n(1-r_n)^{n-1}$ (Eq. (149)).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 6.2, p.38, Eq. (149)

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_rN

namespace GeomDRSub.Supplement

/-- **`ℓ_n = n(1 − r_n)^{n−1}`**, Eq. (149). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 6.2, p.38, for `n ≥ 2`
(so `n − 1` is the ordinary predecessor). -/
noncomputable def ellN (n : ℕ) : ℝ :=
  n * (1 - rN n) ^ (n - 1)

end GeomDRSub.Supplement


