-- Prove2me | Definitions.Def_GeomDRSub_Supplement_xiN
-- name    : GeomDRSub_Supplement_xiN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:46:51.578083+00:00
-- url     : https://prove2.me/theorems/1386a96c-a1bc-4c7e-8516-823114506853
-- title:
--   $\xi_{n,\zeta}=(\zeta-r_n)_+/(1/2-\zeta)$
-- statement:
--   For $n\ge2$ and $0\le\zeta<1/2$,
--   $$\xi_{n,\zeta}=\frac{(\zeta-r_n)_+}{1/2-\zeta}$$
--   (Eq. (145)).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 6.2, p.37, Eq. (145)

import Mathlib
import Definitions.Def_GeomDRSub_Supplement_rN

namespace GeomDRSub.Supplement

/-- **`ξ_{n,ζ} = (ζ − r_n)₊/(1/2 − ζ)`**, Eq. (145). Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 6.2, p.37, for
`n ≥ 2` and `0 ≤ ζ < 1/2`. -/
noncomputable def xiN (n : ℕ) (ζ : ℝ) : ℝ :=
  max (ζ - rN n) 0 / (1 / 2 - ζ)

end GeomDRSub.Supplement


