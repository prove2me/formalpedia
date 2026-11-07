-- Prove2me | Definitions.Def_HeilmanMax3Cut_j1
-- name    : HeilmanMax3Cut_j1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:59.642991+00:00
-- url     : https://prove2.me/theorems/b58635b6-20f1-4d93-91dd-4ddf42413a23
-- title:
--   The constant $j^{(1)}=(9-\sqrt3\pi)/(4\pi^2)$
-- statement:
--   $$j^{(1)}=\frac{9-\sqrt3\,\pi}{4\pi^2}\approx0.0901404,$$
--
--   the diagonal coefficient $j_r=P_r-3k_r$ of (83) for $r=r^{(1)}$.
--
--   **Formalization Note** Defined by the closed form printed in (85).
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (85), p.27

import Mathlib
open Real

namespace HeilmanMax3Cut

/-- **The constant `j^{(1)}`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (85), p.27: `j^{(1)} := j_{r^{(1)}} = (9 − √3 π)/(4π²)`
(≈ 0.0901404).

**Formalization Note.** Defined by the closed form the paper prints in (85); it equals
`P_r − 3k_r` of (83) for `r = r^{(1)}` (`k_r = 1/9 − 3/(4π²)`, `P_r = 1/3 − √3/(4π)`). -/
noncomputable def j1 : ℝ :=
  (9 - Real.sqrt 3 * π) / (4 * π ^ 2)

end HeilmanMax3Cut


