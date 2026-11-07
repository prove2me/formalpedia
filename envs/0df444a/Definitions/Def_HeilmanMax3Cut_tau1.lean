-- Prove2me | Definitions.Def_HeilmanMax3Cut_tau1
-- name    : HeilmanMax3Cut_tau1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:13.189749+00:00
-- url     : https://prove2.me/theorems/4382fa3a-13d2-4ffc-b242-531dfa1e5148
-- title:
--   The constant $\tau^{(1)}=1+(9-4\sqrt3\pi)/(4\pi^2)$
-- statement:
--   $$\tau^{(1)}=1+\frac{9-4\sqrt3\,\pi}{4\pi^2}\approx0.676644,$$
--
--   the cross coefficient $\tau_r=4P_r-3k_r$ of (83) for $r=r^{(1)}$.
--
--   **Formalization Note** Defined by the closed form printed in (85).
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (85), p.27

import Mathlib
open Real

namespace HeilmanMax3Cut

/-- **The constant `τ^{(1)}`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (85), p.27: `τ^{(1)} := τ_{r^{(1)}} = 1 + (9 − 4√3 π)/(4π²)`
(≈ 0.676644).

**Formalization Note.** Defined by the closed form the paper prints in (85); it equals
`4P_r − 3k_r` of (83) for `r = r^{(1)}`. -/
noncomputable def tau1 : ℝ :=
  1 + (9 - 4 * Real.sqrt 3 * π) / (4 * π ^ 2)

end HeilmanMax3Cut


