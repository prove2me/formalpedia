-- Prove2me | Definitions.Def_HeilmanMax3Cut_aR
-- name    : HeilmanMax3Cut_aR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:26.39611+00:00
-- url     : https://prove2.me/theorems/3052dfc7-92bb-4f9e-8554-afea67ec3423
-- title:
--   The angular coupling $a(t,s)=2\sigma\sqrt{ts}/d$
-- statement:
--   With $d=1-\sigma^2$,
--
--   $$a(t,s)=\frac{2\sigma\sqrt{ts}}{d}.$$
--
--   Conditionally on the radii $t=|\xi|^2/2$, $s=|\eta|^2/2$ of a $\sigma$-correlated Gaussian pair in $\mathbb R^2$, the angles have joint density $e^{a\cos(\theta-\phi)}/I_0(a)$ with this $a$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eqs. (56), (96), pp.21, 30

import Mathlib

namespace HeilmanMax3Cut

/-- **The angular coupling `a(t, s)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eqs. (56), (96), pp.21, 30: with `d := 1 − σ²`,
`a = a(t, s) := 2σ√(ts)/d`. -/
noncomputable def aR (σ t s : ℝ) : ℝ :=
  2 * σ * Real.sqrt (t * s) / (1 - σ ^ 2)

end HeilmanMax3Cut


