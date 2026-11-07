-- Prove2me | Definitions.Def_HeilmanMax3Cut_R0
-- name    : HeilmanMax3Cut_R0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:14.910911+00:00
-- url     : https://prove2.me/theorems/e8681bd4-5318-46db-8778-d588e96efa11
-- title:
--   The radial density $R_0(t,s)$
-- statement:
--   With $d=1-\sigma^2$ and $a=a(t,s)$,
--
--   $$R_0(t,s)=\frac1d\,e^{-\sigma^2(t+s)/d}\,I_0\Bigl(\frac{2\sigma\sqrt{ts}}{d}\Bigr),\qquad t,s\ge0,$$
--
--   the density of the joint law of $(t,s)=(|\xi|^2/2,|\eta|^2/2)$ with respect to $\nu\otimes\nu$, for $\sigma$-correlated standard Gaussian vectors $\xi,\eta\in\mathbb R^2$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (98), p.30

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_besselI
import Definitions.Def_HeilmanMax3Cut_aR
open QueueingFundamentals.Transient

namespace HeilmanMax3Cut

/-- **The radial density `R₀(t, s)`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (98), p.30: the Radon–Nikodym derivative of the
joint law of `(t, s) = (|ξ|²/2, |η|²/2)`, for a `σ`-correlated pair `(ξ, η)` of standard Gaussian
vectors in `ℝ²`, with respect to `ν ⊗ ν`:

`R₀(t, s) = (1/d) e^{−σ²(t+s)/d} I₀(2σ√(ts)/d)`, `d = 1 − σ²`, `t, s ≥ 0`.

**Formalization Note.** `I₀` is the published `QueueingFundamentals.Transient.besselI 0`. -/
noncomputable def R0 (σ t s : ℝ) : ℝ :=
  1 / (1 - σ ^ 2) * Real.exp (-(σ ^ 2 * (t + s)) / (1 - σ ^ 2)) * besselI 0 (aR σ t s)

end HeilmanMax3Cut


