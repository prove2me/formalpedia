-- Prove2me | Definitions.Def_FractionalCalc_rlIntegral
-- name    : FractionalCalc_rlIntegral
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T16:37:35.210783+00:00
-- url     : https://prove2.me/theorems/936338f4-a306-403c-b29e-f09ef08f3859
-- title:
--   Left Riemann–Liouville fractional integral $I_{a+}^{\nu}f$
-- statement:
--   For a base point $a\in\mathbb R$, an order $\nu\in\mathbb R$ and a function $f:\mathbb R\to\mathbb R$, the **left Riemann–Liouville fractional integral** of order $\nu$ is
--   $$I_{a+}^{\nu}f(x)=\frac{1}{\Gamma(\nu)}\int_a^x (x-t)^{\nu-1}f(t)\,dt,\qquad x>a,$$
--   the left-sided fractional integral of Definition 2.1, Eq. (1) of the source. It is the convolution of $f$ with the power kernel $t^{\nu-1}/\Gamma(\nu)$, the basic smoothing operator of fractional calculus.
--
--   **Formalization Note** The value at $\nu=0$ is set to $f(x)$ (the identity $I^0=\mathrm{id}$), the natural extension needed so that integer orders reduce to classical calculus. The integral is a Bochner integral over $(a,x)$; it is $0$ when $x\le a$ (empty interval) or the integrand is not integrable. Theorems assume $\nu>0$ and the integrability they need.
-- source:
--   F. G. Rodrigues & E. C. de Oliveira, Rev. Bras. Ens. Fís. 37(3), 3305 (2015), https://doi.org/10.1590/S1806-11173731842, §2, Definition 2.1, Eq. (1) (left-sided). Extended by $I^0=\mathrm{id}$ for the integer-order reduction.

import Mathlib
open MeasureTheory Set Classical
namespace FractionalCalc
/-- Left Riemann–Liouville fractional integral of order `ν`, with `I^0 = id`. -/
noncomputable def rlIntegral (a ν : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if ν = 0 then f x
  else (Real.Gamma ν)⁻¹ * ∫ t in Ioo a x, (x - t) ^ (ν - 1) * f t
end FractionalCalc


