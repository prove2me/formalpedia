-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalCutoff32_EnvelopeBounds
-- name    : HlawkaSchatten_DiagonalCutoff32_EnvelopeBounds
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:18:39.866256+00:00
-- url     : https://prove2.me/theorems/731c16ac-577f-4dbb-a1c9-8b56e5cfe770
-- title:
--   Polynomial bounds for the scalar envelope certificate
-- statement:
--   Three explicit polynomials in $x=1/p$ used to certify the scalar envelope bound $\mathrm{scalarEnvelope}(p,q)<K_p$ on a slab of exponents.
--
--   Each is a plain polynomial; the comparisons with the analytic quantities are proved where the polynomials are used.
--
--   1. $\mathrm{NloG}(c,Z_c,Z_k,x)$ serves as a lower bound for the cyclic numerator $3A_p(w)-3^{1/p}|2-w|$ at the witness $w=(c/p)^{1/p}$. With $z=Z_cx+Z_k$, $u=cx/2$, $y=(0.6931471803+u-u^2/2)x$ and $C=1.098612289\,x$ it equals
--   $$3\Big(1+y+\frac{y^2}{2}+\frac{y^3}{6}\Big)-\Big(1+C+\frac{C^2}{2}+\frac{C^3}{6}+\frac{C^4}{12}\Big)\Big(1+z-\frac{z^2}{2}+\frac{z^3}{6}-\frac{z^4}{24}+\frac{z^5}{100}\Big).$$
--   2. $\mathrm{DupG}(c,x)=6\big(t+t^2/2+t^3/6+t^4/12\big)$ with $t=(0.6931471808+u-u^2/2+u^3/3+2u^4)x$ serves as an upper bound for the cyclic denominator at the same witness.
--   3. $\mathrm{GloG}(x)=g-w^2/2+g^3/6-w^4/24-w^5/100$ with $g=(0.6931471803-x^2/10^6)x$ and $w=0.6931471808\,x$ serves as a lower bound for the envelope gap $1-\big((1+q^p)/2\big)^{1/p}$ at $x=1/p$.
--
--   These are the data of the polynomial certificates checked on each slab of the cutoff-32 scalar window.
-- source:
--   Sharp diagonal Hlawka constant campaign, cutoff-32 entry (https://prove2.me/campaigns/sharp-diagonal-hlawka-constant); definitions of the foundation mission (Ezzeri Esa, Apache-2.0).

import Mathlib.Data.Real.Basic

/-
Cutoff-32 development for the sharp diagonal Hlawka constant. Builds on Ezzeri Esa's Apache-2.0
Hlawka-Schatten construction (Definitions.Def_HlawkaSchatten_*). Released under Apache 2.0.
-/

namespace HlawkaSchatten.DiagonalCutoff32

/-- Lower bound for the cyclic numerator at the witness `(c/p)^{1/p}`. -/
noncomputable def NloG (c Zc Zk x : ℝ) : ℝ :=
  let z := Zc*x+Zk
  let u := c/2*x
  let y := (6931471803/10^10+u-u^2/2)*x
  let C := (1098612289/10^9 : ℝ)*x
  3*(1+y+y^2/2+y^3/6)-(1+C+C^2/2+C^3/6+C^4/12)*(1+z-z^2/2+z^3/6-z^4/24+z^5/100)

/-- Upper bound for the cyclic denominator at the witness `(c/p)^{1/p}`. -/
noncomputable def DupG (c x : ℝ) : ℝ :=
  let u := c/2*x
  let t := (6931471808/10^10+u-u^2/2+u^3/3+2*u^4)*x
  6*(t+t^2/2+t^3/6+t^4/12)

/-- Lower bound for the envelope deficit. -/
noncomputable def GloG (x : ℝ) : ℝ :=
  let g := (6931471803/10^10-x^2/10^6)*x
  let w := (6931471808/10^10 : ℝ)*x
  g-w^2/2+g^3/6-w^4/24-w^5/100

end HlawkaSchatten.DiagonalCutoff32


