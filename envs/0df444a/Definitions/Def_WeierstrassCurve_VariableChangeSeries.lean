-- Prove2me | Definitions.Def_WeierstrassCurve_VariableChangeSeries
-- name    : WeierstrassCurve_VariableChangeSeries
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/ec88d878-3d37-5c9c-80fd-6d9d14c90c10
-- title:
--   Change of formal parameter under a Weierstrass variable change
-- statement:
--   Fix a commutative ring $R$, a Weierstrass cubic $W$ over $R$ with coefficients $a_1,a_2,a_3,a_4,a_6$, and a variable change $C=(u,r,s,t)$ with $u\in R^\times$ (Mathlib's `WeierstrassCurve.VariableChange`, corresponding to $x=u^2x'+r$, $y=u^3y'+u^2sx'+t$). Both definitions are built from the series $w_W=$ `W.formalW` $\in R[\![X]\!]$, the unique power series with zero constant term satisfying
--   $$w = X^3 + a_1Xw + a_2X^2w + a_3w^2 + a_4Xw^2 + a_6w^3,$$
--   which has order $3$ with $X^3$-coefficient $1$.
--
--   [`WeierstrassCurve.variableChangeDenom`](../def/WeierstrassCurve_VariableChangeSeries.html#L14) is the series
--   $$1 + s\,(X - r\,w_W) + t\,w_W \in R[\![X]\!],$$
--   where $s,t,r$ enter as constant series. [`WeierstrassCurve.variableChangeSeries`](../def/WeierstrassCurve_VariableChangeSeries.html#L17) is
--   $$u\,(X - r\,w_W)\cdot \mathrm{inv}\bigl(1 + s\,(X - r\,w_W) + t\,w_W\bigr),$$
--   the inverse of the denominator being formed with `PowerSeries.invOfUnit` at the unit $1$, i.e. the formal inverse of a series whose constant term is $1$; so the definition is the formal quotient
--   $$\psi_C = \frac{u\,(X - r\,w_W)}{1 + s\,(X - r\,w_W) + t\,w_W},$$
--   the expression of the parameter of the transformed model in terms of the parameter of $W$.
--
--   Two accompanying statements record the elementary normalisations that make this well posed and give $\psi_C$ a formal meaning: `constantCoeff_variableChangeDenom` says the denominator has constant coefficient $1$ (so that the chosen `invOfUnit` at $1$ is the genuine inverse), and `constantCoeff_variableChangeSeries` says $\psi_C$ has zero constant coefficient, i.e. $\psi_C \in X\,R[\![X]\!]$.
--
--   **Relation to Mathlib.** The quadruple $C=(u,r,s,t)$ is Mathlib's `WeierstrassCurve.VariableChange` and the formal inverse is Mathlib's `PowerSeries.invOfUnit`; the series $w_W$ ([`WeierstrassCurve.formalW`](../def/WeierstrassCurve_FormalGroupLaw.html#L136), characterised by the cubic fixed-point equation above) and the two series defined here are the project's own.
--
--   **Where it is used.** These series are the substitutions that compare the formal parameter of a Weierstrass model with that of a model obtained from it by an admissible change of coordinates, and hence allow formal-group data attached to one Weierstrass model to be transported to an isomorphic one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_VariableChangeSeries.lean

import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open PowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

def variableChangeDenom : R⟦X⟧ :=
  1 + PowerSeries.C C.s * (PowerSeries.X - PowerSeries.C C.r * W.formalW) + PowerSeries.C C.t * W.formalW

def variableChangeSeries : R⟦X⟧ :=
  PowerSeries.C (C.u : R) * (PowerSeries.X - PowerSeries.C C.r * W.formalW) *
    PowerSeries.invOfUnit (W.variableChangeDenom C) 1

theorem constantCoeff_variableChangeDenom : PowerSeries.constantCoeff (W.variableChangeDenom C) = 1 := by
  simp [variableChangeDenom, W.constantCoeff_formalW]

theorem constantCoeff_variableChangeSeries : PowerSeries.constantCoeff (W.variableChangeSeries C) = 0 := by
  simp [variableChangeSeries, W.constantCoeff_formalW]

end WeierstrassCurve

end


