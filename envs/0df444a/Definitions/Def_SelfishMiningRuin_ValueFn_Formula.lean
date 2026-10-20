-- Prove2me | Definitions.Def_SelfishMiningRuin_ValueFn_Formula
-- name    : SelfishMiningRuin_ValueFn_Formula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:24.08598+00:00
-- url     : https://prove2.me/theorems/73262bde-3d96-475e-85e9-d31b67fbf64b
-- title:
--   Theorem 3.1 constants, characteristic function and advanced operator
-- statement:
--   For block rate $\lambda$, cost rate $c$, reward $b$, mean horizon $t$, hash share $p$, and fork-connectivity probability $q$, this module defines the explicit constant $C$ and coefficients $D_1,\ldots,D_7$ of (22). It also defines the coefficients $B_1,B_2,B_3$ of (24), the characteristic function given by the left side minus the right side of (21), and the operator given by the left side of (32).
--
--   The explicit candidate associated with roots $\rho_1,\rho_2\pm i\rho_3$ and coefficients $A_1,A_2,A_3$ is
--
--   $$
--   F(u)=A_1e^{\rho_1u}+e^{\rho_2u}\bigl(A_2\cos(\rho_3u)+A_3\sin(\rho_3u)\bigr)+u+C.
--   $$
--
--   The module states the corrected version of linear system (23) as a predicate on the coefficients. These objects provide common notation for the root-count milestone, the explicit-solution milestone, and the main theorem.
--
--   **Formalization Note** The printed third right-hand side of (23) omits the factor $\lambda^2p^2/c^2$ on $2b+C$; the predicate uses the correction forced by (33).
-- source:
--   Albrecher & Goffard, On the profitability of selfish blockchain mining under consideration of ruin, arXiv:2010.12577v1, p. 11, equations (20)–(24); pp. 25–26, equations (32), (34), (35)

import Mathlib

set_option autoImplicit false

namespace SelfishMiningRuin.ValueFn

/-- The denominator shared by the two terms in C, equation (22). -/
noncomputable def Cden (lam t p : ℝ) : ℝ :=
  lam^2 * t^2 * (p^2 - 2*p - 1) - (p + 2)*lam*t - 1

/-- The constant C in equation (22). -/
noncomputable def Cconst (lam c b t p q : ℝ) : ℝ :=
  -(lam^2 * t^3 * (lam*p*b*((q-2)*p^2 + (4-2*q)*p + q) + c*(p^2-2*p-1))) /
    Cden lam t p -
  (lam*t^2*(2*b*p^2*lam - c*(p+2)) - c*t) / Cden lam t p

noncomputable def D1 (_lam c _t p : ℝ) : ℝ := p*c/(1-p)
noncomputable def D2 (lam t p : ℝ) : ℝ := p*(1+t*(2-p)*lam)/(t*(1-p))
noncomputable def D3 (lam p q : ℝ) : ℝ := (1-p)*lam*q
noncomputable def D4 (lam c p : ℝ) : ℝ := c^3/(lam^2*(1-p)*p)
noncomputable def D5 (lam c t p : ℝ) : ℝ := c^2*(3+lam*t*(p+2))/(lam^2*t*(1-p)*p)
noncomputable def D6 (lam c t p : ℝ) : ℝ :=
  (3+lam*t*(2*p+1))*c*(lam*t+1)/(t^2*lam^2*(1-p)*p)
noncomputable def D7 (lam t p q : ℝ) : ℝ :=
  (1 + lam*t*(p+2) + lam^2*t^2*(2*p+1) +
    lam^3*t^3*p*(p*(1-q)*(2-p)+q))/(lam^2*t^3*(1-p)*p)

/-- Left minus right of the characteristic equation (21). -/
noncomputable def charFun (lam c b t p q : ℝ) (rho : ℂ) : ℂ :=
  ((D1 lam c t p : ℂ)*rho + (D2 lam t p : ℂ)) * Complex.exp (2*rho*(b:ℂ)) +
    (D3 lam p q : ℂ)*Complex.exp (rho*(b:ℂ)) -
    ((D4 lam c p : ℂ)*rho^3 + (D5 lam c t p : ℂ)*rho^2 +
      (D6 lam c t p : ℂ)*rho + (D7 lam t p q : ℂ))

/-- Coefficients of the corrected third boundary equation (23), as in (24). -/
noncomputable def B1 (lam c b p rho1 : ℝ) : ℝ :=
  -rho1^2 + lam^2*p^2*Real.exp (2*b*rho1)/c^2
noncomputable def B2 (lam c b p rho2 rho3 : ℝ) : ℝ :=
  -rho2^2 + rho3^2 + lam^2*p^2*Real.exp (2*b*rho2)*Real.cos (2*b*rho3)/c^2
noncomputable def B3 (lam c b p rho2 rho3 : ℝ) : ℝ :=
  -2*rho2*rho3 + lam^2*p^2*Real.exp (2*b*rho2)*Real.sin (2*b*rho3)/c^2

/-- Corrected equation (23): its printed third right-hand side omits a factor. -/
def System23 (lam c b t p q rho1 rho2 rho3 A1 A2 A3 : ℝ) : Prop :=
  A1 + A2 = -Cconst lam c b t p q ∧
  rho1*A1 + rho2*A2 + rho3*A3 = -1 ∧
  B1 lam c b p rho1*A1 + B2 lam c b p rho2 rho3*A2 +
    B3 lam c b p rho2 rho3*A3 =
      -(lam^2*p^2/c^2)*(2*b + Cconst lam c b t p q) - 1/(c*t)

/-- The explicit real function in equation (20), with C from (22). -/
noncomputable def closedForm (lam c b t p q rho1 rho2 rho3 A1 A2 A3 : ℝ) (u : ℝ) : ℝ :=
  A1 * Real.exp (rho1*u) + Real.exp (rho2*u) *
    (A2*Real.cos (rho3*u) + A3*Real.sin (rho3*u)) + u + Cconst lam c b t p q

/-- The left side of the inhomogeneous advanced equation (32). -/
noncomputable def E32 (lam c b t p q : ℝ) (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  D4 lam c p * iteratedDeriv 3 F u + D5 lam c t p * iteratedDeriv 2 F u +
  D6 lam c t p * deriv F u + D7 lam t p q * F u -
  D3 lam p q * F (u+b) - D2 lam t p * F (u+2*b) -
  D1 lam c t p * deriv F (u+2*b) -
  (1+lam*t*(p+2)-lam^2*t^2*(p^2-2*p-1))/(t^3*lam^2*(1-p)*p)*u -
  (2+lam*t*(p+2))*c/(lam^2*t^2*(1-p)*p)

end SelfishMiningRuin.ValueFn


