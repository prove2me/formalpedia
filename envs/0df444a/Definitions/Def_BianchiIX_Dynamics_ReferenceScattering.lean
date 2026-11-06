-- Prove2me | Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
-- name    : BianchiIX_Dynamics_ReferenceScattering
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T21:45:30.575028+00:00
-- url     : https://prove2.me/theorems/86bee862-d9ad-44a1-a854-d850de124b67
-- title:
--   The forced reference variation, its invariant, and exit projection
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   For real $k,t$, define the boundary pulse
--   $$\beta_k(t)=(m_k(t),0,v_k(t),0)
--   =\left(1-k\tanh(kt),0,\frac{k}{\cosh(kt)},0\right).$$
--
--   Set
--   $$h_k=\frac{\operatorname{arcosh}k}{k},\qquad
--   T_k=\frac{(k^2+4)\operatorname{arcosh}k}{3k},\qquad
--   d_k=\sqrt{k^2-1},$$
--   $$H_k(t)=\frac{k^2+4}{6}t-\frac13\log\cosh(kt).$$
--   Use the total real conventions $x/0=0$, $\sqrt{x}=\sqrt{\max(x,0)}$,
--   $\log0=0$, and $\log x=\log|x|$ for $x<0$, with
--   $\operatorname{arcosh}x=\log(x+\sqrt{x^2-1})$.
--   Write $\alpha_{x,0}$ for the maximal normalized solution starting at $x$
--   at time zero, with domain $I_{\max}(x,0)$.
--
--   The positive transverse modes and crossing multipliers are
--   $$M_{k,r}(t)=e^{-rt}\cosh(kt),\qquad
--   \mu_u(k)=e^{-k\operatorname{arcosh}k},\qquad
--   \mu_w(k)=e^{-4\operatorname{arcosh}k/k}.$$
--
--   Define the variational velocity with tangent forcing by
--   $$V_k(t,\xi,a)=dF_{\beta_k(t)}\xi+aF(\beta_k(t)).$$
--   For $\xi=(\xi_m,\xi_u,\xi_v,\xi_w)$, set
--   $$J_k(t,\xi)=2(m_k(t)-1)\xi_m+2v_k(t)\xi_v-4v_k(t)\xi_u,$$
--   $$P_k\xi=(\xi_m-\xi_v/d_k,\xi_u,0,\xi_w).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ReferenceScattering.lean

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section

namespace BianchiIX

open Set

/-- A tangent forcing accounts for a change of the time coordinate. -/
def referenceVariationVelocity (k t : ℝ) (xi : ProjectiveState) (a : ℝ) : ProjectiveState :=
  fderiv ℝ projectiveField (referencePulse k t) xi + a • projectiveField (referencePulse k t)



def referenceVariationInvariant (k t : ℝ) (xi : ProjectiveState) : ℝ :=
  2 * (referencePulse k t 0 - 1) * xi 0 + 2 * referencePulse k t 2 * xi 2 -
    4 * referencePulse k t 2 * xi 1







def referenceExitProjection (k : ℝ) (xi : ProjectiveState) : ProjectiveState :=
  ![xi 0 - xi 2 / Real.sqrt (k ^ 2 - 1), xi 1, 0, xi 3]









end BianchiIX


