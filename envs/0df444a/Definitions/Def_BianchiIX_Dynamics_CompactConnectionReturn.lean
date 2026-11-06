-- Prove2me | Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
-- name    : BianchiIX_Dynamics_CompactConnectionReturn
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T07:40:49.696528+00:00
-- url     : https://prove2.me/theorems/7012dd24-65c9-42a0-951a-6667e0202e28
-- title:
--   The exact connection composed from finite tail and entrance
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
--   The projective vector field in normalized time is
--   $$G(y)=\frac6{D(y)}F(y).$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   For $Y=(k,u,w)\in\mathbb R^3$, define
--   $$e_-(Y)=(1-\sqrt{k^2-1},u,1,w),\quad x_Y=\Xi(e_-(Y)),\quad
--   \beta_Y(t)=\Psi_0(e_-(Y),t),\quad g(x)=(\Pi(x))_v.$$
--   For any real height $\eta$, put
--   $$H_{\eta,Y}=\{t>0:t\in I_{\max}(x_Y,0),\ g(\alpha_{x_Y,0}(t))=\eta\},$$
--   $$T_\eta(Y)=\inf H_{\eta,Y},\qquad P_\eta(Y)=\beta_Y(T_\eta(Y)).$$
--   The infimum uses the total real-order convention. Let
--   $\operatorname{TailValid}_\eta(Y)$ mean that $T_\eta(Y)$ is the least
--   element of $H_{\eta,Y}$, and, writing $T=T_\eta(Y)$, that
--   $$t\in I_{\max}(x_Y,0),\quad 1+(\alpha_{x_Y,0}(t))_0>0
--   \quad(0\leq t\leq T),$$
--   $$g(\alpha_{x_Y,0}(t))>\eta\quad(0\leq t<T),$$
--   $$dg_{\alpha_{x_Y,0}(t)}N(\alpha_{x_Y,0}(t))<0,\quad
--   |(\Pi(\alpha_{x_Y,0}(t)))_w|<1/2\quad(0\leq t\leq T).$$
--   All vector and operator norms use the finite-product supremum norms.
--
--   For $i=0,1$ put $j(0)=1$, $j(1)=3$, and define
--   $$m_i(\eta,Y)=\exp\left(\log(1+(x_Y)_0)
--   -\log(1+(\alpha_{x_Y,0}(T_\eta(Y)))_0)
--   +\int_0^{T_\eta(Y)}r_{j(i)}(\alpha_{x_Y,0}(t))\,dt\right).$$
--   Let $\mathcal R(m,u,v,w)=(-m,u,w,v)$.
--
--   Put $c=u(v+w-u)$, $s(m,u,v,w)=m-1-c$,
--   $b(m,u,v,w)=(1-m^2-(v-w)^2+u^2)/2$,
--   $D(m,u,v,w)=3+m^2+K(u,v,w)$, and $r(m,v)=\sqrt{(m-1)^2+v^2}$.
--
--   For $y\in\mathbb R^4$, put $x_y=\Xi(y)$,
--   $$T_+(y)=\inf\{t>0:t\in I_{\max}(x_y,0),\ (\Psi_0(y,t))_v=1\},
--   \qquad P_+(y)=\Psi_0(y,T_+(y)).$$
--   Let $V_+(y)$ mean that this infimum is a least element, the full interval
--   $[0,T_+(y)]$ lies in the maximal domain with
--   $1+(\alpha_{x_y,0}(t))_0>0$, the active wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive throughout the interval. The infimum has its total
--   real-order meaning.
--
--   Define the reflected radius and the composed entrance, time and state by
--   $$R_\eta(Y)=r((\mathcal R P_\eta(Y))_m,(\mathcal R P_\eta(Y))_v),
--   \qquad e_\eta(Y)=\mathcal R P_\eta(Y),$$
--   $$T_c(\eta,Y)=T_+(e_\eta(Y))+T_\eta(Y),\qquad
--   P_c(\eta,Y)=P_+(e_\eta(Y)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/CompactConnectionReturn.lean

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

namespace BianchiIX

open Set

def compactConnectionEntry (η : ℝ) (Y : CoreAngleState) : ProjectiveState :=
  projectiveReflection (coreTailState η Y)

def compactConnectionTime (η : ℝ) (Y : CoreAngleState) : ℝ :=
  entranceReturnTime (compactConnectionEntry η Y) + coreTailTime η Y

def compactConnectionState (η : ℝ) (Y : CoreAngleState) : ProjectiveState :=
  entranceReturnState (compactConnectionEntry η Y)





end BianchiIX


