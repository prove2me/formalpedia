-- Prove2me | Definitions.Def_BianchiIX_EntrancePhaseResponseData
-- name    : BianchiIX_EntrancePhaseResponseData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T16:23:30.630242+00:00
-- url     : https://prove2.me/theorems/7cd95505-7e8e-46d2-870a-253f0b4387c0
-- title:
--   Radial entrance coordinates and exact connection phase response
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
--   On the invariant plane with zero active wall, use $y=(m,u,w)\in\mathbb R^3$,
--   the inclusion $\iota(m,u,w)=(m,u,0,w)$ and the restriction
--   $\pi_s(m,u,v,w)=(m,u,w)$. Define
--   $$f(y)=\left(mu^2-(m+1)uw+w^2,
--   \frac{1-m^2-w^2+u^2}{2}u,-(m+1+uw-u^2)w\right),$$
--   $$\Delta(y)=3+m^2+(u-w)^2,\qquad f_o(y)=6f(y)/\Delta(y).$$
--   Write $J=df$, $H=d^2f$, $J_o=df_o$, $H_o=d^2f_o$ for their explicit
--   Jacobian and Hessian expressions. The denominator derivatives are
--   $d\Delta=(2m,2(u-w),2(w-u))$ and
--   $d^2\Delta(v,z)=2v_0z_0+2(v_1-v_2)(z_1-z_2)$.
--   The exact original-time boundary flow and its projected variation are
--   $$\Phi(y,t)=\pi_s\Psi_0(\iota y,t),\qquad
--   L(y,t)=\pi_s\mathcal J_{\iota y,0}(t)\iota.$$
--   For a fixed scale $K$, set $\Phi_K(y,s)=\Phi(y,Ks)$,
--   $L_K(y,s)=L(y,Ks)$ and $Q_K(y,s)=d_yL_K(y,s)$.
--   For directions $v,z$, define
--   $$S_K(y,s;v,z)=K\left[H_o(\Phi_K)(L_Kv,L_Kz)+J_o(\Phi_K)Q_K(v,z)\right].$$
--   All vector norms are sup norms, and operator norms are induced by them.
--   Write $b(y)=|u|+|w|$, $E(y)=e^{512b(y)}$, $v_s=(v_1,v_2)$, and
--   $$\mathcal H(y;v,z)=b(y)\|v\|\|z\|+\|v_s\|\|z\|+\|v\|\|z_s\|,$$
--   $$B_2(y)=192b(y)(40000E(y)^3)+10000E(y)^2.$$
--   The closed boundary region is
--   $\mathcal S_c=\{(m,u,0,w):|m-c|\leq1/10,\ |u|,|w|\leq1/100\}$.
--   The boundary projection $P(m,u,w)$ is the limit of $\Phi(m,u,w;t)_0$
--   as $t\to\infty$, using the total limit convention of the formal definitions.
--
--   Define
--   $$\mathcal E_k=\{(m,u,v,w):m\geq1,\ |r(m,v)-k|\leq k/100,
--   \ 0\leq u,w\leq1/10000,\ 0\leq v\leq1\},$$
--   and $\omega_+(m,u,v,w)=s(m,u,v,w)$.
--   For a normalized trajectory write
--   $$\beta(t)=\Pi(\alpha_{x,t_0}(t)),\quad A(t)=1+(\alpha_{x,t_0}(t))_0,
--   \quad I=I_{\max}(x,t_0).$$
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
--   For $y=(m,u,v,w)$, define $p(y)=P(m,u,w)$,
--   $\rho(y)=\sqrt{(p(y)-1)^2+v^2}$, $\omega(y)=m-1-u(v+w-u)$,
--   and $\chi(y)=(\rho(y),u,v,w)$. Write $p_i=\partial_i p$.
--   The inverse differential $J_\chi(y)$ preserves the last three coordinates
--   and has first row
--   $$\left(\frac{\rho}{(p-1)p_0},-\frac{p_1}{p_0},
--   -\frac{v}{(p-1)p_0},-\frac{p_3}{p_0}\right).$$
--   An admissible local inverse $\psi$ at $y$ is $C^2$ at $\chi(y)$,
--   maps $\chi(y)$ to $y$, has derivative $J_\chi(y)$ there, and is a
--   two-sided inverse to $\chi$ on neighborhoods of these points.
--   For a scalar function $f$, write $\bar\partial_i f=d(f\circ\psi)_{\chi(y)}e_i$.
--   The radial coefficients and drift are
--   $$N(y)=m-1-u(w-u)-(p-1)p_0,\qquad B(y)=\frac{N(y)}{\rho\omega},$$
--   $$A(y)=\frac{(p-1)((1-m)p_0+w(p_1-p_3))-v^2
--   -\tfrac12(p-1)vp_1}{\rho\omega},\qquad G(y)=uvA(y)+v^2B(y).$$
--   Set
--   $$S(y)=(p-1)((p-m)-(m-1)(p_0-1))+(p-1)w(p_1-p_3)
--   -\tfrac12(p-1)vp_1,\quad H(y)=p-1-(m-1)p_0,$$
--   $$N_2(y)=(1-L^{-2})u^2+(-1+4L^{-2})uw-w^2/L^2,\qquad L=m+1,$$
--   $$R_e(y)=R_q(m,u,w),\quad
--   N_4(y)=-R_e-(m-1)\partial_0R_e-(p-m)(p_0-1),\quad
--   E(y)=\rho(y)-r(m,v).$$
--   Here
--   $$R_q(m,u,w)=P(m,u,w)-
--   \left[m+\frac{mu^2}{m^2-1}-\frac{2uw}{m+1}+\frac{w^2}{2(m+1)}\right].$$
--   The logarithmic wall rates are
--   $$a_s=\frac{1-m^2-(v-w)^2+u^2}{2\omega},\qquad
--   a_w=-1-\frac{2(1+u(v+w-u))}{\omega}.$$
--   Let $D_\chi f=df\,J_\chi$, define
--   $$c(y)=(D_\chi G\,e_0,uD_\chi G\,e_1,wD_\chi G\,e_3),$$
--   $$\mathcal A_k(y)=
--   \begin{pmatrix}uD_\chi a_s\,e_1&(w/k^2)D_\chi a_s\,e_3\\
--   k^2uD_\chi a_w\,e_1&wD_\chi a_w\,e_3\end{pmatrix},$$
--   and $\ell_k(y)=(\log u,k^2\log w)$.
--   All vector and operator norms use the sup norm.
--
--   For $C,A\geq0$ define
--   $$S_{C,A,x,y}(c)=|c_1||x|+|c_2||y|+CA(|c_1|+|c_2|),$$
--   $$K_{C,l}(c)=(C+1)(|c_0|+l(|c_1|+|c_2|)).$$
--
--   The logarithmic active-wall field is $F/\omega$, its observable is $\log v$,
--   and its original-time rate is $6\omega/D$. The tangent projection at fixed
--   relative active-wall clock is
--   $$\Pi_{\rm clk}(y,h,\zeta)=h-(h_2/y_2-\zeta)F(y)/\omega(y).$$
--   Applied to the exact flow differential, it uses $\zeta=h_2/y_2$ at the
--   initial point. Radial input variations first apply $J_\chi$.
--   The wall tangent is $(h_1/u,k^2h_3/w)$; the radial source column is
--   $(D_\chi a_s e_0,k^2D_\chi a_w e_0)$.
--   The two column envelopes are the sums of the absolute entries of
--   $\mathcal A_k$. The weighted phase coefficient is $(c_0,c_1,c_2/k^2)$,
--   and its feedback rate is $|c_0|+l(|c_1|+|c_2|/k^2)$.
--   For the reflected finite-tail entry $e_\eta(Y)=\mathcal R P_\eta(Y)$,
--   define
--   $$F_\eta=\rho\circ e_\eta,\quad
--   \widehat F_\eta(Y)=r(P_+(e_\eta(Y))_0,P_+(e_\eta(Y))_2),\quad
--   D_\eta=\widehat F_\eta-F_\eta.$$
--   Its radial entrance coordinates are
--   $\chi(e_\eta(Y))=(F_\eta(Y),Y_1m_0(\eta,Y),Y_2m_1(\eta,Y),\eta)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def coupledVariationSource (C A x y : ℝ) (c : Fin 3 → ℝ) : ℝ :=
  |c 1| * |x| + |c 2| * |y| + C * A * (|c 1| + |c 2|)

def coupledVariationFeedback (C l : ℝ) (c : Fin 3 → ℝ) : ℝ :=
  (C + 1) * (|c 0| + l * (|c 1| + |c 2|))



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def entranceLogField (y : ProjectiveState) : ProjectiveState :=
  (entranceClockRate y)⁻¹ • projectiveField y

def entranceLogClock (y : ProjectiveState) : ℝ := Real.log (y 2)

def entranceOriginalClockRate (y : ProjectiveState) : ℝ :=
  (6 / projectiveStateDenom y) * entranceClockRate y

















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Tangent at fixed log(V/V_entry); zeta is the initial logarithmic wall variation. -/
def entranceClockProjection (y v : ProjectiveState) (ζ : ℝ) : ProjectiveState :=
  v - (v 2 / y 2 - ζ) • entranceLogField y





def entranceProjectedFlowVariation (y : ProjectiveState) (t₀ t : ℝ) (w : ProjectiveState) :
    ProjectiveState := entranceClockProjection (projectiveOriginalFlow y t₀ t)
      (projectiveFlowDifferential y t₀ t w) (w 2 / y 2)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def entranceWeakNumerator (y : ProjectiveState) : ℝ :=
  y 0 - 1 - y 1 * (y 3 - y 1) - (entranceStablePhase y - 1) * entranceStablePartial y 0

def entranceRadialStrongCoefficient (y : ProjectiveState) : ℝ :=
  ((entranceStablePhase y - 1) * ((1 - y 0) * entranceStablePartial y 0 +
    y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3)) - y 2 ^ 2 -
    (1 / 2) * (entranceStablePhase y - 1) * y 2 * entranceStablePartial y 1) /
      (entranceStableRadius y * entranceClockRate y)

def entranceRadialWeakCoefficient (y : ProjectiveState) : ℝ :=
  entranceWeakNumerator y / (entranceStableRadius y * entranceClockRate y)

def entranceStrongRemainder (y : ProjectiveState) : ℝ :=
  (entranceStablePhase y - 1) * ((entranceStablePhase y - y 0) -
    (y 0 - 1) * (entranceStablePartial y 0 - 1)) +
  (entranceStablePhase y - 1) * y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) -
  (1 / 2) * (entranceStablePhase y - 1) * y 2 * entranceStablePartial y 1











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX




def entranceStrongBracket (y : ProjectiveState) : ℝ :=
  entranceStablePhase y - 1 - (y 0 - 1) * entranceStablePartial y 0





















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def entranceRadialCoordinates (y : ProjectiveState) : ProjectiveState :=
  ![entranceStableRadius y, y 1, y 2, y 3]

def entranceRadialDifferential (y : ProjectiveState) : ProjectiveState →L[ℝ] ProjectiveState :=
  ContinuousLinearMap.pi ![fderiv ℝ entranceStableRadius y, ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 3]

def entranceRadialInverseDifferential (y : ProjectiveState) : ProjectiveState →L[ℝ] ProjectiveState :=
  ContinuousLinearMap.pi ![
    (entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0)) • ContinuousLinearMap.proj 0 -
    (entranceStablePartial y 1 / entranceStablePartial y 0) • ContinuousLinearMap.proj 1 -
    (y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0)) • ContinuousLinearMap.proj 2 -
    (entranceStablePartial y 3 / entranceStablePartial y 0) • ContinuousLinearMap.proj 3,
    ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 3]













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

structure EntranceRadialInverseAt (y : ProjectiveState) (Ψ : ProjectiveState → ProjectiveState) : Prop where
  apply_base : Ψ (entranceRadialCoordinates y) = y
  contDiffAt : ContDiffAt ℝ 2 Ψ (entranceRadialCoordinates y)
  hasFDerivAt : HasFDerivAt Ψ (entranceRadialInverseDifferential y) (entranceRadialCoordinates y)
  left_inverse : ∀ᶠ z in 𝓝 y, Ψ (entranceRadialCoordinates z) = z
  right_inverse : ∀ᶠ z in 𝓝 (entranceRadialCoordinates y), entranceRadialCoordinates (Ψ z) = z















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

def compactConnectionCoordinates (η : ℝ) (Y : CoreAngleState) : ProjectiveState :=
  ![compactConnectionFinitePhase η Y, Y 1 * coreTailMultiplier η Y 0,
    Y 2 * coreTailMultiplier η Y 1, η]









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def compactConnectionPhase (η : ℝ) (Y : CoreAngleState) : ℝ :=
  coreRadius (compactConnectionState η Y 0) (compactConnectionState η Y 2)

def compactConnectionError (η : ℝ) (Y : CoreAngleState) : ℝ :=
  compactConnectionPhase η Y - compactConnectionFinitePhase η Y





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def entranceRadiusCorrection (y : ProjectiveState) : ℝ :=
  entranceStableRadius y - coreRadius (y 0) (y 2)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology



local instance entranceStableOperatorGroup : NormedAddCommGroup (StableState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance entranceStableOperatorSpace : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX


local instance entranceOperatorSpace : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology



local instance entranceQuarticStableOperatorGroup : NormedAddCommGroup (StableState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance entranceQuarticStableOperatorSpace : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance

def entranceQuarticRemainder (y : ProjectiveState) : ℝ := stableQuadraticRemainder (stableRestriction y)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def entranceStrongLogRate (y : ProjectiveState) : ℝ := connectionStrongClockRate (y 0) (y 1) (y 2) (y 3)

def entranceWeakLogRate (y : ProjectiveState) : ℝ := connectionWeakClockRate (y 0) (y 1) (y 2) (y 3)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def entranceWeakQuadratic (y : ProjectiveState) : ℝ :=
  (1 - 1 / (y 0 + 1) ^ 2) * y 1 ^ 2 + (-1 + 4 / (y 0 + 1) ^ 2) * y 1 * y 3 - y 3 ^ 2 / (y 0 + 1) ^ 2

def entranceWeakRemainder (y : ProjectiveState) : ℝ :=
  -entranceQuarticRemainder y - (y 0 - 1) * fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) -
    (entranceStablePhase y - y 0) * (entranceStablePartial y 0 - 1)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def entranceRadialDrift (y : ProjectiveState) : ℝ :=
  y 1 * y 2 * entranceRadialStrongCoefficient y + y 2 ^ 2 * entranceRadialWeakCoefficient y







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def entranceRadialDriftDifferential (y : ProjectiveState) : ProjectiveState →L[ℝ] ℝ :=
  (fderiv ℝ entranceRadialDrift y).comp (entranceRadialInverseDifferential y)

def entranceRadialVariationCoefficients (y : ProjectiveState) : Fin 3 → ℝ :=
  ![entranceRadialDriftDifferential y (Pi.single 0 1),
    y 1 * entranceRadialDriftDifferential y (Pi.single 1 1),
    y 3 * entranceRadialDriftDifferential y (Pi.single 3 1)]













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def entranceStrongLogDifferential (y : ProjectiveState) : ProjectiveState →L[ℝ] ℝ :=
  (fderiv ℝ entranceStrongLogRate y).comp (entranceRadialInverseDifferential y)

def entranceWeakLogDifferential (y : ProjectiveState) : ProjectiveState →L[ℝ] ℝ :=
  (fderiv ℝ entranceWeakLogRate y).comp (entranceRadialInverseDifferential y)

def entranceWallWeightedMatrix (k : ℝ) (y : ProjectiveState) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![y 1 * entranceStrongLogDifferential y (Pi.single 1 1),
      y 3 / k ^ 2 * entranceStrongLogDifferential y (Pi.single 3 1);
    k ^ 2 * y 1 * entranceWeakLogDifferential y (Pi.single 1 1),
      y 3 * entranceWeakLogDifferential y (Pi.single 3 1)]

def entranceWallWeightedColumn (k : ℝ) (y : ProjectiveState) (j : Fin 2) : ℝ :=
  |entranceWallWeightedMatrix k y 0 j| + |entranceWallWeightedMatrix k y 1 j|















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def entranceWallRadialSource (k : ℝ) (y : ProjectiveState) : Fin 2 → ℝ :=
  ![entranceStrongLogDifferential y (Pi.single 0 1), k ^ 2 * entranceWeakLogDifferential y (Pi.single 0 1)]





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def entrancePhaseFeedbackRate (k l : ℝ) (y : ProjectiveState) : ℝ :=
  |entranceRadialVariationCoefficients y 0| +
    l * (|entranceRadialVariationCoefficients y 1| + |entranceRadialVariationCoefficients y 2| / k ^ 2)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def entranceWallTangent (k : ℝ) (y v : ProjectiveState) : Fin 2 → ℝ :=
  ![v 1 / y 1, k ^ 2 * (v 3 / y 3)]













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def entranceLogWalls (k : ℝ) (y : ProjectiveState) : Fin 2 → ℝ :=
  ![Real.log (y 1), k ^ 2 * Real.log (y 3)]









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def entranceWeightedPhaseCoefficients (k : ℝ) (y : ProjectiveState) : Fin 3 → ℝ :=
  ![entranceRadialVariationCoefficients y 0, entranceRadialVariationCoefficients y 1,
    entranceRadialVariationCoefficients y 2 / k ^ 2]







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def entranceRadialClockVariation (y : ProjectiveState) (t₀ t : ℝ) (d : ProjectiveState) : ProjectiveState :=
  entranceProjectedFlowVariation y t₀ t (entranceRadialInverseDifferential y d)















end BianchiIX

end
end


