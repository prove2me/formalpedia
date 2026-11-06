-- Prove2me | Definitions.Def_BianchiIX_CompactPhaseExpansionData
-- name    : BianchiIX_CompactPhaseExpansionData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T15:09:56.137195+00:00
-- url     : https://prove2.me/theorems/6f2f5d4c-e0d7-46bb-b323-c9da08f2428d
-- title:
--   Stable boundary projection and finite connection phase
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
--   For $y\in\mathbb R^4$, put
--   $$P_e(y)=P(y_0,y_1,y_3),\quad R_e(y)=\sqrt{(P_e(y)-1)^2+y_2^2}.$$
--   The reflected finite-tail entry is $e_\eta(Y)=\mathcal R P_\eta(Y)$,
--   and its finite matching phase is $F_\eta(Y)=R_e(e_\eta(Y))$.
--   For $A_Y(t)=1+(\alpha_{x_Y,0}(t))_0$, define the weak-wall multiplier
--   $$M_w(Y,t)=\exp\left(\log(1+(x_Y)_0)-\log A_Y(t)
--   +\int_0^t r_3(\alpha_{x_Y,0}(q))\,dq\right),$$
--   where $r_3$ is the third normalized wall rate. Set
--   $$B_\eta(Y)=\int_0^{T_\eta(Y)}2A_Y(t)(\beta_Y(t)_0-1)M_w(Y,t)^2\,dt.$$
--
--   Set $r=\sqrt{(m+1)^2+w^2}$ and
--   $$A(m)=\frac{m}{m^2-1},\quad C(m)=-\frac2{m+1},\quad
--   \Theta(m,u,w)=r-1+A(m)u^2+C(m)uw.$$
--   Its explicit gradient is used together with the residual
--   $R=r_4u^4+r_3u^3w+r_2u^2w^2+r_1uw^3$, where
--   $$r_4=-\frac{2m}{(m^2-1)^2},\quad r_3=\frac{2(3m-1)}{(m^2-1)^2},$$
--   $$r_2=-\frac{m^2+1}{(m^2-1)^2}-\frac m{m^2-1}
--   +\frac{r+1}{r(r+m+1)},\quad
--   r_1=\frac2{(m+1)^2}+\frac1{m+1}-\frac1{r+m+1}.$$
--
--   The two scalar wall rates are $(1-m^2-w^2+u^2)/2$ and $-(m+1+uw-u^2)$.
--   The stable linear block is the last two rows and columns of $KJ_o$;
--   its center column is $(K(J_o)_{10},K(J_o)_{20})$.
--   The first and second center variations are the zeroth components of
--   $L_{c+1}$ and $Q_{c+1}$; their limiting operators use the same total
--   limit convention. The open parameter neighborhood is
--   $|m-c|<1/40$, $|u|,|w|<1/200$.
--   The center approximation is $\Phi_{c+1}(y,s)_0$ and the corrected
--   approximation is $\Theta(\Phi(y,t))$.
--   The derivative of $Kdf_o(\Phi_K(y,s))(L_K(y,s)z)$ with respect to $y$,
--   integrated from zero to $s$, defines the second-variation integral.
--   The center budgets are
--   $$128b\|v_s\|+33000b^2E\|v\|,\qquad 128b+33000b^2E,\qquad B_2(y).$$
--   For a normalized boundary orbit, its stable clock is
--   $(c+1)\int_a^t(1+\alpha_{x,t_0}(q)_0)\,dq$.
--   For the orbit from $\iota(m,u,w)$, the corrected residual integral is
--   $$I_R(m,u,w,T)=\int_0^T(1+\alpha_{\Xi(\iota(m,u,w)),0}(t)_0)
--   R(\Phi(m,u,w;t))\,dt.$$
--   The entrance partials are the four ordinary components of $dP_e$.
--   Writing $r_\eta(Y)=\sqrt{(P_\eta(Y)_0-1)^2+\eta^2}$, the weak finite-phase
--   coefficient is
--   $$\frac{B_\eta(Y)(1-4/(r_\eta(Y)+Y_0))+m_1(\eta,Y)^2}
--   {F_\eta(Y)+Y_0-2}.$$
--   Finally, for the reference pulse
--   $\beta_k(t)=(1-k\tanh(kt),0,k\operatorname{sech}(kt),0)$,
--   the shifted original-time clock is $\tau_k(a,t)=\int_a^tD(\beta_k(q))/6\,dq$,
--   and the shifted variation is $\mathcal J_{\beta_k(a),0}(\tau_k(a,t))v$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveWallMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Module
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
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Order.ProjIcc
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers

section

noncomputable section

namespace BianchiIX

def stableStrongRate (m u w : ℝ) : ℝ := (1 - m ^ 2 - w ^ 2 + u ^ 2) / 2

def stableWeakRate (m u w : ℝ) : ℝ := -(m + 1 + u * w - u ^ 2)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableWeakRadius (m w : ℝ) : ℝ := phaseNorm (m + 1) w

def stableCorrectionA (m : ℝ) : ℝ := m / (m ^ 2 - 1)

def stableCorrectionC (m : ℝ) : ℝ := -2 / (m + 1)

def stableCorrectedPhase (m u w : ℝ) : ℝ :=
  stableWeakRadius m w - 1 + stableCorrectionA m * u ^ 2 + stableCorrectionC m * u * w

def stableCorrectedGradient (m u w : ℝ) : Fin 3 → ℝ :=
  ![(m + 1) / stableWeakRadius m w - (m ^ 2 + 1) / (m ^ 2 - 1) ^ 2 * u ^ 2 +
      2 / (m + 1) ^ 2 * u * w,
    2 * stableCorrectionA m * u + stableCorrectionC m * w,
    w / stableWeakRadius m w + stableCorrectionC m * u]



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableResidual4 (m : ℝ) : ℝ := -2 * m / (m ^ 2 - 1) ^ 2

def stableResidual3 (m : ℝ) : ℝ := 2 * (3 * m - 1) / (m ^ 2 - 1) ^ 2

def stableResidual2 (m w : ℝ) : ℝ :=
  -(m ^ 2 + 1) / (m ^ 2 - 1) ^ 2 - m / (m ^ 2 - 1) +
    (stableWeakRadius m w + 1) / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1)))

def stableResidual1 (m w : ℝ) : ℝ :=
  2 / (m + 1) ^ 2 + 1 / (m + 1) - 1 / (stableWeakRadius m w + (m + 1))

def stableCorrectedResidual (m u w : ℝ) : ℝ :=
  stableResidual4 m * u ^ 4 + stableResidual3 m * u ^ 3 * w +
    stableResidual2 m w * u ^ 2 * w ^ 2 + stableResidual1 m w * u * w ^ 3









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def referenceShiftClock (k s t : ℝ) : ℝ :=
  referenceClockPrimitive k t - referenceClockPrimitive k s













def referenceShiftedVariation (k s : ℝ) (w : ProjectiveState) (t : ℝ) : ProjectiveState :=
  projectiveFlowDifferential (referencePulse k s) 0 (referenceShiftClock k s t) w





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def stableBoundaryRegion (c : ℝ) (y : ProjectiveState) : Prop :=
  |y 0 - c| ≤ 1 / 10 ∧ |y 1| ≤ 1 / 100 ∧ y 2 = 0 ∧ |y 3| ≤ 1 / 100

def normalizedStableClock (x : NormalizedState) (t₀ s c t : ℝ) : ℝ :=
  (c + 1) * integralClock (normalizedProjectiveRate x t₀) s t









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology





def stableBoundaryEntry (m u w : ℝ) : ProjectiveState := ![m, u, 0, w]

def stableBoundaryOrbit (m u w t : ℝ) : ProjectiveState :=
  toProjectiveState (normalizedMaxCurve (fromProjectiveState (stableBoundaryEntry m u w)) 0 t)

/-- The projection is defined from the exact Einstein orbit in original time. -/
def stableBoundaryProjection (m u w : ℝ) : ℝ :=
  limUnder atTop (fun t => stableBoundaryOrbit m u w t 0)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

abbrev StableState := Fin 3 → ℝ

def stableInclusion : StableState →L[ℝ] ProjectiveState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1,
    0, ContinuousLinearMap.proj 2]

def stableRestriction : ProjectiveState →L[ℝ] StableState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 3]

def stableBoundaryField (y : StableState) : StableState :=
  ![y 0 * y 1 ^ 2 - (y 0 + 1) * y 1 * y 2 + y 2 ^ 2,
    stableStrongRate (y 0) (y 1) (y 2) * y 1,
    stableWeakRate (y 0) (y 1) (y 2) * y 2]

def stableBoundaryDenom (y : StableState) : ℝ := 3 + y 0 ^ 2 + (y 1 - y 2) ^ 2

def stableOriginalField (y : StableState) : StableState :=
  (6 / stableBoundaryDenom y) • stableBoundaryField y



























end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def stableCorrectedApproximation (y : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  let Y := stableBoundaryOrbit (y 0) (y 1) (y 2) t
  stableCorrectedPhase (Y 0) (Y 1) (Y 3)

def stableResidualIntegral (m u w T : ℝ) : ℝ :=
  ∫ t in 0..T, normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 t *
    stableCorrectedResidual (stableBoundaryOrbit m u w t 0)
      (stableBoundaryOrbit m u w t 1) (stableBoundaryOrbit m u w t 3)













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableOriginalFlow (y : StableState) (t : ℝ) : StableState :=
  stableRestriction (projectiveOriginalFlow (stableInclusion y) 0 t)

def stableFlowDifferential (y : StableState) (t : ℝ) : StableState →L[ℝ] StableState :=
  stableRestriction.comp ((projectiveFlowDifferential (stableInclusion y) 0 t).comp stableInclusion)



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableBoundaryJacobian (y : StableState) : Matrix (Fin 3) (Fin 3) ℝ :=
  let m := y 0
  let u := y 1
  let w := y 2
  ![![u ^ 2 - u * w, 2 * m * u - (m + 1) * w, -(m + 1) * u + 2 * w],
    ![-m * u, (1 - m ^ 2 - w ^ 2 + 3 * u ^ 2) / 2, -u * w],
    ![-w, (2 * u - w) * w, -(m + 1 + 2 * u * w - u ^ 2)]]

def stableDenomGradient (y : StableState) : StableState :=
  ![2 * y 0, 2 * (y 1 - y 2), 2 * (y 2 - y 1)]

def stableOriginalJacobian (y : StableState) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => 6 / stableBoundaryDenom y * stableBoundaryJacobian y i j -
    6 / stableBoundaryDenom y ^ 2 * stableBoundaryField y i * stableDenomGradient y j















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableBoundaryHessian (y v w : StableState) : StableState :=
  ![(2 * y 1 - y 2) * (v 0 * w 1 + v 1 * w 0) -
      y 1 * (v 0 * w 2 + v 2 * w 0) + 2 * y 0 * v 1 * w 1 -
      (y 0 + 1) * (v 1 * w 2 + v 2 * w 1) + 2 * v 2 * w 2,
    -y 1 * v 0 * w 0 - y 0 * (v 0 * w 1 + v 1 * w 0) +
      3 * y 1 * v 1 * w 1 - y 2 * (v 1 * w 2 + v 2 * w 1) -
      y 1 * v 2 * w 2,
    -(v 0 * w 2 + v 2 * w 0) + 2 * y 2 * v 1 * w 1 +
      2 * (y 1 - y 2) * (v 1 * w 2 + v 2 * w 1) - 2 * y 1 * v 2 * w 2]

def stableDenomHessian (v w : StableState) : ℝ :=
  2 * v 0 * w 0 + 2 * (v 1 - v 2) * (w 1 - w 2)

















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- The scale is held fixed when differentiating the initial state. -/
def stableRescaledFlow (K : ℝ) (y : StableState) (s : ℝ) : StableState :=
  stableOriginalFlow y (K * s)

def stableRescaledDifferential (K : ℝ) (y : StableState) (s : ℝ) : StableState →L[ℝ] StableState :=
  stableFlowDifferential y (K * s)



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableOriginalHessian (y v w : StableState) : StableState :=
  (6 / stableBoundaryDenom y) • stableBoundaryHessian y v w -
    (6 / stableBoundaryDenom y ^ 2) •
      (dotProduct (stableDenomGradient y) v • (stableBoundaryJacobian y).mulVec w +
        dotProduct (stableDenomGradient y) w • (stableBoundaryJacobian y).mulVec v +
        stableDenomHessian v w • stableBoundaryField y) +
    (12 * dotProduct (stableDenomGradient y) v * dotProduct (stableDenomGradient y) w /
      stableBoundaryDenom y ^ 3) • stableBoundaryField y













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableRescaledSecondDifferential (K : ℝ) (y : StableState) (s : ℝ) :
    StableState →L[ℝ] (StableState →L[ℝ] StableState) :=
  (fderiv ℝ (fun z : StableState × ℝ => stableRescaledDifferential K z.1 z.2) (y, s)).comp
    (ContinuousLinearMap.inl ℝ StableState ℝ)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def stableLinearBlock (K : ℝ) (y : StableState) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![K * stableOriginalJacobian y 1 1, K * stableOriginalJacobian y 1 2],
    ![K * stableOriginalJacobian y 2 1, K * stableOriginalJacobian y 2 2]]

def stableCenterColumn (K : ℝ) (y : StableState) : Fin 2 → ℝ :=
  ![K * stableOriginalJacobian y 1 0, K * stableOriginalJacobian y 2 0]









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableRescaledVariationRate (K : ℝ) (w : StableState) (p : StableState × ℝ) : StableState :=
  K • fderiv ℝ stableOriginalField (stableRescaledFlow K p.1 p.2)
    (stableRescaledDifferential K p.1 p.2 w)

def stableRescaledSecondSource (K : ℝ) (v w : StableState) (p : StableState × ℝ) : StableState :=
  K • (stableOriginalHessian (stableRescaledFlow K p.1 p.2)
      (stableRescaledDifferential K p.1 p.2 v) (stableRescaledDifferential K p.1 p.2 w) +
    (stableOriginalJacobian (stableRescaledFlow K p.1 p.2)).mulVec
      (stableRescaledSecondDifferential K p.1 p.2 v w))





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def coreTailWeakEnergyIntegrand (p : CoreAngleState × ℝ) : ℝ :=
  2 * normalizedProjectiveRate (fromProjectiveState (coreTailEntry p.1)) 0 p.2 *
    (projectiveOriginalFlow (coreTailEntry p.1) 0 p.2 0 - 1) *
    (normalizedProjectiveWallMultiplier (fromProjectiveState (coreTailEntry p.1)) p.2 2) ^ 2

def coreTailWeakEnergyCoefficient (η : ℝ) (Y : CoreAngleState) : ℝ :=
  ∫ t in 0..coreTailTime η Y, coreTailWeakEnergyIntegrand (Y, t)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableHessianBudget (y v w : StableState) : ℝ :=
  (|y 1| + |y 2|) * ‖v‖ * ‖w‖ + ‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def stableVariationCenterBudget (y v : StableState) : ℝ :=
  128 * (|y 1| + |y 2|) * ‖![v 1, v 2]‖ +
    33000 * (|y 1| + |y 2|) ^ 2 * Real.exp (512 * (|y 1| + |y 2|)) * ‖v‖











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def stableCenterDifferential (c : ℝ) (y : StableState) (s : ℝ) : StableState →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (stableRescaledDifferential (c + 1) y s)

def stableCenterDifferentialLimit (c : ℝ) (y : StableState) : StableState →L[ℝ] ℝ :=
  limUnder atTop (stableCenterDifferential c y)

def stableCenterTailCoefficient (y : StableState) : ℝ :=
  128 * (|y 1| + |y 2|) + 33000 * (|y 1| + |y 2|) ^ 2 * Real.exp (512 * (|y 1| + |y 2|))













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableParameterDomain (c : ℝ) : Set StableState :=
  {y | |y 0 - c| < 1 / 40 ∧ |y 1| < 1 / 200 ∧ |y 2| < 1 / 200}

def stableCenterApproximation (c s : ℝ) (y : StableState) : ℝ := stableRescaledFlow (c + 1) y s 0





















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def stableSecondIntegral (K : ℝ) (y w : StableState) (s : ℝ) : StableState →L[ℝ] StableState :=
  ∫ r in 0..s, (fderiv ℝ (stableRescaledVariationRate K w) (y, r)).comp
    (ContinuousLinearMap.inl ℝ StableState ℝ)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def stableSecondCenterBudget (y : StableState) : ℝ :=
  192 * (|y 1| + |y 2|) * (40000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3) +
    10000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 2







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableCenterSecondDifferential (c : ℝ) (y : StableState) (s : ℝ) :
    StableState →L[ℝ] (StableState →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ StableState StableState ℝ (ContinuousLinearMap.proj 0)).comp
    (stableRescaledSecondDifferential (c + 1) y s)

def stableCenterSecondDifferentialLimit (c : ℝ) (y : StableState) :
    StableState →L[ℝ] (StableState →L[ℝ] ℝ) :=
  limUnder atTop (stableCenterSecondDifferential c y)















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def entranceStablePhase (y : ProjectiveState) : ℝ :=
  stableBoundaryProjection (y 0) (y 1) (y 3)

def entranceStablePartial (y : ProjectiveState) (i : Fin 4) : ℝ :=
  fderiv ℝ entranceStablePhase y (Pi.single i 1)

def entranceStableRadius (y : ProjectiveState) : ℝ := coreRadius (entranceStablePhase y) (y 2)





















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- The finite phase in (B.47), before the long entrance. -/
def compactConnectionFinitePhase (η : ℝ) (Y : CoreAngleState) : ℝ :=
  entranceStableRadius (compactConnectionEntry η Y)















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def compactConnectionWeakCoefficient (η : ℝ) (Y : CoreAngleState) : ℝ :=
  (coreTailWeakEnergyCoefficient η Y * (1 - 4 / (coreRadius (coreTailState η Y 0) η + Y 0)) +
    coreTailMultiplier η Y 1 ^ 2) / (compactConnectionFinitePhase η Y + Y 0 - 2)









end BianchiIX

end
end


