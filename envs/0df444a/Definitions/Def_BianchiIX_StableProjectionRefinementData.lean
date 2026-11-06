-- Prove2me | Definitions.Def_BianchiIX_StableProjectionRefinementData
-- name    : BianchiIX_StableProjectionRefinementData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T16:22:51.95858+00:00
-- url     : https://prove2.me/theorems/25fd36c9-92a1-41f8-b1f2-8b22725f29a9
-- title:
--   Weighted stable residuals and quadratic phase remainders
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
--   Write $L=m+1$, $b=|u|+|w|$, $v_s=(v_1,v_2)$, and set
--   $$W_b(v)=b\|v\|+\|v_s\|,\quad
--   H_s(y;v,z)=|u|\|v\|\|z\|+|v_0||z_1|+|v_1||z_0|
--   +b(|v_1|\|z\|+\|v\||z_1|).$$
--   The corrected and quadratic remainders are
--   $$R_c=P-\Theta,\quad R_q=P-\left(m+A(m)u^2+C(m)uw+\frac{w^2}{2L}\right).$$
--   For $K\in\mathbb R$, let $a_i(K,y)=6K r_{4-i}(m,w)/\Delta(y)$,
--   where $r_4,r_3$ are independent of $w$, and put
--   $$M(y)=(u^3,u^2w,uw^2,w^3),\quad C_K(y)=\sum_{i=0}^3a_i(K,y)M_i(y),$$
--   $$g_{K,s}(y)=\frac{6K}{\Delta(\Phi_K(y,s))}R(\Phi_K(y,s)).$$
--   The cubic derivative budgets are
--   $$B_1(y;v)=b^3\|v\|+3b^2\|v_s\|,$$
--   $$B_2^c(y;v,z)=b^3\|v\|\|z\|
--   +3b^2(\|v\|\|z_s\|+\|v_s\|\|z\|)+6b\|v_s\|\|z_s\|.$$
--   A direction is radial if its last two coordinates vanish, and transverse
--   if its zeroth coordinate vanishes.
--
--   This data includes the explicit first two derivatives of $A(m)$ and $C(m)$,
--   the bilinear Hessian of $\Theta$, and the cubic monomials $M_i$ with their
--   linear and bilinear derivatives. The reciprocal coordinate map is
--   $(m,w)\mapsto(x,w)$, where $x=(m+1)^{-1}$. With $R_x=\sqrt{1+x^2w^2}$,
--   the four compactified residual profiles are
--   $$-\frac{2(1-x)x^2}{(1-2x)^2},\quad
--   \frac{2(3-4x)x^2}{(1-2x)^2},$$
--   $$-\frac{x((1-x)^2+x^2)}{(1-2x)^2}-\frac{1-x}{1-2x}
--   +\frac{R_x+x}{R_x(R_x+1)},\quad 2x+1-\frac1{R_x+1}.$$
--   The weak-radius remainder is
--   $e(m,w)=\sqrt{(m+1)^2+w^2}-(m+1)-w^2/[2(m+1)]$,
--   together with its two first and three second partial derivatives.
--   Its second-derivative kernel is
--   $$\frac{r^2+rL+L^2}{r^3(r+L)},\qquad r=\sqrt{L^2+w^2},\quad L=m+1.$$
--   The additional second input weight is
--   $b\|v\|\|z\|+\|v_s\|\|z\|+\|v\|\|z_s\|$.
--   The residual tail is $\int_T^\infty g_{K,s}(y)\,ds$,
--   and the corrected phase tail is $P(y)-\Theta(\Phi_K(y,T))$.
--   All spaces of continuous linear maps carry their usual operator norms.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Fin.VecNotation
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



-- Fix the operator norm structure before forming the second operator space.
local instance _root_.BianchiIX.instNormedAddCommGroupContinuousLinearMapRealId_bianchiIX : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance _root_.BianchiIX.instNormedSpaceRealContinuousLinearMapId_bianchiIX : NormedSpace ℝ (E →L[ℝ] F) := inferInstance



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def reciprocalParameter (y : Fin 2 → ℝ) : ℝ := (y 0 + 1)⁻¹

def reciprocalParameterMap (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![reciprocalParameter y, y 1]

















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open scoped Topology

def stableCorrectionADeriv (m : ℝ) : ℝ := -(m ^ 2 + 1) / (m ^ 2 - 1) ^ 2

def stableCorrectionASecond (m : ℝ) : ℝ := 2 * m * (m ^ 2 + 3) / (m ^ 2 - 1) ^ 3

def stableCorrectionCDeriv (m : ℝ) : ℝ := 2 / (m + 1) ^ 2

def stableCorrectionCSecond (m : ℝ) : ℝ := -4 / (m + 1) ^ 3

def stableCorrectedHessian (m u w : ℝ) (v r : Fin 3 → ℝ) : ℝ :=
  (w ^ 2 / stableWeakRadius m w ^ 3 + stableCorrectionASecond m * u ^ 2 +
    stableCorrectionCSecond m * u * w) * v 0 * r 0 +
  (2 * stableCorrectionADeriv m * u + stableCorrectionCDeriv m * w) * (v 0 * r 1 + v 1 * r 0) +
  (-(m + 1) * w / stableWeakRadius m w ^ 3 + stableCorrectionCDeriv m * u) * (v 0 * r 2 + v 2 * r 0) +
  2 * stableCorrectionA m * v 1 * r 1 +
  stableCorrectionC m * (v 1 * r 2 + v 2 * r 1) +
  (m + 1) ^ 2 / stableWeakRadius m w ^ 3 * v 2 * r 2













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open scoped Topology

def stableWeakRemainder (m w : ℝ) : ℝ :=
  stableWeakRadius m w - (m + 1) - w ^ 2 / (2 * (m + 1))

def stableWeakRemainderM (m w : ℝ) : ℝ :=
  (m + 1) / stableWeakRadius m w - 1 + w ^ 2 / (2 * (m + 1) ^ 2)

def stableWeakRemainderW (m w : ℝ) : ℝ :=
  w / stableWeakRadius m w - w / (m + 1)

def stableWeakRemainderMM (m w : ℝ) : ℝ :=
  w ^ 2 / stableWeakRadius m w ^ 3 - w ^ 2 / (m + 1) ^ 3

def stableWeakRemainderMW (m w : ℝ) : ℝ :=
  -(m + 1) * w / stableWeakRadius m w ^ 3 + w / (m + 1) ^ 2

def stableWeakRemainderWW (m w : ℝ) : ℝ :=
  (m + 1) ^ 2 / stableWeakRadius m w ^ 3 - 1 / (m + 1)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableResidualCoefficient (i : Fin 4) (y : Fin 2 → ℝ) : ℝ :=
  ![stableResidual4 (y 0), stableResidual3 (y 0),
    stableResidual2 (y 0) (y 1), stableResidual1 (y 0) (y 1)] i

def stableResidualProfile (i : Fin 4) (p : Fin 2 → ℝ) : ℝ :=
  let x := p 0
  let R := phaseNorm 1 (x * p 1)
  ![-2 * (1 - x) * x ^ 2 / (1 - 2 * x) ^ 2,
    2 * (3 - 4 * x) * x ^ 2 / (1 - 2 * x) ^ 2,
    -x * ((1 - x) ^ 2 + x ^ 2) / (1 - 2 * x) ^ 2 - (1 - x) / (1 - 2 * x) +
      (R + x) / (R * (R + 1)),
    2 * x + 1 - 1 / (R + 1)] i







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableWeakSecondKernel (m w : ℝ) : ℝ :=
  (stableWeakRadius m w ^ 2 + stableWeakRadius m w * (m + 1) + (m + 1) ^ 2) /
    (stableWeakRadius m w ^ 3 * (stableWeakRadius m w + (m + 1)))









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableCubicMonomial (i : Fin 4) (y : StableState) : ℝ :=
  ![y 1 ^ 3, y 1 ^ 2 * y 2, y 1 * y 2 ^ 2, y 2 ^ 3] i

def stableCubicDifferential (i : Fin 4) (y v : StableState) : ℝ :=
  ![3 * y 1 ^ 2 * v 1, 2 * y 1 * y 2 * v 1 + y 1 ^ 2 * v 2,
    y 2 ^ 2 * v 1 + 2 * y 1 * y 2 * v 2, 3 * y 2 ^ 2 * v 2] i

def stableCubicHessian (i : Fin 4) (y v w : StableState) : ℝ :=
  ![6 * y 1 * v 1 * w 1,
    2 * y 2 * v 1 * w 1 + 2 * y 1 * v 1 * w 2 + 2 * y 1 * v 2 * w 1,
    2 * y 2 * v 1 * w 2 + 2 * y 2 * v 2 * w 1 + 2 * y 1 * v 2 * w 2,
    6 * y 2 * v 2 * w 2] i











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableResidualClock (K : ℝ) (y : StableState) : ℝ := 6 * K / stableBoundaryDenom y









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableCenterWeakProjection : StableState →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 2]





def stableScaledResidualCoefficient (K : ℝ) (i : Fin 4) (y : StableState) : ℝ :=
  stableResidualClock K y * stableResidualCoefficient i (stableCenterWeakProjection y)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableScaledResidual (K : ℝ) (y : StableState) : ℝ :=
  stableResidualClock K y * stableCorrectedResidual (y 0) (y 1) (y 2)

def stableScaledResidualCubic (K : ℝ) (y : StableState) : ℝ :=
  ∑ i : Fin 4, stableScaledResidualCoefficient K i y * stableCubicMonomial i y

def stableCubicFirstBudget (y v : StableState) : ℝ :=
  (|y 1| + |y 2|) ^ 3 * ‖v‖ + 3 * (|y 1| + |y 2|) ^ 2 * ‖![v 1, v 2]‖

def stableCubicSecondBudget (y v w : StableState) : ℝ :=
  (|y 1| + |y 2|) ^ 3 * ‖v‖ * ‖w‖ +
    3 * (|y 1| + |y 2|) ^ 2 * (‖v‖ * ‖![w 1, w 2]‖ + ‖![v 1, v 2]‖ * ‖w‖) +
    6 * (|y 1| + |y 2|) * ‖![v 1, v 2]‖ * ‖![w 1, w 2]‖











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableStrongHessianBudget (y v w : StableState) : ℝ :=
  |y 1| * ‖v‖ * ‖w‖ + (|v 0| * |w 1| + |v 1| * |w 0|) +
    (|y 1| + |y 2|) * (|v 1| * ‖w‖ + ‖v‖ * |w 1|)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableFirstInputWeight (b : ℝ) (v : StableState) : ℝ :=
  b * ‖v‖ + ‖![v 1, v 2]‖

def stableSecondInputWeight (b : ℝ) (v w : StableState) : ℝ :=
  b * ‖v‖ * ‖w‖ + ‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖

















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def stableRescaledResidualRate (K s : ℝ) (y : StableState) : ℝ :=
  stableScaledResidual K (stableRescaledFlow K y s)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

local instance _root_.BianchiIX.instNormedAddCommGroupContinuousLinearMapRealIdStableState : NormedAddCommGroup (StableState →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance _root_.BianchiIX.instNormedSpaceRealContinuousLinearMapIdStableState : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance

def stableResidualTailIntegral (K T : ℝ) (y : StableState) : ℝ :=
  ∫ s in Ioi T, stableRescaledResidualRate K s y







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def stableCorrectedRemainder (y : StableState) : ℝ :=
  stableBoundaryProjection (y 0) (y 1) (y 2) - stableCorrectedPhase (y 0) (y 1) (y 2)

def stableCorrectedPhaseTail (K T : ℝ) (y : StableState) : ℝ :=
  stableBoundaryProjection (y 0) (y 1) (y 2) -
    stableCorrectedPhase (stableRescaledFlow K y T 0) (stableRescaledFlow K y T 1) (stableRescaledFlow K y T 2)















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

local instance _root_.BianchiIX.instNormedAddCommGroupContinuousLinearMapRealIdStableState_1 : NormedAddCommGroup (StableState →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance _root_.BianchiIX.instNormedSpaceRealContinuousLinearMapIdStableState_1 : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

local instance stableQuadraticExpansionOperatorGroup : NormedAddCommGroup (StableState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance stableQuadraticExpansionOperatorSpace : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance

def stableQuadraticPhase (m u w : ℝ) : ℝ :=
  m + stableCorrectionA m * u ^ 2 + stableCorrectionC m * u * w + w ^ 2 / (2 * (m + 1))

def stableQuadraticRemainder (y : StableState) : ℝ :=
  stableBoundaryProjection (y 0) (y 1) (y 2) - stableQuadraticPhase (y 0) (y 1) (y 2)









end BianchiIX

end
end


