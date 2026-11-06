-- Prove2me | Definitions.Def_BianchiIX_TerminalConnectionData
-- name    : BianchiIX_TerminalConnectionData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T17:55:05.789963+00:00
-- url     : https://prove2.me/theorems/de00740a-c3b1-40c1-ae34-bb59bfac709e
-- title:
--   Terminal exit clocks, cyclic charts and physical connection maps
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and define
--   $$g(R,v)=\sqrt{R^2-v^2},\qquad d(R,u,v,w)=g(R,v)+u(v+w-u),$$
--   $$f_R=\frac{-u(v+w-u)R-g(R,v)(u-w)^2/R}{d},$$
--   $$a_s=\frac{2g(R,v)-R^2+2vw-w^2+u^2}{2d},\qquad
--   a_w=\frac{g(R,v)-2-u(v+w-u)}d.$$
--   The exit clock rate is $\omega(y)=1-m+u(v+w-u)$, and its field is
--   $F_{\log}(y)=F(y)/\omega(y)$. Division and square roots have their total
--   real-valued Lean meanings.
--
--   For $Y=(R,u,w)$ define $E_v(Y)=(f_R,a_su,a_ww)$, evaluated at $(R,u,v,w)$.
--   The coordinate maps are $Q(m,u,v,w)=(r(m,v),u,w)$ and
--   $Q_v^{-1}(R,u,w)=(1-g(R,v),u,v,w)$.
--   For a curve $Y(s)$ set
--   $$M_i(Y,t)=\exp\int_0^t a_i(Y_0(s),Y_1(s),e^{-s},Y_2(s))\,ds
--   \quad(i=s,w).$$
--   Let $\mathcal R_{\alpha,b,A,D}$ consist of the states satisfying
--   $$7/4\leq R\leq17/4,\quad |u|,|w|\leq1/100,\quad
--   |u|+|w|\leq Ab,\quad |R-(2+2\alpha)|\leq Db.$$
--   Put
--   $$B(\alpha,b,A,D,T)=[10(\alpha+Db)+100(Ab)^2]T+100Ab+5,$$
--   $$L(\eta,\alpha,J)=\log(1/\eta)+J\log(1/\alpha).$$
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
--   For $y=(m,u,v,w)$ define the cyclic chart by
--   $$H(y)=(m+1)^2+K(u,v,w),\qquad
--   \mathcal A(y)=(1-4(m+1)/H,4v/H,4w/H,4u/H).$$
--   Its normalized symmetry is
--   $$A(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a).$$
--   Put $z_h(Y)=\mathcal A(P_h(Y))$ and
--   $$\mathcal T(h,Y)=T_h(Y)+T_+(z_h(Y)),\qquad
--   \mathcal P(h,Y)=P_+(z_h(Y)),\qquad x_Y^c=A\Xi(e_-(Y)).$$
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and $g_*(x)=(\Pi(x))_v$.
--
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and $g_*(x)=(\Pi(x))_v$.
--   The closed exit region $\mathcal E_h$ is defined by
--   $$m\leq0,\quad7/4\leq r(m,v)\leq17/4,\quad
--   |u|,|w|\leq1/100,\quad h\leq v\leq1.$$
--   Let $L(\eta,\alpha,J)=\log(1/\eta)+J\log(1/\alpha)$.
--
--   The logarithmic wall map for the compact connection is
--   $(\log P_+(\mathcal R P_\eta(Y))_1,
--   \log P_+(\mathcal R P_\eta(Y))_3)$, where
--   $\mathcal R(m,u,v,w)=(-m,u,w,v)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_BianchiIX_Algebra_Projective
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

section

noncomputable section

namespace BianchiIX

def exitTailLength (η α : ℝ) (J : ℕ) : ℝ := Real.log (1 / η) + J * Real.log (1 / α)













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def exitTailGap (R v : ℝ) : ℝ := Real.sqrt (R ^ 2 - v ^ 2)

def exitTailSpeed (R u v w : ℝ) : ℝ := exitTailGap R v + coupling u v w

def exitTailRadial (R u v w : ℝ) : ℝ :=
  (-coupling u v w * R - exitTailGap R v * (u - w) ^ 2 / R) / exitTailSpeed R u v w

def exitTailStrongRate (R u v w : ℝ) : ℝ :=
  (2 * exitTailGap R v - R ^ 2 + 2 * v * w - w ^ 2 + u ^ 2) / (2 * exitTailSpeed R u v w)

def exitTailWeakRate (R u v w : ℝ) : ℝ :=
  (exitTailGap R v - 2 - coupling u v w) / exitTailSpeed R u v w











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def axisCycleDenom (m u v w : ℝ) : ℝ := (m + 1) ^ 2 + curvature u v w











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def exitClockRate (y : ProjectiveState) : ℝ := 1 - y 0 + coupling (y 1) (y 2) (y 3)

def exitLogField (y : ProjectiveState) : ProjectiveState := (exitClockRate y)⁻¹ • projectiveField y













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

abbrev ExitTailState := Fin 3 → ℝ

def toExitTailState (y : ProjectiveState) : ExitTailState := ![coreRadius (y 0) (y 2), y 1, y 3]

def fromExitTailState (v : ℝ) (Y : ExitTailState) : ProjectiveState :=
  ![1 - exitTailGap (Y 0) v, Y 1, v, Y 2]

def exitTailField (v : ℝ) (Y : ExitTailState) : ExitTailState :=
  ![exitTailRadial (Y 0) (Y 1) v (Y 2),
    exitTailStrongRate (Y 0) (Y 1) v (Y 2) * Y 1,
    exitTailWeakRate (Y 0) (Y 1) v (Y 2) * Y 2]















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def exitTailWallRate (v : ℝ) (Y : ExitTailState) : Fin 2 → ℝ :=
  ![exitTailStrongRate (Y 0) (Y 1) v (Y 2), exitTailWeakRate (Y 0) (Y 1) v (Y 2)]

def exitTailMultiplier (Y : ℝ → ExitTailState) (i : Fin 2) (T : ℝ) : ℝ :=
  Real.exp (∫ s in (0 : ℝ)..T, exitTailWallRate (Real.exp (-s)) (Y s) i)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def projectiveCycleDenom (y : ProjectiveState) : ℝ := axisCycleDenom (y 0) (y 1) (y 2) (y 3)

def projectiveCycle (y : ProjectiveState) : ProjectiveState :=
  ![1 - 4 * (y 0 + 1) / projectiveCycleDenom y, 4 * y 2 / projectiveCycleDenom y,
    4 * y 3 / projectiveCycleDenom y, 4 * y 1 / projectiveCycleDenom y]

















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def exitTailRegion (α b A D : ℝ) (Y : ExitTailState) : Prop :=
  (7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) ∧ |Y 1| ≤ 1 / 100 ∧ |Y 2| ≤ 1 / 100 ∧
    |Y 1| + |Y 2| ≤ A * b ∧ |Y 0 - (2 + 2 * α)| ≤ D * b

def exitTailRateBudget (α b A D T : ℝ) : ℝ :=
  (10 * (α + D * b) + 100 * (A * b) ^ 2) * T + 100 * A * b + 5









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def exitPhysicalRegion (h : ℝ) (y : ProjectiveState) : Prop :=
  y 0 ≤ 0 ∧ (7 / 4 ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 17 / 4) ∧
    |y 1| ≤ 1 / 100 ∧ (h ≤ y 2 ∧ y 2 ≤ 1) ∧ |y 3| ≤ 1 / 100











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def terminalConnectionTime (h : ℝ) (Y : ExitTailState) : ℝ :=
  coreTailTime h Y + entranceReturnTime (projectiveCycle (coreTailState h Y))

def terminalConnectionState (h : ℝ) (Y : ExitTailState) : ProjectiveState :=
  entranceReturnState (projectiveCycle (coreTailState h Y))







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def compactConnectionLogWalls (η : ℝ) (Y : CoreAngleState) : Fin 2 → ℝ :=
  entranceLogWalls 1 (compactConnectionState η Y)







end BianchiIX

end
end


