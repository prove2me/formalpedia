-- Prove2me | Definitions.Def_BianchiIX_SectionRestartData
-- name    : BianchiIX_SectionRestartData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-06T04:04:00.901119+00:00
-- url     : https://prove2.me/theorems/68e72d7d-713b-40b7-902b-65d1467b1fd5
-- title:
--   Physical restart states and budgets on angular and shear labels
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   Let $X=\mathbb R^5$ with coordinates $x=(p,s,a,b,c)$ and the sup norm. Write
--   $$F(x)=(P,Q,r_1a,r_2b,r_3c),\qquad \mathcal C(x)=C(p,s,a,b,c),$$
--   and let $W=\{(p,s,a,b,c)\in X:a>0,\ b>0,\ c>0\}$.
--
--   Write $N_1(x)=a$, $N_2(x)=b$, and $N_3(x)=c$. For initial data $(x_0,t_0)$,
--   let $I_{\max}(x_0,t_0)$ be the union of all open convex domains of solutions
--   with these initial data, and let $\alpha_{x_0,t_0}$ be their compatible curve.
--   A solution $S$ has such a domain $I_S$, a curve $\alpha_S$, and
--   $\alpha_S(t_0)=x_0$.
--
--   Let $\mathcal L(X,X)$ be the continuous linear operators on $X$ and set
--   $$A(x)=dF_x,\qquad \widetilde F(x,J)=(F(x),A(x)\circ J).$$
--
--   For a fixed initial time $t_0$, put
--   $$\mathcal D_{t_0}=\{(x,t):t\in I_{\max}(x,t_0)\},\qquad
--   \Phi_{t_0}(x,t)=\alpha_{x,t_0}(t),\qquad
--   J_{x,t_0}(t)=d_x\Phi_{t_0}(x,t).$$
--
--   Write $\lambda_x=d\mathcal C_x:X\to\mathbb R$ for the constraint differential.
--
--   For $x=(p,s,a,b,c)$, define
--   $$H(x)=(abc)^{2/3},\quad w(x)=abc(1+4H(x)),\quad
--   \delta(x)=2K-3S,\quad \bar\delta(x)=\frac{2(K+4H(x))}{1+4H(x)},$$
--   $$V(x,t_0,t)=\frac{w(x)\det J_{x,t_0}(t)}{w(\alpha_{x,t_0}(t))}.$$
--   Write $[L]$ for the matrix of a continuous linear operator $L:X\to X$
--   in the standard basis. Set $\Omega(v_0,\ldots,v_4)=\det(v_0,\ldots,v_4)$,
--   $$\omega_x(v_0,\ldots,v_3)=\frac{\Omega(x/2,v_0,\ldots,v_3)}{w(x)},\qquad
--   \varphi_x(v_0,v_1,v_2)=\omega_x(F(x),v_0,v_1,v_2).$$
--
--   A normalized symmetry is a continuous linear equivalence $L:X\to X$ satisfying
--   $$\mathcal C(Lx)=\mathcal C(x),\quad Lx\in W\ \Longleftrightarrow\ x\in W,
--   \quad F(Lx)=LF(x),\quad w(Lx)=w(x),\quad\det L=1.$$
--   These symmetries include the identity, composition, inverse, and the two maps
--   $$R(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a),\qquad
--   S_0(p,s,a,b,c)=(p,-s,a,c,b).$$
--   Transforming a solution replaces its curve $\alpha$ by $L\alpha$ and
--   keeps its time domain.
--
--   Write $\Phi^s_t(x)=\alpha_{x,s}(t)$, with domain $I(x,s)$, and
--   $\mathcal X=\{x:\mathcal C(x)=1,\ N_i(x)>0\ (i=1,2,3)\}$.
--   For $y=(v,l,r)\in\mathbb R^3$ and a wall height $h$, put
--   $$b=e^{-l},\quad c=e^{-r},\quad d=1-v^2-K(h,b,c),\quad
--   U_h=\{y:d>0\},\quad c_h(y)=(-\sqrt d,v,h,b,c).$$
--   For a normalized axis symmetry $A$, the chart is $c_{A,h}=A^{-1}c_h$,
--   with coordinates $\pi_A(x)=((Ax)_1,-\log (Ax)_3,-\log (Ax)_4)$.
--   At $p=-\sqrt d$ its flux density and measure are
--   $$\rho_h(y)=\frac{p^2+v^2-2p}{2|p|(1+4(hbc)^{2/3})},
--   \qquad d\mu_h={\bf1}_{U_h}\rho_h^+\,dy.$$
--   Write $\varphi$ for the signed section flux and $\bar\delta$ for the
--   corrected divergence. The three primary frames interchange axis zero
--   with the chosen dominant axis.
--
--   In wall coordinates $y=(v,l,r)$ put $u=e^{-l}$, $w=e^{-r}$,
--   $M=\max(u,w)$, $S_d^\circ=\{|v|,M<d\}$, and let $S_d$ use weak
--   inequalities. Put $R=|v|$ when $M\le\epsilon|v|$ and $R=M$ otherwise.
--   For $a=a_j=d2^{-j-1}$ and $a<\rho<2a$, $\rho<d$, there are four
--   charts $L_k$ with domains $D_{kj}$. The two shear charts send
--   $(\rho,u,w)$ to $(\pm\rho,-\log u,-\log w)$ for $u,w>0$,
--   $M\le\epsilon\rho$. The angular chart sends $(\rho,\theta,\zeta)$
--   to $(\theta\rho,-\log\rho,-\log\zeta)$, with $|\theta|<L=1/\epsilon$,
--   $|\theta|\rho<d$ and $0<\zeta\le\rho$. Its reflected chart composes
--   with $(v,l,r)\mapsto(-v,r,l)$ and has $\zeta<\rho$.
--
--   The actual return follows the initial trajectory, the partial core flight
--   and the connection to the next entrance. Its elapsed time and its phase
--   and two wall coordinates depend on the label and initial radius. At
--   scale $a$, the angular budget is $51200(L+1)\zeta/a^3$ and the shear
--   budget is $800uw/a^4$. The reference transports and extended curves
--   describe the radius dependence of these returns.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FinCases
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_ConnectionPhysicalReturn
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_BianchiIX_EraCodingData
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable

section

noncomputable section

namespace BianchiIX

def restartReferenceRoot (n : ℝ) : ℝ := Real.sqrt (1 - n ^ 2)

def restartShearFactor (n : ℝ) : ℝ := 3 / (2 + restartReferenceRoot n)

def restartWallFactor (n : ℝ) : ℝ :=
  9 * (1 + restartReferenceRoot n) / (2 * (2 + restartReferenceRoot n) ^ 2)

def restartShearCoupling (n : ℝ) : ℝ :=
  3 * Real.sqrt 3 * n / (2 + restartReferenceRoot n) ^ 2

def restartReferenceStrongRate (n : ℝ) : ℝ := n ^ 2 - 1 - 2 * restartReferenceRoot n

def restartReferenceWallRate (n : ℝ) : ℝ := n ^ 2 - 1 + restartReferenceRoot n

/-- The square of the transported radial phase, before the normalization by three. -/
def restartQuadratic (n s v : ℝ) : ℝ :=
  (restartShearFactor n * s + restartShearCoupling n * v) ^ 2 +
    (restartWallFactor n * v) ^ 2

def restartQuadraticStrongDerivative (n s v : ℝ) : ℝ :=
  2 * (restartShearFactor n * s + restartShearCoupling n * v) *
      (deriv restartShearFactor n * s + deriv restartShearCoupling n * v) +
    2 * restartWallFactor n * deriv restartWallFactor n * v ^ 2

def restartRotationDefect (n s v : ℝ) : ℝ :=
  restartShearFactor n * restartShearCoupling n * (s ^ 2 - v ^ 2) +
    (restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - restartShearFactor n ^ 2) * s * v





























end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

abbrev RestartCenterState := Fin 3 → ℝ

def restartCenterTransfer (n : ℝ) : RestartCenterState →L[ℝ] RestartCenterState :=
  let p : Fin 3 → (RestartCenterState →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
  ContinuousLinearMap.pi ![
    restartShearFactor n • p 0 + restartShearCoupling n • (p 1 - p 2),
    restartWallFactor n • p 1, restartWallFactor n • p 2]











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartReferenceInitial (h : ℝ) : NormalizedState := ![-restartReferenceRoot h, 0, h, 0, 0]

def restartReferenceCurve (h t : ℝ) : NormalizedState := normalizedMaxCurve (restartReferenceInitial h) 0 t

























end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

/-- Exchange the weak walls in logarithmic section coordinates. -/
def mainWallReflection (y : SectionCoordinates) : SectionCoordinates := ![-y 0, y 2, y 1]

@[simp] theorem mainWallReflection_twice (y : SectionCoordinates) :
    mainWallReflection (mainWallReflection y) = y := by
  ext i
  fin_cases i <;> simp [mainWallReflection]

def mainWallReflectionLinear : SectionCoordinates →ₗ[ℝ] SectionCoordinates where
  toFun := mainWallReflection
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mainWallReflection]
    ring
  map_smul' r x := by
    ext i
    fin_cases i <;> simp [mainWallReflection]

def mainWallReflectionEquiv : SectionCoordinates ≃L[ℝ] SectionCoordinates :=
  ({ mainWallReflectionLinear with
    invFun := mainWallReflection
    left_inv := mainWallReflection_twice
    right_inv := mainWallReflection_twice } : SectionCoordinates ≃ₗ[ℝ] SectionCoordinates).toContinuousLinearEquiv















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartCenterProjection : NormalizedState →L[ℝ] RestartCenterState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 3,
    ContinuousLinearMap.proj 4]

def restartSectionRadicand (h : ℝ) (Z : RestartCenterState) : ℝ :=
  1 - Z 0 ^ 2 - curvature h (Z 1) (Z 2)

/-- Ordinary center coordinates on the fixed strong-wall section, including zero weak walls. -/
def restartSectionChart (h : ℝ) (Z : RestartCenterState) : NormalizedState :=
  ![-Real.sqrt (restartSectionRadicand h Z), Z 0, h, Z 1, Z 2]











def restartSectionCenterFlow (h t : ℝ) (Z : RestartCenterState) : RestartCenterState :=
  restartCenterProjection (normalizedMaxCurve (restartSectionChart h Z) 0 t)

def restartReferenceCenterDifferential (h t : ℝ) : RestartCenterState →L[ℝ] RestartCenterState :=
  restartCenterProjection.comp ((normalizedFlowDifferential (restartReferenceInitial h) 0 t).comp
    (fderiv ℝ (restartSectionChart h) 0))











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def partialCoreReturnTime (y : ProjectiveState) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
    projectiveOriginalFlow y 0 t 2 = 1}

def partialCoreReturnState (y : ProjectiveState) : CoreAngleState :=
  toCoreAngleState (projectiveOriginalFlow y 0 (partialCoreReturnTime y))









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartRadialCurve (θ ζ ρ : ℝ) : RestartCenterState := ![θ * ρ, ρ, ζ]

def restartRadialDirection (θ : ℝ) : RestartCenterState := ![θ, 1, 0]











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartShearCurve (σ n₂ n₃ ρ : ℝ) : RestartCenterState := ![σ * ρ, n₂, n₃]

def restartShearDirection (σ : ℝ) : RestartCenterState := ![σ, 0, 0]











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartShearFluxDensity (h n₂ n₃ ρ : ℝ) : ℝ :=
  correctedSectionFluxDensity (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ) 0) ρ h n₂ n₃









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartFastShearHeight (h T σ n₂ n₃ ρ : ℝ) : ℝ :=
  1 + normalizedMaxCurve (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 T 0

def restartFastShearProjectiveEntry (h T σ n₂ n₃ ρ : ℝ) : ProjectiveState :=
  toProjectiveState (normalizedMaxCurve (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 T)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartFastProjectiveEntry (h T θ ζ ρ : ℝ) : ProjectiveState :=
  toProjectiveState (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T)

def restartFastCoreAngle (h T θ ζ ρ : ℝ) : ℝ :=
  coreAngle (restartFastProjectiveEntry h T θ ζ ρ 0) (restartFastProjectiveEntry h T θ ζ ρ 2)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- The positive-shear restart uses one fixed downward event, also across the incoming boundary. -/
def restartShearReturnParameters (h s n₂ n₃ ρ : ℝ) : ConnectionParameters :=
  coreExitConnectionParameters (partialCoreDownwardReturnState (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ))

def restartShearReturnState (h s n₂ n₃ ρ : ℝ) : CoreAngleState :=
  connectionReturnPhysicalState (restartShearReturnParameters h s n₂ n₃ ρ)

def restartShearReturnPhase (h s n₂ n₃ ρ : ℝ) : ℝ := 2 / restartShearReturnState h s n₂ n₃ ρ 0

def restartShearReturnTime (h s n₂ n₃ ρ : ℝ) : ℝ :=
  s + partialCoreDownwardReturnTime (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ) +
    connectionReturnTime (restartShearReturnParameters h s n₂ n₃ ρ)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartReturnParameters (h s θ ζ ρ : ℝ) : ConnectionParameters :=
  coreExitConnectionParameters (partialCoreReturnState (restartFastProjectiveEntry h s θ ζ ρ))

def restartReturnState (h s θ ζ ρ : ℝ) : CoreAngleState :=
  connectionReturnPhysicalState (restartReturnParameters h s θ ζ ρ)

def restartReturnPhase (h s θ ζ ρ : ℝ) : ℝ := 2 / restartReturnState h s θ ζ ρ 0

def restartReturnTime (h s θ ζ ρ : ℝ) : ℝ :=
  s + partialCoreReturnTime (restartFastProjectiveEntry h s θ ζ ρ) +
    connectionReturnTime (restartReturnParameters h s θ ζ ρ)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartAmplitudeExtension (h s θ ζ r : ℝ) (i : Fin 3) : ℝ → ℝ :=
  radiusAmplitudeExtension (fun a => restartReturnState h s θ ζ a 0)
    (fun a => restartReturnState h s θ ζ a i) r (2 * r)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartLabelSet (L r P : ℝ) : Set (ℝ × ℝ) :=
  {z | |z.1| ≤ L ∧ 0 < z.2 ∧ z.2 ≤ r ^ P}







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartShearAmplitudeExtension (h s n₂ n₃ a : ℝ) (i : Fin 3) : ℝ → ℝ :=
  radiusAmplitudeExtension (fun r => restartShearReturnState h s n₂ n₃ r 0)
    (fun r => restartShearReturnState h s n₂ n₃ r i) a (2 * a)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartShearCommonLabelSet (ε a P : ℝ) : Set (ℝ × ℝ) :=
  {z | (0 < z.1 ∧ z.1 ≤ 2 * ε * a) ∧ (0 < z.2 ∧ z.2 ≤ 2 * ε * a) ∧ min z.1 z.2 ≤ a ^ P}





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartEraCurve (h s θ ζ r : ℝ) : EraCurve :=
  ⟨restartAmplitudeExtension h s θ ζ r 1, restartAmplitudeExtension h s θ ζ r 2⟩

def restartAmplitudeBudget (L r ζ : ℝ) : ℝ := 6400 * (8 * (L + 1)) * ζ / r ^ 3



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartShearEraCurve (h s n₂ n₃ a : ℝ) : EraCurve :=
  ⟨restartShearAmplitudeExtension h s n₂ n₃ a 1, restartShearAmplitudeExtension h s n₂ n₃ a 2⟩

def restartShearAmplitudeBudget (a n₂ n₃ : ℝ) : ℝ := 800 * n₂ * n₃ / a ^ 4



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def eraRadialFailure (η : ℝ) (J : ℕ) (σ B Bcap a b : ℝ) (Y : ℝ → CoreAngleState) : Set ℝ :=
  Icc a b \ (fun ρ => (B, Y ρ)) ⁻¹' EraSurvivor.typicalDomain η J σ Bcap





end BianchiIX

end
end


