-- Prove2me | Definitions.Def_BianchiIX_RadialFailureData
-- name    : BianchiIX_RadialFailureData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-06T04:04:42.47521+00:00
-- url     : https://prove2.me/theorems/f8be31d9-17f1-4ae1-90a2-197b21a4eaab
-- title:
--   Dyadic radial pieces and exceptional sets on the physical section
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
--   The selected angular labels satisfy $|\theta|\le L$, $0<\zeta\le a^P$;
--   their budget is $51200(L+1)\zeta/a^3$. The shear labels have
--   $0<u,w\le2\epsilon a$, $\min(u,w)\le a^P$, with budget $800uw/a^4$.
--   Order the shear label as $(w,u)$ on the negative branch and $(u,w)$
--   on the positive one. Write $s_j=(q/2)\log(1/a_j)$. Let $F_{kj}$
--   contain points with $\rho\in[a,2a]$ whose label is unselected or whose
--   budget and actual restart core at $(h,s_j)$ lie outside the typical
--   survivor domain for $(\eta,J,\sigma,B_{\rm cap})$. The section failure
--   is $F=H\cup\bigcup_{kj}L_k(D_{kj}\cap F_{kj})$, where
--   $H=S_d^\circ\cap\bigcup_j\{R=2a_j\}$. The comparison regions
--   $A(B_A),S(B_S)$ consist of the corresponding dyadic unions of the
--   symmetrized selected failure layers at those caps and the unselected layers.
--
--   The original flux on $U_h$ has density $[(p^2+v^2-2p)/(2|p|)]^+$.
--   The closed-section failure adds $S_d\setminus S_d^\circ$ to the
--   given exception. The inverse radial charts recover the labels and
--   radius used to select the restart time, budget and core; the frame
--   index is zero on the reflected branch and three on the other.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Definitions.Def_BianchiIX_SectionRestartData
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_EraCodingData
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
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
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_BianchiIX_PhysicalEraData
import Definitions.Def_BianchiIX_GeometricExceptionData

section

noncomputable section

namespace BianchiIX

open MeasureTheory
open scoped Topology ENNReal

def dyadicScale (d : ℝ) (j : ℕ) : ℝ := d * (1 / 2 : ℝ) ^ (j + 1)





















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def scaledAngularLogCoordinates (a : ℝ) (z : SectionCoordinates) : SectionCoordinates :=
  ![z 1 * z 0, -Real.log (z 0), -Real.log (2 * a * z 2)]

def scaledAngularLogDifferential (z : SectionCoordinates) : SectionCoordinates →L[ℝ] SectionCoordinates :=
  ContinuousLinearMap.pi ![z 1 • ContinuousLinearMap.proj 0 + z 0 • ContinuousLinearMap.proj 1,
    (-(z 0)⁻¹) • ContinuousLinearMap.proj 0, (-(z 2)⁻¹) • ContinuousLinearMap.proj 2]









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal





def mainWallSymmetrization (A : Set SectionCoordinates) : Set SectionCoordinates :=
  A ∪ mainWallReflection '' A







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def mainWallOriginalDensity (h : ℝ) (z : SectionCoordinates) : ℝ :=
  sectionFluxDensity (mainWallChart h z 0) (z 0)

/-- The unmodified section flux in logarithmic wall coordinates. -/
def mainWallOriginalMeasure (h : ℝ) : Measure SectionCoordinates :=
  (volume.restrict (mainWallChartDomain h)).withDensity
    (fun z => ENNReal.ofReal (mainWallOriginalDensity h z))



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal







def signedShearLogCoordinates (σ : ℝ) (z : SectionCoordinates) : SectionCoordinates :=
  ![σ * z 0, -Real.log (z 1), -Real.log (z 2)]

def signedShearLogDifferential (σ : ℝ) (z : SectionCoordinates) :
    SectionCoordinates →L[ℝ] SectionCoordinates :=
  ContinuousLinearMap.pi ![σ • ContinuousLinearMap.proj 0,
    (-(z 1)⁻¹) • ContinuousLinearMap.proj 1, (-(z 2)⁻¹) • ContinuousLinearMap.proj 2]









/-- The two orders give respectively (s,N2,N3) = (theta*r,r,zeta) and (-theta*r,zeta,r). -/
def orderedAngularLogCoordinates (otherWall : Bool) (z : SectionCoordinates) : SectionCoordinates :=
  if otherWall then mainWallReflection (scaledAngularLogCoordinates (1 / 2) z)
    else scaledAngularLogCoordinates (1 / 2) z





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def shearRadialInterval (a d ε n₂ n₃ : ℝ) : Set ℝ :=
  Ioo a (2 * a) ∩ {r | max n₂ n₃ ≤ ε * r ∧ r < d}

def angularRadialInterval (otherWall : Bool) (a d θ ζ : ℝ) : Set ℝ :=
  Ioo a (2 * a) ∩ {r | (if otherWall then ζ < r else ζ ≤ r) ∧ r < d ∧ |θ| * r < d}









def shearRadialDomain (a d ε : ℝ) : Set SectionCoordinates :=
  {z | 0 < z 1 ∧ 0 < z 2 ∧ z 0 ∈ shearRadialInterval a d ε (z 1) (z 2)}

def angularRadialDomain (otherWall : Bool) (a d L : ℝ) : Set SectionCoordinates :=
  {z | |z 1| < L ∧ 0 < z 2 ∧ z 0 ∈ angularRadialInterval otherWall a d (z 1) (z 2)}





















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def mainWallOpenSection (d : ℝ) : Set SectionCoordinates :=
  {z | |z 0| < d ∧ max (Real.exp (-z 1)) (Real.exp (-z 2)) < d}

def mainWallRadialRadius (ε : ℝ) (z : SectionCoordinates) : ℝ :=
  if max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ ε * |z 0| then |z 0|
    else max (Real.exp (-z 1)) (Real.exp (-z 2))

/-- The two summands distinguish shear signs and angular wall orders. -/
abbrev RadialPieceIndex := (Bool ⊕ Bool) × ℕ

def radialPieceMap (k : Bool ⊕ Bool) : SectionCoordinates → SectionCoordinates :=
  match k with
  | Sum.inl neg => signedShearLogCoordinates (if neg then -1 else 1)
  | Sum.inr other => orderedAngularLogCoordinates other

def radialPieceDomain (d ε : ℝ) (i : RadialPieceIndex) : Set SectionCoordinates :=
  match i.1 with
  | Sum.inl _ => shearRadialDomain (dyadicScale d i.2) d ε
  | Sum.inr other => angularRadialDomain other (dyadicScale d i.2) d (1 / ε)

def physicalRadialPiece (d ε : ℝ) (i : RadialPieceIndex) : Set SectionCoordinates :=
  radialPieceMap i.1 '' radialPieceDomain d ε i

def radialPieceInverse (k : Bool ⊕ Bool) (z : SectionCoordinates) : SectionCoordinates :=
  match k with
  | Sum.inl neg => ![(if neg then -1 else 1) * z 0, Real.exp (-z 1), Real.exp (-z 2)]
  | Sum.inr false => ![Real.exp (-z 1), z 0 / Real.exp (-z 1), Real.exp (-z 2)]
  | Sum.inr true => ![Real.exp (-z 2), -z 0 / Real.exp (-z 2), Real.exp (-z 1)]































end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def mainWallRadialBoundary (d ε : ℝ) : Set SectionCoordinates :=
  mainWallOpenSection d ∩ ⋃ j : ℕ, {z | mainWallRadialRadius ε z = 2 * dyadicScale d j}



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def radialFailurePiece (d ε : ℝ) (F : RadialPieceIndex → Set SectionCoordinates)
    (i : RadialPieceIndex) : Set SectionCoordinates :=
  radialPieceMap i.1 '' (radialPieceDomain d ε i ∩ F i)

def radialFailureSet (d ε : ℝ) (F : RadialPieceIndex → Set SectionCoordinates) : Set SectionCoordinates :=
  mainWallRadialBoundary d ε ∪ ⋃ i : RadialPieceIndex, radialFailurePiece d ε F i

def radialFailureIntegral (h d ε : ℝ) (F : RadialPieceIndex → Set SectionCoordinates)
    (i : RadialPieceIndex) : ℝ≥0∞ :=
  match i.1 with
  | Sum.inl neg =>
      ∫⁻ n₂ : ℝ, ∫⁻ n₃ : ℝ, ENNReal.ofReal (1 / (n₂ * n₃)) *
        ∫⁻ r in {r : ℝ | 0 < n₂ ∧ 0 < n₃ ∧
          r ∈ shearRadialInterval (dyadicScale d i.2) d ε n₂ n₃ ∧ ![r, n₂, n₃] ∈ F i},
          ENNReal.ofReal (mainWallOriginalDensity h
            (signedShearLogCoordinates (if neg then -1 else 1) ![r, n₂, n₃]))
  | Sum.inr other =>
      ∫⁻ θ : ℝ, ∫⁻ ζ : ℝ, ENNReal.ofReal (1 / ζ) *
        ∫⁻ r in {r : ℝ | |θ| < 1 / ε ∧ 0 < ζ ∧
          r ∈ angularRadialInterval other (dyadicScale d i.2) d θ ζ ∧ ![r, θ, ζ] ∈ F i},
          ENNReal.ofReal (mainWallOriginalDensity h (orderedAngularLogCoordinates other ![r, θ, ζ]))















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def scaledShearLogCoordinates (a : ℝ) (z : SectionCoordinates) : SectionCoordinates :=
  ![z 0, -Real.log (a * z 1), -Real.log (a * z 2)]

def scaledShearLogDifferential (z : SectionCoordinates) : SectionCoordinates →L[ℝ] SectionCoordinates :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0,
    (-(z 1)⁻¹) • ContinuousLinearMap.proj 1, (-(z 2)⁻¹) • ContinuousLinearMap.proj 2]











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def shearSectionLayer (a ε : ℝ) : Set SectionCoordinates :=
  {z | |z 0| ∈ Icc a (2 * a) ∧ Real.exp (-z 1) ≤ 2 * ε * a ∧ Real.exp (-z 2) ≤ 2 * ε * a}

def shearUnselectedSection (a ε P : ℝ) : Set SectionCoordinates :=
  {z ∈ shearSectionLayer a ε | a ^ P < Real.exp (-z 1) ∧ a ^ P < Real.exp (-z 2)}













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def angularUnselectedSection (a L P : ℝ) : Set SectionCoordinates :=
  {z | max (Real.exp (-z 1)) (Real.exp (-z 2)) ∈ Icc a (2 * a) ∧
    |z 0| ≤ L * max (Real.exp (-z 1)) (Real.exp (-z 2)) ∧
    a ^ P < min (Real.exp (-z 1)) (Real.exp (-z 2))}

def angularLogBox (a L P : ℝ) : Set SectionCoordinates :=
  Icc ![-2 * L * a, -Real.log (2 * a), 0] ![2 * L * a, -Real.log a, P * |Real.log a|]

def angularLogBoxSwapped (a L P : ℝ) : Set SectionCoordinates :=
  Icc ![-2 * L * a, 0, -Real.log (2 * a)] ![2 * L * a, P * |Real.log a|, -Real.log a]









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def labelRadialFailure (a : ℝ) (L : Set (ℝ × ℝ)) (G : Set (ℝ × CoreAngleState))
    (Z : (ℝ × ℝ) → ℝ → ℝ × CoreAngleState) : Set SectionCoordinates :=
  {z | z 0 ∈ Icc a (2 * a) ∧ ((z 1, z 2) ∉ L ∨ Z (z 1, z 2) (z 0) ∉ G)}



def restartRadialFailureFamily (h q d ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ)
    (i : RadialPieceIndex) : Set SectionCoordinates :=
  let a := dyadicScale d i.2
  let s := q / 2 * Real.log (1 / a)
  let G := EraSurvivor.typicalDomain η J σ Bcap
  match i.1 with
  | Sum.inl neg =>
      let F := labelRadialFailure a (restartShearCommonLabelSet ε a P) G
        (fun l r => (restartShearAmplitudeBudget a l.1 l.2, restartShearReturnState h s l.1 l.2 r))
      if neg then (fun z => ![z 0, z 2, z 1]) ⁻¹' F else F
  | Sum.inr _ =>
      labelRadialFailure a (restartLabelSet (1 / ε) a P) G
        (fun l r => (restartAmplitudeBudget (1 / ε) a l.2, restartReturnState h s l.1 l.2 r))

def restartRadialOutput (h q d ε : ℝ) (i : RadialPieceIndex) (z : SectionCoordinates) : ℝ × CoreAngleState :=
  let a := dyadicScale d i.2
  let s := q / 2 * Real.log (1 / a)
  match i.1 with
  | Sum.inl neg =>
      let l := if neg then (z 2, z 1) else (z 1, z 2)
      (restartShearAmplitudeBudget a l.1 l.2, restartShearReturnState h s l.1 l.2 (z 0))
  | Sum.inr _ => (restartAmplitudeBudget (1 / ε) a (z 2), restartReturnState h s (z 1) (z 2) (z 0))







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def restartAngularFailureCoordinates (h s a L P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  {z | z 1 ∈ Icc (-L) L ∧ z 2 ∈ Ioo (0 : ℝ) 1 ∧
    (z 1, 2 * a * z 2) ∈ restartLabelSet L a P ∧
    z 0 ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a (2 * a * z 2)) Bcap a (2 * a)
      (restartReturnState h s (z 1) (2 * a * z 2))}

def restartAngularFailureSection (h s a L P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  scaledAngularLogCoordinates a '' restartAngularFailureCoordinates h s a L P η J σ Bcap







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def restartShearRadialFlux (h n₂ n₃ : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ ρ in A, ENNReal.ofReal (restartShearFluxDensity h n₂ n₃ ρ)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal Classical

def shearLabelFailureCoordinates (a : ℝ) (L : Set (ℝ × ℝ)) (F : ℝ × ℝ → Set ℝ) :
    Set SectionCoordinates :=
  {z | z 1 ∈ Ioo (0 : ℝ) 1 ∧ z 2 ∈ Ioo (0 : ℝ) 1 ∧
    (a * z 1, a * z 2) ∈ L ∧ z 0 ∈ F (a * z 1, a * z 2)}

def shearLabelFailureSection (a : ℝ) (L : Set (ℝ × ℝ)) (F : ℝ × ℝ → Set ℝ) :
    Set SectionCoordinates := scaledShearLogCoordinates a '' shearLabelFailureCoordinates a L F

def shearLabelFailureLayer (h a : ℝ) (L : Set (ℝ × ℝ)) (F : ℝ × ℝ → Set ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1,
    if (a * x, a * y) ∈ L then
      restartShearRadialFlux h (a * x) (a * y) (F (a * x, a * y)) / ENNReal.ofReal (x * y)
    else 0















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def restartShearFailureFibers (h s a η : ℝ) (J : ℕ) (σ Bcap : ℝ) : ℝ × ℝ → Set ℝ :=
  fun z => eraRadialFailure η J σ (restartShearAmplitudeBudget a z.1 z.2) Bcap a (2 * a)
    (restartShearReturnState h s z.1 z.2)

def restartShearCommonFailureSection (h s a ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  shearLabelFailureSection a (restartShearCommonLabelSet ε a P) (restartShearFailureFibers h s a η J σ Bcap)

def restartShearCommonFailureLayer (h s a ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : ℝ≥0∞ :=
  shearLabelFailureLayer h a (restartShearCommonLabelSet ε a P) (restartShearFailureFibers h s a η J σ Bcap)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def angularFailureRegion (h q d L P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  (⋃ j : ℕ, mainWallSymmetrization (restartAngularFailureSection h
    (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) L P η J σ Bcap)) ∪
  ⋃ j : ℕ, angularUnselectedSection (dyadicScale d j) L P



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def shearFailureRegion (h q d ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  (⋃ j : ℕ, mainWallSymmetrization (restartShearCommonFailureSection h
    (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) ε P η J σ Bcap)) ∪
  ⋃ j : ℕ, shearUnselectedSection (dyadicScale d j) ε P



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def angularRestartParameterDomain (a L P : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  restartLabelSet L a P ×ˢ Icc a (2 * a)

def angularRestartChart (o : Bool) (p : (ℝ × ℝ) × ℝ) : SectionCoordinates :=
  let y : SectionCoordinates := ![p.1.1 * p.2, -Real.log p.2, -Real.log p.1.2]
  if o then mainWallReflection y else y

def angularRestartData (h s a L : ℝ) (o : Bool) (p : (ℝ × ℝ) × ℝ) : CoreRestartData :=
  ((if o then 0 else 3, restartReturnTime h s p.1.1 p.1.2 p.2),
    (restartAmplitudeBudget L a p.1.2, restartReturnState h s p.1.1 p.1.2 p.2))















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def shearRestartParameterDomain (ε a P : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  restartShearCommonLabelSet ε a P ×ˢ Icc a (2 * a)

def shearRestartChart (o : Bool) (p : (ℝ × ℝ) × ℝ) : SectionCoordinates :=
  let y : SectionCoordinates := ![p.2, -Real.log p.1.1, -Real.log p.1.2]
  if o then mainWallReflection y else y

def shearRestartData (h s a : ℝ) (o : Bool) (p : (ℝ × ℝ) × ℝ) : CoreRestartData :=
  ((if o then 0 else 3, restartShearReturnTime h s p.1.1 p.1.2 p.2),
    (restartShearAmplitudeBudget a p.1.1 p.1.2, restartShearReturnState h s p.1.1 p.1.2 p.2))













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def mainWallSectionBoundary (d : ℝ) : Set SectionCoordinates :=
  mainWallSmallSection d \ mainWallOpenSection d

def mainWallClosedFailure (d : ℝ) (E : Set SectionCoordinates) : Set SectionCoordinates :=
  mainWallSectionBoundary d ∪ E





















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def radialRestartParameter (k : Bool ⊕ Bool) (z : SectionCoordinates) : (ℝ × ℝ) × ℝ :=
  match k with
  | Sum.inl neg => ((if neg then (z 2, z 1) else (z 1, z 2)), z 0)
  | Sum.inr _ => ((z 1, z 2), z 0)

def radialRestartParameterDomain (a ε P : ℝ) : Bool ⊕ Bool → Set ((ℝ × ℝ) × ℝ)
  | Sum.inl _ => shearRestartParameterDomain ε a P
  | Sum.inr _ => angularRestartParameterDomain a (1 / ε) P

def radialRestartChart : Bool ⊕ Bool → ((ℝ × ℝ) × ℝ) → SectionCoordinates
  | Sum.inl neg => shearRestartChart neg
  | Sum.inr other => angularRestartChart other

def radialRestartData (h s a ε : ℝ) : Bool ⊕ Bool → ((ℝ × ℝ) × ℝ) → CoreRestartData
  | Sum.inl neg => shearRestartData h s a neg
  | Sum.inr other => angularRestartData h s a (1 / ε) other











end BianchiIX

end
end


