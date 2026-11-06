-- Prove2me | Definitions.Def_BianchiIX_GeometricExceptionData
-- name    : BianchiIX_GeometricExceptionData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-06T04:04:00.247056+00:00
-- url     : https://prove2.me/theorems/55c8dcba-eeeb-4234-93a5-dfae264cfb80
-- title:
--   Taub avoidance, compact entrances and the geometric exceptional set
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
--   Write $x_t=\Phi^0_t(x)$, $d_T(x)=\min_i|x-T_i|_2$ for the distance to
--   the three Taub points, and $V_\epsilon(x)$ for $d_T(x_t)\ge\epsilon$
--   at every existing $t\ge0$. Write $D_\Delta(x)$ if $4N_iN_j\le\Delta^2$
--   for all distinct walls, and $u_i$ for their logarithmic rates:
--   $\dot N_i=u_iN_i$. In the primary frame put $r_T^2=s^2+(b-c)^2$.
--
--   For a projective state put $r(y)=\sqrt{(y_0-1)^2+y_2^2}$.
--   The reference entrance is $e(k,v)=(1+\sqrt{k^2-v^2},0,v,0)$;
--   $f(K)=\sqrt3/(4+(1+K)^2)$. Write $g(x)=(\Pi x)_2$ for the active
--   wall, $\Xi$ for the inverse projective chart, and $E(x)$ for the first
--   entrance data (return time, projective endpoint, normalized endpoint,
--   radius). For core coordinates $Y$ write $x(Y)=\Xi(e_+(Y))$,
--   $b(Y)=Y_1+Y_2$, and let $K_{N,\gamma}$ be the range
--   $2+2\gamma\le Y_0\le2N$, $\gamma\le Y_0/2-\lfloor Y_0/2\rfloor\le1-\gamma$.
--
--   The single-wall projection retains the primary wall and rescales the two
--   shears to the constraint circle at that height. The geometric exception
--   consists of physical points in one of the Taub subspaces or eventually
--   separated from every Taub point by a fixed positive distance.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_BianchiIX_Dynamics_Normalized
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
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Mathlib.LinearAlgebra.Alternating.Curry
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_EraCodingData
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.ByContra
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Algebra.Order.Archimedean.Basic

section

noncomputable section

namespace BianchiIX

/-- The radial shear factor preserving the height of the first wall. -/
def singleWallProjectionScale (p s n : ℝ) : ℝ :=
  Real.sqrt ((1 - n ^ 2) / shearSq p s)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

/-- The squared bounds corresponding to `2 * sqrt (N_i * N_j) <= Delta`. -/
def normalizedWallProductsBound (Δ : ℝ) (x : NormalizedState) : Prop :=
  4 * x 2 * x 3 ≤ Δ ^ 2 ∧ 4 * x 3 * x 4 ≤ Δ ^ 2 ∧ 4 * x 4 * x 2 ≤ Δ ^ 2







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def wallGrowthMargin (x : NormalizedState) : ℝ :=
  max (min (wallRate 0 x) (min (-wallRate 1 x) (-wallRate 2 x)))
    (max (min (wallRate 1 x) (min (-wallRate 0 x) (-wallRate 2 x)))
      (min (wallRate 2 x) (min (-wallRate 0 x) (-wallRate 1 x))))









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def singleWallProjection (x : NormalizedState) : NormalizedState :=
  ![singleWallProjectionScale (x 0) (x 1) (x 2) * x 0,
    singleWallProjectionScale (x 0) (x 1) (x 2) * x 1, x 2, 0, 0]





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def referenceEntranceState (k v : ℝ) : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - v ^ 2), 0, v, 0]









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

/-- Order the stable axes so that the single-wall reference radius is at least two. -/
def singleWallFrame (x : NormalizedState) : Fin 6 := if 0 ≤ x 1 then 2 else 4











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Time, projective endpoint, physical endpoint, and radius in ordinary physical initial coordinates. -/
def physicalEntranceData (x : NormalizedState) : ℝ × ProjectiveState × NormalizedState × ℝ :=
  let y := toProjectiveState x
  let P := entranceReturnState y
  (entranceReturnTime y, P, fromProjectiveState P, coreRadius (P 0) (P 2))









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def referenceCoreWallFloor (K : ℝ) : ℝ := Real.sqrt 3 / (4 + (1 + K) ^ 2)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def normalizedWallMaximum (x : NormalizedState) : ℝ := max (x 2) (max (x 3) (x 4))





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def normalizedCoreCoordinates (x : NormalizedState) : SectionCoordinates :=
  coreSectionCoordinates (toProjectiveState x)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def transverseCoreHittingDomain (C : SectionCoordinates → NormalizedState) (t₀ : ℝ)
    (Z : Set SectionCoordinates) : Set SectionCoordinates :=
  {y | ∃ t, t ∈ normalizedMaxDomain (C y) t₀ ∧
    projectiveActiveWall (normalizedMaxCurve (C y) t₀ t) = 1 ∧
    normalizedEventRate projectiveActiveWall (C y) t₀ t ≠ 0 ∧
    normalizedCoreCoordinates (normalizedMaxCurve (C y) t₀ t) ∈ Z}





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def compactEraPhase (N : ℕ) (γ : ℝ) : Set CoreAngleState :=
  {X | 2 + 2 * γ ≤ X 0 ∧ X 0 ≤ 2 * N ∧
    X 0 / 2 - (⌊X 0 / 2⌋₊ : ℝ) ∈ Icc γ (1 - γ)}









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace EraSurvivor

def boundedDigitDomain (η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set (ℝ × CoreAngleState) :=
  Subtype.val '' {p : eraSurvivorDomain η J σ Bcap | ∃ N : ℕ, ∀ n, (digits p n : ℕ) ≤ N}



def curveBoundedDigits (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B Bcap : ℝ) : Set ℝ :=
  Ioo 0 1 ∩ (fun x => (B, Γ.state (2 / x))) ⁻¹' boundedDigitDomain η J σ Bcap

end EraSurvivor

namespace EraCurve.Realization



end EraCurve.Realization



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The positive-wall core coordinates with a bounded actual survivor code. -/
def coreBoundedDigits (η : ℝ) (J : ℕ) (σ B Bcap : ℝ) : Set CoreAngleState :=
  {q | q 0 ∈ Ioo (0 : ℝ) 1 ∧ 0 < q 1 ∧ 0 < q 2 ∧ q 1 + q 2 ≤ B ∧
    (B, ![2 / q 0, q 1, q 2]) ∈ EraSurvivor.boundedDigitDomain η J σ Bcap}







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

/-- Compactness is required only at the end of each finite selected history that already exists. -/
def compactEraHistories (η : ℝ) (J : ℕ) (σ Bcap : ℝ) (N : ℕ) (γ : ℝ)
    (p : ℝ × CoreAngleState) : Prop :=
  ∀ w : List ℕ+, p ∈ eraPrefixDomain η J σ Bcap w →
    (eraPrefixState η J w p).2 ∈ compactEraPhase N γ









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def curveCompactEraHistories (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B Bcap : ℝ) (N : ℕ) (γ : ℝ) : Set ℝ :=
  {x | x ∈ Ioo (0 : ℝ) 1 ∧ compactEraHistories η J σ Bcap N γ (B, Γ.state (2 / x))}

def coreCompactEraHistories (η : ℝ) (J : ℕ) (σ B Bcap : ℝ) (N : ℕ) (γ : ℝ) : Set CoreAngleState :=
  {q | q 0 ∈ Ioo (0 : ℝ) 1 ∧ 0 < q 1 ∧ 0 < q 2 ∧ q 1 + q 2 ≤ B ∧
    compactEraHistories η J σ Bcap N γ (B, ![2 / q 0, q 1, q 2])}







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Core-curve parameters whose exact future orbit avoids every Taub point by a fixed distance. -/
def curveTaubAvoidance (Γ : EraCurve) (ε : ℝ) : Set ℝ :=
  {x | x ∈ Ioo (0 : ℝ) 1 ∧
    normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry (Γ.state (2 / x))))}

/-- Small positive-wall core coordinates with uniform physical Taub avoidance. -/
def coreTaubAvoidance (ε B : ℝ) : Set CoreAngleState :=
  {q | q 0 ∈ Ioo (0 : ℝ) 1 ∧ 0 < q 1 ∧ 0 < q 2 ∧ q 1 + q 2 ≤ B ∧
    normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry ![2 / q 0, q 1, q 2]))}



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def EventuallyTaubSeparated (x : NormalizedState) : Prop :=
  ∃ ε > (0 : ℝ), ∀ᶠ t in atTop, ∀ i : Fin 3,
    ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

def corePhaseSectionCoordinates (q : SectionCoordinates) : SectionCoordinates :=
  coreSectionCoordinates (coreRadiusEntry ![2 / q 0, q 1, q 2])











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def geometricException : Set NormalizedState :=
  {x | x ∈ physicalPhaseSpace ∧ (x ∈ taubSubspaces ∨ EventuallyTaubSeparated x)}











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology







def corePhasePhysicalState (q : CoreAngleState) : NormalizedState :=
  fromProjectiveState (coreRadiusEntry ![2 / q 0, q 1, q 2])







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def mainWallSmallSection (d : ℝ) : Set SectionCoordinates :=
  {z | |z 0| ≤ d ∧ max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ d}







end BianchiIX

end
end


