-- Prove2me | Definitions.Def_BianchiIX_AxisSectionMeasureData
-- name    : BianchiIX_AxisSectionMeasureData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-06T03:32:10.627424+00:00
-- url     : https://prove2.me/theorems/e22bd93e-1c7b-4791-905a-6f9b78cee6b0
-- title:
--   Flux measures and first hitting data on labelled wall sections
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
--   For target frames $B_i$, heights $k_i$, and coordinate sets $E_i$ put
--   $c(i,y)=c_{B_i,k_i}(y)$, $E^\sqcup=\{(i,y):y\in E_i\}$ and
--   $\nu_k=\sum_i(y\mapsto(i,y))_*\mu_{k_i}$.
--   A hit from $z=(i,y)$ at time $t$ starts with $y\in U_{k_i}$ at $t_0$,
--   exists in the maximal domain, and reaches a target frame with its first
--   wall at the prescribed height, negative first shear, and coordinates in
--   the corresponding target set. Write $H(z)$ for these times $t>t_0$,
--   and $D_E=\{z\in E^\sqcup:H(z)\ne\varnothing\}$.
--   A wall arrival atlas from $(A,h)$ gives countably many injective $C^1$
--   branches covering each crossing time in each target chart.
--   For a branch $q=(i,n)$ with map $R_q$ and time $\tau_q$, put
--   $$j_q(y)=\rho_{k_i}(R_qy)|\det DR_q(y)|/\rho_h(y).$$
--   Given a time set $I$, an eligible point lies on the branch, has time in
--   $I$ and target in $E_i$. Its delay is $(\tau_q-t_0)^+$ there and
--   $+\infty$ otherwise. The first piece $L_q$ consists of eligible points
--   attaining the infimum of all delays with the least branch encoding.
--
--   The first delay is the infimum over eligible branches, and the first time
--   is the initial time plus the real value of this delay. For general initial
--   data at time zero, global hitting times are all existing times in the
--   given time set with endpoint in a target chart image. The first state is
--   the flow evaluated at the real value of the infimum of the nonnegative
--   extended hitting times. A success target removes the corresponding
--   labelled failure slice. Four-coordinate nullity of $S$ means
--   $\lambda_4(Q(S))=0$ for every differentiable $Q:\mathbb R^5\to\mathbb R^4$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof
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
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_BianchiIX_AxisAndOrbitData
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
import Mathlib.MeasureTheory.Measure.WithDensity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Compactness.Compact

section

/-! Strict expansion on a finite-measure invariant failure set, Section 7.1. -/

open MeasureTheory Set
open scoped ENNReal

namespace BianchiIX

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}



/-- Iterates outside the return domain are excluded, even if a total extension is used. -/
def permanentFailure (R : X → X) (D E : Set X) : Set X :=
  {x | ∀ n : ℕ, R^[n] x ∈ D ∩ E}











end BianchiIX

end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped Topology ENNReal

abbrev FourCoordinates := Fin 4 → ℝ

/-- Nullity after every differentiable four-dimensional coordinate observation. -/
def NullInFourCoordinates (S : Set NormalizedState) : Prop :=
  ∀ P : NormalizedState → FourCoordinates, Differentiable ℝ P → volume (P '' S) = 0















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal





def mainWallMeasure (h : ℝ) : Measure SectionCoordinates :=
  (volume.restrict (mainWallChartDomain h)).withDensity (fun y => ENNReal.ofReal (mainWallChartDensity h y))











namespace MainWallArrival













end MainWallArrival



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

def transverseAxisWallOrbitPreimage (C : SectionCoordinates → NormalizedState)
    (A : NormalizedSymmetry) (h t₀ : ℝ) (Z : Set SectionCoordinates) : Set SectionCoordinates :=
  {y | ∃ t ∈ normalizedMaxDomain (C y) t₀, ∃ z ∈ Z,
    axisWallChart A h z = normalizedMaxCurve (C y) t₀ t}





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The sum of the verified coordinate flux measures on labelled section charts. -/
def axisFamilyMeasure {ι : Type*} [MeasurableSpace ι] (k : ι → ℝ) : Measure (ι × SectionCoordinates) :=
  Measure.sum (fun i => (mainWallMeasure (k i)).map (Prod.mk i))











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace AxisWallArrival

variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

def eligible (E : Set SectionCoordinates) (I : Set ℝ) : Set SectionCoordinates :=
  {y | y ∈ P.source ∧ P.coordinateTime y ∈ I ∧ P.map y ∈ E}



def delay (E : Set SectionCoordinates) (I : Set ℝ) : SectionCoordinates → ℝ≥0∞ := by
  classical
  exact (P.eligible E I).piecewise (fun y => ENNReal.ofReal (P.coordinateTime y - t₀)) (fun _ => ∞)







end AxisWallArrival

/-- Actual target hits; labels may overlap and are not identified with disjoint physical sections. -/
def axisFamilyHittingTimes {ι : Type*} (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry)
    (h : ℝ) (k : ι → ℝ) (t₀ : ℝ) (E : ι → Set SectionCoordinates) (I : Set ℝ)
    (y : SectionCoordinates) : Set ℝ :=
  {t | t ∈ I ∧ ∃ i, (y, t) ∈ axisWallArrivalRelation A (B i) h (k i) t₀ ∧
    axisWallCoordinates (B i) (normalizedMaxCurve (axisWallChart A h y) t₀ t) ∈ E i}

def axisFamilyHittingDomain {ι : Type*} (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry)
    (h : ℝ) (k : ι → ℝ) (t₀ : ℝ) (E : ι → Set SectionCoordinates) (I : Set ℝ) : Set SectionCoordinates :=
  {y | (axisFamilyHittingTimes A B h k t₀ E I y).Nonempty}

namespace AxisWallAtlasFamily

variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)





def firstDelay (E : ι → Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) : ℝ≥0∞ :=
  ⨅ i, ⨅ n, ((C i).branch n).delay (E i) I y





end AxisWallAtlasFamily



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def globalAxisWallHittingTimes {ι : Type*} (A : ι → NormalizedSymmetry) (h : ι → ℝ)
    (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) : Set ℝ :=
  {t | t ∈ I ∧ t ∈ normalizedMaxDomain x 0 ∧
    ∃ i, ∃ y ∈ B i, axisWallChart (A i) (h i) y = normalizedMaxCurve x 0 t}

def globalAxisWallHittingDomain {ι : Type*} (A : ι → NormalizedSymmetry) (h : ι → ℝ)
    (B : ι → Set SectionCoordinates) (I : Set ℝ) : Set NormalizedState :=
  {x | (globalAxisWallHittingTimes A h B I x).Nonempty}





def globalAxisWallFirstDelay {ι : Type*} (A : ι → NormalizedSymmetry) (h : ι → ℝ)
    (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) : ℝ≥0∞ :=
  ⨅ t : globalAxisWallHittingTimes A h B I x, ENNReal.ofReal t.val













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal





namespace AxisWallAtlasFamily

variable {ι : Type*} {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)





def firstTime (E : ι → Set SectionCoordinates) (I : Set ℝ) (y : SectionCoordinates) : ℝ :=
  t₀ + (C.firstDelay E I y).toReal







end AxisWallAtlasFamily



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal



def globalAxisWallFirstTime {ι : Type*} (A : ι → NormalizedSymmetry) (h : ι → ℝ)
    (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) : ℝ :=
  (globalAxisWallFirstDelay A h B I x).toReal

def globalAxisWallFirstState {ι : Type*} (A : ι → NormalizedSymmetry) (h : ι → ℝ)
    (B : ι → Set SectionCoordinates) (I : Set ℝ) (x : NormalizedState) : NormalizedState :=
  normalizedMaxCurve x 0 (globalAxisWallFirstTime A h B I x)



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace MainWallArrivalAtlas









end MainWallArrivalAtlas





def cumulativeReturnTime {X : Type*} (R : X → X) (τ : X → ℝ) (t₀ : ℝ) (n : ℕ) (y : X) : ℝ :=
  t₀ + ∑ i ∈ Finset.range n, (τ (R^[i] y) - t₀)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def axisFamilyReturnTimes {ι : Type*} (B : ι → NormalizedSymmetry) (k : ι → ℝ) (t₀ : ℝ)
    (E : ι → Set SectionCoordinates) (z : ι × SectionCoordinates) : Set ℝ :=
  axisFamilyHittingTimes (B z.1) B (k z.1) k t₀ E (Ioi t₀) z.2

def axisFamilyReturnDomain {ι : Type*} (B : ι → NormalizedSymmetry) (k : ι → ℝ) (t₀ : ℝ)
    (E : ι → Set SectionCoordinates) : Set (ι × SectionCoordinates) :=
  {z | z.2 ∈ E z.1 ∧ (axisFamilyReturnTimes B k t₀ E z).Nonempty}







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace AxisWallAtlasFamily

variable {ι : Type*} [Encodable ι] {A : NormalizedSymmetry} {B : ι → NormalizedSymmetry}
  {h t₀ : ℝ} {k : ι → ℝ} (C : AxisWallAtlasFamily A B h k t₀)

/-- Choose the first encoded target and branch among those attaining the true earliest time. -/
def firstPiece (E : ι → Set SectionCoordinates) (I : Set ℝ) (q : ι × ℕ) : Set SectionCoordinates :=
  {y | y ∈ ((C q.1).branch q.2).eligible (E q.1) I ∧
    ((C q.1).branch q.2).delay (E q.1) I y = C.firstDelay E I y ∧
    ∀ r : ι × ℕ, Encodable.encode r < Encodable.encode q →
      ((C r.1).branch r.2).delay (E r.1) I y ≠ C.firstDelay E I y}











end AxisWallAtlasFamily



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def axisFamilyInfiniteReturns {ι : Type*} (B : ι → NormalizedSymmetry) (k : ι → ℝ) (t₀ : ℝ)
    (E : ι → Set SectionCoordinates) : Set (ι × SectionCoordinates) :=
  {z | z ∈ axisFamilySection E ∧ (axisFamilyReturnTimes B k t₀ E z).Infinite}







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def axisFamilySuccessTargets {ι : Type*} (E : ι → Set SectionCoordinates)
    (F : Set (ι × SectionCoordinates)) (i : ι) : Set SectionCoordinates :=
  E i \ (Prod.mk i ⁻¹' F)









end BianchiIX

end
end


