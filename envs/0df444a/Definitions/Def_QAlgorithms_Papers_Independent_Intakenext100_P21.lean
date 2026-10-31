-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P21
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P21
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:43:50.972989+00:00
-- url     : https://prove2.me/theorems/cb0eabe4-14a5-4b16-a9d9-1521e8c792e3
-- title:
--   Definitions for Integrability of unitary representations on reproducing kernel spaces
-- statement:
--   The objects the formalized statements of *Integrability of unitary representations on reproducing kernel spaces* (arXiv:1406.2681) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `HasTimeDerivative`: Section 2, PDF p. 6: the ordinary derivative of a locally convex valued curve. This definition does not require a Banach target.
--   - `CoordinateField`: Sections 2--3, PDF pp. 5, 10: a tangent-section coordinate family. Only components for c in the atlas and m in c.source are used. The predicate IsSmoothVectorField imposes the tangent transition law, so this type alone does not purport to be the space of smooth vector fields.
--   - `IsSmoothVectorField`: Section 2, PDF p. 5: smooth tangent-section coordinates. The second clause transforms each component by the derivative of the actual chart transition; no independent tangent bundle or arbitrary derivative is supplied.
--   - `IsIntegralCurve`: Definition 2.3(b), PDF p. 6: an integral curve on an open interval containing zero. Continuity and the chartwise differential equation express differentiability into M, with no normability restriction.
--   - `FlowData`: Definition 2.1, PDF p. 6: raw domain and a total representative of the flow. Off-domain values are never used in any identity or uniqueness claim.
--   - `IsSmoothFlowMap`: Definition 2.1, PDF p. 6: joint smoothness in time and space in the product atlas, on the specified open flow domain.
--   - `IsLocalFlow`: Definition 2.1, PDF p. 6: open domain containing zero times every point, interval time fibers, and the local addition law precisely wherever both sides are defined. No maximality or uniqueness is assumed.
--   - `HasVelocityField`: Definition 2.3(a), PDF p. 6: X is the velocity at zero of this flow; the integral-curve property at other times is a theorem, not a hypothesis.
--   - `IsLocallyIntegrable`: Definition 2.3(a), PDF p. 6: local integrability requires a smooth vector field and one actual jointly smooth local flow with this velocity.
--   - `CurveExtends`: Definition 2.3(c), PDF p. 6: extension includes the original domain and agrees there; total representatives outside it are immaterial.
--   - `IsMaximalIntegralCurve`: Definition 2.3(c), PDF p. 6: no integral curve on a strictly larger open interval extends the given integral curve.
--   - `maximalCurveDomain`: Lemma 2.5(iv), PDF p. 8: union of the actual integral-curve intervals through the given initial point, not an independently chosen domain.
--   - `maximalCurve`: Lemma 2.5(iv), PDF p. 8: glue by selecting an attained integral-curve value. Lemma 2.5 proves agreement of all choices. The default m is used only outside maximalCurveDomain, and is never part of an asserted curve.
--   - `maximalFlow`: Theorem 2.6, PDF p. 8: the flow domain and values constructed from all integral curves. This construction assumes no smoothness of the glued map.
--   - `bracketCoordinate`: Section 3, PDF p. 10: coordinate formula for the actual Lie bracket of two vector fields, dY(X)-dX(Y), computed in a chart.
--   - `pullbackCoordinate`: Section 3, PDF pp. 10--11: coordinates at m of (Phi[-t])_*Y, using a chart centered at Phi[t](m). Its genuine domain is M_t; nearby times around zero suffice for the Lie derivative.
--   - `linearField`: Proposition 2.9, PDF p. 10: X(v)=Dv in the standard one-chart atlas of the locally convex vector space itself.
--   - `adjointField`: Definition 3.3, PDF p. 11: the linear adjoint vector field at y is [x,y], in the standard atlas of the vector space A.
--   - `IsAdIntegrable`: Definition 3.3, PDF p. 11: every adjoint field generates a global flow. Local integrability and the entire maximal domain express the source's global-flow definition without an operator exponential on a nonnormable space.
--   - `adjointEvolution`: Definition 3.3, PDF p. 11: e^(t ad x)y is the actual global linear flow, not a formal power series or a bounded-operator exponential.
--   - `IsSmoothInfinitesimalAction`: Lemma 3.4, PDF p. 11: the coordinate form of a smooth Lie algebra homomorphism into vector fields. Joint evaluation is smooth into the actual tangent coordinates, and bracket preservation uses dY(X)-dX(Y).
-- source:
--   Integrability of unitary representations on reproducing kernel spaces, arXiv:1406.2681v3, https://arxiv.org/abs/1406.2681v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P15

/-!
Statements from Merigon--Neeb--Olafsson, arXiv:1406.2681v3, Sections 2--3.
The calculus below is jointly continuous iterated directional calculus over
Hausdorff locally convex models. The derivative tower and atlas predicate are imported from the pinned
accepted Claimed50.P22; directional limits and their selection are imported
from Next46.P15. No normability is imposed.
Coordinate representatives are compared only in actual chart domains. Flow and
curve representatives outside their domains have no mathematical meaning.
Analytic and representation-theoretic nodes deferred in this bounded stage are
listed individually in HARD.md and GAPS.json. Compilation is pending handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P21

open Set Filter Topology
open QAlgorithms.Papers.Independent.Claimed50.P22 (BastianiSmoothOn BastianiAtlas)
open QAlgorithms.Papers.Independent.Next46.P15 (HasDirectionalDerivative directionalDerivative)

attribute [local instance] Classical.propDecidable

universe u v w

section Calculus

variable {E : Type u} {F : Type v}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The constant zero map has the zero tower, also in order zero. -/
example (U : Set E) : BastianiSmoothOn U (fun _ : E => (0 : F)) := by
  refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
  · intro x hx
    rfl
  · intro n
    exact continuousOn_const
  · intro n x hx a h
    simpa only [sub_self, smul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

/-- Section 2, PDF p. 6: the ordinary derivative of a locally convex valued
curve. This definition does not require a Banach target. -/
def HasTimeDerivative (f : ℝ → F) (t : ℝ) (y : F) : Prop :=
  Tendsto (fun s : ℝ => s⁻¹ • (f (t + s) - f t))
    (𝓝[≠] (0 : ℝ)) (𝓝 y)

/-- A constant curve has zero velocity. -/
example (v : F) (t : ℝ) : HasTimeDerivative (fun _ : ℝ => v) t 0 := by
  simpa only [HasTimeDerivative, sub_self, smul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : F))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : F)))

end Calculus

section Manifolds

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]

/-- Sections 2--3, PDF pp. 5, 10: a tangent-section coordinate family.
Only components for c in the atlas and m in c.source are used. The predicate
IsSmoothVectorField imposes the tangent transition law, so this type alone
does not purport to be the space of smooth vector fields. -/
abbrev CoordinateField (E : Type u) (M : Type v)
    [TopologicalSpace E] [TopologicalSpace M] :=
  OpenPartialHomeomorph M E → M → E

/-- Section 2, PDF p. 5: smooth tangent-section coordinates. The second
clause transforms each component by the derivative of the actual chart
transition; no independent tangent bundle or arbitrary derivative is supplied. -/
def IsSmoothVectorField (X : CoordinateField E M) : Prop :=
  (∀ c ∈ atlas E M,
    BastianiSmoothOn c.target (fun z => X c (c.symm z))) ∧
  (∀ c ∈ atlas E M, ∀ d ∈ atlas E M, ∀ m : M,
    m ∈ c.source → m ∈ d.source →
      HasDirectionalDerivative (fun z => d (c.symm z)) (c m) (X c m) (X d m))

/-- Definition 2.3(b), PDF p. 6: an integral curve on an open interval
containing zero. Continuity and the chartwise differential equation express
differentiability into M, with no normability restriction. -/
def IsIntegralCurve (X : CoordinateField E M) (I : Set ℝ) (gamma : ℝ → M) : Prop :=
  IsOpen I ∧ OrdConnected I ∧ (0 : ℝ) ∈ I ∧ ContinuousOn gamma I ∧
    ∀ t ∈ I, ∀ c ∈ atlas E M, gamma t ∈ c.source →
      HasTimeDerivative (fun s => c (gamma s)) t (X c (gamma t))

/-- A stationary point gives a constant integral curve on every open
interval containing zero. In particular this applies to the zero field. -/
example (X : CoordinateField E M) (m : M) (I : Set ℝ)
    (hOpen : IsOpen I) (hInterval : OrdConnected I) (hZero : (0 : ℝ) ∈ I)
    (hStationary : ∀ c ∈ atlas E M, m ∈ c.source → X c m = 0) :
    IsIntegralCurve X I (fun _ => m) := by
  refine ⟨hOpen, hInterval, hZero, continuousOn_const, ?_⟩
  intro t ht c hc hm
  rw [hStationary c hc hm]
  simpa only [HasTimeDerivative, sub_self, smul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : E))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : E)))

/-- Definition 2.1, PDF p. 6: raw domain and a total representative of the
flow. Off-domain values are never used in any identity or uniqueness claim. -/
structure FlowData (M : Type v) where
  domain : Set (ℝ × M)
  value : ℝ → M → M

/-- Definition 2.1, PDF p. 6: joint smoothness in time and space in the
product atlas, on the specified open flow domain. -/
def IsSmoothFlowMap (P : FlowData M) : Prop :=
  ContinuousOn (fun p : ℝ × M => P.value p.1 p.2) P.domain ∧
    ∀ c ∈ atlas E M, ∀ d ∈ atlas E M,
      BastianiSmoothOn
        {p : ℝ × E | p.2 ∈ c.target ∧
          (p.1, c.symm p.2) ∈ P.domain ∧
          P.value p.1 (c.symm p.2) ∈ d.source}
        (fun p : ℝ × E => d (P.value p.1 (c.symm p.2)))

/-- Definition 2.1, PDF p. 6: open domain containing zero times every
point, interval time fibers, and the local addition law precisely wherever
both sides are defined. No maximality or uniqueness is assumed. -/
def IsLocalFlow (P : FlowData M) : Prop :=
  IsOpen P.domain ∧ (∀ m : M, (0, m) ∈ P.domain) ∧
    (∀ m : M, OrdConnected {t : ℝ | (t, m) ∈ P.domain}) ∧
    IsSmoothFlowMap (E := E) P ∧
    (∀ m : M, P.value 0 m = m) ∧
    (∀ s t : ℝ, ∀ m : M,
      (s, m) ∈ P.domain → (t, P.value s m) ∈ P.domain →
      (s + t, m) ∈ P.domain →
      P.value t (P.value s m) = P.value (s + t) m)

/-- Definition 2.3(a), PDF p. 6: X is the velocity at zero of this flow;
the integral-curve property at other times is a theorem, not a hypothesis. -/
def HasVelocityField (P : FlowData M) (X : CoordinateField E M) : Prop :=
  ∀ m : M, ∀ c ∈ atlas E M, m ∈ c.source →
    HasTimeDerivative (fun t => c (P.value t m)) 0 (X c m)

/-- Definition 2.3(a), PDF p. 6: local integrability requires a smooth
vector field and one actual jointly smooth local flow with this velocity. -/
def IsLocallyIntegrable (X : CoordinateField E M) : Prop :=
  IsSmoothVectorField X ∧
    ∃ P : FlowData M, IsLocalFlow (E := E) P ∧ HasVelocityField P X

/-- Definition 2.3(c), PDF p. 6: extension includes the original domain
and agrees there; total representatives outside it are immaterial. -/
def CurveExtends (I : Set ℝ) (gamma : ℝ → M) (J : Set ℝ) (eta : ℝ → M) : Prop :=
  I ⊆ J ∧ ∀ t ∈ I, eta t = gamma t

/-- Definition 2.3(c), PDF p. 6: no integral curve on a strictly larger
open interval extends the given integral curve. -/
def IsMaximalIntegralCurve (X : CoordinateField E M) (I : Set ℝ)
    (gamma : ℝ → M) : Prop :=
  IsIntegralCurve X I gamma ∧
    ∀ J eta, IsIntegralCurve X J eta → CurveExtends I gamma J eta → J ⊆ I

/-- Lemma 2.5(iv), PDF p. 8: union of the actual integral-curve intervals
through the given initial point, not an independently chosen domain. -/
def maximalCurveDomain (X : CoordinateField E M) (m : M) : Set ℝ :=
  {t | ∃ (I : Set ℝ) (gamma : ℝ → M),
    IsIntegralCurve X I gamma ∧ gamma 0 = m ∧ t ∈ I}

/-- Lemma 2.5(iv), PDF p. 8: glue by selecting an attained integral-curve
value. Lemma 2.5 proves agreement of all choices. The default m is used only
outside maximalCurveDomain, and is never part of an asserted curve. -/
noncomputable def maximalCurve (X : CoordinateField E M) (m : M) (t : ℝ) : M :=
  if h : ∃ y : M, ∃ (I : Set ℝ) (gamma : ℝ → M),
      IsIntegralCurve X I gamma ∧ gamma 0 = m ∧ t ∈ I ∧ gamma t = y
  then Classical.choose h else m

/-- Theorem 2.6, PDF p. 8: the flow domain and values constructed from
all integral curves. This construction assumes no smoothness of the glued map. -/
noncomputable def maximalFlow (X : CoordinateField E M) : FlowData M where
  domain := {p | p.1 ∈ maximalCurveDomain X p.2}
  value := fun t m => maximalCurve X m t

/-- The constructed flow has precisely the union-of-curves time fiber. -/
example (X : CoordinateField E M) (t : ℝ) (m : M) :
    (t, m) ∈ (maximalFlow X).domain ↔ t ∈ maximalCurveDomain X m := Iff.rfl

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable [LocallyConvexSpace ℝ E] [T2Space E] [T2Space M]

/-- Section 3, PDF p. 10: coordinate formula for the actual Lie bracket
of two vector fields, dY(X)-dX(Y), computed in a chart. -/
noncomputable def bracketCoordinate (X Y : CoordinateField E M)
    (c : OpenPartialHomeomorph M E) (m : M) : E :=
  directionalDerivative (fun z => Y c (c.symm z)) (c m) (X c m) -
    directionalDerivative (fun z => X c (c.symm z)) (c m) (Y c m)

/-- Section 3, PDF pp. 10--11: coordinates at m of (Phi[-t])_*Y,
using a chart centered at Phi[t](m). Its genuine domain is M_t; nearby
times around zero suffice for the Lie derivative. -/
noncomputable def pullbackCoordinate (P : FlowData M) (Y : CoordinateField E M)
    (t : ℝ) (c : OpenPartialHomeomorph M E) (m : M) : E :=
  let d := chartAt E (P.value t m)
  directionalDerivative (fun z => c (P.value (-t) (d.symm z)))
    (d (P.value t m)) (Y d (P.value t m))

end Manifolds

section LinearFields

variable {V : Type u} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]

/-- Proposition 2.9, PDF p. 10: X(v)=Dv in the standard one-chart atlas
of the locally convex vector space itself. -/
def linearField (D : V →L[ℝ] V) : CoordinateField V V := fun _ v => D v

/-- The zero continuous linear map gives the zero field. -/
example (c : OpenPartialHomeomorph V V) (v : V) :
    linearField (0 : V →L[ℝ] V) c v = 0 := rfl

end LinearFields

section AdjointFlows

variable {A : Type u} [TopologicalSpace A] [LieRing A] [Module ℝ A]
variable [LieAlgebra ℝ A]

/-- Definition 3.3, PDF p. 11: the linear adjoint vector field
at y is [x,y], in the standard atlas of the vector space A. -/
def adjointField (x : A) : CoordinateField A A := fun _ y => ⁅x, y⁆

/-- Definition 3.3, PDF p. 11: every adjoint field generates a global
flow. Local integrability and the entire maximal domain express the source's
global-flow definition without an operator exponential on a nonnormable space. -/
def IsAdIntegrable : Prop :=
  ∀ x : A, IsLocallyIntegrable (adjointField x) ∧
    (maximalFlow (adjointField x)).domain = Set.univ

/-- Definition 3.3, PDF p. 11: e^(t ad x)y is the actual global linear
flow, not a formal power series or a bounded-operator exponential. -/
noncomputable def adjointEvolution (x y : A) (t : ℝ) : A :=
  (maximalFlow (adjointField x)).value t y

/-- The adjoint field at zero vanishes, including for the zero Lie algebra. -/
example (c : OpenPartialHomeomorph A A) (y : A) : adjointField (0 : A) c y = 0 := by
  exact zero_lie _

variable {E : Type v} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace E M]

/-- Lemma 3.4, PDF p. 11: the coordinate form of a smooth Lie algebra
homomorphism into vector fields. Joint evaluation is smooth into the actual
tangent coordinates, and bracket preservation uses dY(X)-dX(Y). -/
def IsSmoothInfinitesimalAction
    (beta : A →ₗ[ℝ] CoordinateField E M) : Prop :=
  (∀ x : A, IsSmoothVectorField (beta x)) ∧
    (∀ x y : A, ∀ c ∈ atlas E M, ∀ m ∈ c.source,
      beta ⁅x, y⁆ c m = bracketCoordinate (beta x) (beta y) c m) ∧
    (∀ c ∈ atlas E M,
      BastianiSmoothOn (Set.univ ×ˢ c.target)
        (fun p : A × E => beta p.1 c (c.symm p.2)))

end AdjointFlows

end QAlgorithms.Papers.Independent.Intakenext100.P21


