-- Prove2me | Definitions.Def_AnosovPlugs_Plugs
-- name    : AnosovPlugs_Plugs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-01T01:28:07.273305+00:00
-- url     : https://prove2.me/theorems/d824ee86-c2df-43da-908e-1f09fd13ad60
-- title:
--   Anosov plugs III: plugs, hyperbolic plugs, laminations, attractors
-- statement:
--   Let $V$ be a 3-manifold with boundary and $X$ a vector field on $V$. At a boundary point, a vector written in the boundary chart points strictly inwards iff its first coordinate $v_0$ is positive.
--
--   1. **Entrance / exit boundary.** $\partial^{in}V$ (resp. $\partial^{out}V$) is the set of boundary points where $X$ points strictly inwards (resp. outwards).
--   2. **Plug** (Definition 3.1). $(V,X)$ is a plug if $X$ is a nonsingular C¹ vector field transverse to $\partial V$. It is **attracting** if $\partial^{out}V=\emptyset$ and **repelling** if $\partial^{in}V=\emptyset$.
--   3. **Maximal invariant set** $\Lambda$: points whose orbit is defined for all real times. **Stable set** $W^s(\Lambda)$: points whose forward orbit is defined for all $t\ge0$; **unstable set** $W^u(\Lambda)$: points whose backward orbit is defined for all $t\le0$.
--   4. **Hyperbolic plug** (Definition 3.2): a plug whose maximal invariant set is a hyperbolic set (with 1-dimensional strong stable/unstable bundles).
--   5. **Entrance and exit laminations**: $L^s_X=W^s(\Lambda)\cap\partial^{in}V$, $L^u_X=W^u(\Lambda)\cap\partial^{out}V$.
--   6. **Leaves.** The weak stable manifold of $p$ is the set of forward-complete points $q$ such that $(X^t q,X^{t+s}p)$ tends to the diagonal as $t\to+\infty$ for some shift $s$. The leaf of $L^s_X$ through $p$ is the path component of $p$ in (weak stable manifold of $p$) $\cap\,\partial^{in}V$; leaves of $L^u_X$ are defined in the same way for $-X$.
--   7. **Attractor / repeller.** An attractor is a nonempty compact invariant subset $A\subseteq\Lambda$ with a dense orbit, admitting a neighbourhood $U$ with $\bigcap_{t\ge0}X^t(U)=A$. A repeller is an attractor of $-X$.
--
--   **Formalization Note** Leaves are defined as path components of intersections of weak stable manifolds with the boundary; since weak stable manifolds are injectively immersed surfaces meeting any transversal in a totally disconnected set, these path components are exactly the leaves of the paper.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, §1.2 and Definitions 3.1–3.2 (pp. 1849–1850), §3.3

import Mathlib
import Definitions.Def_AnosovPlugs_Hyperbolic

/-!
Béguin–Bonatti–Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017).
Plugs and hyperbolic plugs (§1.2, Definitions 3.1 and 3.2), their maximal invariant set, stable
and unstable sets, entrance/exit laminations and the leaves of these laminations, attractors and
repellers.

Tangent vectors at `x` are expressed in the chart at `x`, whose model is the half-space
`{x₀ ≥ 0}`; at a boundary point `x`, a vector `v` points strictly inwards iff `v₀ > 0`.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace AnosovPlugs

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold I3 ∞ M]

/-- The first coordinate `v₀` of a vector `v ∈ ℝ³`. A tangent vector at a boundary point,
written in the chart at that point (modelled on the half-space `{x₀ ≥ 0}`), points strictly
inwards iff its first coordinate is positive. -/
def normalCoord (v : EuclideanSpace ℝ (Fin 3)) : ℝ := v 0

/-- The entrance boundary `∂^{in} M`: boundary points at which `X` points strictly inwards. -/
def inBoundary (X : (x : M) → TangentSpace I3 x) : Set M :=
  {x | x ∈ I3.boundary M ∧ 0 < normalCoord (X x)}

/-- The exit boundary `∂^{out} M`: boundary points at which `X` points strictly outwards. -/
def outBoundary (X : (x : M) → TangentSpace I3 x) : Set M :=
  {x | x ∈ I3.boundary M ∧ normalCoord (X x) < 0}

/-- `X` is nonsingular and transverse to the boundary `∂M`. -/
def IsNonsingularTransverse (X : (x : M) → TangentSpace I3 x) : Prop :=
  (∀ x, X x ≠ 0) ∧ ∀ x ∈ I3.boundary M, normalCoord (X x) ≠ 0

/-- `(M, X)` is a plug (Definition 3.1): `X` is a nonsingular C¹ vector field transverse to the
boundary `∂M`. (Compactness of `M` is a standing typeclass assumption where plugs are used.) -/
def IsPlug (X : (x : M) → TangentSpace I3 x) : Prop :=
  IsC1VectorField X ∧ IsNonsingularTransverse X

/-- Attracting plug: a plug with empty exit boundary. -/
def IsAttractingPlug (X : (x : M) → TangentSpace I3 x) : Prop :=
  IsPlug X ∧ outBoundary X = ∅

/-- Repelling plug: a plug with empty entrance boundary. -/
def IsRepellingPlug (X : (x : M) → TangentSpace I3 x) : Prop :=
  IsPlug X ∧ inBoundary X = ∅

/-- The maximal invariant set `Λ`: points whose forward and backward orbits are defined for all
times. -/
def maxInvSet (X : (x : M) → TangentSpace I3 x) : Set M :=
  {x | ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ X}

/-- The stable set `W^s(Λ)`: points whose forward orbit is defined for all positive times. -/
def stableSet (X : (x : M) → TangentSpace I3 x) : Set M :=
  {x | ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ X (Ici 0)}

/-- The unstable set `W^u(Λ)`: points whose backward orbit is defined for all negative times. -/
def unstableSet (X : (x : M) → TangentSpace I3 x) : Set M :=
  {x | ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ X (Iic 0)}

/-- `(M, X)` is a hyperbolic plug (Definition 3.2): a plug whose maximal invariant set is a
hyperbolic set with one-dimensional strong stable and strong unstable bundles. -/
def IsHyperbolicPlug (X : (x : M) → TangentSpace I3 x) : Prop :=
  IsPlug X ∧ IsHyperbolicSet X (maxInvSet X)

/-- The entrance lamination `L^s_X = W^s(Λ) ∩ ∂^{in} M`. -/
def entranceLamination (X : (x : M) → TangentSpace I3 x) : Set M :=
  stableSet X ∩ inBoundary X

/-- The exit lamination `L^u_X = W^u(Λ) ∩ ∂^{out} M`. -/
def exitLamination (X : (x : M) → TangentSpace I3 x) : Set M :=
  unstableSet X ∩ outBoundary X

/-- The weak stable manifold of a point `p`: the points `q` with forward-complete orbit whose
forward orbit is asymptotic to the forward orbit of `p` up to a time shift `s`, i.e.
`(X^t q, X^{t+s} p)` tends to the diagonal as `t → +∞`. -/
def weakStableSet (X : (x : M) → TangentSpace I3 x) (p : M) : Set M :=
  {q | q ∈ stableSet X ∧ ∃ s : ℝ,
    Tendsto (fun t : ℝ => (flowMap X t q, flowMap X (t + s) p)) atTop (𝓝ˢ (diagonal M))}

/-- The leaf through `p` of the entrance lamination: the path component of `p` in the
intersection of the weak stable manifold of `p` with the entrance boundary. -/
def entranceLeaf (X : (x : M) → TangentSpace I3 x) (p : M) : Set M :=
  pathComponentIn (weakStableSet X p ∩ inBoundary X) p

/-- The leaf through `p` of the exit lamination (the entrance leaf for the reversed field). -/
def exitLeaf (X : (x : M) → TangentSpace I3 x) (p : M) : Set M :=
  entranceLeaf (fun x => -X x) p

/-- `A` is an attractor of `X`: a nonempty compact invariant set, contained in the maximal
invariant set, with a dense orbit, admitting a neighbourhood `U` with
`⋂_{t ≥ 0} X^t(U) = A` (where `X^t(U)` is the set of points `X^t(y)`, `y ∈ U`, whose forward
orbit is defined up to time `t`). -/
def IsAttractor (X : (x : M) → TangentSpace I3 x) (A : Set M) : Prop :=
  A.Nonempty ∧ IsCompact A ∧ A ⊆ maxInvSet X ∧ (∀ x ∈ A, ∀ t : ℝ, flowMap X t x ∈ A) ∧
    (∃ x ∈ A, A ⊆ closure (range fun t : ℝ => flowMap X t x)) ∧
    ∃ U ∈ 𝓝ˢ A, (⋂ t ∈ Ici (0 : ℝ), {y | ∃ z ∈ U, FlowDefined X z t ∧ flowMap X t z = y}) = A

/-- `A` is a repeller of `X`: an attractor of `-X`. -/
def IsRepeller (X : (x : M) → TangentSpace I3 x) (A : Set M) : Prop :=
  IsAttractor (fun x => -X x) A

/-- The maximal invariant set of `X` contains neither attractors nor repellers. -/
def NoAttractorNorRepeller (X : (x : M) → TangentSpace I3 x) : Prop :=
  ∀ A ⊆ maxInvSet X, ¬ IsAttractor X A ∧ ¬ IsRepeller X A

end AnosovPlugs


