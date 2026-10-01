-- Prove2me | Definitions.Def_AnosovPlugs_Flows
-- name    : AnosovPlugs_Flows
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-01T01:11:36.184099+00:00
-- url     : https://prove2.me/theorems/42344297-cc30-48e0-bc91-6b0c9f2318bd
-- title:
--   Anosov plugs I: C¹ vector fields, partial flows, orientability, topological equivalence
-- statement:
--   Basic vocabulary for flows of vector fields on smooth 3-manifolds, possibly with boundary.
--
--   Every 3-manifold $M$ is a smooth manifold modelled on the closed half-space $\mathbb H^3=\{x\in\mathbb R^3 : x_0\ge 0\}$ (model $I_3$); a **closed** 3-manifold is a compact one with empty boundary. Tangent vectors at $x$ are written in the chart at $x$.
--
--   1. **C¹ vector field.** $X$ is C¹ if the section $x\mapsto (x,X(x))$ of $TM$ is C¹.
--   2. **Partial flow.** $\mathrm{FlowDefined}(X,x,t)$ holds when some integral curve $\gamma$ of $X$ with $\gamma(0)=x$ is defined (inside $M$) on the closed interval between $0$ and $t$. The time-$t$ map $X^t(x)$ is $\gamma(t)$ for such a curve, and (by convention) $x$ when no such curve exists.
--   3. **Transitivity.** $X$ is transitive if some orbit $\{X^t(x):t\in\mathbb R\}$ is dense in $M$.
--   4. **Orientability.** $M$ is orientable if it has an atlas of smooth charts covering $M$ whose transition maps all have positive Jacobian determinant.
--   5. **Topological equivalence.** A homeomorphism $h:M\to N$ is an orbit equivalence from $X$ to $Y$ if for every $x$ there is a continuous strictly increasing $\tau:\mathbb R\to\mathbb R$ with $\tau(0)=0$, mapping the set of times at which the $X$-orbit of $x$ is defined onto the corresponding set for the $Y$-orbit of $h(x)$, such that
--   $$h(X^t(x)) = Y^{\tau(t)}(h(x)).$$
--   $X$ and $Y$ are topologically equivalent if such an $h$ exists.
--
--   These notions are shared by every statement of the mission.
--
--   **Formalization Note** The flow is encoded through integral curves (`IsMIntegralCurveOn`), so that it also makes sense on manifolds with boundary, where orbits leave the manifold in finite time. Uniqueness of integral curves (C¹ fields) makes `flowMap` well defined.
-- source:
--   F. Béguin, C. Bonatti, B. Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930, https://doi.org/10.2140/gt.2017.21.1837, §1.1–1.3 and §3.1 (Definitions 3.1; conventions for flows and topological equivalence)

import Mathlib

/-!
Béguin–Bonatti–Yu, *Building Anosov flows on 3-manifolds*, Geom. Topol. 21 (2017) 1837–1930.
Basic layer: C¹ vector fields on smooth 3-manifolds (possibly with boundary), their (partial)
flows, orientability, transitivity, and topological (orbital) equivalence.

All 3-manifolds are modelled on the closed half-space `EuclideanHalfSpace 3`; a closed
3-manifold is a compact one with empty boundary (`BoundarylessManifold`).
-/

open scoped Manifold ContDiff Topology
open Set

namespace AnosovPlugs

/-- The model with corners of 3-manifolds with (possibly empty) boundary: the closed
half-space `{x ∈ ℝ³ | x₀ ≥ 0}`. -/
noncomputable abbrev I3 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 3) :=
  𝓡∂ 3

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold I3 ∞ M]

/-- `X` is a C¹ vector field: the section `x ↦ (x, X x)` of the tangent bundle is C¹. -/
def IsC1VectorField (X : (x : M) → TangentSpace I3 x) : Prop :=
  ContMDiff I3 I3.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I3 M))

/-- The orbit of `x` under `X` is defined on the whole closed time interval between `0` and `t`:
there is an integral curve `γ` of `X` with `γ 0 = x`, defined (inside `M`) on `[0, t]`
(or `[t, 0]` if `t < 0`). -/
def FlowDefined (X : (x : M) → TangentSpace I3 x) (x : M) (t : ℝ) : Prop :=
  ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ X (uIcc 0 t)

open Classical in
/-- The (partial) time-`t` map of the flow of `X`: the position at time `t` of the integral
curve of `X` through `x`, when this orbit is defined on the time interval between `0` and
`t`; by convention it is `x` otherwise. -/
noncomputable def flowMap (X : (x : M) → TangentSpace I3 x) (t : ℝ) (x : M) : M :=
  if h : FlowDefined X x t then h.choose t else x

/-- The flow of `X` is topologically transitive: some orbit is dense in `M`
(used for vector fields on closed manifolds, whose flows are complete). -/
def IsTransitiveFlow (X : (x : M) → TangentSpace I3 x) : Prop :=
  ∃ x : M, Dense (range fun t : ℝ => flowMap X t x)

/-- `M` is orientable: it admits an atlas of charts from its (smooth) maximal atlas, covering
`M`, all of whose transition maps have positive Jacobian determinant. -/
def IsOrientable (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] : Prop :=
  ∃ A : Set (OpenPartialHomeomorph M (EuclideanHalfSpace 3)),
    A ⊆ IsManifold.maximalAtlas I3 ∞ M ∧ (∀ x : M, ∃ e ∈ A, x ∈ e.source) ∧
    ∀ e ∈ A, ∀ e' ∈ A, ∀ x ∈ e.source ∩ e'.source,
      0 < LinearMap.det
        (fderivWithin ℝ (e'.extend I3 ∘ (e.extend I3).symm) (range I3) (e.extend I3 x) :
          EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))

variable {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
  [IsManifold I3 ∞ N]

/-- `h : M ≃ₜ N` is a topological (orbital) equivalence from `X` to `Y`: it maps every oriented
orbit (segment) of `X` onto an oriented orbit (segment) of `Y`. Precisely, for every `x` there
is a continuous increasing reparametrisation `τ` with `τ 0 = 0`, mapping the set of times for
which the `X`-orbit of `x` is defined onto the set of times for which the `Y`-orbit of `h x`
is defined, with `h (X^t x) = Y^{τ t} (h x)`. -/
def IsOrbitEquivalence (X : (x : M) → TangentSpace I3 x) (Y : (y : N) → TangentSpace I3 y)
    (h : M ≃ₜ N) : Prop :=
  ∀ x : M, ∃ τ : ℝ → ℝ, Continuous τ ∧ StrictMono τ ∧ τ 0 = 0 ∧
    τ '' {t | FlowDefined X x t} = {s | FlowDefined Y (h x) s} ∧
    ∀ t, FlowDefined X x t → h (flowMap X t x) = flowMap Y (τ t) (h x)

/-- `X` (on `M`) and `Y` (on `N`) are topologically equivalent. -/
def TopologicallyEquivalent (X : (x : M) → TangentSpace I3 x)
    (Y : (y : N) → TangentSpace I3 y) : Prop :=
  ∃ h : M ≃ₜ N, IsOrbitEquivalence X Y h

end AnosovPlugs


