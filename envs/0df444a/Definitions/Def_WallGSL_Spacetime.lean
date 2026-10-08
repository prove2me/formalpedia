-- Prove2me | Definitions.Def_WallGSL_Spacetime
-- name    : WallGSL_Spacetime
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-04T17:18:25.054385+00:00
-- url     : https://prove2.me/theorems/aaae8599-0b0a-4e5a-9aec-e7dc51e8629e
-- title:
--   Time-oriented Lorentzian spacetimes and causal structure
-- statement:
--   This definition file sets up time-oriented Lorentzian spacetimes and their causal structure, following §3.2 of Wall (2013) and the standard conventions of Hawking–Ellis.
--
--   A **Lorentzian metric** `LorentzianMetric E M` on a manifold $M$ modelled on a finite-dimensional real inner product space $E$ consists of
--
--   1. a field of symmetric bilinear forms $g_x$ on the tangent spaces $T_xM\cong E$, whose components are $C^\infty$ in every chart;
--   2. a continuous vector field $\tau$ (`timeField`) with $g_x(\tau_x,\tau_x)<0$, such that $g_x$ is positive definite on the $g_x$-orthogonal complement of $\tau_x$; this says that $g_x$ has signature $(-,+,\dots,+)$, and $\tau$ fixes the time orientation.
--
--   On top of this the file defines: future-directed timelike / causal / null vectors; **affinely parametrized geodesics** through the coordinate geodesic equation $\ddot c^k+\Gamma^k_{ij}\dot c^i\dot c^j=0$; $C^1$ future-directed causal and timelike curves; the relations $p\le q$ and $p\ll q$ (finite concatenations of such curves); the sets $I^\pm(S)$, $J^\pm(S)$; achronal sets; **global hyperbolicity** (no closed timelike curves and $J^+(p)\cap J^-(q)$ compact); inextendible timelike curves; **Cauchy surfaces** (met exactly once by every inextendible timelike curve); **null geodesic completeness** (every null geodesic on an open interval extends to a geodesic on all of $\mathbb R$); proper time; **future-infinite timelike worldlines** (timelike, infinite proper time to the future); and **future-infinite null rays** (future-directed null geodesics defined for all affine parameters $t>a$).
--
--   These are the geometric notions in which the GSL, quantum trapped surfaces and the singularity theorem are stated.
--
--   **Formalization Note** Tangent spaces are identified with the model space $E$, as in Mathlib's manifold library. The global hyperbolicity definition is the one written in the paper (footnote 11 there explains why strong causality is not needed).
-- source:
--   A. C. Wall, The generalized second law implies a quantum singularity theorem, Class. Quantum Grav. 30 (2013) 165003, https://doi.org/10.1088/0264-9381/30/16/165003, §3.2 (global hyperbolicity, p. 15), §2.2 (observers, p. 6)

import Mathlib

/-!
# Lorentzian spacetimes and their causal structure

Definition layer for the formalization of
A. C. Wall, *The generalized second law implies a quantum singularity theorem*,
Class. Quantum Grav. 30 (2013) 165003.

A spacetime is a smooth manifold (modelled on a finite-dimensional real inner product
space `E`, without boundary) carrying a smooth Lorentzian metric of signature
`(-,+,…,+)` and a continuous timelike vector field fixing the time orientation.
-/

open scoped Manifold Topology ContDiff
open Set Filter

namespace WallGSL

/-- A time-oriented Lorentzian metric on the manifold `M`.

* `g x` is the metric on the tangent space at `x`, a bilinear form;
* `timeField` is a continuous vector field which is timelike everywhere; it fixes the
  time orientation (a causal vector is future-directed when it has negative `g`-product
  with `timeField`);
* `posDef_orth` says that `g x` is positive definite on the `g x`-orthogonal complement
  of the timelike vector `timeField x`.  Together with `timelike` this says exactly that
  `g x` is nondegenerate of signature `(-,+,…,+)`;
* `smooth` says that in every chart the coordinate components of the metric are `C^∞`. -/
structure LorentzianMetric (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] where
  /-- The metric tensor. -/
  g : M → E →L[ℝ] E →L[ℝ] ℝ
  /-- A time-orientation vector field. -/
  timeField : M → E
  symm : ∀ x v w, g x v w = g x w v
  timelike : ∀ x, g x (timeField x) (timeField x) < 0
  posDef_orth : ∀ x v, g x v (timeField x) = 0 → v ≠ 0 → 0 < g x v v
  continuous_timeField :
    Continuous (fun x => (⟨x, timeField x⟩ : TangentBundle 𝓘(ℝ, E) M))
  smooth : ∀ p : M, ContDiffOn ℝ ∞
    (fun y : E => (g ((extChartAt 𝓘(ℝ, E) p).symm y)).bilinearComp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm y : E →L[ℝ] E)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm y : E →L[ℝ] E))
    (extChartAt 𝓘(ℝ, E) p).target

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

namespace LorentzianMetric

variable (st : LorentzianMetric E M)

/-- The coordinate expression `G_p(y)` of the metric in the chart at `p`, as a bilinear
form on the model space `E`. -/
noncomputable def coordMetric (p : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (st.g ((extChartAt 𝓘(ℝ, E) p).symm y)).bilinearComp
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm y : E →L[ℝ] E)
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p).symm y : E →L[ℝ] E)

/-- The velocity `γ'(t) ∈ T_{γ(t)} M` of a curve `γ : ℝ → M`. -/
noncomputable def velocity (γ : ℝ → M) (t : ℝ) : E :=
  (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t : ℝ →L[ℝ] E) 1

/-- The one-sided velocity of `γ` at `t`, computed within the set `s`. -/
noncomputable def velocityWithin (γ : ℝ → M) (s : Set ℝ) (t : ℝ) : E :=
  (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s t : ℝ →L[ℝ] E) 1

/-- A tangent vector is causal and future-directed. -/
def IsFutureCausal (x : M) (v : E) : Prop :=
  st.g x v v ≤ 0 ∧ v ≠ 0 ∧ st.g x v (st.timeField x) < 0

/-- A tangent vector is timelike and future-directed. -/
def IsFutureTimelike (x : M) (v : E) : Prop :=
  st.g x v v < 0 ∧ st.g x v (st.timeField x) < 0

/-- A tangent vector is null (lightlike) and future-directed. -/
def IsFutureNull (x : M) (v : E) : Prop :=
  st.g x v v = 0 ∧ v ≠ 0 ∧ st.g x v (st.timeField x) < 0

/-- `γ` is an affinely parametrized geodesic on the set `s ⊆ ℝ` (intended to be open):
it is `C²` there and, for every `t₀ ∈ s`, the coordinate curve `c = φ ∘ γ` in the chart
`φ` at `γ t₀` satisfies the geodesic equation `c'' + Γ(c)(c', c') = 0` at `t₀`.  The
equation is written with the index lowered, i.e. for every `w ∈ E`
`G(c)(c'', w) + DG(c)[c'](c', w) - ½ DG(c)[w](c', c') = 0`,
which is equivalent to the usual form because `G(c)` is nondegenerate. -/
def IsGeodesicOn (γ : ℝ → M) (s : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 2 γ s ∧
  ∀ t₀ ∈ s,
    let c : ℝ → E := fun t => extChartAt 𝓘(ℝ, E) (γ t₀) (γ t)
    let G := st.coordMetric (γ t₀)
    ∀ w : E,
      G (c t₀) (deriv (deriv c) t₀) w
        + fderiv ℝ G (c t₀) (deriv c t₀) (deriv c t₀) w
        - (1 / 2 : ℝ) * fderiv ℝ G (c t₀) w (deriv c t₀) (deriv c t₀) = 0

/-- `γ` restricted to `[a, b]` is a `C¹` future-directed causal curve. -/
def IsFutureCausalCurveOn (γ : ℝ → M) (a b : ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc a b) ∧
  ∀ t ∈ Icc a b, st.IsFutureCausal (γ t) (velocityWithin γ (Icc a b) t)

/-- `γ` restricted to `[a, b]` is a `C¹` future-directed timelike curve. -/
def IsFutureTimelikeCurveOn (γ : ℝ → M) (a b : ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc a b) ∧
  ∀ t ∈ Icc a b, st.IsFutureTimelike (γ t) (velocityWithin γ (Icc a b) t)

/-- One `C¹` future-directed causal segment from `p` to `q`. -/
def CausalStep (p q : M) : Prop :=
  ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ γ a = p ∧ γ b = q ∧ st.IsFutureCausalCurveOn γ a b

/-- One `C¹` future-directed timelike segment from `p` to `q`. -/
def TimelikeStep (p q : M) : Prop :=
  ∃ (γ : ℝ → M) (a b : ℝ), a < b ∧ γ a = p ∧ γ b = q ∧ st.IsFutureTimelikeCurveOn γ a b

/-- The causal relation `p ≤ q`: `q = p` or `q` is reached from `p` by a piecewise `C¹`
future-directed causal curve. -/
def CausalPrec (p q : M) : Prop := Relation.ReflTransGen st.CausalStep p q

/-- The chronological relation `p ≪ q`: `q` is reached from `p` by a piecewise `C¹`
future-directed timelike curve. -/
def ChronPrec (p q : M) : Prop := Relation.TransGen st.TimelikeStep p q

/-- Chronological future `I⁺(S)`. -/
def chronFuture (S : Set M) : Set M := {q | ∃ p ∈ S, st.ChronPrec p q}

/-- Chronological past `I⁻(S)`. -/
def chronPast (S : Set M) : Set M := {q | ∃ p ∈ S, st.ChronPrec q p}

/-- Causal future `J⁺(S)`. -/
def causalFuture (S : Set M) : Set M := {q | ∃ p ∈ S, st.CausalPrec p q}

/-- Causal past `J⁻(S)`. -/
def causalPast (S : Set M) : Set M := {q | ∃ p ∈ S, st.CausalPrec q p}

/-- A set is achronal: no two of its points are chronologically related. -/
def IsAchronal (S : Set M) : Prop := ∀ p ∈ S, ∀ q ∈ S, ¬ st.ChronPrec p q

/-- Global hyperbolicity in the sense of the paper (§3.2): there are no closed timelike
curves, and `J⁺(p) ∩ J⁻(q)` is compact for all points `p, q`. -/
def IsGloballyHyperbolic : Prop :=
  (∀ p : M, ¬ st.ChronPrec p p) ∧
  ∀ p q : M, IsCompact (st.causalFuture {p} ∩ st.causalPast {q})

/-- An inextendible timelike curve, parametrized by all of `ℝ`: it is future-directed
timelike on every compact parameter interval and has no endpoint in either direction. -/
def IsInextendibleTimelike (γ : ℝ → M) : Prop :=
  (∀ a b, a < b → st.IsFutureTimelikeCurveOn γ a b) ∧
  (¬ ∃ x, Tendsto γ atTop (𝓝 x)) ∧ (¬ ∃ x, Tendsto γ atBot (𝓝 x))

/-- A Cauchy surface: a set met exactly once by every inextendible timelike curve. -/
def IsCauchySurface (S : Set M) : Prop :=
  ∀ γ : ℝ → M, st.IsInextendibleTimelike γ → ∃! t, γ t ∈ S

/-- Null geodesic completeness: every null geodesic defined on an open interval extends
to a geodesic defined on all of `ℝ` (i.e. it can be continued to all values of its
affine parameter). -/
def IsNullGeodesicallyComplete : Prop :=
  ∀ (γ : ℝ → M) (a b : ℝ), a < b → st.IsGeodesicOn γ (Ioo a b) →
    (∀ t ∈ Ioo a b, st.g (γ t) (velocity γ t) (velocity γ t) = 0 ∧ velocity (E := E) γ t ≠ 0) →
    ∃ δ : ℝ → M, st.IsGeodesicOn δ univ ∧ EqOn δ γ (Ioo a b)

/-- The proper time `∫ₐᵇ √(-g(γ', γ')) dt` of a curve between parameters `a` and `b`. -/
noncomputable def properTime (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt (-(st.g (γ t) (velocity γ t) (velocity γ t)))

/-- A future-infinite timelike worldline (an "observer") starting at parameter `a`:
future-directed timelike on every `[a, b]`, with infinite proper time to the future. -/
def IsFutureInfiniteTimelike (W : ℝ → M) (a : ℝ) : Prop :=
  (∀ b, a < b → st.IsFutureTimelikeCurveOn W a b) ∧
  Tendsto (fun b => st.properTime W a b) atTop atTop

/-- A future-directed null geodesic ray starting at `W a` whose affine parameter is
infinite to the future: `W` is a geodesic on `(a, ∞)`, continuous from the right at `a`,
with future-directed null velocity. -/
def IsFutureInfiniteNullRay (W : ℝ → M) (a : ℝ) : Prop :=
  st.IsGeodesicOn W (Ioi a) ∧ ContinuousWithinAt W (Ici a) a ∧
  ∀ t > a, st.IsFutureNull (W t) (velocity W t)

end LorentzianMetric

end WallGSL


