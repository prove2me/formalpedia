-- Prove2me | Definitions.Def_PathoSubgrad_Circle_Setting
-- name    : PathoSubgrad_Circle_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:51.893547+00:00
-- url     : https://prove2.me/theorems/0c4bd3fb-5105-43d9-83b2-58bba255a09a
-- title:
--   Definitions 1–5, pp. 1–2 — Clarke subdifferential, subgradient sequence, path differentiability, weak Sard condition, accumulation set, Whitney C^∞ stratifiable functions
-- statement:
--   This file fixes the vocabulary of the paper for functions $f:\mathbb R^n\to\mathbb R$ on Euclidean space.
--
--   1. **Clarke subdifferential.** For $x\in\mathbb R^n$, $\partial^c f(x)$ is the convex envelope of the set of vectors $v$ for which there is a sequence $y_i\to x$ of points where $f$ is differentiable with $\nabla f(y_i)\to v$.
--   2. **Critical set.** $\operatorname{crit} f=\{x : 0\in\partial^c f(x)\}$.
--   3. **Subgradient sequence (Definition 1).** Given a locally Lipschitz $f$ and positive step sizes $\varepsilon_i$ with $\sum_{i\ge0}\varepsilon_i=+\infty$ and $\varepsilon_i\to0$, a sequence $(x_i)_{i\ge0}$ is a subgradient sequence if for every $i\ge0$
--   $$x_{i+1}=x_i-\varepsilon_i v_i\quad\text{for some } v_i\in\partial^c f(x_i).$$
--   4. **Path differentiability (Definition 2).** A locally Lipschitz $f$ is path-differentiable if for every Lipschitz curve $\gamma:\mathbb R\to\mathbb R^n$ and almost every $t\in\mathbb R$, $f\circ\gamma$ is differentiable at $t$ and $(f\circ\gamma)'(t)=v\cdot\gamma'(t)$ for **all** $v\in\partial^c f(\gamma(t))$.
--   5. **Weak Sard condition (Definition 3).** $f$ is constant on each connected component of $\operatorname{crit} f$.
--   6. **Accumulation set.** $\operatorname{acc}\{x_i\}_i$ is the set of points $p$ such that every neighbourhood of $p$ meets the set $\{x_i\}_i$ in infinitely many points.
--   7. **Whitney $C^\infty$ stratifications (Definition 5, $p=+\infty$).** A family $\{X_i\}_{i\in I}$ is a Whitney $C^\infty$ stratification of a nonempty $X\subseteq\mathbb R^m$ if it is a partition of $X$, locally finite, into connected $C^\infty$ submanifolds of $\mathbb R^m$, such that for $i\ne j$
--   $$\overline{X_i}\cap X_j\neq\emptyset\ \Longrightarrow\ X_j\subseteq\overline{X_i}\setminus X_i,$$
--   and Whitney's condition A holds: whenever $i\ne j$, $x\in\overline{X_i}\cap X_j$, $x_k\in X_i$, $x_k\to x$, and the tangent spaces $T_{x_k}X_i$ converge in the Grassmannian to a subspace $V$, then $T_xX_j\subseteq V$. A function $f:\mathbb R^n\to\mathbb R$ is Whitney $C^\infty$-stratifiable if its graph $\{(x,f(x))\}\subseteq\mathbb R^{n+1}$ admits such a stratification.
--
--   These notions are the hypotheses and conclusions of every statement of the mission: the paper's counterexample is a function satisfying 2–7 together with a subgradient sequence that does not converge.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The Clarke subdifferential is the convex hull of the published `almostGradients`, which uses cluster points of $\nabla f(y_k)$ rather than limits; passing to a subsequence shows the two sets coincide. In Definition 2 the a.e. clause also asserts that $\gamma$ is differentiable at $t$, which holds a.e. by Rademacher's theorem and makes $\gamma'(t)$ meaningful. Convergence in the Grassmannian is convergence to $0$ of the gap $\max(\sup_{v\in V,\|v\|=1}\operatorname{dist}(v,W),\sup_{w\in W,\|w\|=1}\operatorname{dist}(w,V))$; this mirrors `ClarkeStrat.Proj.subspaceGap`, which is not available in this workspace. Submanifolds use the published `ProjLikeRetr.Retractor.IsSubmanifold` (a coordinate-slice $C^k$ submanifold of a fixed dimension); "class $C^\infty$" is "class $C^k$ for every $k\in\mathbb N$". Tangent spaces are the published `tangentSpace` (span of the tangent cone). Local finiteness is required at the points of $X$, and the graph puts the value in the last coordinate.
-- source:
--   Ríos-Zertuche, Examples of pathological dynamics of the subgradient method for Lipschitz path-differentiable functions, arXiv:2007.11699v1, pp. 1–2, Clarke subdifferential (p. 1), Definitions 1, 2, 3, 5, accumulation set (p. 2)

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

open Filter Topology MeasureTheory
open scoped InnerProductSpace

namespace PathoSubgrad.Circle

/-- §1, p. 1: the Clarke subdifferential `∂^c f(x)`, the convex envelope of the set of limiting
gradients `lim ∇f(y_i)` along sequences `y_i → x` of points where `f` is differentiable. The
published `almostGradients` takes cluster points of the gradient sequence; passing to a
subsequence shows that this is the same set as the set of limits. -/
noncomputable def clarkeSubdiff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ (ShorNonsmooth.AlmostDiff.almostGradients f x)

/-- Definition 3, p. 2: the critical set `crit f = {x : 0 ∈ ∂^c f(x)}`. -/
def critSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (0 : EuclideanSpace ℝ (Fin n)) ∈ clarkeSubdiff f x}

/-- Definition 1, p. 1 (small-step subgradient method): `f` is locally Lipschitz, the step sizes
`ε_i` are positive with `Σ_{i ≥ 0} ε_i = +∞` and `ε_i → 0`, and `x_{i+1} = x_i − ε_i v_i` for some
`v_i ∈ ∂^c f(x_i)`, for every `i ≥ 0`. -/
def IsSubgradientSeq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (ε : ℕ → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  LocallyLipschitz f ∧ (∀ i, 0 < ε i) ∧
    Tendsto (fun N => ∑ i ∈ Finset.range N, ε i) atTop atTop ∧
    Tendsto ε atTop (𝓝 0) ∧
    ∀ i, ∃ v ∈ clarkeSubdiff f (x i), x (i + 1) = x i - ε i • v

/-- Definition 2, p. 2 (path-differentiable functions): `f` is locally Lipschitz and, for every
Lipschitz curve `γ : ℝ → ℝⁿ`, for almost every `t`, both `f ∘ γ` and `γ` are differentiable at `t`
and `(f ∘ γ)'(t) = v · γ'(t)` for all `v ∈ ∂^c f(γ(t))`. -/
def IsPathDifferentiable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  LocallyLipschitz f ∧
    ∀ γ : ℝ → EuclideanSpace ℝ (Fin n), (∃ K, LipschitzWith K γ) →
      ∀ᵐ t ∂volume, DifferentiableAt ℝ (f ∘ γ) t ∧ DifferentiableAt ℝ γ t ∧
        ∀ v ∈ clarkeSubdiff f (γ t), deriv (f ∘ γ) t = ⟪v, deriv γ t⟫_ℝ

/-- Definition 3, p. 2 (weak Sard condition): `f` is constant on each connected component of
its critical set. -/
def WeakSard {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x ∈ critSet f, ∀ y ∈ connectedComponentIn (critSet f) x, f y = f x

/-- p. 2: the accumulation set `acc{x_i}`, the points `p` such that every neighbourhood `U` of `p`
meets the set `{x_i}_i` in an infinite set. -/
def accSet {n : ℕ} (x : ℕ → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {p | ∀ U ∈ 𝓝 p, (U ∩ Set.range x).Infinite}

/-- The graph `{(x, f(x))} ⊂ ℝ^{n+1}` of `f : ℝⁿ → ℝ`; the value is the last coordinate. -/
def graphSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {z | f (WithLp.toLp 2 (fun i : Fin n => z (Fin.castSucc i))) = z (Fin.last n)}

/-- The gap between two linear subspaces, the usual metric of the Grassmannian:
`max (sup_{v ∈ V, ‖v‖ = 1} dist(v, W), sup_{w ∈ W, ‖w‖ = 1} dist(w, V))`. -/
noncomputable def subspaceGap {m : ℕ} (V W : Submodule ℝ (EuclideanSpace ℝ (Fin m))) : ℝ :=
  max (sSup ((fun v => Metric.infDist v (W : Set (EuclideanSpace ℝ (Fin m)))) ''
      {v | v ∈ V ∧ ‖v‖ = 1}))
    (sSup ((fun w => Metric.infDist w (V : Set (EuclideanSpace ℝ (Fin m)))) ''
      {w | w ∈ W ∧ ‖w‖ = 1}))

/-- Definition 5, p. 2, with `p = +∞`: `S` is a Whitney `C^∞` stratification of the nonempty set
`X ⊆ ℝ^m`: a partition of `X` (pairwise disjoint pieces with union `X`), locally finite at the
points of `X`, into connected submanifolds of class `C^∞` (of class `C^k` for every `k`, of a fixed
dimension `d`); the frontier condition `cl(X_i) ∩ X_j ≠ ∅ ⟹ X_j ⊆ cl(X_i) \ X_i` for `i ≠ j`;
and Whitney's condition A: for `i ≠ j`, `x ∈ cl(X_i) ∩ X_j`, and `x_k ∈ X_i` with `x_k → x` and
`T_{x_k} X_i → V` in the Grassmannian, `T_x X_j ⊆ V`. -/
def IsWhitneyCInfStratification {m : ℕ} {I : Type} (X : Set (EuclideanSpace ℝ (Fin m)))
    (S : I → Set (EuclideanSpace ℝ (Fin m))) : Prop :=
  X.Nonempty ∧
    (⋃ i, S i) = X ∧
    Pairwise (fun i j => Disjoint (S i) (S j)) ∧
    (∀ x ∈ X, ∃ U ∈ 𝓝 x, {i | (S i ∩ U).Nonempty}.Finite) ∧
    (∀ i, IsConnected (S i) ∧ ∃ d : ℕ, ∀ k : ℕ, ProjLikeRetr.Retractor.IsSubmanifold k d (S i)) ∧
    (∀ i j, i ≠ j → (closure (S i) ∩ S j).Nonempty → S j ⊆ closure (S i) \ S i) ∧
    (∀ i j, i ≠ j → ∀ x ∈ closure (S i) ∩ S j, ∀ (xs : ℕ → EuclideanSpace ℝ (Fin m))
      (V : Submodule ℝ (EuclideanSpace ℝ (Fin m))), (∀ k, xs k ∈ S i) →
      Tendsto xs atTop (𝓝 x) →
      Tendsto (fun k => subspaceGap (ProjLikeRetr.Retractor.tangentSpace (S i) (xs k)) V)
        atTop (𝓝 0) →
      ProjLikeRetr.Retractor.tangentSpace (S j) x ≤ V)

/-- Definition 5, p. 2: `f : ℝⁿ → ℝ` is Whitney `C^∞`-stratifiable if its graph, as a subset of
`ℝ^{n+1}`, has a Whitney `C^∞` stratification. -/
def IsWhitneyCInfStratifiable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∃ (I : Type) (S : I → Set (EuclideanSpace ℝ (Fin (n + 1)))),
    IsWhitneyCInfStratification (graphSet f) S

end PathoSubgrad.Circle


