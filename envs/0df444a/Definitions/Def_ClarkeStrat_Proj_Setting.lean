-- Prove2me | Definitions.Def_ClarkeStrat_Proj_Setting
-- name    : ClarkeStrat_Proj_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:35.280605+00:00
-- url     : https://prove2.me/theorems/43a50c4e-1347-4afd-98fd-98a46379aa32
-- title:
--   §2–§3, pp. 557–561 — singular and Clarke subdifferentials (5)–(6), C^p stratifications, Whitney-(a), nonverticality (H), the stratum gradient
-- statement:
--   This module fixes the objects of §2–§3 of Bolte, Daniilidis, Lewis and Shiota.
--
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$, with domain $\operatorname{dom} f=\{x: f(x)<+\infty\}$. The Fréchet subdifferential $\hat\partial f(x)$ of (1) and the limiting subdifferential $\partial f(x)$ of (4) are the published definitions `IsRegularSubgrad` and `LimitingSubdiff`.
--
--   1. **Graph and projection.** $\Pi:\mathbb R^{n+1}\to\mathbb R^n$, $\Pi(x_1,\dots,x_n,t)=(x_1,\dots,x_n)$, drops the last coordinate; $(x,t)\in\mathbb R^{n+1}$ is the point with last coordinate $t$; $e_{n+1}=(0,\dots,0,1)$. The graph is $\operatorname{Graph} f=\{(x,f(x)):x\in\operatorname{dom} f\}$.
--   2. **Singular limiting subdifferential** (5), p. 558. For $x\in\operatorname{dom} f$, $y^*\in\partial^\infty f(x)$ iff there are $y_k\to x$ with $f(y_k)\to f(x)$, $y_k^*\in\hat\partial f(y_k)$ and $t_k\searrow 0^+$ with $t_ky_k^*\to y^*$. It is empty off $\operatorname{dom} f$.
--   3. **Clarke subdifferential** (6), Definition 1, p. 559:
--   $$\partial^\circ f(x)=\begin{cases}\overline{\operatorname{co}}\,\{\partial f(x)+\partial^\infty f(x)\} & x\in\operatorname{dom} f,\\ \emptyset & x\notin\operatorname{dom} f,\end{cases}$$
--   where $\overline{\operatorname{co}}$ is the closed convex hull.
--   4. **Gap of subspaces** (p. 560). $D(V,W)=\max\{\sup_{v\in V,\|v\|=1}d(v,W),\ \sup_{w\in W,\|w\|=1}d(w,V)\}$; $V_k\to V$ means $D(V_k,V)\to0$.
--   5. **$C^p$ stratification** (p. 560). A family $(X_i)_{i\in I}$ is a $C^p$ stratification of a nonempty set $X$ if the $X_i$ are $C^p$ submanifolds, pairwise disjoint, with union $X$, locally finite (each point of $X$ has a neighbourhood meeting finitely many $X_i$), and satisfy the frontier condition: for $i\neq j$, $\overline{X_i}\cap X_j\neq\emptyset\Rightarrow X_j\subset\overline{X_i}\setminus X_i$.
--   6. **Whitney-(a)** (p. 560). For $i\neq j$, $x\in\overline{X_i}\cap X_j$ and $x_k\in X_i$ with $x_k\to x$ and $T_{x_k}X_i\to\mathcal T$, one has $T_xX_j\subset\mathcal T$. A Whitney stratification is a $C^1$ stratification with this property.
--   7. **Nonverticality** (H), p. 561: $e_{n+1}\notin T_uS_i$ for every stratum $S_i$ of $\operatorname{Graph} f$ and $u\in S_i$.
--   8. **Stratum gradient** (p. 561). For a stratum $S$ of $\operatorname{Graph} f$ and $u=(x,f(x))\in S$, set $T_xX_x:=\Pi(T_uS)$. A vector $g\in\mathbb R^n$ is the gradient $\nabla_R f(x)$ of $f$ relative to the stratum if $g\in T_xX_x$ and every $w\in T_uS$ has last coordinate $\langle g,\Pi w\rangle$, i.e. $(g,-1)\perp T_uS$: the tangent space of the stratum is the graph of $v\mapsto\langle g,v\rangle$ over $T_xX_x$.
--
--   These objects are the vocabulary of the projection formula (Proposition 4) and of Corollary 5.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\mathbb R\cup\{+\infty\}$ is `EReal`; the graph contains only points over finite values. The tangent space $T_uM$ is the published `tangentSpace` (span of Mathlib's tangent cone), and a $C^p$ submanifold is the published coordinate-slice `IsSubmanifold`; each stratum has some dimension $d$. In the gap, a supremum over an empty unit sphere ($V=\{0\}$) is $0$, which keeps the page's remark $\sup_{v\in V,\|v\|=1}d(v,W)=0\iff V\subset W$. Strata may be empty, and local finiteness is required at points of the stratified set only. The stratum gradient is defined intrinsically from the tangent space of the stratum of the graph, rather than as a derivative of $f$ along the whole projected set $\Pi(S_i)$: the page's claim (8)(i) that $\Pi(S_i)$ is a $C^1$ submanifold holds near each point but can fail globally for discontinuous $f$.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), https://doi.org/10.1137/060670080, pp. 557–561, (1), (4)–(6), Definition 1, §2 Stratification results (p. 560), (H) and (8), Notation (p. 561)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold

open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared ProjLikeRetr.Retractor

namespace ClarkeStrat.Proj

/-- The canonical projection `Π : ℝⁿ⁺¹ → ℝⁿ`, `Π(x₁, …, xₙ, t) = (x₁, …, xₙ)` (p. 561): it drops the
last coordinate. -/
noncomputable def projL (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i : Fin n => z (Fin.castSucc i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The point `(x, t) = (x₁, …, xₙ, t) ∈ ℝⁿ⁺¹`: the value `t` is the last coordinate. -/
noncomputable def lift {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => x i) t)

/-- The last unit vector `e_{n+1} = (0, …, 0, 1) ∈ ℝⁿ⁺¹` (p. 561). -/
noncomputable def eLast (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  EuclideanSpace.single (Fin.last n) (1 : ℝ)

/-- `Graph f = {(x, f(x)) : x ∈ dom f} ⊂ ℝⁿ⁺¹` of `f : ℝⁿ → ℝ ∪ {+∞}`: the points `z` whose last
coordinate is the (finite) value of `f` at `Π z`. Points over `f = +∞` are not in the graph. -/
def graphSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {z | f (projL n z) = ((z (Fin.last n) : ℝ) : EReal)}

/-- The singular limiting subdifferential `∂^∞f(x)` of (5), p. 558: `y ∈ ∂^∞f(x)` iff `x ∈ dom f`
and there are `yₖ → x` with `f(yₖ) → f(x)`, Fréchet subgradients `y*ₖ ∈ ∂̂f(yₖ)`, and `tₖ ↘ 0⁺`
(positive, nonincreasing, tending to `0`) with `tₖ y*ₖ → y`. Empty off `dom f`. -/
def SingularSubdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) (x : E) : Set E :=
  {y | f x ≠ ⊤ ∧ ∃ (ys vs : ℕ → E) (t : ℕ → ℝ),
    Tendsto ys atTop (𝓝 x) ∧ Tendsto (fun k => f (ys k)) atTop (𝓝 (f x)) ∧
    (∀ k, 0 < t k) ∧ Antitone t ∧ Tendsto t atTop (𝓝 0) ∧
    Tendsto (fun k => t k • vs k) atTop (𝓝 y) ∧ ∀ k, IsRegularSubgrad f (ys k) (vs k)}

/-- The Clarke subdifferential `∂°f(x)` of Definition 1, (6), p. 559: the *closed* convex hull of
`∂f(x) + ∂^∞f(x)` if `x ∈ dom f`, and `∅` otherwise. -/
noncomputable def ClarkeSubdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) (x : E) : Set E :=
  if f x = ⊤ then ∅ else closedConvexHull ℝ (LimitingSubdiff f x + SingularSubdiff f x)

/-- The gap `D(V, W)` of two linear subspaces (p. 560):
`max {sup_{v ∈ V, ‖v‖ = 1} d(v, W), sup_{w ∈ W, ‖w‖ = 1} d(w, V)}`. Both suprema are of sets bounded
by `1`; the supremum over an empty unit sphere (`V = 0`) is `0`. -/
noncomputable def subspaceGap {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (V W : Submodule ℝ F) : ℝ :=
  max (sSup ((fun v => Metric.infDist v (W : Set F)) '' {v | v ∈ V ∧ ‖v‖ = 1}))
    (sSup ((fun w => Metric.infDist w (V : Set F)) '' {w | w ∈ W ∧ ‖w‖ = 1}))

/-- A `C^p` stratification `(X_i)_{i ∈ I}` of a nonempty set `X` (p. 560): a locally finite
partition of `X` into `C^p` submanifolds `X_i` such that, for `i ≠ j`,
`cl(X_i) ∩ X_j ≠ ∅ ⟹ X_j ⊂ cl(X_i) \ X_i`. Each stratum is a `C^p` submanifold of some dimension
`d`; local finiteness is read at the points of `X`. -/
def IsCpStratification {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {I : Type*} (p : ℕ) (X : Set F) (S : I → Set F) : Prop :=
  X.Nonempty ∧
  (∀ i, ∃ d : ℕ, IsSubmanifold p d (S i)) ∧
  Pairwise (fun i j => Disjoint (S i) (S j)) ∧
  (⋃ i, S i) = X ∧
  (∀ x ∈ X, ∃ U ∈ 𝓝 x, {i | (S i ∩ U).Nonempty}.Finite) ∧
  (∀ i j, i ≠ j → (closure (S i) ∩ S j).Nonempty → S j ⊆ closure (S i) \ S i)

/-- The Whitney-(a) property (p. 560): for `i ≠ j`, `x ∈ cl(X_i) ∩ X_j` and every sequence
`xₖ ∈ X_i` with `xₖ → x` and `T_{xₖ}X_i → 𝒯` (in the gap `D`), one has `T_x X_j ⊂ 𝒯`. -/
def WhitneyA {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {I : Type*}
    (S : I → Set F) : Prop :=
  ∀ i j, i ≠ j → ∀ x ∈ closure (S i) ∩ S j, ∀ (xs : ℕ → F) (T : Submodule ℝ F),
    (∀ k, xs k ∈ S i) → Tendsto xs atTop (𝓝 x) →
    Tendsto (fun k => subspaceGap (tangentSpace (S i) (xs k)) T) atTop (𝓝 0) →
    tangentSpace (S j) x ≤ T

/-- Nonverticality (H), p. 561: `e_{n+1} ∉ T_u S_i` for every `i` and every `u ∈ S_i`. -/
def IsNonvertical {n : ℕ} {I : Type*} (S : I → Set (EuclideanSpace ℝ (Fin (n + 1)))) : Prop :=
  ∀ i, ∀ u ∈ S i, eLast n ∉ tangentSpace (S i) u

/-- `T_x X_x := Π(T_u S)`, the tangent space at `x = Π u` of the projected stratum `X = Π(S)` (8),
p. 561, read through the tangent space of the stratum `S` of the graph at `u = (x, f(x))`. -/
noncomputable def tangentX {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (u : EuclideanSpace ℝ (Fin (n + 1))) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  (tangentSpace S u).map (projL n : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))

/-- `g` is the stratum gradient `∇_R f(x)` (p. 561) of `f` at `x`, relative to the stratum `S` of
`Graph f` through `u = (x, f(x))`: `g ∈ T_x X_x = Π(T_u S)` and every tangent vector `w ∈ T_u S`
has last coordinate `⟨g, Π w⟩`, i.e. `(g, −1) ⊥ T_u S`. -/
def IsStratumGrad {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (u : EuclideanSpace ℝ (Fin (n + 1))) (g : EuclideanSpace ℝ (Fin n)) : Prop :=
  g ∈ tangentX S u ∧ ∀ w ∈ tangentSpace S u, w (Fin.last n) = ⟪g, projL n w⟫_ℝ

end ClarkeStrat.Proj


