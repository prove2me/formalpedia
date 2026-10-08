-- Prove2me | Definitions.Def_ClarkeStrat_KL_Setting
-- name    : ClarkeStrat_KL_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:40.798987+00:00
-- url     : https://prove2.me/theorems/be41c9d9-04fd-417c-b30f-8043bc62f45b
-- title:
--   §2–§4, pp. 557–563 — (5)–(6), C^p stratifications, Whitney-(a), (H), o-minimal structures and definability (Definitions 6–7), Riemannian gradient
-- statement:
--   This file fixes the objects of Bolte, Daniilidis, Lewis and Shiota, *Clarke subgradients of stratifiable functions*, used in §4 of the paper. Throughout, $\mathbb R^n$ carries the Euclidean norm $\|\cdot\|$ and inner product $\langle\cdot,\cdot\rangle$, and $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ has domain $\operatorname{dom} f=\{x: f(x)<+\infty\}$.
--
--   1. **Coordinates.** $\mathbb R^{n+1}=\mathbb R^n\times\mathbb R$ with the value in the last coordinate; $\Pi(x_1,\dots,x_n,t)=(x_1,\dots,x_n)$ is the canonical projection, $e_{n+1}=(0,\dots,0,1)$, and $\operatorname{Graph} f=\{(x,f(x)) : x\in\operatorname{dom} f\}$.
--   2. **Singular limiting subdifferential** (5): $y^*\in\partial^\infty f(x)$ iff $x\in\operatorname{dom} f$ and there are $y_k\to x$ with $f(y_k)\to f(x)$, Fréchet subgradients $y_k^*\in\hat\partial f(y_k)$ and $t_k\searrow 0^+$ with $t_k y_k^*\to y^*$. The limiting subdifferential $\partial f$ of (4) and the Fréchet subdifferential $\hat\partial f$ of (1) are the published items `LimitingSubdiff` and `IsRegularSubgrad`.
--   3. **Clarke subdifferential** (Definition 1, (6)):
--   $$\partial^\circ f(x)=\begin{cases}\overline{\mathrm{co}}\,\big(\partial f(x)+\partial^\infty f(x)\big) & x\in\operatorname{dom} f,\\ \emptyset & x\notin\operatorname{dom} f,\end{cases}$$
--   where $\overline{\mathrm{co}}$ is the closed convex hull.
--   4. **Tangent space** $T_xM$ of a set $M$ at $x$: the linear span of the tangent cone of $M$ at $x$. A **$C^p$ submanifold** is a set which near each of its points is the graph of a $C^p$ map between complementary linear subspaces.
--   5. **Gap of subspaces** (p. 560): $D(V,W)=\max\{\sup_{v\in V,\|v\|=1}d(v,W),\ \sup_{w\in W,\|w\|=1}d(w,V)\}$, and $V_k\to V$ means $D(V_k,V)\to 0$.
--   6. **$C^p$ stratification** of $X$ (p. 560): a locally finite partition $(X_i)$ of $X$ into $C^p$ submanifolds with the frontier condition $\overline{X_i}\cap X_j\neq\emptyset\Rightarrow X_j\subset\overline{X_i}\setminus X_i$ for $i\ne j$. It has the **Whitney-(a) property** if, for $x\in\overline{X_i}\cap X_j$ ($i\neq j$) and $x_k\in X_i$ with $x_k\to x$ and $T_{x_k}X_i\to\mathcal T$, one has $T_xX_j\subset\mathcal T$. A stratification $(S_i)$ of a subset of $\mathbb R^{n+1}$ is **nonvertical** (H) if $e_{n+1}\notin T_uS_i$ for all $i$ and $u\in S_i$.
--   7. **O-minimal structure** on $(\mathbb R,+,\cdot)$ (Definition 6): a sequence $(\mathcal O_n)$ of Boolean algebras of subsets of $\mathbb R^n$ such that $A\in\mathcal O_n$ implies $A\times\mathbb R,\ \mathbb R\times A\in\mathcal O_{n+1}$; $A\in\mathcal O_{n+1}$ implies $\Pi(A)\in\mathcal O_n$; $\mathcal O_n$ contains every algebraic set $\{x: p(x)=0\}$, $p$ a polynomial; and the elements of $\mathcal O_1$ are exactly the finite unions of intervals and points.
--   8. **Definability** (Definition 7): $f$ is definable in $\mathcal O$ if $\operatorname{Graph} f\in\mathcal O_{n+1}$. A real function $h$ on a set $D\subseteq\mathbb R^m$ is definable if its graph $\{(x,h(x)):x\in D\}$ belongs to $\mathcal O_{m+1}$.
--   9. **Riemannian gradient** (Remark 7): for $h$ on a set $U$ and $x\in U$, $g=\nabla h(x)$ is the vector of $T_xU$ such that $y\mapsto\langle g,y-x\rangle$ is the derivative of $h$ at $x$ along $U$.
--
--   These are the objects in terms of which the Kurdyka–Łojasiewicz inequalities of §4 are stated.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\mathbb R\cup\{+\infty\}$ is `EReal`; the theorems assume $f\ne-\infty$ everywhere. "Boolean algebra" is encoded as: contains $\emptyset$, closed under complement and binary union. "Finite unions of intervals and points" is encoded as finite unions of order-connected subsets of $\mathbb R$ (intervals of every kind, points, and $\emptyset$). The gap uses the convention $\sup\emptyset=0$ (only relevant for the zero subspace). Empty strata are allowed. A Riemannian gradient is a vector $g$ in the tangent space with `HasFDerivWithinAt h ⟪g, ·⟫ U x`; on a $C^1$ submanifold it is unique.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), pp. 557–563, (1), (4)–(6), Definition 1, §2 Stratification results (p. 560), (H) (p. 561), Definitions 6–7 (p. 563), Remark 7 (p. 567)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open Filter Topology
open scoped Pointwise InnerProductSpace Function
open NonconvexSplitting.Shared

namespace ClarkeStrat.KL

noncomputable section

/-! ### Coordinates on `ℝⁿ⁺¹ = ℝⁿ × ℝ` (value in the last coordinate) -/

/-- The canonical projection `Π : ℝⁿ⁺¹ → ℝⁿ`, `Π(x₁, …, xₙ, t) = (x₁, …, xₙ)` (p. 561). -/
def projL {n : ℕ} : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => z (Fin.castSucc i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The map `ℝⁿ⁺¹ → ℝⁿ` dropping the first coordinate, so that `{z | tailL z ∈ A}` is `ℝ × A`. -/
def tailL {n : ℕ} : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i => z (Fin.succ i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The point `(x, t) ∈ ℝⁿ⁺¹` with `x ∈ ℝⁿ` and last coordinate `t`. -/
def lift {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun i => x i) t)

/-- `e_{n+1} = (0, …, 0, 1) ∈ ℝⁿ⁺¹` (p. 561). -/
def eLast (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single (Fin.last n) (1 : ℝ)

/-- `Graph f = {(x, f x) : x ∈ dom f} ⊆ ℝⁿ⁺¹` for `f : ℝⁿ → ℝ ∪ {+∞}`; it lies over `dom f`. -/
def graphSet {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {z | f (projL z) = ((z (Fin.last n) : ℝ) : EReal)}

/-! ### Subdifferentials (5)–(6) -/

/-- The singular limiting subdifferential `∂^∞ f(x)` of (5), p. 558; empty off `dom f`. -/
def SingularSubdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) (x : E) : Set E :=
  {y | f x ≠ ⊤ ∧ ∃ (ys vs : ℕ → E) (t : ℕ → ℝ), Tendsto ys atTop (𝓝 x) ∧
    Tendsto (fun k => f (ys k)) atTop (𝓝 (f x)) ∧ (∀ k, 0 < t k) ∧ Antitone t ∧
    Tendsto t atTop (𝓝 0) ∧ Tendsto (fun k => t k • vs k) atTop (𝓝 y) ∧
    ∀ k, IsRegularSubgrad f (ys k) (vs k)}

/-- The Clarke subdifferential `∂°f(x) = co̅ (∂f(x) + ∂^∞f(x))` of Definition 1 (6), p. 559
(closed convex hull), and `∅` off `dom f`. -/
def ClarkeSubdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) (x : E) : Set E :=
  if f x = ⊤ then ∅ else closedConvexHull ℝ (LimitingSubdiff f x + SingularSubdiff f x)

/-! ### Submanifolds, stratifications, Whitney-(a), nonverticality (§2–§3) -/

/-- The tangent space of `M` at `x`: the span of the tangent cone. -/
def tangentSpace {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (M : Set F) (x : F) :
    Submodule ℝ F :=
  Submodule.span ℝ (tangentConeAt ℝ M x)

/-- `M` is a `C^p` submanifold of `F`: near each of its points it is the graph of a `C^p` map
`g : V → W` over a pair of complementary subspaces. -/
def IsCpSubmanifold {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℕ) (M : Set F) :
    Prop :=
  ∀ x ∈ M, ∃ V W : Submodule ℝ F, IsCompl V W ∧ ∃ g : V → W, ContDiff ℝ p g ∧
    ∃ U ∈ 𝓝 x, M ∩ U = {y | ∃ v : V, y = (v : F) + (g v : F)} ∩ U

/-- The gap `D(V, W)` of two subspaces (p. 560); a supremum over an empty unit sphere is `0`. -/
def subspaceGap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (V W : Submodule ℝ F) : ℝ :=
  max (sSup ((fun v => Metric.infDist v (W : Set F)) '' {v | v ∈ V ∧ ‖v‖ = 1}))
    (sSup ((fun w => Metric.infDist w (V : Set F)) '' {w | w ∈ W ∧ ‖w‖ = 1}))

/-- `(S i)_{i ∈ I}` is a `C^p` stratification of `X` (p. 560): a locally finite partition of `X`
into `C^p` submanifolds satisfying the frontier condition. Empty strata are allowed. -/
def IsCpStratification {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {I : Type*}
    (p : ℕ) (X : Set F) (S : I → Set F) : Prop :=
  (∀ i, IsCpSubmanifold p (S i)) ∧ Pairwise (Disjoint on S) ∧ (⋃ i, S i) = X ∧
    (∀ x ∈ X, ∃ U ∈ 𝓝 x, {i | (S i ∩ U).Nonempty}.Finite) ∧
    ∀ i j, i ≠ j → (closure (S i) ∩ S j).Nonempty → S j ⊆ closure (S i) \ S i

/-- The Whitney-(a) property (p. 560). -/
def WhitneyA {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {I : Type*}
    (S : I → Set F) : Prop :=
  ∀ i j, i ≠ j → ∀ x ∈ closure (S i) ∩ S j, ∀ (xs : ℕ → F) (T : Submodule ℝ F),
    (∀ k, xs k ∈ S i) → Tendsto xs atTop (𝓝 x) →
    Tendsto (fun k => subspaceGap (tangentSpace (S i) (xs k)) T) atTop (𝓝 0) →
    tangentSpace (S j) x ≤ T

/-- Nonverticality (H), p. 561: `e_{n+1} ∉ T_u S_i` for every stratum and every `u ∈ S_i`. -/
def IsNonvertical {n : ℕ} {I : Type*} (S : I → Set (EuclideanSpace ℝ (Fin (n + 1)))) : Prop :=
  ∀ i, ∀ u ∈ S i, eLast n ∉ tangentSpace (S i) u

/-! ### O-minimal structures and definability (Definitions 6–7, p. 563) -/

/-- An o-minimal structure on `(ℝ, +, ·)` (Definition 6): Boolean algebras `𝒪ₙ` of subsets of `ℝⁿ`
stable under `A ↦ A × ℝ`, `A ↦ ℝ × A` and the projection `Π`, containing the algebraic sets,
with `𝒪₁` exactly the finite unions of intervals and points. -/
structure OMinimalStructure where
  O : (n : ℕ) → Set (Set (EuclideanSpace ℝ (Fin n)))
  empty_mem : ∀ n, (∅ : Set (EuclideanSpace ℝ (Fin n))) ∈ O n
  compl_mem : ∀ n A, A ∈ O n → Aᶜ ∈ O n
  union_mem : ∀ n A B, A ∈ O n → B ∈ O n → A ∪ B ∈ O n
  prod_right : ∀ n A, A ∈ O n → {z : EuclideanSpace ℝ (Fin (n + 1)) | projL z ∈ A} ∈ O (n + 1)
  prod_left : ∀ n A, A ∈ O n → {z : EuclideanSpace ℝ (Fin (n + 1)) | tailL z ∈ A} ∈ O (n + 1)
  proj_mem : ∀ n A, A ∈ O (n + 1) → (projL '' A : Set (EuclideanSpace ℝ (Fin n))) ∈ O n
  alg_mem : ∀ n (p : MvPolynomial (Fin n) ℝ),
    {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun i => x i) p = 0} ∈ O n
  omin : ∀ A, A ∈ O 1 ↔ ∃ s : Finset (Set ℝ), (∀ J ∈ s, J.OrdConnected) ∧
    (fun x : EuclideanSpace ℝ (Fin 1) => x 0) '' A = ⋃ J ∈ s, J

/-- A real function `h`, considered on `D ⊆ ℝᵐ`, is definable in `O`: its graph over `D` is in `𝒪ₘ₊₁`. -/
def DefinableOn (O : OMinimalStructure) {m : ℕ} (D : Set (EuclideanSpace ℝ (Fin m)))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  {z : EuclideanSpace ℝ (Fin (m + 1)) | projL z ∈ D ∧ z (Fin.last m) = h (projL z)} ∈ O.O (m + 1)

/-- A one-variable real function `ψ`, considered on `D ⊆ ℝ`, is definable in `O`. -/
def DefinableOn1 (O : OMinimalStructure) (D : Set ℝ) (ψ : ℝ → ℝ) : Prop :=
  {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ D ∧ z 1 = ψ (z 0)} ∈ O.O 2

/-- `g` is the Riemannian gradient at `x` of `h` restricted to the set `U` (Remark 7, p. 567):
`g` is tangent to `U` at `x` and `y ↦ ⟨g, y - x⟩` is the derivative of `h` within `U` at `x`. -/
def IsRiemGrad {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n)))
    (x g : EuclideanSpace ℝ (Fin n)) : Prop :=
  g ∈ tangentSpace U x ∧ HasFDerivWithinAt h (innerSL ℝ g) U x

end

end ClarkeStrat.KL


