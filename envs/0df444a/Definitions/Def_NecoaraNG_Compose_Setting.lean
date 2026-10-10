-- Prove2me | Definitions.Def_NecoaraNG_Compose_Setting
-- name    : NecoaraNG_Compose_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:17.641418+00:00
-- url     : https://prove2.me/theorems/389a2b61-c452-4413-8d9e-60cd5d9c00da
-- title:
--   (P), (1), (10), (17), (22), Hoffman inequality, (38), pp. 3–17 — polyhedra, nearest points, Hoffman constants and the relaxed classes
-- statement:
--   The objects of §4 of Necoara, Nesterov and Glineur, on $\mathbb R^n$ with the Euclidean inner product $\langle u,v\rangle=u^Tv$ and the Euclidean norm.
--
--   1. **Optimal set.** For $X\subseteq\mathbb R^n$ and $f:\mathbb R^n\to\mathbb R$, $X^*=\{x\in X: f(x)\le f(y)\ \forall y\in X\}$.
--   2. **Nearest point.** $p$ is a nearest point of $S$ to $u$, written $p=[u]_S$, when $p\in S$ and $\|u-p\|\le\|u-z\|$ for all $z\in S$.
--   3. **Polyhedron.** For a linear map $C:\mathbb R^n\to\mathbb R^p$ and $d\in\mathbb R^p$, $X=\{x: Cx\le d\}$, componentwise; $[v]_+$ is the componentwise positive part, $([v]_+)_i=\max(v_i,0)$.
--   4. **Hoffman constants.** $\theta>0$ is a Hoffman constant for $\{z: Az=t,\ Cz\le d\}$ when, for every $x\in\mathbb R^n$ and every nearest point $\bar x$ of that polyhedron to $x$,
--   $$\|x-\bar x\|\le\theta\,\left\|\begin{bmatrix}Ax-t\\ [Cx-d]_+\end{bmatrix}\right\|=\theta\sqrt{\|Ax-t\|^2+\|[Cx-d]_+\|^2}.$$
--   Two variants are used: for the affine set $\{z: Az=t\}$, $\|x-\bar x\|\le\theta\|Ax-t\|$ (the constant $\theta(A,0)$ of Theorem 9); and for $\{z: Az=t,\ c^Tz=s,\ Cz\le d\}$, $\|x-\bar x\|\le\theta\sqrt{\|Ax-t\|^2+(c^Tx-s)^2+\|[Cx-d]_+\|^2}$ (the constant $\theta(A,c,C)$ of Theorem 10).
--   5. **Lipschitz gradient (1)** on $X$ with constant $L$: $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y\in X$.
--   6. **Quasi-strong convexity (10)**, **quadratic gradient growth (17)** and **quadratic functional growth (22)** with constant $\kappa$: for every $x\in X$ and $\bar x=[x]_{X^*}$, respectively
--   $$f^*\ge f(x)+\langle\nabla f(x),\bar x-x\rangle+\tfrac\kappa2\|x-\bar x\|^2,\qquad \langle\nabla f(x)-\nabla f(\bar x),x-\bar x\rangle\ge\kappa\|x-\bar x\|^2,\qquad f(x)-f^*\ge\tfrac\kappa2\|x-\bar x\|^2.$$
--
--   These are the definitions under which Theorems 8–10 place compositions $g(Ax)$ (plus a linear term) in the classes $q\mathcal S_{L_f,\kappa_f}$, $\mathcal G_{L_f,\kappa_f}$ and $\mathcal F_{L_f,\kappa_f}$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, and $A$, $C$ are continuous linear maps, so $\|A\|$ is the operator (spectral) norm. The projection is a predicate, never a choice function, and $f^*$ is written $f(\bar x)$, which is exact because $\bar x\in X^*$. The Hoffman inequality is used with Euclidean norms on both sides ($\alpha=\beta=2$), as in the proofs of Theorems 8–10. The class predicates are stated separately from convexity and (1), which the theorems list as separate conjuncts.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, pp. 3, 5, 7, 8, 12–17: (P), (1), Definitions 1, 3, 4, Hoffman inequality (pp. 12–13), (38), (42)

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

namespace NecoaraNG.Compose

open scoped InnerProductSpace

/-- The polyhedral set `X = {x ∈ ℝⁿ : Cx ≤ d}` of (38) and (42), the inequality read
componentwise. -/
def polyhedron {n p : ℕ} (C : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E p) (d : NecoaraNG.Chain.E p) : Set (NecoaraNG.Chain.E n) :=
  {x | ∀ i, C x i ≤ d i}

/-- The componentwise positive part `[v]₊`, with `([v]₊)ᵢ = max(vᵢ, 0)`. -/
def posPart {p : ℕ} (v : NecoaraNG.Chain.E p) : NecoaraNG.Chain.E p :=
  WithLp.toLp 2 (fun i => max (v i) 0)

/-- Hoffman inequality (p. 13, Euclidean norms) for the polyhedron
`{z : Az = t, Cz ≤ d}` with constant `θ`: for every `x ∈ ℝⁿ` and every nearest point `x̄` of
that polyhedron to `x`,
`‖x - x̄‖ ≤ θ ‖[Ax - t; [Cx - d]₊]‖`, the stacked vector's Euclidean norm being
`√(‖Ax - t‖² + ‖[Cx - d]₊‖²)`. -/
def IsHoffmanConst {n m p : ℕ} (A : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E m) (C : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E p) (t : NecoaraNG.Chain.E m) (d : NecoaraNG.Chain.E p)
    (θ : ℝ) : Prop :=
  ∀ x xbar, NecoaraNG.Chain.IsNearest {z | A z = t ∧ ∀ i, C z i ≤ d i} x xbar →
    ‖x - xbar‖ ≤ θ * Real.sqrt (‖A x - t‖ ^ 2 + ‖posPart (C x - d)‖ ^ 2)

/-- Hoffman inequality for the affine set `{z : Az = t}` (no inequalities, the constant
`θ(A, 0)` of Theorem 9): `‖x - x̄‖ ≤ θ ‖Ax - t‖` for every `x` and every nearest point `x̄`. -/
def IsHoffmanConstEq {n m : ℕ} (A : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E m) (t : NecoaraNG.Chain.E m) (θ : ℝ) : Prop :=
  ∀ x xbar, NecoaraNG.Chain.IsNearest {z | A z = t} x xbar → ‖x - xbar‖ ≤ θ * ‖A x - t‖

/-- Hoffman inequality for the polyhedron `{z : Az = t, cᵀz = s, Cz ≤ d}` (the constant
`θ(A, c, C)` of Theorem 10): `‖x - x̄‖ ≤ θ ‖[Ax - t; cᵀx - s; [Cx - d]₊]‖` for every `x` and
every nearest point `x̄`, the stacked norm being `√(‖Ax - t‖² + (cᵀx - s)² + ‖[Cx - d]₊‖²)`. -/
def IsHoffmanConstLin {n m p : ℕ} (A : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E m) (c : NecoaraNG.Chain.E n) (C : NecoaraNG.Chain.E n →L[ℝ] NecoaraNG.Chain.E p)
    (t : NecoaraNG.Chain.E m) (s : ℝ) (d : NecoaraNG.Chain.E p) (θ : ℝ) : Prop :=
  ∀ x xbar, NecoaraNG.Chain.IsNearest {z | A z = t ∧ ⟪c, z⟫_ℝ = s ∧ ∀ i, C z i ≤ d i} x xbar →
    ‖x - xbar‖ ≤ θ * Real.sqrt (‖A x - t‖ ^ 2 + (⟪c, x⟫_ℝ - s) ^ 2 + ‖posPart (C x - d)‖ ^ 2)

/-- Lipschitz continuity (1) of the gradient on `X` with constant `L`:
`‖∇f x - ∇f y‖ ≤ L ‖x - y‖` for all `x, y ∈ X`. -/
def LipGradOn {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (f : NecoaraNG.Chain.E n → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

end NecoaraNG.Compose


