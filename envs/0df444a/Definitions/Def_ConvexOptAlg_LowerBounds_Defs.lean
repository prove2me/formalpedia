-- Prove2me | Definitions.Def_ConvexOptAlg_LowerBounds_Defs
-- name    : ConvexOptAlg_LowerBounds_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:24:58.17056+00:00
-- url     : https://prove2.me/theorems/d88b9780-92f4-4012-a532-59de896be20f
-- title:
--   §3.5, pp. 280–282 — black-box procedures (3.15), subgradients, Lipschitz and strongly convex functions, the tridiagonal A_k, f_k and x*_k
-- statement:
--   This file fixes the objects of §3.5 (*Lower bounds*) of Bubeck, *Convex Optimization: Algorithms and Complexity*. Throughout, $\mathbb R^n$ is Euclidean space with inner product $x^\top y$, coordinates $x(1),\dots,x(n)$ and canonical basis $e_1,\dots,e_n$; $\mathrm B_2(R)=\{x\in\mathbb R^n:\|x\|\le R\}$.
--
--   1. **Subgradient** (Definition 1.2, p. 235, with constraint set $\mathbb R^n$). A vector $g$ is a subgradient of $f:\mathbb R^n\to\mathbb R$ at $x$ if $f(x)-f(y)\le g^\top(x-y)$ for every $y\in\mathbb R^n$. This is the published definition `ShorNonsmooth.AlmostDiff.IsSubgradient`, which this file imports.
--   2. **$L$-Lipschitz on $\mathcal X$** (§3.1, p. 263). Every subgradient $g\in\partial f(x)$ at every $x\in\mathcal X$ has $\|g\|\le L$.
--   3. **$\alpha$-strongly convex** (§3.4, p. 276). The map $x\mapsto f(x)-\frac\alpha2\|x\|^2$ is convex; the book states this as equivalent to the improved subgradient inequality (3.13).
--   4. **$\beta$-smooth** (§3.2, p. 266). The gradient map $g=\nabla f$ is $\beta$-Lipschitz: $\|g(x)-g(y)\|\le\beta\|x-y\|$.
--   5. **Black-box procedure satisfying (3.15)** (p. 280). The oracle answers a query $x_s$ with $g_s=g(x_s)$. The query sequence satisfies
--   $$x_1=0,\qquad x_{t+1}\in\mathrm{Span}(g_1,\dots,g_t)\quad\text{for every }t\ge0 .$$
--   6. **The tridiagonal matrix $A_k$** (proof of Theorem 3.14, p. 282). For $k\le n$, $A_k\in\mathbb R^{n\times n}$ has entries
--   $$(A_k)_{i,j}=\begin{cases}2,& i=j,\ i\le k\\ -1,& j\in\{i-1,i+1\},\ i\le k,\ j\ne k+1\\ 0,&\text{otherwise.}\end{cases}$$
--   7. **The functions $f_k$ and points $x^*_k$** (p. 282). $f_k(x)=\frac\beta8x^\top A_kx-\frac\beta4x^\top e_1$, and $x^*_k(i)=1-\frac{i}{k+1}$ for $i=1,\dots,k$, $x^*_k(i)=0$ for $i>k$.
--
--   These are the objects of the oracle lower bounds of §3.5: the hard smooth instance of Theorem 3.14 is $f_{2t+1}$, and (3.15) is the class of methods the lower bounds cover.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, so coordinates are 0-based in Lean: the book's $x(i)$ is `coord x i`, the `Fin n` entry $i-1$ (and $0$ out of range), and $e_i$ is `basisVec n i`. In `tridiag` the book's indices $i,j$ become `Fin n` indices $a=i-1$, $b=j-1$. The query sequence is indexed from $1$ as in the book; index $0$ is unused. The oracle is a fixed map $g$, so $g_s=g(x_s)$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.5, Eq. (3.15), p. 280; proof of Theorem 3.14, p. 282; Definition 1.2, p. 235; §3.1, p. 263; §3.2, p. 266; §3.4, p. 276

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient

open scoped InnerProductSpace

namespace ConvexOptAlg.LowerBounds

/-- Bubeck, §3.1, p. 263: `f` is **`L`-Lipschitz on `X`** in the book's sense: every subgradient
`g ∈ ∂f(x)` at every point `x ∈ X` has `‖g‖ ≤ L`. Subgradients are those of Definition 1.2
(p. 235) with constraint set `ℝⁿ`, `f(x) − f(y) ≤ gᵀ(x − y)` for all `y`, which is the published
`ShorNonsmooth.AlmostDiff.IsSubgradient` (`f y − f x ≥ ⟪g, y − x⟫` for all `y`). -/
def IsLipschitzOnBySubgrad {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (L : ℝ) : Prop :=
  ∀ x ∈ X, ∀ gx, ShorNonsmooth.AlmostDiff.IsSubgradient f x gx → ‖gx‖ ≤ L

/-- Bubeck, §3.4, p. 276: `f` is **`α`-strongly convex** on `ℝⁿ`, in the form the book states as
equivalent to (3.13) for non-differentiable `f`: `x ↦ f(x) − (α/2)‖x‖²` is convex. -/
def IsStronglyConvex {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ) : Prop :=
  ConvexOn ℝ Set.univ (fun x => f x - α / 2 * ‖x‖ ^ 2)

/-- β-smoothness (Bubeck, §3.2, p. 266): the gradient map `g` is β-Lipschitz,
`‖∇f(x) − ∇f(y)‖ ≤ β‖x − y‖` for all `x, y ∈ ℝⁿ`. That `g` is the gradient of `f` is stated
separately (`HasGradientAt`). (Redefined here; the same notion appears in other missions of this
book.) -/
def IsBetaSmooth {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) :
    Prop :=
  ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖

/-- Bubeck, §3.5, p. 280, assumption (3.15) on the black-box procedure. The oracle answers the
query `x_s` with `g (x_s)` (a subgradient, or for smooth `f` the gradient). The query sequence
`x` (first query `x 1`; index `0` unused) satisfies (3.15) if `x₁ = 0` and, for every `t ≥ 0`,
`x_{t+1} ∈ Span(g(x₁), …, g(x_t))` (for `t = 0` the span is `{0}`). -/
def SatisfiesSpanCondition {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 1 = 0 ∧ ∀ t : ℕ, x (t + 1) ∈ Submodule.span ℝ ((fun s => g (x s)) '' Set.Icc 1 t)

/-- The book's 1-based coordinate `x(i)` of `x ∈ ℝⁿ` (`i = 1, …, n`), i.e. the `Fin n` entry
`i − 1`; it is `0` for `i = 0` or `i > n` (never used out of range below). -/
noncomputable def coord {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ n then x ⟨i - 1, by omega⟩ else 0

/-- The canonical basis vector `e_i` of `ℝⁿ` (1-based, `i = 1, …, n`): the `Fin n` entry `j`
is `1` if `j + 1 = i` and `0` otherwise. -/
noncomputable def basisVec (n : ℕ) (i : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j : Fin n => if (j : ℕ) + 1 = i then (1 : ℝ) else 0)

/-- Bubeck, proof of Theorem 3.14, p. 282: the symmetric tridiagonal matrix `A_k ∈ ℝ^{n×n}`,
`(A_k)_{i,j} = 2` if `i = j, i ≤ k`; `−1` if `j ∈ {i − 1, i + 1}, i ≤ k, j ≠ k + 1`; `0` otherwise
(book indices `i, j ∈ {1, …, n}`). Translation to `Fin n`: book index `i` is the `Fin n` index
`a = i − 1`, so `i ≤ k ↔ a < k`, `j = i ± 1 ↔ b = a ± 1`, `j ≠ k + 1 ↔ b ≠ k`. -/
def tridiag (n k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b =>
    if (a : ℕ) = b ∧ (a : ℕ) < k then 2
    else if ((b : ℕ) + 1 = a ∨ (b : ℕ) = (a : ℕ) + 1) ∧ (a : ℕ) < k ∧ (b : ℕ) ≠ k then -1
    else 0

/-- The quadratic form `xᵀ A x` of a matrix `A ∈ ℝ^{n×n}` at `x ∈ ℝⁿ`. -/
def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  dotProduct x.ofLp (A.mulVec x.ofLp)

/-- Bubeck, proof of Theorem 3.14, p. 282: `f_k(x) = (β/8) xᵀA_k x − (β/4) xᵀe₁`. The function of
Theorem 3.14 is `f = f_{2t+1}`. -/
noncomputable def fK (n : ℕ) (β : ℝ) (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  β / 8 * quadForm (tridiag n k) x - β / 4 * ⟪x, basisVec n 1⟫_ℝ

/-- Bubeck, proof of Theorem 3.14, p. 282: the point `x*_k ∈ ℝⁿ` with `x*_k(i) = 1 − i/(k+1)` for
`i = 1, …, k` and `x*_k(i) = 0` for `i > k` (book indices; `Fin n` entry `j` is book index
`j + 1`). -/
noncomputable def xstarK (n k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j : Fin n =>
    if (j : ℕ) + 1 ≤ k then 1 - ((j : ℕ) + 1 : ℝ) / ((k : ℝ) + 1) else 0)

end ConvexOptAlg.LowerBounds


