-- Prove2me | Definitions.Def_NecoaraNG_Chain_Setting
-- name    : NecoaraNG_Chain_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T11:46:18.430612+00:00
-- url     : https://prove2.me/theorems/6d779925-eca4-4a25-9e2f-d214ca511403
-- title:
--   (P), (7), (10), (13), (17), (22), pp. 3–8 — the optimal set, nearest points, and the strong-convexity relaxations
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean inner product $\langle u,v\rangle=u^\top v$ and norm $\|u\|$. For a set $X\subseteq\mathbb R^n$ and a function $f$, the **optimal set** of the problem $\min_{x\in X} f(x)$ is
--   $$X^*=\{x\in X:\ f(x)\le f(y)\ \text{for all } y\in X\}.$$
--   For a set $S$ and a point $u$, a point $p$ is a **nearest point** of $S$ to $u$, written $p=[u]_S$, if $p\in S$ and $\|u-p\|\le\|u-z\|$ for every $z\in S$.
--
--   For a constant $\kappa$ and $\nabla f$ the gradient of $f$, the following five conditions are defined. In conditions 2–5, $x$ ranges over $X$, $\bar x=[x]_{X^*}$ is a nearest point of $X^*$ to $x$, and $f^*=f(\bar x)$ is the optimal value.
--
--   1. **First inequality of (7)** (first-order strong convexity): $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\kappa}{2}\|x-y\|^2$ for all $x,y\in X$.
--   2. **Quasi-strong convexity (10)**: $f^*\ge f(x)+\langle\nabla f(x),\bar x-x\rangle+\frac{\kappa}{2}\|x-\bar x\|^2$.
--   3. **Quadratic under-approximation (13)**: $f(x)\ge f^*+\langle\nabla f(\bar x),x-\bar x\rangle+\frac{\kappa}{2}\|x-\bar x\|^2$.
--   4. **Quadratic gradient growth (17)**: $\langle\nabla f(x)-\nabla f(\bar x),x-\bar x\rangle\ge\kappa\|x-\bar x\|^2$.
--   5. **Quadratic functional growth (22)**: $f(x)-f^*\ge\frac{\kappa}{2}\|x-\bar x\|^2$.
--
--   The paper's classes $\mathcal S_{L_f,\kappa_f}(X)$, $q\mathcal S_{L_f,\kappa_f}(X)$, $\mathcal U_{L_f,\kappa_f}(X)$, $\mathcal G_{L_f,\kappa_f}(X)$, $\mathcal F_{L_f,\kappa_f}(X)$ consist of the convex functions with $L_f$-Lipschitz gradient on $X$ that satisfy condition 1, 2, 3, 4, 5 respectively with constant $\kappa_f>0$. These are the objects compared in Theorem 4.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, abbreviated `E n`. The nearest point $[x]_{X^*}$ is a predicate `IsNearest`, never a choice function: each of conditions 2–5 is required for every nearest point $\bar x$ (when $X$ is closed and convex and $f$ convex and continuous on $X$, $X^*$ is closed and convex, so the nearest point is unique when $X^*\ne\emptyset$). The optimal value $f^*$ is written $f(\bar x)$, which is exact because $\bar x\in X^*$. The constant $\kappa$ is a parameter; its positivity, convexity of $f$, the Lipschitz condition (1) and the nonemptiness of $X^*$ are hypotheses of each theorem, not part of these predicates. `gradient f x` is the gradient of $f$ as a function on all of $\mathbb R^n$; the theorems assume differentiability at every point of $X$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, pp. 2–8, projection [u]_X (pp. 2–3), (P) and (1) (p. 3), (7) (p. 4), Definitions 1–4 with (10), (13), (17), (22) (pp. 5, 5, 7, 8)

import Mathlib

namespace NecoaraNG.Chain

open scoped InnerProductSpace

/-- The Euclidean space `ℝⁿ`, with `⟪u, v⟫_ℝ = uᵀv` and the Euclidean norm. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The optimal set `X* = argmin_{x ∈ X} f x` of problem (P). -/
def optSet {n : ℕ} (X : Set (E n)) (f : E n → ℝ) : Set (E n) :=
  {x | x ∈ X ∧ ∀ y ∈ X, f x ≤ f y}

/-- `p` is a nearest point of `S` to `u`, i.e. `p = [u]_S = argmin_{z ∈ S} ‖z - u‖`. -/
def IsNearest {n : ℕ} (S : Set (E n)) (u p : E n) : Prop :=
  p ∈ S ∧ ∀ z ∈ S, ‖u - p‖ ≤ ‖u - z‖

/-- First inequality of (7) with constant `κ`:
`f y ≥ f x + ⟪∇f x, y - x⟫ + κ/2 ‖x - y‖²` for all `x, y ∈ X`. -/
def StrongIneq {n : ℕ} (X : Set (E n)) (f : E n → ℝ) (κ : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X,
    f x + ⟪gradient f x, y - x⟫_ℝ + κ / 2 * ‖x - y‖ ^ 2 ≤ f y

/-- Quasi-strong convexity (10) with constant `κ`: for `x ∈ X` and `x̄ = [x]_{X*}`,
`f* ≥ f x + ⟪∇f x, x̄ - x⟫ + κ/2 ‖x - x̄‖²`, with `f* = f x̄`. -/
def QuasiStrong {n : ℕ} (X : Set (E n)) (f : E n → ℝ) (κ : ℝ) : Prop :=
  ∀ x ∈ X, ∀ xbar, IsNearest (optSet X f) x xbar →
    f x + ⟪gradient f x, xbar - x⟫_ℝ + κ / 2 * ‖x - xbar‖ ^ 2 ≤ f xbar

/-- Quadratic under-approximation (13) with constant `κ`: for `x ∈ X` and `x̄ = [x]_{X*}`,
`f x ≥ f* + ⟪∇f x̄, x - x̄⟫ + κ/2 ‖x - x̄‖²`, with `f* = f x̄`. -/
def QuadUnder {n : ℕ} (X : Set (E n)) (f : E n → ℝ) (κ : ℝ) : Prop :=
  ∀ x ∈ X, ∀ xbar, IsNearest (optSet X f) x xbar →
    f xbar + ⟪gradient f xbar, x - xbar⟫_ℝ + κ / 2 * ‖x - xbar‖ ^ 2 ≤ f x

/-- Quadratic gradient growth (17) with constant `κ`: for `x ∈ X` and `x̄ = [x]_{X*}`,
`⟪∇f x - ∇f x̄, x - x̄⟫ ≥ κ ‖x - x̄‖²`. -/
def QuadGradGrowth {n : ℕ} (X : Set (E n)) (f : E n → ℝ) (κ : ℝ) : Prop :=
  ∀ x ∈ X, ∀ xbar, IsNearest (optSet X f) x xbar →
    κ * ‖x - xbar‖ ^ 2 ≤ ⟪gradient f x - gradient f xbar, x - xbar⟫_ℝ

/-- Quadratic functional growth (22) with constant `κ`: for `x ∈ X` and `x̄ = [x]_{X*}`,
`f x - f* ≥ κ/2 ‖x - x̄‖²`, with `f* = f x̄`. -/
def QuadFunGrowth {n : ℕ} (X : Set (E n)) (f : E n → ℝ) (κ : ℝ) : Prop :=
  ∀ x ∈ X, ∀ xbar, IsNearest (optSet X f) x xbar →
    κ / 2 * ‖x - xbar‖ ^ 2 ≤ f x - f xbar

end NecoaraNG.Chain


