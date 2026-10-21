-- Prove2me | Definitions.Def_AccelMM_BTMap_Framework
-- name    : AccelMM_BTMap_Framework
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:38.918639+00:00
-- url     : https://prove2.me/theorems/d1b6fe78-518e-400c-a441-d42d78e5847d
-- title:
--   §2, p. 7 and §4.1, pp. 11–12 — smoothness, strong convexity, PL inequality on a set, 𝒳₀, majorant surrogates, P_d
-- statement:
--   The general first-order framework of the paper, for a function $f:\mathbb R^n\to\mathbb R$ on Euclidean space $\mathbb R^n$ (indexed by $\{0,\dots,n-1\}$), a set $\mathcal X\subseteq\mathbb R^n$ and constants $\mu,\gamma$.
--
--   1. **$\mu$-smoothness on $\mathcal X$** (p. 7): $\nabla f$ is $\mu$-Lipschitz on $\mathcal X$,
--   $$\|\nabla f(x)-\nabla f(y)\|\le\mu\|x-y\|\qquad\text{for all }x,y\in\mathcal X.$$
--   2. **$\gamma$-strong convexity on $\mathcal X$** (p. 7), in the paper's subgradient form: for all $x,y\in\mathcal X$,
--   $$f(x)-f(y)\le\nabla f(x)^\top(x-y)-\frac{\gamma}{2}\|x-y\|^2 .$$
--   3. **The $\gamma$-PL inequality on $\mathcal X$** relative to a point $x^*$ (eq. (2.12)): for all $x\in\mathcal X$,
--   $$f(x)-f(x^*)\le\frac{1}{2\gamma}\|\nabla f(x)\|^2 .$$
--   4. **The set $\mathcal X_0$** of (4.3) for a direction $d\in\mathbb R^n$: $\mathcal X_0=\mathcal X\cap\{x:\nabla f(x)^\top d=0\}$.
--   5. **Majorant surrogate** (p. 6): $g(x;y)$ majorizes $f$ if $f(x)\le g(x;y)$ and $f(x)=g(x;x)$ for all $x,y$.
--   6. **The projection** $P_d=I-\frac{1}{\|d\|^2}dd^\top$ of Lemma 4.1.
--
--   These are the hypotheses of the general convergence results of §4.1 (Lemma 4.1 and Theorem 4.2), stated for an arbitrary objective so that they can be applied to the Bradley–Terry MAP problem.
--
--   **Formalization Note** $\nabla f$ is Mathlib's `gradient`, which is $0$ at points where $f$ is not differentiable; every theorem that uses these predicates assumes the differentiability it needs. In the PL predicate, $x^*$ is a parameter; that it minimizes $f$ is a separate hypothesis of each theorem, as in the paper ("where $x^*$ is a minimizer of $f$"). $1/(2\gamma)$ is $0$ at $\gamma=0$, so the theorems assume $\gamma>0$, as (2.12) does. $P_d$ uses $1/\|d\|^2$, which is $0$ at $d=0$; Lemma 4.1 assumes $d\ne0$.
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), pp. 6–7, 11–12, (2.12), (4.3), Lemma 4.1

import Mathlib

namespace AccelMM.BTMap

open scoped InnerProductSpace

/-- The parameter space `ℝⁿ` with the Euclidean norm, indexed by `Fin n` (0-based). -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- §2, p. 7: `f` is `μ`-smooth on `X` if `∇f` is `μ`-Lipschitz on `X`. -/
def SmoothOn {n : ℕ} (f : E n → ℝ) (X : Set (E n)) (μ : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ μ * ‖x - y‖

/-- §2, p. 7: `f` is `γ`-strongly convex on `X` in the paper's subgradient form:
`f(x) − f(y) ≤ ∇f(x)ᵀ(x − y) − (γ/2)‖x − y‖²` for all `x, y ∈ X`. -/
def StronglyConvexOn {n : ℕ} (f : E n → ℝ) (X : Set (E n)) (γ : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, f x - f y ≤ ⟪gradient f x, x - y⟫_ℝ - γ / 2 * ‖x - y‖ ^ 2

/-- (2.12), p. 7: the `γ`-PL inequality on `X`, relative to the point `xstar`
(that `xstar` is a minimizer of `f` is a separate hypothesis wherever this is used). -/
def PLOn {n : ℕ} (f : E n → ℝ) (X : Set (E n)) (γ : ℝ) (xstar : E n) : Prop :=
  ∀ x ∈ X, f x - f xstar ≤ 1 / (2 * γ) * ‖gradient f x‖ ^ 2

/-- (4.3), p. 11: `X₀ = X ∩ {x : ∇f(x)ᵀd = 0}`. -/
def X0 {n : ℕ} (f : E n → ℝ) (X : Set (E n)) (d : E n) : Set (E n) :=
  X ∩ {x | ⟪gradient f x, d⟫_ℝ = 0}

/-- §2, p. 6: `g` is a majorant surrogate function of `f`:
`f(x) ≤ g(x; y)` and `f(x) = g(x; x)` for all `x` and `y`. -/
def IsMajorant {n : ℕ} (g : E n → E n → ℝ) (f : E n → ℝ) : Prop :=
  ∀ x y, f x ≤ g x y ∧ f x = g x x

/-- Lemma 4.1, p. 12: `P_d = I − (1/‖d‖²) d dᵀ`. -/
noncomputable def projD {n : ℕ} (d : E n) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (1 / ‖d‖ ^ 2) • Matrix.vecMulVec d.ofLp d.ofLp

end AccelMM.BTMap


