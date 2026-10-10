-- Prove2me | Definitions.Def_NecoaraNG_FGM_Setting
-- name    : NecoaraNG_FGM_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:21.853593+00:00
-- url     : https://prove2.me/theorems/a1e700d6-fb13-41ca-9409-ada2e685daf9
-- title:
--   (P), (10), (FGM), (55), pp. 3–24 — optimal set, nearest points, quasi-strong convexity on ℝⁿ, the fast gradient run and the estimate functions
-- statement:
--   This file fixes the objects of the linear-convergence analysis of the fast gradient method (FGM) for quasi-strongly convex problems.
--
--   Throughout, $\mathbb{R}^n$ carries the Euclidean inner product $\langle u, v\rangle = u^\top v$ and norm $\|u\|$. Problem (P) is $f^* = \min_{x \in X} f(x)$, where $X \subseteq \mathbb{R}^n$ is closed and convex and $f$ is convex with $L_f$-Lipschitz gradient.
--
--   1. **Optimal set.** $X^* = \{x \in X : f(x) \le f(y) \text{ for all } y \in X\}$.
--   2. **Nearest point.** For a set $S$ and a point $u$, $p$ is a nearest point of $u$ in $S$ (written $p = [u]_S$) if $p \in S$ and $\|u - p\| \le \|u - z\|$ for every $z \in S$.
--   3. **Quasi-strong convexity on all of $\mathbb{R}^n$.** $f$ satisfies, for every $x \in \mathbb{R}^n$ and every nearest point $\bar x = [x]_{X^*}$,
--   $$f^* \ge f(x) + \langle \nabla f(x), \bar x - x\rangle + \frac{\kappa}{2}\|x - \bar x\|^2,$$
--   where $f^* = f(\bar x)$. This is inequality (10) of Definition 1, required at every point of $\mathbb{R}^n$ instead of only at points of $X$.
--   4. **A run of (FGM) with parameter $\beta$.** Sequences $(x^k)_{k\ge 0}$, $(y^k)_{k \ge 0}$ with $x^0 = y^0 \in X$ and, for every $k \ge 0$,
--   $$x^{k+1} = \Big[y^k - \tfrac{1}{L_f}\nabla f(y^k)\Big]_X, \qquad y^{k+1} = x^{k+1} + \beta\,(x^{k+1} - x^k).$$
--   5. **The sequence $\lambda_k$ of Lemma 1.** For $(\alpha_k)_{k \ge 0}$: $\lambda_0 = 1$ and $\lambda_{k+1} = (1 - \alpha_k)\lambda_k$.
--   6. **The estimate functions (55).** For sequences $x, y$ and $(\alpha_k)$, with $g(y^k) = L_f(y^k - x^{k+1})$ the gradient mapping at $y^k$:
--   $$\phi_0(z) = f(y^0) + \frac{\kappa}{2}\|z - y^0\|^2,$$
--   $$\phi_{k+1}(z) = (1 - \alpha_k)\phi_k(z) + \alpha_k\Big(f(x^{k+1}) + \frac{1}{2L_f}\|g(y^k)\|^2 + \langle g(y^k), z - y^k\rangle + \frac{\kappa}{2}\|z - y^k\|^2\Big).$$
--
--   These are the objects of Section 5.2.1 of the paper; the initial data are $\gamma_0 = \kappa$, $v^0 = y^0$ and $\phi_0^* = f(y^0)$.
--
--   **Formalization Note** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. The projection is the predicate `IsNearest`, never a choice function. Quasi-strong convexity, smoothness and convexity are assumed on all of $\mathbb{R}^n$ (in the theorems) because inequality (54) is used at the extrapolated points $y^k$, which may lie outside $X$; for $X = \mathbb{R}^n$ this is exactly the paper's hypothesis. The estimate function $\phi_k$ is defined for arbitrary sequences; its link to the projected step is a hypothesis of each theorem. The minimum $\phi_k^*$ is never defined as an infimum: statements write $f(x^k) \le \phi_k(z)$ for all $z$.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, pp. 3, 5, 23–24, problem (P), Definition 1 (10), Algorithm (FGM), Lemma 1 (55)

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

namespace NecoaraNG.FGM

open scoped InnerProductSpace

/-- Quasi-strong convexity (10) with constant `κ`, required at **every** `x ∈ ℝⁿ` (not only
`x ∈ X`): for `x̄ = [x]_{X*}`, `f* ≥ f x + ⟪∇f x, x̄ - x⟫ + κ/2 ‖x - x̄‖²`, with `f* = f x̄`.
The strengthening is needed because (54) is applied at the extrapolated points `y^k` of (FGM),
which may lie outside `X`; for `X = ℝⁿ` it is exactly (10). -/
def QuasiStrongEverywhere {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (f : NecoaraNG.Chain.E n → ℝ) (κ : ℝ) : Prop :=
  ∀ x xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xbar →
    f x + ⟪gradient f x, xbar - x⟫_ℝ + κ / 2 * ‖x - xbar‖ ^ 2 ≤ f xbar

/-- A run of the fast gradient method (FGM) with constant parameter `β`:
`x⁰ = y⁰ ∈ X`, and for every `k ≥ 0`, `x^{k+1} = [y^k - (1/L_f) ∇f(y^k)]_X` and
`y^{k+1} = x^{k+1} + β (x^{k+1} - x^k)`. -/
def IsFGMRun {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (f : NecoaraNG.Chain.E n → ℝ) (Lf β : ℝ) (x y : ℕ → NecoaraNG.Chain.E n) : Prop :=
  x 0 ∈ X ∧ y 0 = x 0 ∧ ∀ k : ℕ,
    NecoaraNG.Chain.IsNearest X (y k - (1 / Lf) • gradient f (y k)) (x (k + 1)) ∧
      y (k + 1) = x (k + 1) + β • (x (k + 1) - x k)

/-- The sequence `λ_k` of Lemma 1: `λ₀ = 1`, `λ_{k+1} = (1 - α_k) λ_k`. -/
def lam (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (1 - α k) * lam α k

/-- The estimate functions `φ_k` of Lemma 1, (55): `φ₀(z) = f(y⁰) + κ/2 ‖z - y⁰‖²`
(`γ₀ = κ`, `v⁰ = y⁰`, `φ₀* = f(y⁰)`), and
`φ_{k+1}(z) = (1 - α_k) φ_k(z) + α_k (f(x^{k+1}) + 1/(2L_f) ‖g(y^k)‖² + ⟪g(y^k), z - y^k⟫
+ κ/2 ‖z - y^k‖²)`, where `g(y^k) = L_f (y^k - x^{k+1})` is the gradient mapping at `y^k`
(the sequences are such that `x^{k+1} = [y^k - (1/L_f)∇f(y^k)]_X`). -/
noncomputable def phi {n : ℕ} (f : NecoaraNG.Chain.E n → ℝ) (Lf κ : ℝ) (α : ℕ → ℝ) (x y : ℕ → NecoaraNG.Chain.E n) : ℕ → NecoaraNG.Chain.E n → ℝ
  | 0, z => f (y 0) + κ / 2 * ‖z - y 0‖ ^ 2
  | k + 1, z => (1 - α k) * phi f Lf κ α x y k z +
      α k * (f (x (k + 1)) + 1 / (2 * Lf) * ‖Lf • (y k - x (k + 1))‖ ^ 2 +
        ⟪Lf • (y k - x (k + 1)), z - y k⟫_ℝ + κ / 2 * ‖z - y k‖ ^ 2)

end NecoaraNG.FGM


