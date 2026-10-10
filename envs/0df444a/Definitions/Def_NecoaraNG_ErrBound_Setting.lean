-- Prove2me | Definitions.Def_NecoaraNG_ErrBound_Setting
-- name    : NecoaraNG_ErrBound_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:20.541334+00:00
-- url     : https://prove2.me/theorems/17c3ff71-059a-472e-a777-f7c9629571be
-- title:
--   Gradient mapping (p. 10) and Definition 5, (31), p. 11 — the projected gradient step x⁺ and the global error bound
-- statement:
--   This file adds two objects of Necoara, Nesterov and Glineur to the shared setting of the paper (the space $\mathbb R^n$, the optimal set $X^*$ and the nearest-point relation $p=[u]_S$, defined in the imported module `NecoaraNG.Chain.Setting`).
--
--   Work in $\mathbb R^n$ with the Euclidean inner product and norm. Let $X\subseteq\mathbb R^n$, let $f$ be a function with gradient $\nabla f$, and let $X^*=\{x\in X:\ f(x)\le f(y)\ \text{for all } y\in X\}$ be the optimal set of $\min_{x\in X}f(x)$.
--
--   1. **Projected gradient step and gradient mapping (p. 10).** For $L_f>0$ and a point $x$, a point $x^+$ is the projected gradient step from $x$ if
--   $$x^+=\bigl[x-\tfrac1{L_f}\nabla f(x)\bigr]_X,$$
--   that is, $x^+$ is a nearest point of $X$ to $x-\tfrac1{L_f}\nabla f(x)$. The gradient mapping is $g(x)=L_f\,(x-x^+)$.
--   2. **Global error bound (31), Definition 5 (p. 11)** with constant $\kappa$: for every $x\in X$, every $\bar x=[x]_{X^*}$ and every projected gradient step $x^+$ from $x$,
--   $$\|g(x)\|\ \ge\ \kappa\,\|x-\bar x\| .$$
--
--   The paper's class $\mathcal E_{L_f,\kappa_f}(X)$ consists of the convex functions with $L_f$-Lipschitz gradient on $X$ that satisfy (31) with some $\kappa_f>0$. Theorems 6 and 7 compare it with the quadratic functional growth class $\mathcal F_{L_f,\kappa_f}(X)$, whose inequality (22) is `NecoaraNG.Chain.QuadFunGrowth`; the feasible descent methods of §5.3 are analysed under (31).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. Both projections are predicates (`IsNearest`, and `IsPGStep` for $x^+$), never choice functions; (31) is required for every nearest point $\bar x$ and every step $x^+$. When $X$ is nonempty, closed and convex and $X^*\ne\emptyset$ both points exist and are unique, so this is the same as "the" points; the theorems that use (31) assume these standing hypotheses of p. 3. The page defines $g$ at every $x\in\mathbb R^n$; so does `IsPGStep`, and (31) restricts to $x\in X$ as on p. 11. The predicate records only the inequality with its constant: convexity, the Lipschitz condition (1) and $L_f,\kappa>0$ are hypotheses of each theorem.
-- source:
--   Necoara, Nesterov & Glineur, Linear convergence of first order methods for non-strongly convex optimization, arXiv:1504.06298v4, p. 10 (gradient mapping g(x) = L_f(x − x⁺), x⁺ = [x − 1/L_f ∇f(x)]_X), p. 11 Definition 5 (31)

import Mathlib
import Definitions.Def_NecoaraNG_Chain_Setting

namespace NecoaraNG.ErrBound

open scoped InnerProductSpace

/-- `xp` is the projected gradient step `x⁺ = [x − (1/L_f) ∇f(x)]_X` from `x` (p. 10). The
gradient mapping of the paper is then `g(x) = L_f (x − x⁺)`, written `Lf • (x - xp)`. -/
def IsPGStep {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (f : NecoaraNG.Chain.E n → ℝ) (Lf : ℝ) (x xp : NecoaraNG.Chain.E n) : Prop :=
  NecoaraNG.Chain.IsNearest X (x - (1 / Lf) • gradient f x) xp

/-- Global error bound (31), Definition 5 (p. 11), with constant `κ`: for every `x ∈ X`,
`x̄ = [x]_{X*}` and projected gradient step `x⁺`, `‖g(x)‖ ≥ κ ‖x − x̄‖` where
`g(x) = L_f (x − x⁺)` is the gradient mapping (p. 10). -/
def ErrorBound {n : ℕ} (X : Set (NecoaraNG.Chain.E n)) (f : NecoaraNG.Chain.E n → ℝ) (Lf κ : ℝ) : Prop :=
  ∀ x ∈ X, ∀ xbar, NecoaraNG.Chain.IsNearest (NecoaraNG.Chain.optSet X f) x xbar →
    ∀ xp, IsPGStep X f Lf x xp → κ * ‖x - xbar‖ ≤ ‖Lf • (x - xp)‖

end NecoaraNG.ErrBound


