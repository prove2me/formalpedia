-- Prove2me | Definitions.Def_KarimiPL_Prox_Setting
-- name    : KarimiPL_Prox_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:11.555986+00:00
-- url     : https://prove2.me/theorems/f9d4503d-9e19-4fd8-b45d-298e5e1525db
-- title:
--   §4, (12)–(14), p. 8 and (27), p. 17 — the proximal-gradient model, $\mathcal D_g$, the proximal-PL inequality, proximal-gradient runs, and $\mathcal R_g$
-- statement:
--   Let $f, g : \mathbb R^d \to \mathbb R$, write $F = f + g$ for the composite objective of problem (11), and let $\nabla f$ denote the gradient of $f$. This file fixes the objects of Section 4 and Appendix E of Karimi, Nutini and Schmidt.
--
--   1. **The proximal model.** For a base point $x$, a parameter $\alpha$ and a trial point $y$,
--   $$
--   m_{x,\alpha}(y) = \langle \nabla f(x), y - x\rangle + \frac{\alpha}{2}\|y - x\|^2 + g(y) - g(x),
--   $$
--   the bracket of (13).
--
--   2. **The function $\mathcal D_g$** of (13):
--   $$
--   \mathcal D_g(x, \alpha) = -2\alpha \inf_{y \in \mathbb R^d} m_{x,\alpha}(y).
--   $$
--
--   3. **The proximal-PL inequality** (12) with modulus $\mu$ about the value $F^*$: for every $x \in \mathbb R^d$,
--   $$
--   \mu\,\bigl(F(x) - F^*\bigr) \le \tfrac12\,\mathcal D_g(x, L).
--   $$
--
--   4. **A run of the proximal-gradient method** (14) with step size $1/L$: a sequence $(x_k)_{k \ge 0}$ such that each $x_{k+1}$ minimizes $y \mapsto m_{x_k, L}(y)$ over $\mathbb R^d$. The starting point $x_0$ is arbitrary.
--
--   5. **The proximal residual function** (27): for $x, a \in \mathbb R^d$ and $\lambda$,
--   $$
--   \mathcal R_g(\lambda, x, a) = \inf_{y \in \mathbb R^d}\Bigl[\|\lambda(y - x) + a\|^2 + 2\lambda\bigl(g(y) - g(x)\bigr)\Bigr].
--   $$
--
--   These are the objects in which Theorem 5 (linear convergence of the proximal-gradient method) and the lemmas of Appendices E and F are stated.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and $\nabla f$ is Mathlib's `gradient f`. The paper's $\min_y$ is written as a real infimum `⨅ y`. A real infimum of a set that is not bounded below has the junk value $0$ in Lean, so $\mathcal D_g$ and $\mathcal R_g$ agree with the paper only when the infimum is finite; for convex real-valued $g$ and a positive parameter it is a minimum (the companion theorems `exists_isMinOn_proxModel` and `exists_isMinOn_Rg`), and every theorem of the mission uses $\mathcal D_g$ and $\mathcal R_g$ only under those hypotheses. $g$ is real-valued, so indicator functions of convex sets (which take the value $+\infty$) are outside the formal scope. The proximal-PL predicate takes $F^*$ as a parameter; the theorems instantiate it at $F(x^*)$ for a minimizer $x^*$ of $F$. The argument order of $\mathcal R_g$ in Lean is $(g, x, a, \lambda)$.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, §4, (11)–(14), p. 8; Appendix E, (26)–(27), p. 17

import Mathlib

namespace KarimiPL.Prox

open InnerProductSpace

/-- The bracket of (13), Karimi–Nutini–Schmidt, arXiv:1608.04636v4, p. 8:
`⟨∇f(x), y − x⟩ + (α/2)‖y − x‖² + g(y) − g(x)`. -/
noncomputable def proxModel {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (α : ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⟪gradient f x, y - x⟫_ℝ + α / 2 * ‖y - x‖ ^ 2 + g y - g x

/-- (13), p. 8: `D_g(x, α) = −2α min_y [⟨∇f(x), y − x⟩ + (α/2)‖y − x‖² + g(y) − g(x)]`.
The minimum is written as a real infimum; for convex real-valued `g` and `α > 0` the
infimum is attained (see `KarimiPL.Prox.exists_isMinOn_proxModel`). -/
noncomputable def Dg {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (α : ℝ) : ℝ :=
  -2 * α * ⨅ y, proxModel f g x α y

/-- The proximal-PL inequality (12), p. 8, about the value `Fstar`:
`(1/2) D_g(x, L) ≥ μ (F(x) − F*)` for every `x`, with `F = f + g`. -/
def ProxPL {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ) (L μ Fstar : ℝ) : Prop :=
  ∀ x, μ * (f x + g x - Fstar) ≤ 1 / 2 * Dg f g x L

/-- A run of the proximal-gradient method (14), p. 8, with step `1/L`: every iterate
`x (k + 1)` minimizes `y ↦ proxModel f g (x k) L y`. -/
def IsProxGradRun {d : ℕ} (f g : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ k y, proxModel f g (x k) L (x (k + 1)) ≤ proxModel f g (x k) L y

/-- The proximal residual function (27), Appendix E, p. 17 (the page's argument order is
`R_g(λ, x, a)`): `R_g(λ, x, a) = min_y [‖λ(y − x) + a‖² + 2λ(g(y) − g(x))]`, written as a
real infimum; for convex real-valued `g` and `λ > 0` it is attained
(see `KarimiPL.Prox.exists_isMinOn_Rg`). -/
noncomputable def Rg {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (x a : EuclideanSpace ℝ (Fin d)) (lam : ℝ) : ℝ :=
  ⨅ y, ‖lam • (y - x) + a‖ ^ 2 + 2 * lam * (g y - g x)

end KarimiPL.Prox


