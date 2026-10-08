-- Prove2me | Definitions.Def_ConvexOptAlg_StrongGD_Defs
-- name    : ConvexOptAlg_StrongGD_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:00:08.922037+00:00
-- url     : https://prove2.me/theorems/352ffef5-6bcb-484a-b1be-938877cc5ed8
-- title:
--   §§3.2, 3.4 — β-smoothness, gradient descent runs, and the auxiliary function φ
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and let $g$ be its gradient field. The function is **$\beta$-smooth** when $\beta\ge0$ and
--   $$\|g(x)-g(y)\|\le\beta\|x-y\|\qquad(x,y\in\mathbb R^n).$$
--
--   A **gradient descent run** with step size $\eta$ is a sequence with $x_{t+1}=x_t-\eta g(x_t)$ for every $t\ge1$; the initial iterate is $x_1$. The auxiliary function used in Lemma 3.11 is $\phi(z)=f(z)-(\alpha/2)\|z\|^2$.
--
--   These definitions fix the gradient, algorithm, and quadratic shift shared by the chapter's inequalities.
--
--   **Formalization Note** The smoothness predicate requires $g$ to be the actual gradient of $f$ at every point. Index zero of a run is unused.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.2, p. 266; Eq. (3.1), p. 262; proof of Lemma 3.11, p. 279

import Mathlib

open scoped InnerProductSpace

namespace ConvexOptAlg.StrongGD

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The book's β-smoothness: the actual gradient is β-Lipschitz. -/
def IsBetaSmooth {n : ℕ} (f : E n → ℝ) (g : E n → E n) (β : ℝ) : Prop :=
  (∀ x : E n, HasGradientAt f (g x) x) ∧
  0 ≤ β ∧ ∀ x y : E n, ‖g x - g y‖ ≤ β * ‖x - y‖

/-- The unconstrained gradient-descent recurrence, with the book's first iterate at index 1. -/
def IsGDRun {n : ℕ} (g : E n → E n) (η : ℝ) (x : ℕ → E n) : Prop :=
  ∀ t : ℕ, 1 ≤ t → x (t + 1) = x t - η • g (x t)

/-- The auxiliary function φ(z) = f(z) − (α/2)‖z‖² from Lemma 3.11. -/
noncomputable def phi {n : ℕ} (f : E n → ℝ) (α : ℝ) (z : E n) : ℝ :=
  f z - (α / 2) * ‖z‖ ^ 2

end ConvexOptAlg.StrongGD


