-- Prove2me | Definitions.Def_RandomGradFree_Smooth_symOracle
-- name    : RandomGradFree_Smooth_symOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T08:30:49.442979+00:00
-- url     : https://prove2.me/theorems/425b16b1-a265-4eb7-b375-32c63d886122
-- title:
--   Symmetric random gradient-free oracle $B^{-1}\hat g_\mu(x)$ (Eq. (30), item 2)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $f : E \to \mathbb R$, $x, u \in E$, and $\mu > 0$. The **symmetric random gradient-free oracle** returns
--
--   $$
--   B^{-1}\hat g_\mu(x) = \frac{f(x+\mu u) - f(x-\mu u)}{2\mu}\, u .
--   $$
--
--   It is the central-difference counterpart of $g_\mu$; with Gaussian $u$ it is also an unbiased estimate of $\nabla f_\mu(x)$ and has a smaller second moment for smooth $f$.
--
--   **Formalization Note** As for $g_\mu$, the definition returns the primal vector $B^{-1}\hat g_\mu(x)$. It is used only with $\mu > 0$.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 536, Section 3, Eq. (30), item 2

import Mathlib

namespace RandomGradFree.Smooth

/-- The symmetric random gradient-free oracle of Nesterov–Spokoiny, Eq. (30), item 2, already
multiplied by `B⁻¹`: `B⁻¹ ĝ_μ(x) = ((f(x + μ u) - f(x - μ u)) / (2μ)) • u`. It is only used
with `μ > 0`. -/
noncomputable def symOracle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (μ : ℝ) (x u : E) : E :=
  ((f (x + μ • u) - f (x - μ • u)) / (2 * μ)) • u

end RandomGradFree.Smooth


