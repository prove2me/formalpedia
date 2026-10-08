-- Prove2me | Definitions.Def_SDCA_Lipschitz_conj
-- name    : SDCA_Lipschitz_conj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:09:11.797419+00:00
-- url     : https://prove2.me/theorems/d3f9ee4a-6261-474f-8f80-ec7518f8680b
-- title:
--   The convex conjugate $\phi^*(u)=\sup_z(zu-\phi(z))$ of a scalar function, and its sub-differential
-- statement:
--   Let $\phi:\mathbb R\to\mathbb R$. Its **convex conjugate** is the extended-real function
--   $$\phi^*(u)=\sup_{z\in\mathbb R}\bigl(zu-\phi(z)\bigr)\in(-\infty,+\infty],\qquad u\in\mathbb R .$$
--   The paper writes $\max_z$; the supremum may be $+\infty$ (for an $L$-Lipschitz $\phi$ it is $+\infty$ whenever $|u|>L$, Lemma 3), and it is never $-\infty$, since $z=0$ contributes $-\phi(0)$.
--
--   The **sub-differential** of $\phi$ at $a\in\mathbb R$ is the set of slopes of supporting lines,
--   $$\partial\phi(a)=\{g\in\mathbb R:\ \phi(a)+g(z-a)\le\phi(z)\ \text{for all } z\in\mathbb R\}.$$
--
--   The conjugates $\phi_i^*$ define the dual problem (2) solved by stochastic dual coordinate ascent, and sub-gradients $-u\in\partial\phi_i(w^\top x_i)$ appear in the analysis (Lemma 1).
--
--   **Formalization Note** The conjugate is an `EReal`-valued `⨆` over all of $\mathbb R$, so it is a genuine supremum and takes the value $\top=+\infty$ where the paper's $\max$ is unbounded; a real-valued supremum would silently return $0$ there.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, p. 2 (convex conjugate, sub-differential) and p. 12 (notation ∂φᵢ(a))

import Mathlib

namespace SDCA.Lipschitz

/-- The convex conjugate `φ*(u) = sup_z (z u − φ(z))` of a scalar function `φ : ℝ → ℝ`
(Shalev-Shwartz–Zhang, arXiv:1209.1873v2, p. 2, where it is written `max_z (zu − φ(z))`).
It is computed in `EReal`, so the supremum is genuine and equals `⊤` where the expression is
unbounded above (e.g. outside `[−L, L]` for an `L`-Lipschitz `φ`, Lemma 3). It is never `⊥`:
the term `z = 0` gives `−φ(0)`. -/
noncomputable def conj (φ : ℝ → ℝ) (u : ℝ) : EReal :=
  ⨆ z : ℝ, ((z * u - φ z : ℝ) : EReal)

/-- The sub-differential `∂φ(a)` of a scalar function `φ : ℝ → ℝ` at `a` (p. 2 and p. 12): the
set of slopes `g` with `φ(a) + g (z − a) ≤ φ(z)` for every `z`. -/
def subdiff (φ : ℝ → ℝ) (a : ℝ) : Set ℝ :=
  {g : ℝ | ∀ z : ℝ, φ a + g * (z - a) ≤ φ z}

end SDCA.Lipschitz


