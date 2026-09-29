-- Prove2me | Definitions.Def_RandomGradFree_Nonsmooth_oracle
-- name    : RandomGradFree_Nonsmooth_oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:58:28.37987+00:00
-- url     : https://prove2.me/theorems/b29aa70b-fa8b-457b-a0f6-953a40d1d220
-- title:
--   Random gradient-free oracle $B^{-1}g_\mu(x) = \frac{f(x+\mu u)-f(x)}{\mu}\,u$ (Eq. (30))
-- statement:
--   Let $f : E \to \mathbb R$, $\mu > 0$, a point $x \in E$ and a direction $u \in E$. The **random gradient-free oracle** of Nesterov and Spokoiny returns, for a randomly generated direction $u$, the vector
--
--   $$
--   g_\mu(x) = \frac{f(x+\mu u) - f(x)}{\mu}\, Bu .
--   $$
--
--   This definition records $B^{-1} g_\mu(x)$, the vector actually used in the update of the random search method:
--
--   $$
--   B^{-1}g_\mu(x) = \frac{f(x+\mu u) - f(x)}{\mu}\, u .
--   $$
--
--   Only two function values are needed per call, which is what makes the methods built on it gradient-free.
--
--   **Formalization Note** The direction $u$ is an explicit argument; randomness enters when $u$ is drawn from the standard Gaussian of $E$. With the inner product chosen as $\langle B\cdot,\cdot\rangle$, $E^*$ is identified with $E$ by the Riesz map and $B^{-1}(Bu) = u$. At $\mu = 0$ the formula returns $0$ (Lean division by zero); it is only used with $\mu > 0$.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 536, Section 3, Eq. (30), item 1

import Mathlib

namespace RandomGradFree.Nonsmooth

/-- The random gradient-free oracle of Nesterov–Spokoiny, Eq. (30), item 1, already multiplied
by `B⁻¹`: for a direction `u`, `B⁻¹ g_μ(x) = ((f(x + μ u) - f(x)) / μ) • u`. It is only used
with `μ > 0`. -/
noncomputable def oracle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (μ : ℝ) (x u : E) : E :=
  ((f (x + μ • u) - f x) / μ) • u

end RandomGradFree.Nonsmooth


