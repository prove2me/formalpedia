-- Prove2me | Definitions.Def_RandomGradFree_Shared_oracle
-- name    : RandomGradFree_Shared_oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:49:39.161807+00:00
-- url     : https://prove2.me/theorems/d0df2220-300f-4046-bcba-e2d3ac379431
-- title:
--   Random gradient-free oracle $B^{-1}g_\mu(x)$, with its limit $B^{-1}g_0(x)$ (Eq. (30))
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $f : E \to \mathbb R$, $x \in E$, and let $u \in E$ be a direction (in the methods, a sample of the standard Gaussian vector). For a smoothing parameter $\mu$, the **random gradient-free oracle** returns the vector
--
--   $$
--   B^{-1}g_\mu(x) = \begin{cases} \dfrac{f(x+\mu u) - f(x)}{\mu}\, u, & \mu \neq 0,\\[2mm] f'(x,u)\, u, & \mu = 0, \end{cases}
--   $$
--
--   where $f'(x,u) = \lim_{\alpha\downarrow 0}\frac{1}{\alpha}[f(x+\alpha u)-f(x)]$ is the directional derivative of $f$ at $x$ along $u$ (Eq. (23)). The first line is the finite-difference oracle $g_\mu$ (item 1 of (30)); the second is the limiting oracle $g_0$ (item 3 of (30)).
--
--   The oracle needs only function values (or one directional derivative) and is an unbiased estimate of $\nabla f_\mu(x)$; it is the step direction of the random gradient method $\mathcal{RG}_\mu$ and of the accelerated method $\mathcal{FG}_\mu$.
--
--   It serves chunk 02-smooth-random-search (p. 536, Eq. (30) items 1 and 3; used in Eq. (21) pp. 534-535, Theorem 4.2 (35) p. 538, method $\mathcal{RG}_\mu$ (54) p. 546) and chunk 03-accelerated-random-search (p. 536; used in Eq. (21) pp. 534-535, Lemma 5 (37) p. 539, method $\mathcal{FG}_\mu$ (60) p. 548).
--
--   **Formalization Note** The paper's oracle $g_\mu(x) = \frac{f(x+\mu u)-f(x)}{\mu}Bu$ is a dual vector; the Lean definition returns $B^{-1}g_\mu(x)$, which is the vector used in the methods' updates, and $\|g_\mu(x)\|_* = \|B^{-1}g_\mu(x)\|$. At $\mu = 0$ the directional derivative is Eq. (23), $f'(x,u) = \lim_{\alpha\downarrow 0}\frac{1}{\alpha}[f(x+\alpha u)-f(x)]$, written as `limUnder (𝓝[>] 0)`; Section 2 assumes this limit exists at every $x$ and $u$ (otherwise `limUnder` returns an unspecified value). Where $f$ is differentiable it equals `fderiv ℝ f x u`. The case split avoids the junk value $(f(x)-f(x))/0 = 0$.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 536, Section 3, Eq. (30), items 1 and 3

import Mathlib

namespace RandomGradFree.Shared

/-- The random gradient-free oracle of Nesterov–Spokoiny, Eq. (30), already multiplied by
`B⁻¹`, evaluated at the direction `u`. For `μ ≠ 0` it is item 1,
`B⁻¹ g_μ(x) = ((f(x + μ u) - f(x)) / μ) • u`; for `μ = 0` it is item 3, the limiting oracle
`B⁻¹ g_0(x) = f'(x, u) • u`, where `f'(x, u) = lim_{α ↓ 0} (f(x + α u) - f(x)) / α` is the
one-sided directional derivative of Eq. (23) (it equals `fderiv ℝ f x u` wherever `f` is
differentiable). -/
noncomputable def oracle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (μ : ℝ) (x u : E) : E :=
  if μ = 0 then
    Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (fun α : ℝ => (f (x + α • u) - f x) / α) • u
  else ((f (x + μ • u) - f x) / μ) • u

end RandomGradFree.Shared


