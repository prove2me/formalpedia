-- Prove2me | Definitions.Def_OnlineLearningOCO_Winnow_OMDDuality
-- name    : OnlineLearningOCO_Winnow_OMDDuality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:28.729446+00:00
-- url     : https://prove2.me/theorems/5b82f704-32ac-4b22-9d35-13d482237180
-- title:
--   Restricted Fenchel conjugate $R^\star$, Online Mirror Descent iterates and the Bregman divergence (2.12) (§2.6–2.7, pp. 142–148)
-- statement:
--   Let $E$ be a real inner product space with inner product $\langle\cdot,\cdot\rangle$. This file fixes three objects used in the duality analysis of Online Mirror Descent (OMD).
--
--   1. **Restricted Fenchel conjugate.** For a set $S\subseteq E$ and a function $R:E\to\mathbb R$ (understood as $+\infty$ off $S$), the conjugate is
--   $$R^\star(\theta)=\sup_{w\in S}\bigl(\langle w,\theta\rangle-R(w)\bigr),\qquad \theta\in E.$$
--
--   2. **OMD iterates.** Given a link function $g:E\to E$ and linear losses $z_1,z_2,\dots\in E$, OMD starts from $\theta_1=0$, predicts $w_t=g(\theta_t)$ and updates $\theta_{t+1}=\theta_t-z_t$, so that
--   $$w_t=g(-z_{1:t-1}),\qquad z_{1:t-1}=\sum_{s=1}^{t-1}z_s .$$
--
--   3. **Bregman divergence.** For a function $F:E\to\mathbb R$ with gradient map $G=\nabla F$, equation (2.12) defines
--   $$D_F(a\,\|\,b)=F(a)-\bigl(F(b)+\langle G(b),a-b\rangle\bigr).$$
--
--   These are the ingredients of Lemma 2.20, which writes the regret of OMD with link $g=\nabla R^\star$ through Bregman divergences of $R^\star$.
--
--   **Formalization Note** The conjugate is a real supremum over the subtype $S$; it equals the paper's $R^\star$ when the set of values is nonempty and bounded above, and every statement using it assumes that the supremum is attained (which gives both). Rounds are numbered from $0$: `omdIterate g z t` is $g\bigl(-\sum_{s<t}z_s\bigr)$, so index $0$ is the paper's $w_1$. The Bregman divergence takes the gradient map as an explicit argument; it is the paper's $D_F$ when that map is $\nabla F$, which the theorems assume through `HasGradientAt`.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 142 (OMD box), p. 146 (§2.7.1 Fenchel conjugate), p. 148 (Bregman divergence (2.12)), p. 149 (§2.7.3, w_t = g(−z_{1:t−1}))

import Mathlib

namespace OnlineLearningOCO.Winnow

open Finset
open scoped InnerProductSpace

/-- The Fenchel conjugate of `R` restricted to the set `S` (Shalev-Shwartz, *Online Learning and
Online Convex Optimization*, §2.7.1, p. 146, with `R = +∞` off `S`):
`conjOn S R θ = sup_{w ∈ S} (⟪w, θ⟫ - R w)`.
The real supremum is the paper's `R⋆(θ)` whenever the set of values is nonempty and bounded above;
every statement using it carries hypotheses that guarantee this. -/
noncomputable def conjOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (R : E → ℝ) (θ : E) : ℝ :=
  ⨆ w : S, (⟪(w : E), θ⟫_ℝ - R w)

/-- The Online Mirror Descent iterate with link function `g` on the linear losses `z`
(§2.6, p. 142): `θ₁ = 0`, `θ_{t+1} = θ_t - z_t`, `w_t = g(θ_t) = g(-z_{1:t-1})`.
Rounds are numbered from `0`: `omdIterate g z t = g (-(∑_{s<t} z s))`, so `omdIterate g z 0 = g 0`
is the paper's `w₁`. -/
def omdIterate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (z : ℕ → E) (t : ℕ) : E :=
  g (-(∑ s ∈ range t, z s))

/-- The Bregman divergence (2.12), p. 148, of a function `F` whose gradient map is `G`:
`D_F(a ‖ b) = F a - (F b + ⟪G b, a - b⟫)`. It is the paper's `D_F` when `G = ∇F`. -/
def bregmanDiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → ℝ) (G : E → E) (a b : E) : ℝ :=
  F a - (F b + ⟪G b, a - b⟫_ℝ)

end OnlineLearningOCO.Winnow


