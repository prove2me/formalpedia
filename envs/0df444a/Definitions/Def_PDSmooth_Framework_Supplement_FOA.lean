-- Prove2me | Definitions.Def_PDSmooth_Framework_Supplement_FOA
-- name    : PDSmooth_Framework_Supplement_FOA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:51:00.4879+00:00
-- url     : https://prove2.me/theorems/f61fa46b-0f76-4fab-a921-47f0335d5dbe
-- title:
--   Definition 5.1, p. 21 — (δ, L̄)-first-order approximation (inexact oracle) of h at u
-- statement:
--   Let $h$ be a real function on a normed space $\mathbb U$ and $\mathcal U\subseteq\mathbb U$. For $u\in\mathcal U$, $\delta\ge0$ and $\bar L$, a pair $(\hat h,\hat\nabla h)\in\mathbb R\times\mathbb U^*$ is a **$(\delta,\bar L)$-first-order approximation** ($(\delta,\bar L)$-FOA) of $h$ at $u$ if for every $u'\in\mathcal U$
--
--   $$
--   \hat h+\langle\hat\nabla h,u'-u\rangle\ \le\ h(u')\ \le\ \hat h+\langle\hat\nabla h,u'-u\rangle+\frac{\bar L}{2}\|u'-u\|^2+\delta. \tag{5.7}
--   $$
--
--   This is the inexact model of Devolder, Glineur and Nesterov; Algorithm 2 queries such an approximation at each of its points $u_t$.
--
--   **Formalization Note** The dual vector is a continuous linear functional `UU →L[ℝ] ℝ`, and $\langle\xi,x\rangle$ is `ξ x`.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 21, Definition 5.1, (5.7)

import Mathlib

namespace PDSmooth.Framework.Supplement

/-- Definition 5.1, p. 21: `(ĥ, ĝ) ∈ ℝ × 𝕌*` is a `(δ, L̄)`-first-order approximation (FOA) of `h`
at `u` on `U` if for every `u' ∈ U`,
`ĥ + ⟨ĝ, u' − u⟩ ≤ h(u') ≤ ĥ + ⟨ĝ, u' − u⟩ + (L̄/2)‖u' − u‖² + δ` (5.7). -/
def IsFOA {UU : Type*} [NormedAddCommGroup UU] [NormedSpace ℝ UU]
    (h : UU → ℝ) (U : Set UU) (δ Lbar : ℝ) (u : UU) (hh : ℝ) (g : UU →L[ℝ] ℝ) : Prop :=
  ∀ u' ∈ U, hh + g (u' - u) ≤ h u' ∧ h u' ≤ hh + g (u' - u) + Lbar / 2 * ‖u' - u‖ ^ 2 + δ

end PDSmooth.Framework.Supplement


