-- Prove2me | Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
-- name    : QuasiHemiVI_Existence_ClarkeDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:36.642986+00:00
-- url     : https://prove2.me/theorems/8fb99120-b48d-42d2-91b4-3d47109b5dfd
-- title:
--   Clarke generalized directional derivative $J^0(u;v)$ and generalized gradient $\partial J(u)$ (Definition 2.4)
-- statement:
--   Let $X$ be a real normed space with dual $X^*$, and let $J:X\to\mathbb R$. The **generalized (Clarke) directional derivative** of $J$ at $u\in X$ in the direction $v\in X$ is
--
--   $$
--   J^0(u;v)=\limsup_{\lambda\to0^+,\ w\to u}\frac{J(w+\lambda v)-J(w)}{\lambda},
--   $$
--
--   and the **generalized gradient** of $J$ at $u$ is the set
--
--   $$
--   \partial J(u)=\{\xi\in X^*\ :\ J^0(u;v)\ge\langle\xi,v\rangle_{X^*\times X}\ \text{for all } v\in X\}.
--   $$
--
--   For a locally Lipschitz $J$ (Lipschitz on a neighbourhood of every point) the difference quotient is bounded near $(u,0^+)$, so $J^0(u;v)$ is a finite real number. These two objects carry the nonsmooth term $J^0(\gamma u;\gamma(v-u))$ of every hemivariational inequality in the mission.
--
--   **Formalization Note** $J^0(u;v)$ is the real `Filter.limsup` of $(w,\lambda)\mapsto (J(w+\lambda v)-J(w))/\lambda$ along the product filter $\mathcal N(u)\times\mathcal N_{>}(0)$, and $X^*$ is `X →L[ℝ] ℝ`. For a $J$ that is not locally Lipschitz the value is Lean's default and carries no meaning; every statement of the mission that uses $J^0$ or $\partial J$ assumes `LocallyLipschitz J` (Mathlib), which is the paper's hypothesis (HJ).
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1249, Definition 2.4 (and the definition of local Lipschitz continuity preceding it)

import Mathlib

namespace QuasiHemiVI.Existence

open Filter Topology

/-- Clarke's generalized directional derivative (Definition 2.4, p. 1249 of Zeng–Migórski–Khan,
SIAM J. Control Optim. 59(2) (2021)):
`J⁰(u; v) = limsup_{λ → 0+, w → u} (J(w + λ v) - J(w)) / λ`,
the real `limsup` along the filter `𝓝 u ×ˢ 𝓝[>] 0` of the pairs `(w, λ)`.
For a locally Lipschitz `J` the difference quotient is bounded near `(u, 0⁺)`, so this is a
genuine limsup; for other `J` the value is Lean's junk value of `Filter.limsup` and every statement
using it assumes `LocallyLipschitz J`. -/
noncomputable def clarkeDeriv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (J : X → ℝ) (u v : X) : ℝ :=
  limsup (fun p : X × ℝ => (J (p.1 + p.2 • v) - J p.1) / p.2) (𝓝 u ×ˢ 𝓝[>] (0 : ℝ))

/-- Clarke's generalized gradient (Definition 2.4, p. 1249):
`∂J(u) = {ξ ∈ X* | J⁰(u; v) ≥ ⟨ξ, v⟩ for all v ∈ X}`, with `X* = X →L[ℝ] ℝ`. -/
def clarkeGrad {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (J : X → ℝ) (u : X) : Set (X →L[ℝ] ℝ) :=
  {ξ | ∀ v : X, ξ v ≤ clarkeDeriv J u v}

end QuasiHemiVI.Existence


