-- Prove2me | Definitions.Def_DiffCtrlRobust_generator
-- name    : DiffCtrlRobust_generator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:32.955671+00:00
-- url     : https://prove2.me/theorems/78e78b1e-8e2b-417a-859c-5c7612b6e45e
-- title:
--   The operator $\mathcal L_\zeta$
-- statement:
--   For $\zeta\in\mathbb U$ and $f\in\mathcal C^2(\mathbb R^d)$,
--
--   $$
--   \mathcal L_\zeta f(x):=\mathrm{Tr}\big(a(x)\nabla^2 f(x)\big)+b(x,\zeta)\cdot\nabla f(x),
--   $$
--
--   with $a=\frac12\sigma\sigma^{\mathsf T}$. Applied to $(b_n,\sigma_n)$ this is $\mathcal L^n_\zeta$ of (2.16). It is the generator of the controlled diffusion with the action frozen at $\zeta$.
--
--   **Formalization Note** $\nabla f(x)\cdot w$ is the Fréchet derivative applied to $w$, and $\partial_i\partial_j f(x)$ is the second iterated derivative on the basis vectors.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, p.7, (2.10), and p.8, (2.16)

import Definitions.Def_DiffCtrlRobust_diffusionMatrix

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- The operator `𝓛_ζ f(x) := Tr(a(x) ∇²f(x)) + b(x, ζ) · ∇f(x)` of (2.10), and `𝓛ⁿ_ζ` of (2.16)
(arXiv:2205.05894v2, p.7 and p.8), with `a = ½ σ σᵀ`.

**Formalization Note.** `∇f(x) · w` is `fderiv ℝ f x w` and `∂ᵢ∂ⱼ f(x)` is
`iteratedFDeriv ℝ 2 f x ![eᵢ, eⱼ]`. -/
noncomputable def generator {d : ℕ} {U : Type*} (b : SDEState d → U → SDEState d)
    (σ : SDEState d → SDEDiffusion d) (ζ : U) (f : SDEState d → ℝ) (x : SDEState d) : ℝ :=
  (∑ i, ∑ j, diffusionMatrix σ x i j *
    iteratedFDeriv ℝ 2 f x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) +
  fderiv ℝ f x (b x ζ)

end DiffCtrlRobust


