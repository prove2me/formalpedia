-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_normPenalty
-- name    : RockafellianRelax_Supplement_normPenalty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:15:05.371507+00:00
-- url     : https://prove2.me/theorems/8a516dc3-d44c-415a-b101-91ce48650485
-- title:
--   The penalized function $f_\theta(u,x) = f(u,x) + \theta\|u\|$
-- statement:
--   For $f : \mathbb R^m\times\mathbb R^n \to \overline{\mathbb R}$, a function $\|\cdot\| : \mathbb R^m \to \mathbb R$ (an arbitrary norm in Proposition 3.5) and $\theta \in \mathbb R$, the **penalized function** is
--
--   $$
--   f_\theta(u,x) = f(u,x) + \theta\|u\| .
--   $$
--
--   Proposition 3.5 gives conditions under which it is an exact Rockafellian.
--
--   **Formalization Note** The added term is real, so $f_\theta$ is $\pm\infty$ exactly where $f$ is.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Proposition 3.5, p.8 (definition of f_θ)

import Mathlib

namespace RockafellianRelax.Supplement

/-- **The penalized function `f_θ` of Proposition 3.5.**
Royset, Chen & Eckstrand, arXiv:2204.04762v4, Proposition 3.5, p.8: "the function given by fθ(u, x) = f(u, x) + θ‖u‖".

**Formalization Note.** `N` is the norm `‖·‖` on `ℝᵐ`, passed as a function. The added term is
real, so `f_θ` is `⊤` where `f` is `⊤` and `⊥` where `f` is `⊥`. -/
noncomputable def normPenalty {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (N : (Fin m → ℝ) → ℝ) (θ : ℝ) : (Fin m → ℝ) × (Fin n → ℝ) → EReal :=
  fun z => f z + ((θ * N z.1 : ℝ) : EReal)

end RockafellianRelax.Supplement


