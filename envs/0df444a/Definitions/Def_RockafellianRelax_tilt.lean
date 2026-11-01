-- Prove2me | Definitions.Def_RockafellianRelax_tilt
-- name    : RockafellianRelax_tilt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:10.788124+00:00
-- url     : https://prove2.me/theorems/305713ac-3820-435f-8355-3ab5d45dbfe8
-- title:
--   Tilted objective $f(u,x) - \langle y, u\rangle$
-- statement:
--   For $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ and $y \in \mathbb R^m$, the **tilted objective** is
--
--   $$
--   (u, x) \mapsto f(u, x) - \langle y, u\rangle .
--   $$
--
--   With $y = \bar y$ it is the objective of the relaxed problem (3.2); with $f = f^\nu$ and $y = y^\nu$ it is the objective of the approximating problem (3.7).
--
--   **Formalization Note** $\langle y, u\rangle$ is the real number `y ⬝ᵥ u`, so the value is $+\infty$ where $f = +\infty$ and $-\infty$ where $f = -\infty$.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, (3.2), p.7 and (3.7), p.9

import Mathlib

namespace RockafellianRelax

/-- **Tilted objective** `(u, x) ↦ f(u, x) − ⟨y, u⟩` of the relaxed problem (3.2) and of the
approximating problem (3.7).
Royset, Chen & Eckstrand, arXiv:2204.04762v4, (3.2), p.7: "minimize_{u∈ℝᵐ,x∈ℝⁿ} f(u, x) − ⟨ȳ, u⟩";
(3.7), p.9: "minimize_{u∈ℝᵐ,x∈ℝⁿ} fν(u, x) − ⟨yν, u⟩".

**Formalization Note.** `⟨y, u⟩` is the real number `y ⬝ᵥ u`, so `f(u, x) − ⟨y, u⟩` is `+∞` where
`f = +∞` and `−∞` where `f = −∞`; no `∞ − ∞` occurs. -/
noncomputable def tilt {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (y : Fin m → ℝ) :
    (Fin m → ℝ) × (Fin n → ℝ) → EReal :=
  fun p => f p - ((y ⬝ᵥ p.1 : ℝ) : EReal)

end RockafellianRelax


