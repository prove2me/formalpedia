-- Prove2me | Definitions.Def_RockafellianRelax_IsRockafellian
-- name    : RockafellianRelax_IsRockafellian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:08.854782+00:00
-- url     : https://prove2.me/theorems/0c80a3a0-5441-4ffd-927b-af9e47a9c9d7
-- title:
--   Rockafellian $f$ for the problem of minimizing $\varphi$
-- statement:
--   Let $\varphi : \mathbb R^n \to \overline{\mathbb R}$ define the **actual problem** $\operatorname{minimize}_{x \in \mathbb R^n} \varphi(x)$ (3.1). A function $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ is a **Rockafellian** for (3.1) if
--
--   $$
--   f(0, x) = \varphi(x) \qquad \forall x \in \mathbb R^n.
--   $$
--
--   The first argument $u$ of $f$ is a perturbation of the actual problem; $u = 0$ recovers it.
--
--   **Formalization Note** $\mathbb R^m \times \mathbb R^n$ is `(Fin m → ℝ) × (Fin n → ℝ)`, values in `EReal`.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §3, p.6

import Mathlib

namespace RockafellianRelax

/-- **Rockafellian** for the actual problem `minimize_{x ∈ ℝⁿ} φ(x)` (3.1).
Royset, Chen & Eckstrand, arXiv:2204.04762v4, §3, p.6: "Generally, a function f : ℝᵐ × ℝⁿ → R̄ is
referred to as a Rockafellian for (3.1) if f(0, x) = φ(x) ∀x ∈ ℝⁿ."

**Formalization Note.** `ℝᵐ × ℝⁿ` is `(Fin m → ℝ) × (Fin n → ℝ)` and `R̄` is `EReal`. -/
def IsRockafellian {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) : Prop :=
  ∀ x : Fin n → ℝ, f (0, x) = φ x

end RockafellianRelax


