-- Prove2me | Definitions.Def_RockafellianRelax_minValue
-- name    : RockafellianRelax_minValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:06.825987+00:00
-- url     : https://prove2.me/theorems/36735ba0-8062-4d27-88e8-9e19a9a7dd17
-- title:
--   Min-value function $\mathcal V(u) = \inf_x f(u,x)$
-- statement:
--   For $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$, the **min-value function** $\mathcal V : \mathbb R^m \to \overline{\mathbb R}$ is
--
--   $$
--   \mathcal V(u) = \inf_{x \in \mathbb R^n} f(u, x).
--   $$
--
--   If $f$ is a Rockafellian for the actual problem of minimizing $\varphi$, then $\mathcal V(0) = \inf\varphi$ is its minimum value, and $\mathcal V(u)$ is the optimal value of the problem perturbed by $u$.
--
--   **Formalization Note** $\mathbb R^m \times \mathbb R^n$ is `(Fin m → ℝ) × (Fin n → ℝ)`; the infimum is taken in `EReal` ($+\infty$ if $f(u,\cdot) \equiv +\infty$, $-\infty$ if $f(u,\cdot)$ is unbounded below).
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §3, p.7 ("we let the min-value function be given by 𝒱(u) = inf_x f(u, x)")

import Mathlib

namespace RockafellianRelax

/-- **Min-value function** `𝒱(u) = inf_x f(u, x)` of `f : ℝᵐ × ℝⁿ → R̄`.
Royset, Chen & Eckstrand, arXiv:2204.04762v4, §3, p.7: "For f : ℝᵐ × ℝⁿ → R̄, we let the min-value
function be given by 𝒱(u) = inf_x f(u, x)."

**Formalization Note.** `ℝᵐ × ℝⁿ` is `(Fin m → ℝ) × (Fin n → ℝ)` and the infimum is taken in the
complete lattice `EReal` (`𝒱(u) = +∞` if `f(u, ·) ≡ +∞`, `−∞` if `f(u, ·)` is unbounded below). -/
noncomputable def minValue {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal) (u : Fin m → ℝ) :
    EReal :=
  ⨅ x : Fin n → ℝ, f (u, x)

end RockafellianRelax


