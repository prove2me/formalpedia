-- Prove2me | Definitions.Def_TeschlODE_Stability_semiOrbit
-- name    : TeschlODE_Stability_semiOrbit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T12:09:19.112981+00:00
-- url     : https://prove2.me/theorems/5300a487-e815-4da8-9d69-262c557e25c1
-- title:
--   Forward and backward orbits $\gamma_\pm(x)$ (6.16)
-- statement:
--   Let $\Phi$ be a flow with maximal intervals $I_x$ and let $\sigma \in \{1, -1\}$. The **forward** ($\sigma = 1$) or **backward** ($\sigma = -1$) **orbit** of $x$ is
--   $$\gamma_\sigma(x) = \Phi\big((0, T_\sigma(x)), x\big) = \{\Phi(t, x) : t \in I_x,\ \sigma t > 0\}. \qquad (6.16)$$
--
--   **Formalization Note.** The sign $\sigma \in \{\pm\}$ of the book is the real number $\sigma = 1$ or $\sigma = -1$; the definition itself accepts any real $\sigma$, and every theorem that uses it assumes $\sigma = 1 \lor \sigma = -1$. Since $I_x$ is an interval containing $0$, $\{t \in I_x : t > 0\} = (0, T_+(x))$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 192, §6.3, Eq. (6.16)

import Mathlib

namespace TeschlODE.Stability

/-- Teschl, §6.3, p. 192, (6.16): the forward (`σ = 1`) or backward (`σ = -1`) orbit
`γ_σ(x) = Φ((0, T_σ(x)), x)`, i.e. the points `Φ t x` with `t ∈ I x` and `σ t > 0`. -/
def semiOrbit {n : ℕ} (σ : ℝ) (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ t ∈ I x, 0 < σ * t ∧ Φ t x = y}

end TeschlODE.Stability


