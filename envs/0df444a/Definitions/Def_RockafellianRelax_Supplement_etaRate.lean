-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_etaRate
-- name    : RockafellianRelax_Supplement_etaRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:12:04.575013+00:00
-- url     : https://prove2.me/theorems/fdc69068-a31d-585e-b8ed-5ad9976294b3
-- title:
--   The rate $\eta^\nu$ of Theorem 4.3
-- statement:
--   For reals $\sigma, \tau, \theta, d$, the **rate** of Theorem 4.3 is
--
--   $$
--   \eta = \sigma d + \max\Bigl\{\tfrac12\theta d^2,\ \tau/\sqrt\theta\Bigr\}.
--   $$
--
--   The theorem takes $\theta = \theta^\nu$ and $d = \|p^\nu - p\|_2$, so $\eta$ is the $\eta^\nu$ of (4.5).
--
--   **Formalization Note** Lean evaluates $\tau/\sqrt 0$ as $0$. Theorem 4.3 reaches $\theta = 0$ only when $\tau = 0$.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Theorem 4.3, p.12 (definition of the rate)

import Mathlib

namespace RockafellianRelax.Supplement

/-- **The rate `ην` of Theorem 4.3.** Royset, Chen & Eckstrand, arXiv:2204.04762v4, Theorem 4.3, p.12: "ην = σ‖pν − p‖₂ +
max{½θν‖pν − p‖₂², τ/√θν}".

**Formalization Note.** `d` stands for `‖pν − p‖₂`. At `θ = 0` Lean's `τ / √0` is `0`. The theorem
reaches `θ = 0` only with `τ = 0` (existence claim: threshold `Θ > 0`; explicit claim: `θ = 0` forces
`β = 0`, hence `τ = βσ = 0`). -/
noncomputable def etaRate (σ τ θ d : ℝ) : ℝ :=
  σ * d + max (1 / 2 * θ * d ^ 2) (τ / Real.sqrt θ)

end RockafellianRelax.Supplement


