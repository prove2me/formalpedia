-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_RateSetting
-- name    : RockafellianRelax_Supplement_RateSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:12:40.858503+00:00
-- url     : https://prove2.me/theorems/c6389b57-9e0d-4d29-b31d-4a00b484c3b1
-- title:
--   Data hypotheses of Theorem 4.3 on $\varepsilon$ and the sequences
-- statement:
--   Fix $f_0,\dots,f_s : \mathbb R^n \to \overline{\mathbb R}$, $p \in \mathbb R^s$ and $\rho \in \mathbb R$, and let $\varphi = f_0 + \sum_i p_i f_i$ be the objective of (2.1). A number $\varepsilon$ and sequences $p^\nu, \theta^\nu, y^\nu, (u^\nu,x^\nu)$ satisfy the **hypotheses of Theorem 4.3** when, with $f^\nu$ from (4.3) and for every $\nu$:
--
--   1. $0 \le \varepsilon \le 2\rho$, $p^\nu \in \Delta$ and $\theta^\nu \ge 0$;
--   2. $\varphi$ has a minimizer in $\mathbb B(0,\rho)$, and $f^\nu(u,x) - \langle y^\nu,u\rangle$ has a minimizer in $\mathbb B(0,\rho)\times\mathbb B(0,\rho)$;
--   3. the minimum values of all these problems lie in $[-\rho,\rho-\varepsilon]$;
--   4. the iterates are approximate minimizers in those balls,
--   $$
--   (u^\nu,x^\nu) \in \varepsilon\text{-}\operatorname*{argmin}_{u,x}\, f^\nu(u,x) - \langle y^\nu,u\rangle,\qquad \|u^\nu\|_2 \le \rho,\quad \|x^\nu\|_2 \le \rho .
--   $$
--
--   Both claims of Theorem 4.3 are stated under these hypotheses.
--
--   **Formalization Note** The conditions on $p$, on the $f_i$ and on $\rho$, and the boundedness of $y^\nu$, are hypotheses of the theorem itself. Minimizers carry the domain condition of `argmin`. The index $\nu$ runs from $0$.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Theorem 4.3, p.12 (hypotheses), with display (4.3), p.10

import Mathlib
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_epsArgmin
import Definitions.Def_RockafellianRelax_tilt
import Definitions.Def_RockafellianRelax_Supplement_euclidNorm
import Definitions.Def_RockafellianRelax_Supplement_expObjective
import Definitions.Def_RockafellianRelax_Supplement_quadApprox

namespace RockafellianRelax.Supplement

/-- **The data hypotheses of Theorem 4.3** on `ε` and the sequences `pν, θν, yν, (uν, xν)`.
Royset, Chen & Eckstrand, arXiv:2204.04762v4, Theorem 4.3, p.12: "with p, pν ∈ ∆ … For ρ ∈ [0, ∞) and ε ∈ [0, 2ρ], suppose that the actual
problem (2.1) has a minimizer in B(0, ρ) and each one of the approximating problems (4.4) has a
minimizer in B(0, ρ) × B(0, ρ) with all these problems having minimum values in [−ρ, ρ − ε]. If
{xν, ν ∈ ℕ} are constructed by (uν, xν) ∈ ε-argmin_{u,x} fν(u, x) − ⟨yν, u⟩ with ‖uν‖₂ ≤ ρ,
‖xν‖₂ ≤ ρ"; and θν ∈ [0, ∞) from (4.3), p.10.

**Formalization Note.** The standing conditions on `p`, `f₀`, `fᵢ`, `ρ` and the boundedness of
`{yν}` are stated in the theorem. "All these problems" covers (2.1) and every (4.4). Minimizers are
members of `argmin`, so they lie in the domain. `ε` is one number for all `ν`. Balls are Euclidean,
and `ν` runs over Lean's `ℕ` from `0`. -/
structure RateSetting {n s : ℕ} (f0 : (Fin n → ℝ) → EReal) (fi : Fin s → (Fin n → ℝ) → EReal)
    (p : Fin s → ℝ) (ρ ε : ℝ) (pseq : ℕ → Fin s → ℝ) (θ : ℕ → ℝ) (y : ℕ → Fin s → ℝ)
    (z : ℕ → (Fin s → ℝ) × (Fin n → ℝ)) : Prop where
  eps_nonneg : 0 ≤ ε
  eps_le : ε ≤ 2 * ρ
  pseq_mem : ∀ ν, pseq ν ∈ stdSimplex ℝ (Fin s)
  theta_nonneg : ∀ ν, 0 ≤ θ ν
  actual_minimizer : ∃ x ∈ argmin (expObjective f0 fi p), euclidNorm x ≤ ρ
  actual_value_lower : ((-ρ : ℝ) : EReal) ≤ ⨅ x, expObjective f0 fi p x
  actual_value_upper : (⨅ x, expObjective f0 fi p x) ≤ ((ρ - ε : ℝ) : EReal)
  approx_minimizer : ∀ ν, ∃ w ∈ argmin (tilt (quadApprox f0 fi (pseq ν) (θ ν)) (y ν)),
    euclidNorm w.1 ≤ ρ ∧ euclidNorm w.2 ≤ ρ
  approx_value_lower : ∀ ν,
    ((-ρ : ℝ) : EReal) ≤ ⨅ w, tilt (quadApprox f0 fi (pseq ν) (θ ν)) (y ν) w
  approx_value_upper : ∀ ν,
    (⨅ w, tilt (quadApprox f0 fi (pseq ν) (θ ν)) (y ν) w) ≤ ((ρ - ε : ℝ) : EReal)
  iterate_mem : ∀ ν, z ν ∈ epsArgmin (tilt (quadApprox f0 fi (pseq ν) (θ ν)) (y ν)) ε
  iterate_u_le : ∀ ν, euclidNorm (z ν).1 ≤ ρ
  iterate_x_le : ∀ ν, euclidNorm (z ν).2 ≤ ρ

end RockafellianRelax.Supplement


