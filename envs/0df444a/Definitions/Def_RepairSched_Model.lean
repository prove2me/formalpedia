-- Prove2me | Definitions.Def_RepairSched_Model
-- name    : RepairSched_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:06.190886+00:00
-- url     : https://prove2.me/theorems/bce60a7f-4f41-424a-a57a-6cce3ba764df
-- title:
--   Parameters of the repair facility: $\mu,\lambda,b,c,h,\theta,\Sigma$
-- statement:
--   The data of the equivalent workload formulation are $n\ge 1$ SKUs with repair rates $\mu_i>0$, limiting breakdown rates $\lambda_i>0$, backorder cost rates $b_i>0$, emergency repair costs $c_i>0$, holding cost rates $h_i>0$, a heavy-traffic drift $\theta\le 0$ and a variance $\Sigma>0$.
--
--   Every object of the mission is built on these data.
--
--   **Formalization Note** The paper writes $\mathcal I=\{1,\dots,I\}$; here the SKU set is `Fin n`, since `I` names the idleness process. The paper has $\Sigma=\sum_i\alpha_i\lambda_i(1+\sigma_i^2)/\mu_i^2$ (p.15), and every statement depends on $\Sigma$ only through $\Sigma>0$, so $\Sigma$ is a positive parameter.
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), §3.1, pp.9–13, and p.15

import Mathlib

namespace RepairSched

/-- **The parameters of the equivalent workload formulation.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), §3.1, pp.9–13, and p.15: `n` SKUs with repair rates `μᵢ > 0` (`mu`), limiting breakdown
rates `λᵢ > 0` (`lam`, Assumption 1 Part 1), costs `bᵢ, cᵢ, hᵢ > 0` (p.13: "We assume that
min{hi,bi,ci} > 0 for all i ∈ I"), the drift `θ ≤ 0` (`theta`, Assumption 1 Part 2) and the
variance `Σ > 0` (`Sigma`).

**Formalization Note.** The paper's SKU set `{1,…,I}` is `Fin n` and its `I` is `n`; `I` is
kept for the idleness process. The paper has `Σ = Σᵢ αᵢλᵢ(1 + σᵢ²)/μᵢ²` (p.15); every statement
depends on `Σ` only through `Σ > 0`, so `Sigma` is a positive parameter. -/
structure Model (n : ℕ) where
  /-- repair rates `μᵢ` -/
  mu : Fin n → ℝ
  /-- limiting breakdown rates `λᵢ` -/
  lam : Fin n → ℝ
  /-- backorder cost rates `bᵢ` -/
  b : Fin n → ℝ
  /-- emergency repair costs `cᵢ` -/
  c : Fin n → ℝ
  /-- inventory holding cost rates `hᵢ` -/
  h : Fin n → ℝ
  /-- the heavy-traffic drift `θ` -/
  theta : ℝ
  /-- the variance `Σ` of the workload Brownian motion -/
  Sigma : ℝ
  mu_pos : ∀ i, 0 < mu i
  lam_pos : ∀ i, 0 < lam i
  b_pos : ∀ i, 0 < b i
  c_pos : ∀ i, 0 < c i
  h_pos : ∀ i, 0 < h i
  theta_nonpos : theta ≤ 0
  Sigma_pos : 0 < Sigma

end RepairSched


