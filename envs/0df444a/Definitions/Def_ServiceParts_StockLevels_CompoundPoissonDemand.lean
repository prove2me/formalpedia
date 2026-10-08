-- Prove2me | Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
-- name    : ServiceParts_StockLevels_CompoundPoissonDemand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T06:54:23.238981+00:00
-- url     : https://prove2.me/theorems/6fab69f0-90f7-4591-a379-2c3ba71e8b24
-- title:
--   Compound Poisson demand for an (s–1, s) item: the steady-state pmf p(x|λτ̄), ready rate R(s), backorders B(s), on-hand E[(s − X)⁺]
-- statement:
--   A single item is stocked at one location under an $(s-1, s)$ policy in the backorder case. Customer orders arrive at rate $\lambda > 0$, the mean resupply time is $\bar\tau > 0$, and an order is for $j$ units with probability $u_j$, where $u_0 = 0$, $u_j \ge 0$, $\sum_j u_j = 1$, and the mean order size
--   $$\bar u = \sum_{j \ge 1} j\,u_j$$
--   is finite. Write $\mu = \lambda\bar\tau\bar u$ for the mean lead-time demand.
--
--   The steady-state probability that $x$ units are in resupply is the compound Poisson probability
--   $$p(0 \mid \lambda\bar\tau) = e^{-\lambda\bar\tau}, \qquad p(x \mid \lambda\bar\tau) = \sum_{j=1}^{\infty} e^{-\lambda\bar\tau}\,\frac{(\lambda\bar\tau)^j}{j!}\,u^{(j)}_x \quad (x \ge 1),$$
--   where $u^{(j)}_x$ is the probability that $j$ orders total $x$ units. With stock level $s$ the book defines:
--
--   1. the **ready rate** $R(s) = \sum_{x=0}^{s} p(x \mid \lambda\bar\tau)$, the probability that no backorder exists;
--   2. the **expected backorders** $B(s) = \sum_{x > s} (x - s)\,p(x \mid \lambda\bar\tau)$;
--   3. the **expected on-hand inventory** $\sum_{x \le s} (s - x)\,p(x \mid \lambda\bar\tau)$, since $s - x$ units are on hand exactly when $x \le s$ units are in resupply.
--
--   Simple Poisson demand is the special case $u_1 = 1$. In Section 3.4.2 the book writes $p(x \mid \mu)$ for the same probabilities.
--
--   **Formalization Note** The finiteness of $\bar u$ is added: without it $B(s)$ is infinite. The on-hand expectation is written as the finite sum $E[(s - X)^+]$, which is what the book's $E[\text{On-hand}]$ is in the $(s-1,s)$ backorder model (inventory position $s$ = on hand + on order − backorders).
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 48-50 and 60, Section 3.2 (P{X = x} = p(x|λτ̄), R(s), B(s)) and Section 3.4.2 (E[On-hand], µ = λτ̄ū)

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic

namespace ServiceParts.StockLevels

/-- A single item managed by an `(s-1, s)` policy in the backorder case, with stationary
compound Poisson demand (Muckstadt 2005, Section 3.2, pp. 48-50): customer orders arrive at
rate `λ > 0`, the mean resupply time is `τ̄ > 0`, and each order is for `j` units with
probability `u j`, where `u 0 = 0`, the `u j` are nonnegative and sum to one, and the mean
order size `ū = Σ j u_j` is finite. -/
structure CompoundPoissonDemand where
  /-- customer order rate `λ` -/
  lam : ℝ
  /-- mean resupply time `τ̄` -/
  tbar : ℝ
  /-- order-size distribution: `u j` is the probability that an order is for `j` units -/
  u : ℕ → ℝ
  lam_pos : 0 < lam
  tbar_pos : 0 < tbar
  u_zero : u 0 = 0
  u_nonneg : ∀ j, 0 ≤ u j
  u_hasSum : HasSum u 1
  u_mean : Summable (fun j : ℕ => (j : ℝ) * u j)

namespace CompoundPoissonDemand

variable (d : CompoundPoissonDemand)

/-- Mean order size `ū = Σ_j j u_j`. -/
noncomputable def ubar : ℝ := ∑' j : ℕ, (j : ℝ) * d.u j

/-- Mean lead-time demand `µ = λ τ̄ ū` (Muckstadt 2005, p. 60). -/
noncomputable def mu : ℝ := d.lam * d.tbar * d.ubar

/-- The steady-state probability that `x` units are in resupply (Muckstadt 2005, p. 49):
`p(0|λτ̄) = e^{-λτ̄}` and, for `x ≥ 1`,
`p(x|λτ̄) = Σ_{j=1}^∞ e^{-λτ̄} (λτ̄)^j / j! · u^{(j)}_x`. -/
noncomputable def pmf (x : ℕ) : ℝ :=
  if x = 0 then Real.exp (-(d.lam * d.tbar))
  else ∑' j : ℕ, Real.exp (-(d.lam * d.tbar)) * (d.lam * d.tbar) ^ (j + 1)
      / ((j + 1).factorial : ℝ) * ServiceParts.Palm.convPow d.u (j + 1) x

/-- Ready rate `R(s) = Σ_{x=0}^{s} p(x|λτ̄)` (Muckstadt 2005, p. 49). -/
noncomputable def readyRate (s : ℕ) : ℝ := ∑ x ∈ Finset.range (s + 1), d.pmf x

/-- Expected backorders `B(s) = Σ_{x > s} (x - s) p(x|λτ̄)` (Muckstadt 2005, p. 50). -/
noncomputable def backorders (s : ℕ) : ℝ :=
  ∑' x : ℕ, if s < x then ((x : ℝ) - s) * d.pmf x else 0

/-- Expected on-hand inventory at stock level `s`: on hand is `(s - X)⁺` when `X` units are
in resupply, so `E[On-hand] = Σ_{x ≤ s} (s - x) p(x|λτ̄)` (Muckstadt 2005, p. 60). -/
noncomputable def expectedOnHand (s : ℕ) : ℝ :=
  ∑ x ∈ Finset.range (s + 1), ((s : ℝ) - x) * d.pmf x

end CompoundPoissonDemand

end ServiceParts.StockLevels


