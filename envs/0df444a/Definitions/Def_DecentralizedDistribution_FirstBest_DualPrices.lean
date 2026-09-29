-- Prove2me | Definitions.Def_DecentralizedDistribution_FirstBest_DualPrices
-- name    : DecentralizedDistribution_FirstBest_DualPrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T06:31:20.950046+00:00
-- url     : https://prove2.me/theorems/ffb97997-ad91-4eec-9e79-eba3197b47de
-- title:
--   Dual prices of the grand-coalition shipping LP and the dual-price allocation (8)
-- statement:
--   This file defines the dual of the shipping LP (6) for the grand coalition $\mathcal N$ and the allocation built from its solutions. The paper refers to "the dual prices associated with the constraints (6b), (6c), and (6d)" without writing the dual; it is written out here.
--
--   A vector of dual prices is $(\nu,\gamma,\delta)$ with $\nu_i$ for constraint (6b) of retailer $i$, $\gamma_w$ for (6c) of warehouse $w$ and $\delta_n$ for (6d) of retailer $n$. It is **dual feasible** when all prices are nonnegative and, for every retailer $n$,
--   $$\beta_{i,n}\,\nu_i+\delta_n\ \ge\ \beta_{i,n}\,(r_n-v_i-t_{i,n})\quad(i\in\mathcal N),\qquad \beta_{w,n}\,\gamma_w+\delta_n\ \ge\ \beta_{w,n}\,(r_n-v_w-t_{w,n})\quad(w\in\mathcal W).$$
--   For $\beta_{i,n}>0$ this is the dual constraint $\nu_i+\delta_n/\beta_{i,n}\ge r_n-v_i-t_{i,n}$ of the column $q_{i,n}$, multiplied by $\beta_{i,n}$; for $\beta_{i,n}=0$ the arc carries no shipment and the constraint reduces to $\delta_n\ge 0$.
--
--   The dual objective at a profile $[Z]$ and demand $\vec D$ is
--   $$\sum_{i\in\mathcal N}\nu_iH_i+\sum_{w\in\mathcal W}\gamma_wY_w+\sum_{n\in\mathcal N}\delta_nE_n,\qquad Y_w=\sum_{n}Y_{w,n},$$
--   and **dual prices** of (6) for $\mathcal N$ are a dual-feasible vector minimizing it. The **dual-price allocation** (8) gives retailer $n$
--   $$\alpha_n([Z],\vec D)=\nu_nH_n+\sum_{w\in\mathcal W}\gamma_wY_{w,n}+\delta_nE_n.$$
--
--   The allocation (8) prices each unit of residual inventory, claimed warehouse stock and residual demand at its shadow price; it is the allocation of Theorem 4.1 and the building block of the side payments of Corollary 5.1.
--
--   **Formalization Note.** A dual vector is a triple of real vectors indexed by `Fin N`, `Fin W`, `Fin N`. Optimality is stated directly (feasible, and no larger objective than any feasible vector), not through a general LP library.
-- source:
--   Anupindi, Bassok & Zemel, A General Framework for the Study of Decentralized Distribution Systems, MSOM 3(4) 2001, p. 358, Theorem 4.1, Eq. (8) (dual of Eq. (6) for the grand coalition)

import Mathlib
import Definitions.Def_DecentralizedDistribution_FirstBest_System

namespace DecentralizedDistribution.FirstBest

/-- A vector of dual prices `(ν, γ, δ)` for the grand-coalition shipping LP (6):
`ν j` for constraint (6b) of retailer `j`, `γ w` for (6c) of warehouse `w`,
`δ n` for (6d) of retailer `n`. -/
abbrev DualPrices (N W : ℕ) := (Fin N → ℝ) × (Fin W → ℝ) × (Fin N → ℝ)

/-- Feasibility in the dual of (6) for the grand coalition `𝒩`: all prices nonnegative and, for
every arc `(i, n)`, `β_{i,n} ν_i + δ_n ≥ β_{i,n} (r_n - v_i - t_{i,n})` (retailer `i`) and
`β_{w,n} γ_w + δ_n ≥ β_{w,n} (r_n - v_w - t_{w,n})` (warehouse `w`). This is the dual constraint
`ν_i + δ_n / β_{i,n} ≥ r_n - v_i - t_{i,n}` of the column `q_{i,n}` multiplied by `β_{i,n}`; it is
vacuous exactly on the arcs with `β_{i,n} = 0`, which carry no shipment. -/
def IsDualFeasible {N W : ℕ} (sys : System N W) (p : DualPrices N W) : Prop :=
  (∀ j, 0 ≤ p.1 j) ∧ (∀ w, 0 ≤ p.2.1 w) ∧ (∀ n, 0 ≤ p.2.2 n) ∧
  (∀ j n, sys.β (Sum.inl j) n * sys.margin (Sum.inl j) n
      ≤ sys.β (Sum.inl j) n * p.1 j + p.2.2 n) ∧
  (∀ w n, sys.β (Sum.inr w) n * sys.margin (Sum.inr w) n
      ≤ sys.β (Sum.inr w) n * p.2.1 w + p.2.2 n)

/-- The dual objective `∑_i ν_i H_i + ∑_w γ_w Y_w + ∑_n δ_n E_n`, with `Y_w = ∑_n Y_{w,n}`. -/
def dualObjective {N W : ℕ} (Z : Profile N W) (D : Demand N) (p : DualPrices N W) : ℝ :=
  (∑ j, p.1 j * residualInv Z D j) + (∑ w, p.2.1 w * ∑ n, (Z n).Y w)
    + ∑ n, p.2.2 n * residualDem Z D n

/-- Dual prices of the shipping problem (6) for `𝒩`: an optimal solution of its dual. -/
def IsOptimalDual {N W : ℕ} (sys : System N W) (Z : Profile N W) (D : Demand N)
    (p : DualPrices N W) : Prop :=
  IsDualFeasible sys p ∧ ∀ p', IsDualFeasible sys p' → dualObjective Z D p ≤ dualObjective Z D p'

/-- The dual-price allocation (8): `α_n = ν_n H_n + ∑_w γ_w Y_{w,n} + δ_n E_n`. -/
def dualAllocation {N W : ℕ} (Z : Profile N W) (D : Demand N) (p : DualPrices N W)
    (n : Fin N) : ℝ :=
  p.1 n * residualInv Z D n + (∑ w, p.2.1 w * (Z n).Y w) + p.2.2 n * residualDem Z D n

end DecentralizedDistribution.FirstBest


