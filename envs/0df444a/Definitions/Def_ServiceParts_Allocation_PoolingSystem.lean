-- Prove2me | Definitions.Def_ServiceParts_Allocation_PoolingSystem
-- name    : ServiceParts_Allocation_PoolingSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T22:56:59.077859+00:00
-- url     : https://prove2.me/theorems/e4191ec4-f1a0-4498-8f6f-b744cd8d406a
-- title:
--   Eppen–Schrage depot/warehouse system with i.i.d. normal demands, balance, and the balanced allocation
-- statement:
--   This definition sets up the periodic review pooling environment of Muckstadt, Section 7.2.1 (after Eppen and Schrage).
--
--   One depot supplies $m \ge 1$ warehouses. The demand $d_{jt}$ at warehouse $j$ in period $t$ is normally distributed with mean $\mu_j$ and variance $\sigma_j^2$, $\sigma_j > 0$; the demands are independent across periods and warehouses. The supplier-to-depot lead time is $D$ periods and the depot-to-warehouse lead time is $A$ periods. The holding cost $h > 0$ and the backorder cost $b > 0$ per unit per period are the same at every warehouse. $\Phi$ denotes the standard normal distribution function.
--
--   1. **Balance** (the Imbalance Assumption, p. 152): inventory positions $I_1, \dots, I_m$ are in balance when
--   $$\Phi\!\left(\frac{I_j - A\mu_j}{\sqrt A\,\sigma_j}\right)$$
--   is the same for all $j$.
--   2. The random variables of Section 7.2.1.2:
--   $$Y_0 = \sum_{t=1}^{D} \sum_{j=1}^{m} d_{jt}, \qquad Y_j = \sum_{t=D+1}^{D+A+1} d_{jt}.$$
--   3. For a system inventory position $s$, the **balanced allocation** of the $s - Y_0$ units at the depot (p. 156) is
--   $$x_j = (A+1)\mu_j + \Bigl(s - Y_0 - (A+1)\sum_{i=1}^m \mu_i\Bigr) \frac{\sigma_j}{\sum_{i=1}^m \sigma_i},$$
--   and $z_j = x_j - Y_j$ is the net inventory at warehouse $j$ at the end of a period.
--   4. The expected holding and backorder cost per period, summed over the warehouses, is $\sum_{j=1}^m E\bigl[h\,(z_j)^+ + b\,(z_j)^-\bigr]$.
--   5. The standardized stock level is
--   $$z = \frac{s - (D+A+1)\sum_{i=1}^m \mu_i}{\bigl[(A+1)\bigl(\sum_{i=1}^m \sigma_i\bigr)^2 + D \sum_{i=1}^m \sigma_i^2\bigr]^{1/2}}.$$
--
--   These objects are used by Lemma 3 and by the Eppen–Schrage stock-level analysis of Section 7.2.1.2.
--
--   **Formalization Note** Demands are real random variables `demand t j` on a measure space; normality is `P.map (demand t j) = gaussianReal μ_j σ_j²`, and independence is mutual independence of the whole family indexed by (period, warehouse). The book's expected cost display on p. 157 reads $h\int_0^\infty z\,dF_{z_j}(z) + b\int_{-\infty}^0 z\,dF_{z_j}(z)$, whose second term has the wrong sign for a backorder cost; the next display on the same page charges $b$ on the shortfall, which is the form used here ($b\,E[(z_j)^-]$). The allocation $x_j$ is the book's formula; it can be negative on some outcomes, which the book's imbalance assumption ignores.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 151-152 and 155-158, Sections 7.2.1, 7.2.1.1 (Imbalance Assumption) and 7.2.1.2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ServiceParts.Allocation

/-- The standard normal distribution function `Φ`. -/
noncomputable def stdNormalCdf (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- Balance of the warehouse inventory positions (the Imbalance Assumption, Section 7.2.1.1,
p. 152): with depot-to-warehouse lead time `A` periods, per-period demand means `μ j` and
standard deviations `σ j`, the inventory positions `I j` are in balance when
`Φ((I_j - A μ_j) / (√A σ_j))` takes the same value at every warehouse `j`. -/
def InBalance {m : ℕ} (A : ℕ) (μ σ I : Fin m → ℝ) : Prop :=
  ∃ p : ℝ, ∀ j, stdNormalCdf ((I j - A * μ j) / (Real.sqrt A * σ j)) = p

/-- The periodic-review depot/warehouse system of Section 7.2.1 (Eppen–Schrage),
pp. 151–152 and 155–156: one depot supplies `m ≥ 1` warehouses; `demand t j` is the demand
`d_{jt}` at warehouse `j` in period `t`; the demands are independent across periods and
warehouses and `d_{jt}` is normal with mean `μ j` and variance `σ j ^ 2`, `σ j > 0`; `D` is
the supplier-to-depot lead time and `A` the depot-to-warehouse lead time, in periods; `h` is
the holding cost and `b` the backorder cost per unit per period, the same at every warehouse. -/
structure PoolingSystem (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (m : ℕ) where
  /-- depot-to-warehouse lead time `A` -/
  A : ℕ
  /-- supplier-to-depot lead time `D` -/
  D : ℕ
  /-- per-period demand means `μ_j` -/
  μ : Fin m → ℝ
  /-- per-period demand standard deviations `σ_j` -/
  σ : Fin m → ℝ
  /-- holding cost per unit per period -/
  h : ℝ
  /-- backorder cost per unit per period -/
  b : ℝ
  /-- `d_{jt}`: demand at warehouse `j` in period `t` -/
  demand : ℕ → Fin m → Ω → ℝ
  m_pos : 0 < m
  σ_pos : ∀ j, 0 < σ j
  h_pos : 0 < h
  b_pos : 0 < b
  demand_measurable : ∀ t j, Measurable (demand t j)
  demand_law : ∀ t j, P.map (demand t j) = gaussianReal (μ j) (Real.toNNReal (σ j ^ 2))
  demand_indep : iIndepFun (fun p : ℕ × Fin m => demand p.1 p.2) P

namespace PoolingSystem

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m : ℕ} (S : PoolingSystem Ω P m)

/-- `Y₀ = Σ_{t=1}^{D} Σ_{j=1}^{m} d_{jt}`: total system demand over a depot lead time. -/
noncomputable def Y0 (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 S.D, ∑ j, S.demand t j ω

/-- `Y_j = Σ_{t=D+1}^{D+A+1} d_{jt}`: demand at warehouse `j` over `A + 1` periods. -/
noncomputable def Yw (j : Fin m) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc (S.D + 1) (S.D + S.A + 1), S.demand t j ω

/-- The balanced allocation of the `s - Y₀` units on hand at the depot (p. 156):
`x_j = (A + 1) μ_j + (s - Y₀ - (A + 1) Σ_i μ_i) σ_j / Σ_i σ_i`. -/
noncomputable def alloc (s : ℝ) (j : Fin m) (ω : Ω) : ℝ :=
  (S.A + 1) * S.μ j + (s - S.Y0 ω - (S.A + 1) * ∑ i, S.μ i) * S.σ j / ∑ i, S.σ i

/-- `z_j = x_j - Y_j`: the net inventory at warehouse `j` at the end of a period, for system
inventory position `s` (p. 156). -/
noncomputable def netInv (s : ℝ) (j : Fin m) (ω : Ω) : ℝ :=
  S.alloc s j ω - S.Yw j ω

/-- The expected holding and backorder cost per period, summed over the warehouses:
`Σ_j E[h (z_j)⁺ + b (z_j)⁻]` (p. 157). -/
noncomputable def expectedCost (s : ℝ) : ℝ :=
  ∑ j, ∫ ω, (S.h * max (S.netInv s j ω) 0 + S.b * max (-S.netInv s j ω) 0) ∂P

/-- The common standardized value (p. 158):
`z = (s - (D + A + 1) Σ_i μ_i) / [(A + 1)(Σ_i σ_i)² + D Σ_i σ_i²]^{1/2}`. -/
noncomputable def zScore (s : ℝ) : ℝ :=
  (s - (S.D + S.A + 1) * ∑ i, S.μ i) /
    Real.sqrt ((S.A + 1) * (∑ i, S.σ i) ^ 2 + S.D * ∑ i, S.σ i ^ 2)

end PoolingSystem

end ServiceParts.Allocation


