-- Prove2me | Definitions.Def_CachonCoord_BaseStock_Model
-- name    : CachonCoord_BaseStock_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:33:44.433277+00:00
-- url     : https://prove2.me/theorems/593733f3-7e6d-4a0b-9739-75a09092f22c
-- title:
--   §6.7.1, pp. 71–74 — lead-time demand, inventory and backorders, costs, and supplier-to-retailer transfers
-- statement:
--   Consider one retailer served by one supplier. Let $D_r\ge 0$ be demand during the retailer's replenishment lead time, with probability law $P$, distribution function $F_r$, density $f_r$, and finite mean $\mu_r$. The model assumes $F_r(0)=0$ and that $F_r$ is continuous and strictly increasing on nonnegative stock levels, with $F_r'=f_r$ at every positive level. The holding cost rate $h_r$, retailer backorder rate $\beta_r$, and supplier backorder rate $\beta_s$ are strictly positive; write $\beta=\beta_r+\beta_s$.
--
--   For any real base-stock level $s$, expected inventory and backorders are
--   $$I_r(s)=\mathbb E[(s-D_r)^+],\qquad B_r(s)=\mathbb E[(D_r-s)^+].$$
--   The retailer, supplier, and channel costs are $c_r(s)=h_r I_r(s)+\beta_r B_r(s)$, $c_s(s)=\beta_s B_r(s)$, and $c(s)=c_r(s)+c_s(s)$. For $0<\lambda\le1$, the proposed contract pays from supplier to retailer at the rates
--   $$t_I=(1-\lambda)h_r,\qquad t_B=\beta_r-\lambda\beta,$$
--   so the expected transfer is $T_\lambda(s)=t_I I_r(s)+t_B B_r(s)$. The contracted costs are $c_r^\lambda=c_r-T_\lambda$ and $c_s^\lambda=c_s+T_\lambda$.
--
--   These definitions isolate the lead-time demand distribution and the cost functions used throughout the single-location coordination result.
--
--   **Formalization Note** The law is a probability measure on the real line supported on $[0,\infty)$; finite mean is an explicit integrability condition. The expectation definitions are primary, so all formulas involving $I_r$ and $B_r$ are consequences. The continuous-review process and the proof that its long-run average equals these cost functions are outside this section's formalized claim; the chapter states that reduction before (30). Risk neutrality and full information are the chapter's standing assumptions.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, Eqs. (28)–(30), pp. 71–74

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- The lead-time demand and cost parameters of Cachon (2003), §6.7.1, pp. 71–73.
The law is that of demand `D_r` during the retailer's replenishment lead time `L_r`.
The section assumes risk neutrality, full information, nonnegative demand, a finite mean,
and a strictly increasing differentiable distribution function on nonnegative levels. -/
structure Model where
  law : Measure ℝ
  probability : IsProbabilityMeasure law
  nonnegativeDemand : law (Set.Iio 0) = 0
  finiteMean : Integrable (id : ℝ → ℝ) law
  density : ℝ → ℝ
  density_nonneg : ∀ y : ℝ, 0 ≤ density y
  density_measurable : Measurable density
  law_eq_withDensity : law = volume.withDensity (fun y => ENNReal.ofReal (density y))
  cdfZero : cdf law 0 = 0
  cdfStrict : StrictMonoOn (cdf law) (Set.Ici 0)
  cdfContinuous : Continuous (cdf law)
  cdfHasDeriv : ∀ y : ℝ, 0 < y → HasDerivAt (cdf law) (density y) y
  hr : ℝ
  br : ℝ
  bs : ℝ
  hr_pos : 0 < hr
  br_pos : 0 < br
  bs_pos : 0 < bs

namespace Model

variable (M : Model)

/-- `F_r(y)`, the distribution function of lead-time demand. -/
noncomputable def F (y : ℝ) : ℝ := cdf M.law y

/-- `μ_r = E[D_r]`, finite by `Model.finiteMean`. -/
noncomputable def meanDemand : ℝ := ∫ x, x ∂M.law

/-- `I_r(y) = E[(y-D_r)⁺]`, expected on-hand inventory (28). -/
noncomputable def I (y : ℝ) : ℝ := ∫ x, max (y - x) 0 ∂M.law

/-- `B_r(y) = E[(D_r-y)⁺]`, expected backorders (29). -/
noncomputable def B (y : ℝ) : ℝ := ∫ x, max (x - y) 0 ∂M.law

/-- `β = β_r + β_s`, the channel's backorder cost rate. -/
def beta : ℝ := M.br + M.bs

/-- `c_r(y) = h_r I_r(y) + β_r B_r(y)` (p. 73). -/
noncomputable def retailerCost (y : ℝ) : ℝ := M.hr * M.I y + M.br * M.B y

/-- `c_s(y) = β_s B_r(y)` (p. 73). -/
noncomputable def supplierCost (y : ℝ) : ℝ := M.bs * M.B y

/-- `c(y) = c_r(y) + c_s(y)` (30). -/
noncomputable def chainCost (y : ℝ) : ℝ := M.retailerCost y + M.supplierCost y

/-- `t_I = (1-λ)h_r`, the supplier-to-retailer inventory transfer rate (p. 74). -/
def tI (lam : ℝ) : ℝ := (1 - lam) * M.hr

/-- `t_B = β_r - λβ`, the supplier-to-retailer backorder transfer rate (p. 74). -/
def tB (lam : ℝ) : ℝ := M.br - lam * M.beta

/-- `t_I I_r(y) + t_B B_r(y)`, positive from supplier to retailer. -/
noncomputable def transfer (lam y : ℝ) : ℝ := M.tI lam * M.I y + M.tB lam * M.B y

/-- The retailer's cost after the transfer, independently defined from the original cost. -/
noncomputable def contractedRetailerCost (lam y : ℝ) : ℝ :=
  M.retailerCost y - M.transfer lam y

/-- The supplier's cost after paying the transfer. -/
noncomputable def contractedSupplierCost (lam y : ℝ) : ℝ :=
  M.supplierCost y + M.transfer lam y

end Model
end CachonCoord.BaseStock


