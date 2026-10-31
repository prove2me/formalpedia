-- Prove2me | Definitions.Def_MarketplaceScalability_Params
-- name    : MarketplaceScalability_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:20.897282+00:00
-- url     : https://prove2.me/theorems/6678baee-2778-4207-8844-e51f3363f62f
-- title:
--   Marketplace data: commission $\alpha$, revenue $R$, demand $D$, costs $\underline c,c,\bar c$, fixed costs $f,F$
-- statement:
--   The data of a monopoly marketplace with one type of seller, the high type.
--
--   1. The platform charges a commission rate $\alpha$ on sellers' revenue.
--   2. A seller who sells $q$ units earns revenue $R(q)$; $D=R'$ is the derived (inverse) demand.
--   3. Each sale needs an ancillary service. The market supplies it at unit cost $\bar c$. A seller who invests $F-f$ supplies it at unit cost $\underline c$. The platform, if it offers the service, has unit cost $c$.
--   4. The fixed entry cost is $f$, and the fixed cost with own service is $F$.
--   5. $\bar q$ is the upper end of the interval of outputs.
--
--   These are data only. The conditions they satisfy are collected in the definition of the model.
--
--   **Formalization Note** The conditions are separated from the data because Assumption 1 refers to objects, such as the output $q(\cdot)$, that are defined from the data.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §2.1–§2.2, pp.4, 6

import Mathlib

namespace MarketplaceScalability

/-- **The data of the marketplace** with high-type sellers only (μ = 1).
Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §2.1–§2.2, pp.4, 6.

* `α` is the platform's commission rate;
* `R` is a seller's revenue function and `D` the derived (inverse) demand, `D = R′`;
* `qbar` is the upper end of the output interval (a correction, see `Model`);
* `cown` is the marginal cost c̲ of a seller's own service, `c` the marginal cost of the
  platform's service, `cbar` the marginal cost c̄ of the market service;
* `f` is the fixed entry cost and `F` the fixed cost with own service, so that own service takes
  an investment `F − f`.

The conditions on these data are the fields of `Model`. -/
structure Params where
  /-- The commission rate α. -/
  α : ℝ
  /-- The revenue function R. -/
  R : ℝ → ℝ
  /-- The derived (inverse) demand D. -/
  D : ℝ → ℝ
  /-- The upper end of the output interval. -/
  qbar : ℝ
  /-- The marginal cost c̲ of a seller's own service. -/
  cown : ℝ
  /-- The marginal cost c of the platform's service. -/
  c : ℝ
  /-- The marginal cost c̄ of the market service. -/
  cbar : ℝ
  /-- The fixed entry cost f. -/
  f : ℝ
  /-- The fixed cost F of a seller with its own service. -/
  F : ℝ

end MarketplaceScalability


