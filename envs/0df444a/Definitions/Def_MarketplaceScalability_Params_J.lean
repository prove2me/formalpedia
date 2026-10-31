-- Prove2me | Definitions.Def_MarketplaceScalability_Params_J
-- name    : MarketplaceScalability_Params_J
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:58.853834+00:00
-- url     : https://prove2.me/theorems/8a42f2c1-a1ca-482f-b979-2b7d7a9c4036
-- title:
--   The output interval $J=(0,\bar q)$
-- statement:
--   The interval of outputs
--   $$
--   J=(0,\bar q).
--   $$
--
--   **Formalization Note** The source does not give a range for $q$. Its conditions on $D$ hold on no unbounded interval, so output ranges over a bounded interval.
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §2.1, p.4

import Mathlib
import Definitions.Def_MarketplaceScalability_Params

namespace MarketplaceScalability

/-- The interval of outputs, `J = (0, q̄)`.
**Formalization Note** The source writes `q` without a range. Its conditions on `D` hold on no
unbounded interval (see `Model`), so output ranges over this bounded interval. -/
def Params.J (P : Params) : Set ℝ := Set.Ioo 0 P.qbar

end MarketplaceScalability


