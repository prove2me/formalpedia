-- Prove2me | Definitions.Def_TradeAgentNV_rho
-- name    : TradeAgentNV_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T10:29:36.645323+00:00
-- url     : https://prove2.me/theorems/c0f1e8e6-24ac-41d6-adf5-42de2f4ca92b
-- title:
--   $\rho=r-t+h+\pi$
-- statement:
--   The constant
--   $$
--   \rho=r-t+h+\pi,
--   $$
--   the unit revenue net of shipping plus the excess-supply and lost-sales costs. It is positive whenever $h>0$ and $r-t+\pi>0$.
-- source:
--   Çakıcı & Karaesmen, When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a Trade Agent, SSRN 4409114 (v. Oct 14, 2023), https://ssrn.com/abstract=4409114, after display (4), p.10

import Mathlib

namespace TradeAgentNV

/-- The constant `ρ = r − t + h + π` (after display (4), p.10, of Çakıcı & Karaesmen, *When Yield is Not the Only Supply Uncertainty: Newsvendor Model of a
Trade Agent*, SSRN 4409114 (v. Oct 14, 2023)):
the unit revenue net of shipping plus the excess-supply cost plus the lost-sales cost. It is
positive under the paper's assumptions `h > 0` and `r − t + π > 0`. -/
def rho (r t h π : ℝ) : ℝ :=
  r - t + h + π

end TradeAgentNV


