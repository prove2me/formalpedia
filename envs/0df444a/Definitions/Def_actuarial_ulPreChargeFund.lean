-- Prove2me | Definitions.Def_actuarial_ulPreChargeFund
-- name    : actuarial_ulPreChargeFund
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:00:16.182744+00:00
-- url     : https://prove2.me/theorems/2c6e5de8-6f2f-4778-ac10-d611eeabc45a
-- title:
--   Premium allocation, bid and offer prices and fund charges: ulPreChargeFund
-- statement:
--   Invested fund after allocated contribution and before charges. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   U_t=U_{t-1}+\frac{a_t P_t}{O_t}-\frac{C_t}{B_t}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 16. FCA, Unit-linked pensions and savings price and value practices, https://www.fca.org.uk/publications/multi-firm-reviews/unit-linked-pensions-and-savings-multi-firm-review-consumer-duty-price-and-value-practices; FCA TR16/2 Fair treatment of long-standing customers, https://www.fca.org.uk/your-fca/documents/thematic-reviews/tr16-02. Parent topic: Allocated premium, offer and bid unit prices, cost of allocation spread, fund charges, net amount at risk, policy expenses and discounted expected non-unit profit. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.fca.org.uk/your-fca/documents/thematic-reviews/tr16-02

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulPreChargeFund (fund premiumAlloc creditedReturn : ℝ) : ℝ := (fund+premiumAlloc)*(1+creditedReturn)

end ActuarialValuation


