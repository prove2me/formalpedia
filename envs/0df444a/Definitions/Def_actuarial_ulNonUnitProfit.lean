-- Prove2me | Definitions.Def_actuarial_ulNonUnitProfit
-- name    : actuarial_ulNonUnitProfit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:01:43.278995+00:00
-- url     : https://prove2.me/theorems/86cf55b6-b52d-492f-8407-e14a13534a5f
-- title:
--   Non-unit profit signatures and discounted insurer margins: ulNonUnitProfit
-- statement:
--   Net period profit of insurer's non-unit fund after real expenses and risk claims. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \Pi=\sum_t v^t p_t\left(\text{income}_t-\text{outgo}_t\right)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 16. FCA, Unit-linked pensions and savings price and value practices, https://www.fca.org.uk/publications/multi-firm-reviews/unit-linked-pensions-and-savings-multi-firm-review-consumer-duty-price-and-value-practices; FCA TR16/2 Fair treatment of long-standing customers, https://www.fca.org.uk/your-fca/documents/thematic-reviews/tr16-02. Parent topic: Allocated premium, offer and bid unit prices, cost of allocation spread, fund charges, net amount at risk, policy expenses and discounted expected non-unit profit. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.fca.org.uk/your-fca/documents/thematic-reviews/tr16-02

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def ulNonUnitProfit (income expense commission deathCost guaranteeCost : ℝ) : ℝ := income-expense-commission-deathCost-guaranteeCost

end ActuarialValuation


