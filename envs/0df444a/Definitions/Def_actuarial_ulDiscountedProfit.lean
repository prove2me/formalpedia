-- Prove2me | Definitions.Def_actuarial_ulDiscountedProfit
-- name    : actuarial_ulDiscountedProfit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:01:51.72969+00:00
-- url     : https://prove2.me/theorems/8f6246e4-e54b-4ecd-a27b-5ca19dcd2486
-- title:
--   Non-unit profit signatures and discounted insurer margins: ulDiscountedProfit
-- statement:
--   Present value of non-unit insurer profit at a risk discount factor. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

noncomputable def ulDiscountedProfit (profit discount : ℝ) : ℝ := profit*discount

end ActuarialValuation


