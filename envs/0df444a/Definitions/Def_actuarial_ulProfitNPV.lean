-- Prove2me | Definitions.Def_actuarial_ulProfitNPV
-- name    : actuarial_ulProfitNPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T19:02:05.605638+00:00
-- url     : https://prove2.me/theorems/71db6125-dca9-4e1e-b4f2-dfbb3009f7e8
-- title:
--   Non-unit profit signatures and discounted insurer margins: ulProfitNPV
-- statement:
--   Complete deterministic or probability-weighted profit signature present value. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ulDiscountedProfit

namespace ActuarialValuation

noncomputable def ulProfitNPV (cash discount : ℕ → ℝ) (n : ℕ) : ℝ := ∑ t ∈ Finset.range n, ulDiscountedProfit (cash t) (discount t)

end ActuarialValuation


