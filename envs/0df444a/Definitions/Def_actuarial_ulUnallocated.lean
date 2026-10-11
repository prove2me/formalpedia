-- Prove2me | Definitions.Def_actuarial_ulUnallocated
-- name    : actuarial_ulUnallocated
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:59:25.707987+00:00
-- url     : https://prove2.me/theorems/c1081fe4-4fde-4ab5-b465-74fb70812629
-- title:
--   Premium allocation, bid and offer prices and fund charges: ulUnallocated
-- statement:
--   Premium income retained in the insurer's non-unit fund. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ulPremiumAlloc

namespace ActuarialValuation

noncomputable def ulUnallocated (premium allocationRate : ℝ) : ℝ := premium-ulPremiumAlloc premium allocationRate

end ActuarialValuation


