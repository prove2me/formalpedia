-- Prove2me | Definitions.Def_SponsoredAssort_utility
-- name    : SponsoredAssort_utility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:01.942758+00:00
-- url     : https://prove2.me/theorems/2fab9a4b-09f3-4c2e-bf51-f5ba523a8827
-- title:
--   Seller utility $u_i(\hat v_i,v)$
-- statement:
--   When seller $i$ reports $\hat v_i$, the other sellers report truthfully, and the true profile is $v$, seller $i$'s utility is
--
--   $$
--   u_i(\hat v_i,v)=r_i\,\pi_i\big(S(\hat v_i,v_{-i}),v\big)-p_i(\hat v_i,v_{-i}).
--   $$
--
--   The assortment and the payment depend on the report, but the consumer chooses according to the **true** attractiveness $v$; this is where the sellers' values interact.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §2, p.11

import Mathlib
import Definitions.Def_SponsoredAssort_choiceProb
import Definitions.Def_SponsoredAssort_Mechanism

open scoped NNReal

namespace SponsoredAssort

/-- The **utility of seller `i`** when he reports `y` and the true attractiveness profile is `v`
(Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), §2, p.11):
`uᵢ(y, v) = rᵢ · πᵢ(S(y, v₋ᵢ), v) − pᵢ(y, v₋ᵢ)`.

**Formalization Note.** `(y, v₋ᵢ)` is `Function.update v i y`. The assortment and the payment are
evaluated at the report, the choice probability at the **true** profile `v`. -/
noncomputable def utility {n : ℕ} (r : Fin n → ℝ) (m : Mechanism n) (i : Fin n) (y : ℝ≥0)
    (v : Attr n) : ℝ :=
  r i * choiceProb (m.alloc (Function.update v i y)) v i - m.pay (Function.update v i y) i

end SponsoredAssort


