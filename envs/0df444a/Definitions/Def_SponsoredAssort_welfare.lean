-- Prove2me | Definitions.Def_SponsoredAssort_welfare
-- name    : SponsoredAssort_welfare
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:51.305749+00:00
-- url     : https://prove2.me/theorems/d41fee2a-09e2-4e69-b099-89eb3da7a1a3
-- title:
--   Welfare $R(S,v)$ of an assortment
-- statement:
--   Seller $i$ earns a public revenue $r_i$ when the consumer chooses its product. The **welfare** of an assortment $S$ at the profile $v$ is the expected revenue of the displayed sellers,
--
--   $$
--   R(S,v)=\sum_{i\in S} r_i\,\pi_i(S,v).
--   $$
--
--   It equals the sum of the sellers' utilities and the platform's revenue, since side-payments cancel. For a mechanism $m$ with allocation $S(\cdot)$ the paper writes $R(m,v)=R(S(v),v)$.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), §2, p.11

import Mathlib
import Definitions.Def_SponsoredAssort_choiceProb

open scoped NNReal

namespace SponsoredAssort

/-- The **welfare** of an assortment (Balseiro, Désir, SSRN 3821382 (Feb. 21, 2022), §2, p.11):
`R(S, v) = ∑_{i ∈ S} rᵢ · πᵢ(S, v)`, the sum of the platform's revenue and the sellers'
utilities (side-payments cancel). Here `r i` is seller `i`'s public revenue. -/
noncomputable def welfare {n : ℕ} (r : Fin n → ℝ) (S : Finset (Fin n)) (v : Attr n) : ℝ :=
  ∑ i ∈ S, r i * choiceProb S v i

end SponsoredAssort


