-- Prove2me | Definitions.Def_SecondBestMatch_roundedMarket
-- name    : SecondBestMatch_roundedMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:59.84344+00:00
-- url     : https://prove2.me/theorems/9a848400-9a18-4611-a915-09b8134bdd00
-- title:
--   One-sided rounded instance $\mathcal I_n$
-- statement:
--   For $n\ge1$ let $\delta_n := 2^{-n}$. The **rounded instance** $\mathcal I_n$ has the same $B, S, E, \mathcal F$, and buyer and seller types
--   $$
--   \underline v_n := \delta_n\Big\lfloor\frac v{\delta_n}\Big\rfloor,\qquad \overline c_n := \min\Big\{1,\ \delta_n\Big\lceil\frac c{\delta_n}\Big\rceil\Big\},
--   $$
--   applied coordinatewise: buyer values are rounded down and seller costs up. The rounded priors are the pushforwards of the original priors and have finite support.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Appendix C, p.33

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch

/-- The rounded instance `ℐ_n` (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), App. C, p.33): the same `B, S, E, ℱ`, with buyer types
rounded down to the grid `δ_n ℤ`, `v_n := δ_n ⌊v/δ_n⌋`, and seller types rounded up and capped,
`c_n := min{1, δ_n ⌈c/δ_n⌉}`, where `δ_n := 2^{−n}`; the priors are the pushforwards. -/
noncomputable def roundedMarket {B S : Type*} (m : Market B S) (n : ℕ) : Market B S where
  edges := m.edges
  family := m.family
  buyerLaw i := (m.buyerLaw i).map fun v => (2 : ℝ) ^ (-(n : ℤ)) * (⌊v / (2 : ℝ) ^ (-(n : ℤ))⌋ : ℝ)
  sellerLaw j := (m.sellerLaw j).map fun c =>
    min 1 ((2 : ℝ) ^ (-(n : ℤ)) * (⌈c / (2 : ℝ) ^ (-(n : ℤ))⌉ : ℝ))

end SecondBestMatch


