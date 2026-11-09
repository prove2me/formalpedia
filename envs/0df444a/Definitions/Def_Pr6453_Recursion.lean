-- Prove2me | Definitions.Def_Pr6453_Recursion
-- name    : Pr6453_Recursion
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T16:24:05.290195+00:00
-- url     : https://prove2.me/theorems/6b3e1bc6-0686-4037-b089-964fa063c38e
-- title:
--   PR #6453: the contraction ratio of the recursion
-- statement:
--   The contraction ratio of the recursion of the PR #6453 word.
--
--   At the claimed saving $\kappa$ a call of the word produces
--   $$\sum_r T_r\, r^{1-\kappa}$$
--   units of productive work and pays
--   $$\sum_r P_r\, r^{1-\kappa}$$
--   units of recursive calls, so the ratio of the two — `gamma` — is the fraction of one level's productivity that the next level costs. The price inequality says exactly that this ratio is strictly below one, and then the cost of the whole call tree is bounded by a constant multiple of the cost of its root, uniformly in the depth.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: the ratio of the two rank moments used by the pricing engine (research/p104-third-anchor-clean-mixed-root/pricing.py, margin k = moment T (1-k) - moment P (1-k)).

/-
PR #6453: the contraction ratio of the recursion.
-/
import Definitions.Def_Pr6453_RankMoments

set_option autoImplicit false

namespace Pr6453

noncomputable section

/-- The fraction of one level's productivity that the next level costs, at the claimed saving:
`gamma = (Σ_r P_r r^(1-κ)) / (Σ_r T_r r^(1-κ))`. -/
def gamma : ℝ := moment paid (1 - (kappa : ℝ)) / moment targets (1 - (kappa : ℝ))

end
end Pr6453


