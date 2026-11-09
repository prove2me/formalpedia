-- Prove2me | Definitions.Def_Pr6453_TailRatiosFixed
-- name    : Pr6453_TailRatiosFixed
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T18:09:51.581973+00:00
-- url     : https://prove2.me/theorems/5335a2a9-a4eb-4aad-b3bb-3cf86cecbcc4
-- title:
--   PR #6453: the three tail ratios (corrected exponents)
-- statement:
--   The three tail ratios of the PR #6453 strictification, with the split `12^(1/7)` written with a real exponent.
--
--   `α = P(1-t)/T(1-t)` is the ratio of the two rank moments at the tested saving, `γ = P(1-t+1/7)/(12^(1/7)·T(1-t))` is the paid moment one step `1/7` further out against the split, and `δ = (13652·13)/(12^t·T(1-t))` is the rounding charged against the split. The certificate requires `α < 1 - 10^-29` and `γ, δ < 31/32`.
--
--   Formalization note: the split in `γ` is written `(12 : ℝ) ^ ((1 : ℝ) / 7)`. With a bare `1 / 7` the exponent elaborates at type `ℕ`, where `1 / 7 = 0`, so the factor would silently be `12 ^ 0 = 1`.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/p104-third-anchor-clean-mixed-root/pricing.py (alpha, gamma, delta).

/-
PR #6453: the three tail ratios of the strictification (corrected exponents).

`γ` divides by `12^(1/7)`.  Written `(12 : ℝ) ^ (1 / 7)` the exponent elaborates as a *natural*
number, `1 / 7 = 0`, so the split factor would be `12 ^ 0 = 1`; the exponent is therefore given
as `((1 : ℝ) / 7)`.
-/
import Definitions.Def_Pr6453_RankMoments
import Definitions.Def_Pr6453_Strictification

set_option autoImplicit false

namespace Pr6453

noncomputable section

/-- `α`, the ratio of the two rank moments at the tested saving. -/
def alpha2 : ℝ := moment paid (1 - (tested : ℝ)) / moment targets (1 - (tested : ℝ))

/-- `γ`, the paid moment one step `1/7` further out, against the split `12^(1/7)`. -/
def gammaTail2 : ℝ :=
  moment paid (1 - (tested : ℝ) + 1 / 7) /
    ((12 : ℝ) ^ ((1 : ℝ) / 7) * moment targets (1 - (tested : ℝ)))

/-- `δ`, the rounding charged against the split `12^t`. -/
def deltaTail2 : ℝ :=
  (13652 * 13) / ((12 : ℝ) ^ (tested : ℝ) * moment targets (1 - (tested : ℝ)))

end
end Pr6453


