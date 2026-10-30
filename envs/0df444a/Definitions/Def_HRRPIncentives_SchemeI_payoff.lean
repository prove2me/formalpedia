-- Prove2me | Definitions.Def_HRRPIncentives_SchemeI_payoff
-- name    : HRRPIncentives_SchemeI_payoff
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:15:09.90061+00:00
-- url     : https://prove2.me/theorems/25a426e8-48c5-4228-9084-1a4c4b848077
-- title:
--   Hospital objective $\Pi_i=T_i-c_i(1+r_i)\lambda-R(r_i,c_i)$ under HRRP-I
-- statement:
--   Hospital $i$'s objective (display (1)) under the HRRP-I transfer $T_i$ of (9):
--
--   $$\Pi_i=T_i-c_i(1+r_i)\lambda-R(r_i,c_i).$$
--
--   It is the transfer received minus the treatment cost of the $(1+r_i)\lambda$ visits and the investment cost. Through $T_i$ it depends on the other hospitals' actions via the yardsticks.
-- source:
--   Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted manuscript, display (1), p. 10, with T given by display (9), p. 14

import Mathlib
import Definitions.Def_HRRPIncentives_SchemeI_transfer

namespace HRRPIncentives.SchemeI

/-- Hospital `i`'s objective (1) under HRRP-I:
`Π_i = T_i − c_i (1 + r_i) λ − R(r_i, c_i)`, with `T_i` the HRRP-I transfer (9).

Source: Arifoğlu, Ren, Tezcan, Hospital Readmissions Reduction Program does not provide the
right incentives: Issues and remedies, Management Science 67(4) (2021), author-accepted
manuscript, display (1), p. 10, with `T` given by display (9), p. 14. -/
noncomputable def payoff (lam : ℝ) (R : ℝ × ℝ → ℝ) {N : ℕ} (x : Fin N → ℝ × ℝ)
    (i : Fin N) : ℝ :=
  transfer lam R x i - (x i).2 * (1 + (x i).1) * lam - R (x i)

end HRRPIncentives.SchemeI


