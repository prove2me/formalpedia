-- Prove2me | Definitions.Def_OnlinePrimalDual_AdAuctions_cParam
-- name    : OnlinePrimalDual_AdAuctions_cParam
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:51:13.386626+00:00
-- url     : https://prove2.me/theorems/f7f92002-6135-4654-bc38-23a2e74dded8
-- title:
--   The competitive-ratio constant c = (1+Rmax)^(1/Rmax)
-- statement:
--   `c = (1 + Rmax)^(1/Rmax)`, the constant the Allocation algorithm's step (3) update rule is
--   parameterized by, fixed to this value in the proof of Claim (3) (p. 214: "This is why we set
--   the value of c to be (1+Rmax)^(1/Rmax)").
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 212, 214, Theorem 10.1 and its proof of Claim (3)

import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance

namespace OnlinePrimalDual.AdAuctions

/-- The constant `c = (1 + Rmax)^(1/Rmax)` the Allocation algorithm's step (3) update rule is
parameterized by ("`c` is determined later", p. 212; fixed at this value in the proof of Claim
(3), p. 214: "This is why we set the value of `c` to be `(1+Rmax)^(1/Rmax)`"). `Real.rpow`
(the `ℝ → ℝ → ℝ` power, notation `^`) realizes the real exponent `1/Rmax`. -/
noncomputable def cParam {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) : ℝ :=
  (1 + inst.Rmax) ^ (1 / inst.Rmax)

end OnlinePrimalDual.AdAuctions


