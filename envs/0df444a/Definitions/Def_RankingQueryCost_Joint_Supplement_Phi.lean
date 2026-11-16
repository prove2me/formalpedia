-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Supplement_Phi
-- name    : RankingQueryCost_Joint_Supplement_Phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:47:43.975193+00:00
-- url     : https://prove2.me/theorems/8a26743c-e06d-4b14-8dec-9b6623b9d2d7
-- title:
--   Density profile for the complete-information threshold
-- statement:
--   For a positive real density $c$, write $\lfloor c\rfloor$ for its integer part. Define
--
--   $$\Phi(c)=\lfloor c\rfloor+(c-\lfloor c\rfloor)^2.$$
--
--   This profile describes $U/n^2$ when the fault density $s/n$ tends to $c$. The Lean function is total on the reals, and the theorem uses it only for $c>0$.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Theorem 2.1, p. 4, PDF p. 5

import Mathlib

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint.Supplement

/-- The density profile in Theorem 2.1; its stated domain is c > 0. -/
def densityProfile (c : ℝ) : ℝ := (⌊c⌋ : ℤ) + (c - (⌊c⌋ : ℤ)) ^ 2

end RankingQueryCost.Joint.Supplement


