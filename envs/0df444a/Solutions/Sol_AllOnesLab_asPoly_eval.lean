-- Prove2me | solution 1 for AllOnesLab.asPoly_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:56:48.408918+00:00
-- url     : https://prove2.me/submissions/ec88a4c3-3f67-4ca0-b2c8-59312dac7c19

import Definitions.Def_AllOnesLab_Trace
import Definitions.Def_AllOnesLab_Hard

set_option autoImplicit true
open Polynomial
open AllOnesLab
variable {K : Type*} [Field K]
namespace AllOnesLab
theorem _root_.solution (a z : K) : (asPoly a).eval z = z ^ 2 + z + a := by
  simp [asPoly]
end AllOnesLab
