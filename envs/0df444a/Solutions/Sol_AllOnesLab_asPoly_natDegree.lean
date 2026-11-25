-- Prove2me | solution 1 for AllOnesLab.asPoly_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:56:32.004778+00:00
-- url     : https://prove2.me/submissions/7383667c-b760-4a41-8d6f-6d1a09beb5cc

import Definitions.Def_AllOnesLab_Trace
import Definitions.Def_AllOnesLab_Hard

set_option autoImplicit true
open Polynomial
open AllOnesLab
variable {K : Type*} [Field K]
namespace AllOnesLab
theorem _root_.solution (a : K) : (asPoly a).natDegree = 2 := by
  unfold asPoly
  compute_degree!
end AllOnesLab
