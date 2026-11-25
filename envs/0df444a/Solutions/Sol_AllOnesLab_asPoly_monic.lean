-- Prove2me | solution 1 for AllOnesLab.asPoly_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:56:53.933231+00:00
-- url     : https://prove2.me/submissions/33be37be-b7a8-4c57-9066-6e0a29705d78

import Definitions.Def_AllOnesLab_Trace
import Definitions.Def_AllOnesLab_Hard

set_option autoImplicit true
open Polynomial
open AllOnesLab
variable {K : Type*} [Field K]
namespace AllOnesLab
theorem _root_.solution (a : K) : (asPoly a).Monic := by
  unfold asPoly
  monicity!
end AllOnesLab
