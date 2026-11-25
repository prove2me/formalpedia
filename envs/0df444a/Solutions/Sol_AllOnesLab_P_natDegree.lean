-- Prove2me | solution 1 for AllOnesLab.P_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:52:43.842501+00:00
-- url     : https://prove2.me/submissions/5845bebb-d9a6-4959-94f5-a214353e15fc

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution : P.natDegree = 2 := by
  unfold P
  compute_degree!
end AllOnesLab
