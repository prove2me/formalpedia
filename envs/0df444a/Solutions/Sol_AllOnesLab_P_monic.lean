-- Prove2me | solution 1 for AllOnesLab.P_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:52:49.076517+00:00
-- url     : https://prove2.me/submissions/012e5da2-b390-4b77-83d8-fe2a199dba56

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution : P.Monic := by
  unfold P
  monicity!
end AllOnesLab
