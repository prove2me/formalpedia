-- Prove2me | solution 1 for AME125.certs1_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:04.770865+00:00
-- url     : https://prove2.me/submissions/9d7b0433-493b-4900-a1c1-8a2d0fb04311

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate

set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix
namespace AME125
theorem _root_.solution : certs1.all certOK = true := by
  decide +kernel
end AME125
