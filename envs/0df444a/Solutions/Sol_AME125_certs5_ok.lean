-- Prove2me | solution 1 for AME125.certs5_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:16:05.489072+00:00
-- url     : https://prove2.me/submissions/ce665d0d-30e9-420e-8141-74ed9e82366a

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
theorem _root_.solution : certs5.all certOK = true := by
  decide +kernel
end AME125
