-- Prove2me | solution 1 for AME125.certs3_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:17.476537+00:00
-- url     : https://prove2.me/submissions/3cc0397c-d141-48ec-b0a7-24fd4b68de7f

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
theorem _root_.solution : certs3.all certOK = true := by
  decide +kernel
end AME125
