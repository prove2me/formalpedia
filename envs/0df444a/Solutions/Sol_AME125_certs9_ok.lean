-- Prove2me | solution 1 for AME125.certs9_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:16:39.000279+00:00
-- url     : https://prove2.me/submissions/e6f7d8af-b1d4-4437-990f-f7dc34dc4719

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
theorem _root_.solution : certs9.all certOK = true := by
  decide +kernel
end AME125
