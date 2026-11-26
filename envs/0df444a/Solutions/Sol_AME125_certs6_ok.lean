-- Prove2me | solution 1 for AME125.certs6_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:16:25.05918+00:00
-- url     : https://prove2.me/submissions/61f117e8-1aac-4963-9969-4a580155d60d

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
theorem _root_.solution : certs6.all certOK = true := by
  decide +kernel
end AME125
