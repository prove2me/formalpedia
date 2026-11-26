-- Prove2me | solution 1 for AME125.certs8_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:16:33.690886+00:00
-- url     : https://prove2.me/submissions/05b911f9-e661-42a6-962c-1ec8e82f7fc5

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
theorem _root_.solution : certs8.all certOK = true := by
  decide +kernel
end AME125
