-- Prove2me | solution 1 for AME125.certs2_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:15:08.49582+00:00
-- url     : https://prove2.me/submissions/5752e73b-b7e2-4cb4-bff3-05bcf9bd054c

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
theorem _root_.solution : certs2.all certOK = true := by
  decide +kernel
end AME125
