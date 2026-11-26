-- Prove2me | solution 1 for AME125.certs_masks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:16:41.592939+00:00
-- url     : https://prove2.me/submissions/c1636cf8-795a-48d2-8911-be12364d0316

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
theorem _root_.solution : certs.map Prod.fst = (List.range 4096).filter fun m ↦ popcount m = 6 := by
  decide +kernel
end AME125
