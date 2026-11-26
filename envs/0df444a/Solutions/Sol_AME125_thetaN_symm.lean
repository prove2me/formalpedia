-- Prove2me | solution 1 for AME125.thetaN_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:14:43.539097+00:00
-- url     : https://prove2.me/submissions/bc1a3259-2d13-42d5-b8af-bc96d6e14f5b

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
theorem _root_.solution : ∀ i < 12, ∀ j < 12, thetaN i j = thetaN j i := by
  decide
end AME125
