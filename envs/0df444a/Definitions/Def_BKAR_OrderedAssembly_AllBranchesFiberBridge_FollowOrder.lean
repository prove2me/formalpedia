-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
-- name    : BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:03:51.025389+00:00
-- url     : https://prove2.me/theorems/bff88b3e-8ce2-5b5b-885e-b032350effc5
-- title:
--   Follow Order
-- statement:
--   Definitions and structural lemmas for Follow Order, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/FollowOrder.lean

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
inductive ChosenGrowth (choices : ActiveExtensionChoice V) :
    Forest V → List (Edge V) → Forest V → Prop
  | nil (F : Forest V) : ChosenGrowth choices F [] F
  | cons {F G : Forest V} {e : Edge V} {order : List (Edge V)}
      (he : e ∈ F.activeEdges)
      (tail :
        ChosenGrowth choices (choices F ⟨e, he⟩).forest order G) :
      ChosenGrowth choices F (e :: order) G
namespace ChosenGrowth
variable {choices : ActiveExtensionChoice V}
variable {F G : Forest V} {order : List (Edge V)}
end ChosenGrowth
noncomputable def followOrder?
    (choices : ActiveExtensionChoice V) :
    Forest V → List (Edge V) → Option (Forest V)
  | F, [] => some F
  | F, e :: order =>
      if he : e ∈ F.activeEdges then
        followOrder? choices (choices F ⟨e, he⟩).forest order
      else
        none
end Forest
end BKAR


