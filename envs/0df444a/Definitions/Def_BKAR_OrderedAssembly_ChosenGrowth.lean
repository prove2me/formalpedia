-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
-- name    : BKAR_OrderedAssembly_ChosenGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:58:24.357692+00:00
-- url     : https://prove2.me/theorems/3d631506-b863-4fdf-a44b-718ee7d9b821
-- title:
--   Chosen Growth
-- statement:
--   Definitions and structural lemmas for Chosen Growth, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ChosenGrowth.lean

import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Theorems.Thm_P2M_BKAR_Forest_chosenGrowth_of_followOrder__eq_some_324c28c4883b
import Theorems.Thm_P2M_BKAR_Forest_followOrder__grownForestForSupportOrder_bd48bf0ce40b

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace ChosenGrowth
variable {choices : ActiveExtensionChoice V}
variable {F G : Forest V} {order : List (Edge V)}
theorem exists_orderedGrowth (path : ChosenGrowth choices F order G) :
    Nonempty (OrderedGrowth F order G) := by
  induction path with
  | nil F =>
      exact ⟨OrderedGrowth.nil F⟩
  | cons he _tail ih =>
      rcases ih with ⟨growth⟩
      exact ⟨OrderedGrowth.cons (choices _ ⟨_, he⟩).extension growth⟩
def toOrderedGrowth (path : ChosenGrowth choices F order G) :
    OrderedGrowth F order G :=
  Classical.choice path.exists_orderedGrowth
end ChosenGrowth
namespace OrderedGrowth
variable {G : Forest V} {order : List (Edge V)}
end OrderedGrowth
namespace ChosenGrowth
variable {choices : ActiveExtensionChoice V}
variable {G : Forest V} {order : List (Edge V)}
end ChosenGrowth
def grownForestForSupportOrder_orderedGrowth
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    OrderedGrowth (Forest.empty V) order.val
      (grownForestForSupportOrder choices I order) :=
  (chosenGrowth_of_followOrder?_eq_some choices
    (followOrder?_grownForestForSupportOrder choices I order)).toOrderedGrowth
def canonicalGrownForestForSupport_orderedGrowth
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    OrderedGrowth (Forest.empty V) I.canonicalOrder.val
      (canonicalGrownForestForSupport choices I) :=
  grownForestForSupportOrder_orderedGrowth choices I I.canonicalOrder
end Forest
end BKAR


