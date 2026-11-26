-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
-- name    : BKAR_OrderedAssembly_CanonicalForestBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:53:58.98983+00:00
-- url     : https://prove2.me/theorems/30838cdb-fe7b-4167-850b-09125cf86208
-- title:
--   Canonical Forest Bridge
-- statement:
--   Definitions and structural lemmas for Canonical Forest Bridge, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalForestBridge.lean

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Theorems.Thm_BKAR_Forest_mem_edgeSetOrders_iff
import Theorems.Thm_P2M_BKAR_Forest_exists_followOrder__eq_some_support_of_mem_edgeSetOrders_94b5d7b04ff1

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace ForestIndex
variable {V : Type*} [Fintype V] [DecidableEq V]
def canonicalOrder (I : ForestIndex V) :
    {order : List (Edge V) // order ∈ Forest.edgeSetOrders I.edges} :=
  ⟨I.edges.toList,
    (Forest.mem_edgeSetOrders_iff I.edges).mpr (List.Perm.refl _)⟩
end ForestIndex
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
def grownForestForSupportOrder
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    Forest V :=
  Classical.choose
    (exists_followOrder?_eq_some_support_of_mem_edgeSetOrders
      choices order.property)
def canonicalGrownForestForSupport
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    Forest V :=
  grownForestForSupportOrder choices I I.canonicalOrder
end Forest
end BKAR


