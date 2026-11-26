-- Prove2me | Definitions.Def_BKAR_CubePartition_Support_Growth
-- name    : BKAR_CubePartition_Support_Growth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:51:46.765271+00:00
-- url     : https://prove2.me/theorems/f2c0444c-7fae-462f-ba40-c79c61c9b1ca
-- title:
--   Growth
-- statement:
--   Definitions and structural lemmas for Growth, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Growth.lean

import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_Forest_OrderedGrowth_order_mem_edgeOrders_of_initial_edges_eq_empty
import Theorems.Thm_BKAR_Forest_TerminalGrowth_order_mem_edgeOrders_of_initial_edges_eq_empty
import Theorems.Thm_BKAR_Forest_cons_mem_edgeOrders_iff
import Theorems.Thm_BKAR_Forest_empty_edges
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace ActiveTerminalBranchData
variable {F : Forest V}
theorem growth_order_mem_edgeOrders_of_initial_edges_eq_empty
    (data : ActiveTerminalBranchData F) (hF : F.edges = ∅)
    (e : {e // e ∈ F.activeEdges}) :
    (e.val :: (data.tail e).order) ∈ (data.growth e).terminal.edgeOrders :=
  (data.growth e).order_mem_edgeOrders_of_initial_edges_eq_empty hF
theorem growth_order_mem_edgeOrders_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (e.val :: (data.tail e).order) ∈ (data.growth e).terminal.edgeOrders :=
  data.growth_order_mem_edgeOrders_of_initial_edges_eq_empty
    (Forest.empty_edges V) e
def growthOrderTail
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    Σ _ : {x : Edge V // x ∈ (data.growth e).terminal.edges},
      List (Edge V) :=
  ⟨⟨e.val,
    ((cons_mem_edgeOrders_iff (data.growth e).terminal).mp
      (data.growth_order_mem_edgeOrders_emptyStart e)).1⟩,
    (data.tail e).order⟩
def growthOrder
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) : List (Edge V) :=
  (data.growthOrderTail e).1.val :: (data.growthOrderTail e).2
end ActiveTerminalBranchData
end Forest
end BKAR


