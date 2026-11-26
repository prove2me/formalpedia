-- Prove2me | Definitions.Def_BKAR_OrderedRemainder
-- name    : BKAR_OrderedRemainder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:35:55.149717+00:00
-- url     : https://prove2.me/theorems/2d7fd2a5-fe13-402a-a088-766b971a3c4a
-- title:
--   Ordered Remainder
-- statement:
--   Definitions and structural lemmas for Ordered Remainder, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean

import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
structure ActiveBranchData (F : Forest V) where
  extension : ∀ e : {e // e ∈ F.activeEdges}, ActiveExtension F e.val
  order : ∀ _ : {e // e ∈ F.activeEdges}, List (Edge V)
  terminal : ∀ _ : {e // e ∈ F.activeEdges}, Forest V
  tail :
    ∀ e : {e // e ∈ F.activeEdges},
      OrderedGrowth (extension e).forest (order e) (terminal e)
namespace ActiveBranchData
variable {F : Forest V}
def growth (data : ActiveBranchData F) (e : {e // e ∈ F.activeEdges}) :
    OrderedGrowth F (e.val :: data.order e) (data.terminal e) :=
  (data.extension e).consGrowth (data.tail e)
def branchIntegralAux (data : ActiveBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum F.activeEdges.attach
    fun e => (data.growth e).branchIntegralAux top u ρ
def branchIntegral (data : ActiveBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  data.branchIntegralAux 1 u ρ
def singleton
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val) :
    ActiveBranchData F where
  extension := extensions
  order := fun _ => []
  terminal := fun e => (extensions e).forest
  tail := fun e => OrderedGrowth.nil (extensions e).forest
end ActiveBranchData
end Forest
end BKAR


