-- Prove2me | Definitions.Def_BKAR_CubePartition_Orders
-- name    : BKAR_CubePartition_Orders
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:44:14.43362+00:00
-- url     : https://prove2.me/theorems/4671919d-d5ee-48bb-81cc-894731c0e0c7
-- title:
--   Orders
-- statement:
--   Definitions and structural lemmas for Orders, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Orders.lean

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_ForestIndex_ext

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
def edgeSetOrders (S : Finset (Edge V)) : Finset (List (Edge V)) :=
  S.toList.permutations.toFinset
omit [Fintype V] in
/-- First-edge/tail-order pairs attached to a finite edge set. -/
def edgeSetOrderTails (S : Finset (Edge V)) :
    Finset (Σ _ : {x : Edge V // x ∈ S}, List (Edge V)) :=
  S.attach.sigma fun e => edgeSetOrders (S.erase e.val)
omit [Fintype V] in
/-- The embedding sending a first-edge/tail-order pair to the consed order. -/
def edgeSetOrderTailConsEmbedding (S : Finset (Edge V)) :
    (Σ _ : {x : Edge V // x ∈ S}, List (Edge V)) ↪ List (Edge V) where
  toFun x := x.1.val :: x.2
  inj' := by
    intro x y hxy
    cases x with
    | mk ex orderX =>
        cases y with
        | mk ey orderY =>
            injection hxy with hhead htail
            have hey : ex = ey := Subtype.ext hhead
            cases hey
            cases htail
            rfl
def edgeOrders (F : Forest V) : Finset (List (Edge V)) :=
  edgeSetOrders F.edges
def paramsOfOrder (F : Forest V) (order : List (Edge V)) (ts : List ℝ) :
    F.EdgeParam → ℝ :=
  fun e => ts.getD (order.idxOf e.val) 0
namespace EdgeExtension
variable {F F' : Forest V} {e : Edge V}
end EdgeExtension
namespace OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}
end OrderedGrowth
def orderedContribution (F : Forest V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  orderedSimplexIntegral order
    (fun ts => mixedPartialList order.reverse ρ
      (F.standardInterp (F.paramsOfOrder order ts)))
def orderedSectorSum (F : Forest V) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum F.edgeOrders fun order => F.orderedContribution order ρ
namespace ActiveExtension
variable {e : Edge V}
end ActiveExtension
end Forest
end BKAR


