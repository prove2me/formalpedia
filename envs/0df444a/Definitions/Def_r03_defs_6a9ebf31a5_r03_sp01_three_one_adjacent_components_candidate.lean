-- Prove2me | Definitions.Def_r03_defs_6a9ebf31a5_r03_sp01_three_one_adjacent_components_candidate
-- name    : r03_defs_6a9ebf31a5_r03_sp01_three_one_adjacent_components_candidate
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:53:29.608976+00:00
-- url     : https://prove2.me/theorems/6bdf5efa-a3ef-4066-bbc0-5ca1759e5f9f
-- title:
--   R03 candidate definition: r03 defs 6a9ebf31a5 r03 sp01 three one adjacent components candidate
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_6a9ebf31a5_r03_sp01_three_one_adjacent_components_candidate.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u
set_option maxHeartbeats 1000000


def R03SP01SumProdDistrib {X Y Z : Type u} :
    ((X ⊕ Y) × Z) ≃ ((X × Z) ⊕ (Y × Z)) where
  toFun z := match z.1 with
    | Sum.inl x => Sum.inl (x, z.2)
    | Sum.inr y => Sum.inr (y, z.2)
  invFun z := match z with
    | Sum.inl x => (Sum.inl x.1, x.2)
    | Sum.inr y => (Sum.inr y.1, y.2)
  left_inv z := by cases z with | mk s z => cases s <;> rfl
  right_inv z := by cases z <;> rfl

end CubicP3Partition


