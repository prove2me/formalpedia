-- Prove2me | Definitions.Def_r03_defs_70d95c7a2a_r03_sp01_three_one_adjacent_center_candidate_v1
-- name    : r03_defs_70d95c7a2a_r03_sp01_three_one_adjacent_center_candidate_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:53:41.1205+00:00
-- url     : https://prove2.me/theorems/b1c7a5af-17ea-40b3-9a0c-b2216a72a732
-- title:
--   R03 candidate definition: r03 defs 70d95c7a2a r03 sp01 three one adjacent center candidate v1
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_70d95c7a2a_r03_sp01_three_one_adjacent_center_candidate_v1.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

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


