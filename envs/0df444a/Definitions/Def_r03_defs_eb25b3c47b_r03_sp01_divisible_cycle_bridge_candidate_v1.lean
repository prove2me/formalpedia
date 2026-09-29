-- Prove2me | Definitions.Def_r03_defs_eb25b3c47b_r03_sp01_divisible_cycle_bridge_candidate_v1
-- name    : r03_defs_eb25b3c47b_r03_sp01_divisible_cycle_bridge_candidate_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:54:03.955588+00:00
-- url     : https://prove2.me/theorems/d3d59335-a0b0-4b58-ba47-fd8eb3e865e0
-- title:
--   R03 candidate definition: r03 defs eb25b3c47b r03 sp01 divisible cycle bridge candidate v1
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_eb25b3c47b_r03_sp01_divisible_cycle_bridge_candidate_v1.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

noncomputable section

set_option maxHeartbeats 1000000

def R03SP01SigmaProdEquiv {I : Type u} (k : I → Nat) :
    ((Σ i : I, Fin (k i)) × Fin 3) ≃ (Σ i : I, Fin (k i) × Fin 3) where
  toFun z := ⟨z.1.1, (z.1.2, z.2)⟩
  invFun z := (⟨z.1, z.2.1⟩, z.2.2)
  left_inv z := by cases z with | mk z l => cases z; rfl
  right_inv z := by cases z with | mk i z => cases z; rfl

end

end CubicP3Partition


