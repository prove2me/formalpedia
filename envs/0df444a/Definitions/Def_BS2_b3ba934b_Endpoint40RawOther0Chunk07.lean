-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk07
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk07
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:13:34.980651+00:00
-- url     : https://prove2.me/theorems/4d4577bf-322c-4c5b-be84-e791869c2767
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk07 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk07` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk07.lean; original SHA-256 58471635180d66278c06f645cdfa503b587c3114e21b5aabb1a3a4e9e8f51661; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_14 : ∀ j : Fin 40, (14 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 14) (recipe 0 j)≤rawProfile0 (.a 14 j) := by
  decide +kernel

theorem other_chunk_0_14 :
    (∀ j : Fin 40, (14 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 14) (recipe 0 j)).eval profile0≤rawProfile0 (.b 14 j)) ∧
    (∀ j : Fin 40, (14 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 14) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 14 j)) ∧
    (∀ l : Fin 40, (14 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 14) (recipe 0 (next 14)) (recipe 0 l)
        (rawProfile0 (.a (next 14) l))≤rawProfile0 (.p 14 l)) := by
  decide +kernel

theorem d_chunk_0_14 : ∀ j l : Fin 40, (14 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 14) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 14 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 14 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_15 : ∀ j : Fin 40, (15 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 15) (recipe 0 j)≤rawProfile0 (.a 15 j) := by
  decide +kernel

theorem other_chunk_0_15 :
    (∀ j : Fin 40, (15 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 15) (recipe 0 j)).eval profile0≤rawProfile0 (.b 15 j)) ∧
    (∀ j : Fin 40, (15 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 15) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 15 j)) ∧
    (∀ l : Fin 40, (15 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 15) (recipe 0 (next 15)) (recipe 0 l)
        (rawProfile0 (.a (next 15) l))≤rawProfile0 (.p 15 l)) := by
  decide +kernel

theorem d_chunk_0_15 : ∀ j l : Fin 40, (15 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 15) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 15 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 15 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_15


