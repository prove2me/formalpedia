-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk04
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk04
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:07:33.240678+00:00
-- url     : https://prove2.me/theorems/1bb4b60f-1316-4191-9d8d-ffd94b472f44
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk04 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk04` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk04.lean; original SHA-256 56fd728d2ea5adf94777e5eceae3882a527114d8aa6c8ab8f599f76fc2065d10; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_8 : ∀ j : Fin 40, (8 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 8) (recipe 2 j)≤rawProfile2 (.a 8 j) := by
  decide +kernel

theorem other_chunk_2_8 :
    (∀ j : Fin 40, (8 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 8) (recipe 2 j)).eval profile2≤rawProfile2 (.b 8 j)) ∧
    (∀ j : Fin 40, (8 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 8) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 8 j)) ∧
    (∀ l : Fin 40, (8 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 8) (recipe 2 (next 8)) (recipe 2 l)
        (rawProfile2 (.a (next 8) l))≤rawProfile2 (.p 8 l)) := by
  decide +kernel

theorem d_chunk_2_8 : ∀ j l : Fin 40, (8 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 8) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 8 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 8 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_9 : ∀ j : Fin 40, (9 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 9) (recipe 2 j)≤rawProfile2 (.a 9 j) := by
  decide +kernel

theorem other_chunk_2_9 :
    (∀ j : Fin 40, (9 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 9) (recipe 2 j)).eval profile2≤rawProfile2 (.b 9 j)) ∧
    (∀ j : Fin 40, (9 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 9) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 9 j)) ∧
    (∀ l : Fin 40, (9 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 9) (recipe 2 (next 9)) (recipe 2 l)
        (rawProfile2 (.a (next 9) l))≤rawProfile2 (.p 9 l)) := by
  decide +kernel

theorem d_chunk_2_9 : ∀ j l : Fin 40, (9 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 9) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 9 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 9 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_9


