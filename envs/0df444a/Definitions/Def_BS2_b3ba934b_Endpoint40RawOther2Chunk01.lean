-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk01
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk01
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:05:33.335035+00:00
-- url     : https://prove2.me/theorems/9c84e545-b5de-4fe6-98a3-82cce2f91371
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk01 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk01` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk01.lean; original SHA-256 a9de23bd7bbb69154c732d17356b444683e3584d8e254485514a74e84e8ff358; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_2 : ∀ j : Fin 40, (2 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 2) (recipe 2 j)≤rawProfile2 (.a 2 j) := by
  decide +kernel

theorem other_chunk_2_2 :
    (∀ j : Fin 40, (2 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 2) (recipe 2 j)).eval profile2≤rawProfile2 (.b 2 j)) ∧
    (∀ j : Fin 40, (2 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 2) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 2 j)) ∧
    (∀ l : Fin 40, (2 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 2) (recipe 2 (next 2)) (recipe 2 l)
        (rawProfile2 (.a (next 2) l))≤rawProfile2 (.p 2 l)) := by
  decide +kernel

theorem d_chunk_2_2 : ∀ j l : Fin 40, (2 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 2) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 2 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 2 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_3 : ∀ j : Fin 40, (3 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 3) (recipe 2 j)≤rawProfile2 (.a 3 j) := by
  decide +kernel

theorem other_chunk_2_3 :
    (∀ j : Fin 40, (3 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 3) (recipe 2 j)).eval profile2≤rawProfile2 (.b 3 j)) ∧
    (∀ j : Fin 40, (3 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 3) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 3 j)) ∧
    (∀ l : Fin 40, (3 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 3) (recipe 2 (next 3)) (recipe 2 l)
        (rawProfile2 (.a (next 3) l))≤rawProfile2 (.p 3 l)) := by
  decide +kernel

theorem d_chunk_2_3 : ∀ j l : Fin 40, (3 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 3) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 3 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 3 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_3


