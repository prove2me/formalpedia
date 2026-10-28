-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk15
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk15
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:21:50.921334+00:00
-- url     : https://prove2.me/theorems/e033880f-c12d-4a0d-9867-b5ee79e6d86f
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk15 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk15` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk15.lean; original SHA-256 a2cddfe37c46e242116926efe1396086cf8b177e51c40f49162e27277a640fe3; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_30 : ∀ j : Fin 40, (30 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 30) (recipe 2 j)≤rawProfile2 (.a 30 j) := by
  decide +kernel

theorem other_chunk_2_30 :
    (∀ j : Fin 40, (30 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 30) (recipe 2 j)).eval profile2≤rawProfile2 (.b 30 j)) ∧
    (∀ j : Fin 40, (30 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 30) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 30 j)) ∧
    (∀ l : Fin 40, (30 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 30) (recipe 2 (next 30)) (recipe 2 l)
        (rawProfile2 (.a (next 30) l))≤rawProfile2 (.p 30 l)) := by
  decide +kernel

theorem d_chunk_2_30 : ∀ j l : Fin 40, (30 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 30) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 30 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 30 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_31 : ∀ j : Fin 40, (31 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 31) (recipe 2 j)≤rawProfile2 (.a 31 j) := by
  decide +kernel

theorem other_chunk_2_31 :
    (∀ j : Fin 40, (31 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 31) (recipe 2 j)).eval profile2≤rawProfile2 (.b 31 j)) ∧
    (∀ j : Fin 40, (31 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 31) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 31 j)) ∧
    (∀ l : Fin 40, (31 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 31) (recipe 2 (next 31)) (recipe 2 l)
        (rawProfile2 (.a (next 31) l))≤rawProfile2 (.p 31 l)) := by
  decide +kernel

theorem d_chunk_2_31 : ∀ j l : Fin 40, (31 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 31) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 31 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 31 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_31


