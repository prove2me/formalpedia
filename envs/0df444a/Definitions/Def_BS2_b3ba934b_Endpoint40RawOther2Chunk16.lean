-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk16
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk16
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:22:24.415396+00:00
-- url     : https://prove2.me/theorems/37db4827-d1fe-4083-bbeb-48ab9a6ebee3
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk16 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk16` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk16.lean; original SHA-256 f9497e4408686056c65730530d4c8f47ab365bef5a101f69237db75225991116; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_32 : ∀ j : Fin 40, (32 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 32) (recipe 2 j)≤rawProfile2 (.a 32 j) := by
  decide +kernel

theorem other_chunk_2_32 :
    (∀ j : Fin 40, (32 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 32) (recipe 2 j)).eval profile2≤rawProfile2 (.b 32 j)) ∧
    (∀ j : Fin 40, (32 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 32) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 32 j)) ∧
    (∀ l : Fin 40, (32 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 32) (recipe 2 (next 32)) (recipe 2 l)
        (rawProfile2 (.a (next 32) l))≤rawProfile2 (.p 32 l)) := by
  decide +kernel

theorem d_chunk_2_32 : ∀ j l : Fin 40, (32 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 32) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 32 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 32 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_33 : ∀ j : Fin 40, (33 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 33) (recipe 2 j)≤rawProfile2 (.a 33 j) := by
  decide +kernel

theorem other_chunk_2_33 :
    (∀ j : Fin 40, (33 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 33) (recipe 2 j)).eval profile2≤rawProfile2 (.b 33 j)) ∧
    (∀ j : Fin 40, (33 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 33) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 33 j)) ∧
    (∀ l : Fin 40, (33 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 33) (recipe 2 (next 33)) (recipe 2 l)
        (rawProfile2 (.a (next 33) l))≤rawProfile2 (.p 33 l)) := by
  decide +kernel

theorem d_chunk_2_33 : ∀ j l : Fin 40, (33 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 33) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 33 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 33 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_33


