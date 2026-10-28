-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk16
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk16
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:23:28.730398+00:00
-- url     : https://prove2.me/theorems/1888bd3f-c535-48fc-8559-9abc34cee00d
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk16 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk16` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk16.lean; original SHA-256 a2b4153907ad767d64f8b255b73a05c8602cf8e42e694832e861e21dda71108f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_32 : ∀ j : Fin 40, (32 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 32) (recipe 3 j)≤rawProfile3 (.a 32 j) := by
  decide +kernel

theorem other_chunk_3_32 :
    (∀ j : Fin 40, (32 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 32) (recipe 3 j)).eval profile3≤rawProfile3 (.b 32 j)) ∧
    (∀ j : Fin 40, (32 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 32) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 32 j)) ∧
    (∀ l : Fin 40, (32 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 32) (recipe 3 (next 32)) (recipe 3 l)
        (rawProfile3 (.a (next 32) l))≤rawProfile3 (.p 32 l)) := by
  decide +kernel

theorem d_chunk_3_32 : ∀ j l : Fin 40, (32 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 32) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 32 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 32 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_33 : ∀ j : Fin 40, (33 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 33) (recipe 3 j)≤rawProfile3 (.a 33 j) := by
  decide +kernel

theorem other_chunk_3_33 :
    (∀ j : Fin 40, (33 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 33) (recipe 3 j)).eval profile3≤rawProfile3 (.b 33 j)) ∧
    (∀ j : Fin 40, (33 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 33) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 33 j)) ∧
    (∀ l : Fin 40, (33 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 33) (recipe 3 (next 33)) (recipe 3 l)
        (rawProfile3 (.a (next 33) l))≤rawProfile3 (.p 33 l)) := by
  decide +kernel

theorem d_chunk_3_33 : ∀ j l : Fin 40, (33 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 33) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 33 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 33 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_33


