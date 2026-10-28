-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk11
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk11
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:12:23.534284+00:00
-- url     : https://prove2.me/theorems/3e4a5ee7-19ce-4b91-b9cc-898790e30631
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk11 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk11` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk11.lean; original SHA-256 5a7dfddce83ffaf00f8d338c09f15b40a1efe4ec070000a7b1abe9629d946db1; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_22 : ∀ j : Fin 40, (22 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 22) (recipe 2 j)≤rawProfile2 (.a 22 j) := by
  decide +kernel

theorem other_chunk_2_22 :
    (∀ j : Fin 40, (22 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 22) (recipe 2 j)).eval profile2≤rawProfile2 (.b 22 j)) ∧
    (∀ j : Fin 40, (22 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 22) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 22 j)) ∧
    (∀ l : Fin 40, (22 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 22) (recipe 2 (next 22)) (recipe 2 l)
        (rawProfile2 (.a (next 22) l))≤rawProfile2 (.p 22 l)) := by
  decide +kernel

theorem d_chunk_2_22 : ∀ j l : Fin 40, (22 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 22) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 22 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 22 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_23 : ∀ j : Fin 40, (23 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 23) (recipe 2 j)≤rawProfile2 (.a 23 j) := by
  decide +kernel

theorem other_chunk_2_23 :
    (∀ j : Fin 40, (23 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 23) (recipe 2 j)).eval profile2≤rawProfile2 (.b 23 j)) ∧
    (∀ j : Fin 40, (23 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 23) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 23 j)) ∧
    (∀ l : Fin 40, (23 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 23) (recipe 2 (next 23)) (recipe 2 l)
        (rawProfile2 (.a (next 23) l))≤rawProfile2 (.p 23 l)) := by
  decide +kernel

theorem d_chunk_2_23 : ∀ j l : Fin 40, (23 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 23) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 23 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 23 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_23


