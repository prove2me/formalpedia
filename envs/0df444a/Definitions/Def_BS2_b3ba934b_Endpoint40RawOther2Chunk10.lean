-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk10
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk10
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:11:44.973205+00:00
-- url     : https://prove2.me/theorems/77e6a518-d77e-4f8b-a48f-1ec542c2b0a2
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk10 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk10` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk10.lean; original SHA-256 d68b54f2b6a2937f008d6f2866c37c29420140e31f8d1a2485294bc1c08dff5b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_20 : ∀ j : Fin 40, (20 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 20) (recipe 2 j)≤rawProfile2 (.a 20 j) := by
  decide +kernel

theorem other_chunk_2_20 :
    (∀ j : Fin 40, (20 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 20) (recipe 2 j)).eval profile2≤rawProfile2 (.b 20 j)) ∧
    (∀ j : Fin 40, (20 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 20) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 20 j)) ∧
    (∀ l : Fin 40, (20 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 20) (recipe 2 (next 20)) (recipe 2 l)
        (rawProfile2 (.a (next 20) l))≤rawProfile2 (.p 20 l)) := by
  decide +kernel

theorem d_chunk_2_20 : ∀ j l : Fin 40, (20 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 20) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 20 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 20 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_21 : ∀ j : Fin 40, (21 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 21) (recipe 2 j)≤rawProfile2 (.a 21 j) := by
  decide +kernel

theorem other_chunk_2_21 :
    (∀ j : Fin 40, (21 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 21) (recipe 2 j)).eval profile2≤rawProfile2 (.b 21 j)) ∧
    (∀ j : Fin 40, (21 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 21) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 21 j)) ∧
    (∀ l : Fin 40, (21 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 21) (recipe 2 (next 21)) (recipe 2 l)
        (rawProfile2 (.a (next 21) l))≤rawProfile2 (.p 21 l)) := by
  decide +kernel

theorem d_chunk_2_21 : ∀ j l : Fin 40, (21 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 21) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 21 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 21 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_21


