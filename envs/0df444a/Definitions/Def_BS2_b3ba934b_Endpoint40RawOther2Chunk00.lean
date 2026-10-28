-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk00
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:04:48.206457+00:00
-- url     : https://prove2.me/theorems/55ee6d3b-aa7e-42f0-9e41-cefb86f8ed48
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk00 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk00` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk00.lean; original SHA-256 243a4b99872a3cb6deaffce00700197195bde81df237e64c4012435cca49692b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_0 : ∀ j : Fin 40, (0 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 0) (recipe 2 j)≤rawProfile2 (.a 0 j) := by
  decide +kernel

theorem other_chunk_2_0 :
    (∀ j : Fin 40, (0 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 0) (recipe 2 j)).eval profile2≤rawProfile2 (.b 0 j)) ∧
    (∀ j : Fin 40, (0 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 0) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 0 j)) ∧
    (∀ l : Fin 40, (0 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 0) (recipe 2 (next 0)) (recipe 2 l)
        (rawProfile2 (.a (next 0) l))≤rawProfile2 (.p 0 l)) := by
  decide +kernel

theorem d_chunk_2_0 : ∀ j l : Fin 40, (0 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 0) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 0 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 0 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_1 : ∀ j : Fin 40, (1 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 1) (recipe 2 j)≤rawProfile2 (.a 1 j) := by
  decide +kernel

theorem other_chunk_2_1 :
    (∀ j : Fin 40, (1 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 1) (recipe 2 j)).eval profile2≤rawProfile2 (.b 1 j)) ∧
    (∀ j : Fin 40, (1 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 1) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 1 j)) ∧
    (∀ l : Fin 40, (1 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 1) (recipe 2 (next 1)) (recipe 2 l)
        (rawProfile2 (.a (next 1) l))≤rawProfile2 (.p 1 l)) := by
  decide +kernel

theorem d_chunk_2_1 : ∀ j l : Fin 40, (1 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 1) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 1 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 1 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_1


