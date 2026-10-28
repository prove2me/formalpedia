-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk02
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk02
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:06:17.114327+00:00
-- url     : https://prove2.me/theorems/633b8b68-6ab1-4a28-8ebc-9a787ff0445c
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk02 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk02` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk02.lean; original SHA-256 909b806d5c71f089b1903fc435743bc00fef3095e2e196a26e26049768dfa6bf; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_4 : ∀ j : Fin 40, (4 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 4) (recipe 2 j)≤rawProfile2 (.a 4 j) := by
  decide +kernel

theorem other_chunk_2_4 :
    (∀ j : Fin 40, (4 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 4) (recipe 2 j)).eval profile2≤rawProfile2 (.b 4 j)) ∧
    (∀ j : Fin 40, (4 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 4) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 4 j)) ∧
    (∀ l : Fin 40, (4 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 4) (recipe 2 (next 4)) (recipe 2 l)
        (rawProfile2 (.a (next 4) l))≤rawProfile2 (.p 4 l)) := by
  decide +kernel

theorem d_chunk_2_4 : ∀ j l : Fin 40, (4 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 4) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 4 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 4 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_5 : ∀ j : Fin 40, (5 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 5) (recipe 2 j)≤rawProfile2 (.a 5 j) := by
  decide +kernel

theorem other_chunk_2_5 :
    (∀ j : Fin 40, (5 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 5) (recipe 2 j)).eval profile2≤rawProfile2 (.b 5 j)) ∧
    (∀ j : Fin 40, (5 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 5) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 5 j)) ∧
    (∀ l : Fin 40, (5 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 5) (recipe 2 (next 5)) (recipe 2 l)
        (rawProfile2 (.a (next 5) l))≤rawProfile2 (.p 5 l)) := by
  decide +kernel

theorem d_chunk_2_5 : ∀ j l : Fin 40, (5 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 5) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 5 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 5 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_5


