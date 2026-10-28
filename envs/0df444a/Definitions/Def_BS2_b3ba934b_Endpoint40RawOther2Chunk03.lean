-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk03
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:06:58.035828+00:00
-- url     : https://prove2.me/theorems/22c8b2de-2455-4922-a4bb-866713b7eac3
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk03 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk03` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk03.lean; original SHA-256 0c8af3495c81cbd12f7b4b5fdfa3f498cafabb76c106c6944c1340ab3fc38fad; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_6 : ∀ j : Fin 40, (6 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 6) (recipe 2 j)≤rawProfile2 (.a 6 j) := by
  decide +kernel

theorem other_chunk_2_6 :
    (∀ j : Fin 40, (6 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 6) (recipe 2 j)).eval profile2≤rawProfile2 (.b 6 j)) ∧
    (∀ j : Fin 40, (6 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 6) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 6 j)) ∧
    (∀ l : Fin 40, (6 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 6) (recipe 2 (next 6)) (recipe 2 l)
        (rawProfile2 (.a (next 6) l))≤rawProfile2 (.p 6 l)) := by
  decide +kernel

theorem d_chunk_2_6 : ∀ j l : Fin 40, (6 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 6) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 6 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 6 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_7 : ∀ j : Fin 40, (7 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 7) (recipe 2 j)≤rawProfile2 (.a 7 j) := by
  decide +kernel

theorem other_chunk_2_7 :
    (∀ j : Fin 40, (7 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 7) (recipe 2 j)).eval profile2≤rawProfile2 (.b 7 j)) ∧
    (∀ j : Fin 40, (7 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 7) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 7 j)) ∧
    (∀ l : Fin 40, (7 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 7) (recipe 2 (next 7)) (recipe 2 l)
        (rawProfile2 (.a (next 7) l))≤rawProfile2 (.p 7 l)) := by
  decide +kernel

theorem d_chunk_2_7 : ∀ j l : Fin 40, (7 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 7) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 7 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 7 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_7


