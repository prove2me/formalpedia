-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk06
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk06
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:08:47.143105+00:00
-- url     : https://prove2.me/theorems/a1645890-269b-4844-996b-23c56584a91a
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk06 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk06` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk06.lean; original SHA-256 d354376b320771116b23f7171f23e27267b1325dd4e05868d731be2c764d146c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_12 : ∀ j : Fin 40, (12 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 12) (recipe 2 j)≤rawProfile2 (.a 12 j) := by
  decide +kernel

theorem other_chunk_2_12 :
    (∀ j : Fin 40, (12 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 12) (recipe 2 j)).eval profile2≤rawProfile2 (.b 12 j)) ∧
    (∀ j : Fin 40, (12 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 12) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 12 j)) ∧
    (∀ l : Fin 40, (12 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 12) (recipe 2 (next 12)) (recipe 2 l)
        (rawProfile2 (.a (next 12) l))≤rawProfile2 (.p 12 l)) := by
  decide +kernel

theorem d_chunk_2_12 : ∀ j l : Fin 40, (12 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 12) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 12 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 12 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_13 : ∀ j : Fin 40, (13 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 13) (recipe 2 j)≤rawProfile2 (.a 13 j) := by
  decide +kernel

theorem other_chunk_2_13 :
    (∀ j : Fin 40, (13 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 13) (recipe 2 j)).eval profile2≤rawProfile2 (.b 13 j)) ∧
    (∀ j : Fin 40, (13 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 13) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 13 j)) ∧
    (∀ l : Fin 40, (13 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 13) (recipe 2 (next 13)) (recipe 2 l)
        (rawProfile2 (.a (next 13) l))≤rawProfile2 (.p 13 l)) := by
  decide +kernel

theorem d_chunk_2_13 : ∀ j l : Fin 40, (13 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 13) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 13 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 13 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_13


