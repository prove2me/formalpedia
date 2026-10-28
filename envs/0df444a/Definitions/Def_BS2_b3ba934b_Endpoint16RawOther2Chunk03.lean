-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther2Chunk03
-- name    : BS2_b3ba934b_Endpoint16RawOther2Chunk03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:30:20.732975+00:00
-- url     : https://prove2.me/theorems/d4ce8bf4-c6dd-4207-a246-e127a4b3ff78
-- title:
--   Sensitivity separation: Endpoint16RawOther2Chunk03 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther2Chunk03` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther2Chunk03.lean; original SHA-256 895506a9b3e296ae37045b4dbea9345d200a0476ef83c2b013f5f0e05cd380c0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_2_12 : ∀ j : Fin 16, (12 : Fin 16)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 12) (recipe 2 j)).eval profile2≤rawProfile2 (.a 12 j) := by
  decide +kernel

theorem other_chunk_2_12 :
    (∀ j : Fin 16, (12 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 2 12) (recipe 2 j)).eval profile2≤rawProfile2 (.b 12 j)) ∧
    (∀ j : Fin 16, (12 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 2 12) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 12 j)) ∧
    (∀ l : Fin 16, (12 : Fin 16)<l →
      pCore 16 caps.pcross profile2 (recipe 2 12) (recipe 2 (next 12)) (recipe 2 l)
        (rawProfile2 (.a (next 12) l))≤rawProfile2 (.p 12 l)) := by
  decide +kernel

theorem d_chunk_2_12 : ∀ j l : Fin 16, (12 : Fin 16)≤j → j<l →
    dCore 16 5003 profile2 (recipe 2 12) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 12 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 12 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_13 : ∀ j : Fin 16, (13 : Fin 16)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 13) (recipe 2 j)).eval profile2≤rawProfile2 (.a 13 j) := by
  decide +kernel

theorem other_chunk_2_13 :
    (∀ j : Fin 16, (13 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 2 13) (recipe 2 j)).eval profile2≤rawProfile2 (.b 13 j)) ∧
    (∀ j : Fin 16, (13 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 2 13) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 13 j)) ∧
    (∀ l : Fin 16, (13 : Fin 16)<l →
      pCore 16 caps.pcross profile2 (recipe 2 13) (recipe 2 (next 13)) (recipe 2 l)
        (rawProfile2 (.a (next 13) l))≤rawProfile2 (.p 13 l)) := by
  decide +kernel

theorem d_chunk_2_13 : ∀ j l : Fin 16, (13 : Fin 16)≤j → j<l →
    dCore 16 5003 profile2 (recipe 2 13) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 13 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 13 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_14 : ∀ j : Fin 16, (14 : Fin 16)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 14) (recipe 2 j)).eval profile2≤rawProfile2 (.a 14 j) := by
  decide +kernel

theorem other_chunk_2_14 :
    (∀ j : Fin 16, (14 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 2 14) (recipe 2 j)).eval profile2≤rawProfile2 (.b 14 j)) ∧
    (∀ j : Fin 16, (14 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 2 14) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 14 j)) ∧
    (∀ l : Fin 16, (14 : Fin 16)<l →
      pCore 16 caps.pcross profile2 (recipe 2 14) (recipe 2 (next 14)) (recipe 2 l)
        (rawProfile2 (.a (next 14) l))≤rawProfile2 (.p 14 l)) := by
  decide +kernel

theorem d_chunk_2_14 : ∀ j l : Fin 16, (14 : Fin 16)≤j → j<l →
    dCore 16 5003 profile2 (recipe 2 14) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 14 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 14 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_15 : ∀ j : Fin 16, (15 : Fin 16)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 15) (recipe 2 j)).eval profile2≤rawProfile2 (.a 15 j) := by
  decide +kernel

theorem other_chunk_2_15 :
    (∀ j : Fin 16, (15 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 2 15) (recipe 2 j)).eval profile2≤rawProfile2 (.b 15 j)) ∧
    (∀ j : Fin 16, (15 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 2 15) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 15 j)) ∧
    (∀ l : Fin 16, (15 : Fin 16)<l →
      pCore 16 caps.pcross profile2 (recipe 2 15) (recipe 2 (next 15)) (recipe 2 l)
        (rawProfile2 (.a (next 15) l))≤rawProfile2 (.p 15 l)) := by
  decide +kernel

theorem d_chunk_2_15 : ∀ j l : Fin 16, (15 : Fin 16)≤j → j<l →
    dCore 16 5003 profile2 (recipe 2 15) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 15 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 15 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_2_15


