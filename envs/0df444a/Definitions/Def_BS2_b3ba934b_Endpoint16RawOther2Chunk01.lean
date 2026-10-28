-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther2Chunk01
-- name    : BS2_b3ba934b_Endpoint16RawOther2Chunk01
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:29:32.64098+00:00
-- url     : https://prove2.me/theorems/e183d955-d1f8-4a41-83d2-e178d6a51b05
-- title:
--   Sensitivity separation: Endpoint16RawOther2Chunk01 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther2Chunk01` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther2Chunk01.lean; original SHA-256 46571eb9db71d320ba38e93a3b7375f2b745e0600cfafe413fe2bf874f67a681; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_2_4 : ∀ j : Fin 16, (4 : Fin 16)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 4) (recipe 2 j)).eval profile2≤rawProfile2 (.a 4 j) := by
  decide +kernel

theorem other_chunk_2_4 :
    (∀ j : Fin 16, (4 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 2 4) (recipe 2 j)).eval profile2≤rawProfile2 (.b 4 j)) ∧
    (∀ j : Fin 16, (4 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 2 4) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 4 j)) ∧
    (∀ l : Fin 16, (4 : Fin 16)<l →
      pCore 16 caps.pcross profile2 (recipe 2 4) (recipe 2 (next 4)) (recipe 2 l)
        (rawProfile2 (.a (next 4) l))≤rawProfile2 (.p 4 l)) := by
  decide +kernel

theorem d_chunk_2_4 : ∀ j l : Fin 16, (4 : Fin 16)≤j → j<l →
    dCore 16 5003 profile2 (recipe 2 4) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 4 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 4 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_5 : ∀ j : Fin 16, (5 : Fin 16)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 5) (recipe 2 j)).eval profile2≤rawProfile2 (.a 5 j) := by
  decide +kernel

theorem other_chunk_2_5 :
    (∀ j : Fin 16, (5 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 2 5) (recipe 2 j)).eval profile2≤rawProfile2 (.b 5 j)) ∧
    (∀ j : Fin 16, (5 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 2 5) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 5 j)) ∧
    (∀ l : Fin 16, (5 : Fin 16)<l →
      pCore 16 caps.pcross profile2 (recipe 2 5) (recipe 2 (next 5)) (recipe 2 l)
        (rawProfile2 (.a (next 5) l))≤rawProfile2 (.p 5 l)) := by
  decide +kernel

theorem d_chunk_2_5 : ∀ j l : Fin 16, (5 : Fin 16)≤j → j<l →
    dCore 16 5003 profile2 (recipe 2 5) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 5 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 5 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_6 : ∀ j : Fin 16, (6 : Fin 16)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 6) (recipe 2 j)).eval profile2≤rawProfile2 (.a 6 j) := by
  decide +kernel

theorem other_chunk_2_6 :
    (∀ j : Fin 16, (6 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 2 6) (recipe 2 j)).eval profile2≤rawProfile2 (.b 6 j)) ∧
    (∀ j : Fin 16, (6 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 2 6) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 6 j)) ∧
    (∀ l : Fin 16, (6 : Fin 16)<l →
      pCore 16 caps.pcross profile2 (recipe 2 6) (recipe 2 (next 6)) (recipe 2 l)
        (rawProfile2 (.a (next 6) l))≤rawProfile2 (.p 6 l)) := by
  decide +kernel

theorem d_chunk_2_6 : ∀ j l : Fin 16, (6 : Fin 16)≤j → j<l →
    dCore 16 5003 profile2 (recipe 2 6) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 6 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 6 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_7 : ∀ j : Fin 16, (7 : Fin 16)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 7) (recipe 2 j)).eval profile2≤rawProfile2 (.a 7 j) := by
  decide +kernel

theorem other_chunk_2_7 :
    (∀ j : Fin 16, (7 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 2 7) (recipe 2 j)).eval profile2≤rawProfile2 (.b 7 j)) ∧
    (∀ j : Fin 16, (7 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 2 7) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 7 j)) ∧
    (∀ l : Fin 16, (7 : Fin 16)<l →
      pCore 16 caps.pcross profile2 (recipe 2 7) (recipe 2 (next 7)) (recipe 2 l)
        (rawProfile2 (.a (next 7) l))≤rawProfile2 (.p 7 l)) := by
  decide +kernel

theorem d_chunk_2_7 : ∀ j l : Fin 16, (7 : Fin 16)≤j → j<l →
    dCore 16 5003 profile2 (recipe 2 7) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 7 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 7 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_2_7


