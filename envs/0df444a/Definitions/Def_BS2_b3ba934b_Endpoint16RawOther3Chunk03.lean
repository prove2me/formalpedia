-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther3Chunk03
-- name    : BS2_b3ba934b_Endpoint16RawOther3Chunk03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:32:22.695328+00:00
-- url     : https://prove2.me/theorems/1be66261-bb84-446c-9afe-39543201467b
-- title:
--   Sensitivity separation: Endpoint16RawOther3Chunk03 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther3Chunk03` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther3Chunk03.lean; original SHA-256 309b07b01164c61f2fe972d919070fccb3367ad7486eb0b3b619592d4a07487c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_3_12 : ∀ j : Fin 16, (12 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 12) (recipe 3 j)).eval profile3≤rawProfile3 (.a 12 j) := by
  decide +kernel

theorem other_chunk_3_12 :
    (∀ j : Fin 16, (12 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 12) (recipe 3 j)).eval profile3≤rawProfile3 (.b 12 j)) ∧
    (∀ j : Fin 16, (12 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 12) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 12 j)) ∧
    (∀ l : Fin 16, (12 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 12) (recipe 3 (next 12)) (recipe 3 l)
        (rawProfile3 (.a (next 12) l))≤rawProfile3 (.p 12 l)) := by
  decide +kernel

theorem d_chunk_3_12 : ∀ j l : Fin 16, (12 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 12) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 12 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 12 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_13 : ∀ j : Fin 16, (13 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 13) (recipe 3 j)).eval profile3≤rawProfile3 (.a 13 j) := by
  decide +kernel

theorem other_chunk_3_13 :
    (∀ j : Fin 16, (13 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 13) (recipe 3 j)).eval profile3≤rawProfile3 (.b 13 j)) ∧
    (∀ j : Fin 16, (13 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 13) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 13 j)) ∧
    (∀ l : Fin 16, (13 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 13) (recipe 3 (next 13)) (recipe 3 l)
        (rawProfile3 (.a (next 13) l))≤rawProfile3 (.p 13 l)) := by
  decide +kernel

theorem d_chunk_3_13 : ∀ j l : Fin 16, (13 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 13) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 13 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 13 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_14 : ∀ j : Fin 16, (14 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 14) (recipe 3 j)).eval profile3≤rawProfile3 (.a 14 j) := by
  decide +kernel

theorem other_chunk_3_14 :
    (∀ j : Fin 16, (14 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 14) (recipe 3 j)).eval profile3≤rawProfile3 (.b 14 j)) ∧
    (∀ j : Fin 16, (14 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 14) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 14 j)) ∧
    (∀ l : Fin 16, (14 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 14) (recipe 3 (next 14)) (recipe 3 l)
        (rawProfile3 (.a (next 14) l))≤rawProfile3 (.p 14 l)) := by
  decide +kernel

theorem d_chunk_3_14 : ∀ j l : Fin 16, (14 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 14) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 14 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 14 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_15 : ∀ j : Fin 16, (15 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 15) (recipe 3 j)).eval profile3≤rawProfile3 (.a 15 j) := by
  decide +kernel

theorem other_chunk_3_15 :
    (∀ j : Fin 16, (15 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 15) (recipe 3 j)).eval profile3≤rawProfile3 (.b 15 j)) ∧
    (∀ j : Fin 16, (15 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 15) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 15 j)) ∧
    (∀ l : Fin 16, (15 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 15) (recipe 3 (next 15)) (recipe 3 l)
        (rawProfile3 (.a (next 15) l))≤rawProfile3 (.p 15 l)) := by
  decide +kernel

theorem d_chunk_3_15 : ∀ j l : Fin 16, (15 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 15) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 15 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 15 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_3_15


