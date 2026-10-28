-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther0Chunk01
-- name    : BS2_b3ba934b_Endpoint16RawOther0Chunk01
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:30:33.200765+00:00
-- url     : https://prove2.me/theorems/0442c525-c7f4-4b2d-937a-2692ff391144
-- title:
--   Sensitivity separation: Endpoint16RawOther0Chunk01 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther0Chunk01` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther0Chunk01.lean; original SHA-256 e416b48297c23f0da2ba1e0ae7ede14bb1543d3fb4034779d92d27946d9bbd36; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_0_4 : ∀ j : Fin 16, (4 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 4) (recipe 0 j)).eval profile0≤rawProfile0 (.a 4 j) := by
  decide +kernel

theorem other_chunk_0_4 :
    (∀ j : Fin 16, (4 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 4) (recipe 0 j)).eval profile0≤rawProfile0 (.b 4 j)) ∧
    (∀ j : Fin 16, (4 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 4) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 4 j)) ∧
    (∀ l : Fin 16, (4 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 4) (recipe 0 (next 4)) (recipe 0 l)
        (rawProfile0 (.a (next 4) l))≤rawProfile0 (.p 4 l)) := by
  decide +kernel

theorem d_chunk_0_4 : ∀ j l : Fin 16, (4 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 4) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 4 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 4 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_5 : ∀ j : Fin 16, (5 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 5) (recipe 0 j)).eval profile0≤rawProfile0 (.a 5 j) := by
  decide +kernel

theorem other_chunk_0_5 :
    (∀ j : Fin 16, (5 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 5) (recipe 0 j)).eval profile0≤rawProfile0 (.b 5 j)) ∧
    (∀ j : Fin 16, (5 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 5) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 5 j)) ∧
    (∀ l : Fin 16, (5 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 5) (recipe 0 (next 5)) (recipe 0 l)
        (rawProfile0 (.a (next 5) l))≤rawProfile0 (.p 5 l)) := by
  decide +kernel

theorem d_chunk_0_5 : ∀ j l : Fin 16, (5 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 5) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 5 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 5 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_6 : ∀ j : Fin 16, (6 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 6) (recipe 0 j)).eval profile0≤rawProfile0 (.a 6 j) := by
  decide +kernel

theorem other_chunk_0_6 :
    (∀ j : Fin 16, (6 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 6) (recipe 0 j)).eval profile0≤rawProfile0 (.b 6 j)) ∧
    (∀ j : Fin 16, (6 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 6) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 6 j)) ∧
    (∀ l : Fin 16, (6 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 6) (recipe 0 (next 6)) (recipe 0 l)
        (rawProfile0 (.a (next 6) l))≤rawProfile0 (.p 6 l)) := by
  decide +kernel

theorem d_chunk_0_6 : ∀ j l : Fin 16, (6 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 6) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 6 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 6 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_7 : ∀ j : Fin 16, (7 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 7) (recipe 0 j)).eval profile0≤rawProfile0 (.a 7 j) := by
  decide +kernel

theorem other_chunk_0_7 :
    (∀ j : Fin 16, (7 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 7) (recipe 0 j)).eval profile0≤rawProfile0 (.b 7 j)) ∧
    (∀ j : Fin 16, (7 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 7) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 7 j)) ∧
    (∀ l : Fin 16, (7 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 7) (recipe 0 (next 7)) (recipe 0 l)
        (rawProfile0 (.a (next 7) l))≤rawProfile0 (.p 7 l)) := by
  decide +kernel

theorem d_chunk_0_7 : ∀ j l : Fin 16, (7 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 7) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 7 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 7 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_0_7


