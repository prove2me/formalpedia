-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther0Chunk00
-- name    : BS2_b3ba934b_Endpoint16RawOther0Chunk00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:29:49.136132+00:00
-- url     : https://prove2.me/theorems/7343b71b-6d76-45ee-80a4-54be1a590e45
-- title:
--   Sensitivity separation: Endpoint16RawOther0Chunk00 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther0Chunk00` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther0Chunk00.lean; original SHA-256 287972b50ab96ca216c8e58afd2eca672905135bc039a109268e18c00aa36aa4; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_0_0 : ∀ j : Fin 16, (0 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 0) (recipe 0 j)).eval profile0≤rawProfile0 (.a 0 j) := by
  decide +kernel

theorem other_chunk_0_0 :
    (∀ j : Fin 16, (0 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 0) (recipe 0 j)).eval profile0≤rawProfile0 (.b 0 j)) ∧
    (∀ j : Fin 16, (0 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 0) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 0 j)) ∧
    (∀ l : Fin 16, (0 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 0) (recipe 0 (next 0)) (recipe 0 l)
        (rawProfile0 (.a (next 0) l))≤rawProfile0 (.p 0 l)) := by
  decide +kernel

theorem d_chunk_0_0 : ∀ j l : Fin 16, (0 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 0) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 0 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 0 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_1 : ∀ j : Fin 16, (1 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 1) (recipe 0 j)).eval profile0≤rawProfile0 (.a 1 j) := by
  decide +kernel

theorem other_chunk_0_1 :
    (∀ j : Fin 16, (1 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 1) (recipe 0 j)).eval profile0≤rawProfile0 (.b 1 j)) ∧
    (∀ j : Fin 16, (1 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 1) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 1 j)) ∧
    (∀ l : Fin 16, (1 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 1) (recipe 0 (next 1)) (recipe 0 l)
        (rawProfile0 (.a (next 1) l))≤rawProfile0 (.p 1 l)) := by
  decide +kernel

theorem d_chunk_0_1 : ∀ j l : Fin 16, (1 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 1) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 1 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 1 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_2 : ∀ j : Fin 16, (2 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 2) (recipe 0 j)).eval profile0≤rawProfile0 (.a 2 j) := by
  decide +kernel

theorem other_chunk_0_2 :
    (∀ j : Fin 16, (2 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 2) (recipe 0 j)).eval profile0≤rawProfile0 (.b 2 j)) ∧
    (∀ j : Fin 16, (2 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 2) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 2 j)) ∧
    (∀ l : Fin 16, (2 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 2) (recipe 0 (next 2)) (recipe 0 l)
        (rawProfile0 (.a (next 2) l))≤rawProfile0 (.p 2 l)) := by
  decide +kernel

theorem d_chunk_0_2 : ∀ j l : Fin 16, (2 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 2) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 2 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 2 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_3 : ∀ j : Fin 16, (3 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 3) (recipe 0 j)).eval profile0≤rawProfile0 (.a 3 j) := by
  decide +kernel

theorem other_chunk_0_3 :
    (∀ j : Fin 16, (3 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 3) (recipe 0 j)).eval profile0≤rawProfile0 (.b 3 j)) ∧
    (∀ j : Fin 16, (3 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 3) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 3 j)) ∧
    (∀ l : Fin 16, (3 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 3) (recipe 0 (next 3)) (recipe 0 l)
        (rawProfile0 (.a (next 3) l))≤rawProfile0 (.p 3 l)) := by
  decide +kernel

theorem d_chunk_0_3 : ∀ j l : Fin 16, (3 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 3) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 3 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 3 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_0_3


