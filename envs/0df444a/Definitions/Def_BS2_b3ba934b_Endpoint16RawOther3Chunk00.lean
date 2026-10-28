-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther3Chunk00
-- name    : BS2_b3ba934b_Endpoint16RawOther3Chunk00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:31:06.418988+00:00
-- url     : https://prove2.me/theorems/55c0e50b-2843-4492-acee-15c6f2331eb2
-- title:
--   Sensitivity separation: Endpoint16RawOther3Chunk00 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther3Chunk00` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther3Chunk00.lean; original SHA-256 62b6e2b40849534658a4f7b418b66bfe89266a1c696481b07bb85d30b5a37220; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_3_0 : ∀ j : Fin 16, (0 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 0) (recipe 3 j)).eval profile3≤rawProfile3 (.a 0 j) := by
  decide +kernel

theorem other_chunk_3_0 :
    (∀ j : Fin 16, (0 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 0) (recipe 3 j)).eval profile3≤rawProfile3 (.b 0 j)) ∧
    (∀ j : Fin 16, (0 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 0) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 0 j)) ∧
    (∀ l : Fin 16, (0 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 0) (recipe 3 (next 0)) (recipe 3 l)
        (rawProfile3 (.a (next 0) l))≤rawProfile3 (.p 0 l)) := by
  decide +kernel

theorem d_chunk_3_0 : ∀ j l : Fin 16, (0 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 0) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 0 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 0 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_1 : ∀ j : Fin 16, (1 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 1) (recipe 3 j)).eval profile3≤rawProfile3 (.a 1 j) := by
  decide +kernel

theorem other_chunk_3_1 :
    (∀ j : Fin 16, (1 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 1) (recipe 3 j)).eval profile3≤rawProfile3 (.b 1 j)) ∧
    (∀ j : Fin 16, (1 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 1) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 1 j)) ∧
    (∀ l : Fin 16, (1 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 1) (recipe 3 (next 1)) (recipe 3 l)
        (rawProfile3 (.a (next 1) l))≤rawProfile3 (.p 1 l)) := by
  decide +kernel

theorem d_chunk_3_1 : ∀ j l : Fin 16, (1 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 1) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 1 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 1 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_2 : ∀ j : Fin 16, (2 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 2) (recipe 3 j)).eval profile3≤rawProfile3 (.a 2 j) := by
  decide +kernel

theorem other_chunk_3_2 :
    (∀ j : Fin 16, (2 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 2) (recipe 3 j)).eval profile3≤rawProfile3 (.b 2 j)) ∧
    (∀ j : Fin 16, (2 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 2) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 2 j)) ∧
    (∀ l : Fin 16, (2 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 2) (recipe 3 (next 2)) (recipe 3 l)
        (rawProfile3 (.a (next 2) l))≤rawProfile3 (.p 2 l)) := by
  decide +kernel

theorem d_chunk_3_2 : ∀ j l : Fin 16, (2 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 2) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 2 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 2 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_3 : ∀ j : Fin 16, (3 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 3) (recipe 3 j)).eval profile3≤rawProfile3 (.a 3 j) := by
  decide +kernel

theorem other_chunk_3_3 :
    (∀ j : Fin 16, (3 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 3) (recipe 3 j)).eval profile3≤rawProfile3 (.b 3 j)) ∧
    (∀ j : Fin 16, (3 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 3) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 3 j)) ∧
    (∀ l : Fin 16, (3 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 3) (recipe 3 (next 3)) (recipe 3 l)
        (rawProfile3 (.a (next 3) l))≤rawProfile3 (.p 3 l)) := by
  decide +kernel

theorem d_chunk_3_3 : ∀ j l : Fin 16, (3 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 3) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 3 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 3 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_3_3


