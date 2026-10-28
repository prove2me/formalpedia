-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther1Chunk00
-- name    : BS2_b3ba934b_Endpoint16RawOther1Chunk00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:31:15.736848+00:00
-- url     : https://prove2.me/theorems/13568223-f536-4f9e-92f9-699994668cf0
-- title:
--   Sensitivity separation: Endpoint16RawOther1Chunk00 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther1Chunk00` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther1Chunk00.lean; original SHA-256 0ef2e183066d76a77a29c34430939985f014030f73644d67857a10677d83c1bb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_1_0 : ∀ j : Fin 16, (0 : Fin 16)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 0) (recipe 1 j)).eval profile1≤rawProfile1 (.a 0 j) := by
  decide +kernel

theorem other_chunk_1_0 :
    (∀ j : Fin 16, (0 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 1 0) (recipe 1 j)).eval profile1≤rawProfile1 (.b 0 j)) ∧
    (∀ j : Fin 16, (0 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 1 0) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 0 j)) ∧
    (∀ l : Fin 16, (0 : Fin 16)<l →
      pCore 16 caps.pcross profile1 (recipe 1 0) (recipe 1 (next 0)) (recipe 1 l)
        (rawProfile1 (.a (next 0) l))≤rawProfile1 (.p 0 l)) := by
  decide +kernel

theorem d_chunk_1_0 : ∀ j l : Fin 16, (0 : Fin 16)≤j → j<l →
    dCore 16 5003 profile1 (recipe 1 0) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 0 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 0 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_1 : ∀ j : Fin 16, (1 : Fin 16)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 1) (recipe 1 j)).eval profile1≤rawProfile1 (.a 1 j) := by
  decide +kernel

theorem other_chunk_1_1 :
    (∀ j : Fin 16, (1 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 1 1) (recipe 1 j)).eval profile1≤rawProfile1 (.b 1 j)) ∧
    (∀ j : Fin 16, (1 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 1 1) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 1 j)) ∧
    (∀ l : Fin 16, (1 : Fin 16)<l →
      pCore 16 caps.pcross profile1 (recipe 1 1) (recipe 1 (next 1)) (recipe 1 l)
        (rawProfile1 (.a (next 1) l))≤rawProfile1 (.p 1 l)) := by
  decide +kernel

theorem d_chunk_1_1 : ∀ j l : Fin 16, (1 : Fin 16)≤j → j<l →
    dCore 16 5003 profile1 (recipe 1 1) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 1 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 1 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_2 : ∀ j : Fin 16, (2 : Fin 16)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 2) (recipe 1 j)).eval profile1≤rawProfile1 (.a 2 j) := by
  decide +kernel

theorem other_chunk_1_2 :
    (∀ j : Fin 16, (2 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 1 2) (recipe 1 j)).eval profile1≤rawProfile1 (.b 2 j)) ∧
    (∀ j : Fin 16, (2 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 1 2) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 2 j)) ∧
    (∀ l : Fin 16, (2 : Fin 16)<l →
      pCore 16 caps.pcross profile1 (recipe 1 2) (recipe 1 (next 2)) (recipe 1 l)
        (rawProfile1 (.a (next 2) l))≤rawProfile1 (.p 2 l)) := by
  decide +kernel

theorem d_chunk_1_2 : ∀ j l : Fin 16, (2 : Fin 16)≤j → j<l →
    dCore 16 5003 profile1 (recipe 1 2) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 2 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 2 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_3 : ∀ j : Fin 16, (3 : Fin 16)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 3) (recipe 1 j)).eval profile1≤rawProfile1 (.a 3 j) := by
  decide +kernel

theorem other_chunk_1_3 :
    (∀ j : Fin 16, (3 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 1 3) (recipe 1 j)).eval profile1≤rawProfile1 (.b 3 j)) ∧
    (∀ j : Fin 16, (3 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 1 3) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 3 j)) ∧
    (∀ l : Fin 16, (3 : Fin 16)<l →
      pCore 16 caps.pcross profile1 (recipe 1 3) (recipe 1 (next 3)) (recipe 1 l)
        (rawProfile1 (.a (next 3) l))≤rawProfile1 (.p 3 l)) := by
  decide +kernel

theorem d_chunk_1_3 : ∀ j l : Fin 16, (3 : Fin 16)≤j → j<l →
    dCore 16 5003 profile1 (recipe 1 3) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 3 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 3 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_1_3


