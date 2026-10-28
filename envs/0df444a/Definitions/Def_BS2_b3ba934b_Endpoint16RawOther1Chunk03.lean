-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther1Chunk03
-- name    : BS2_b3ba934b_Endpoint16RawOther1Chunk03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:30:58.169888+00:00
-- url     : https://prove2.me/theorems/4173245d-dd62-4c5e-820c-6906ed62e8fb
-- title:
--   Sensitivity separation: Endpoint16RawOther1Chunk03 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther1Chunk03` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther1Chunk03.lean; original SHA-256 161a6a0bf7771ec792dcd731135726c183fb939217e57a24a7ac2f280d40f39c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_1_12 : ∀ j : Fin 16, (12 : Fin 16)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 12) (recipe 1 j)).eval profile1≤rawProfile1 (.a 12 j) := by
  decide +kernel

theorem other_chunk_1_12 :
    (∀ j : Fin 16, (12 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 1 12) (recipe 1 j)).eval profile1≤rawProfile1 (.b 12 j)) ∧
    (∀ j : Fin 16, (12 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 1 12) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 12 j)) ∧
    (∀ l : Fin 16, (12 : Fin 16)<l →
      pCore 16 caps.pcross profile1 (recipe 1 12) (recipe 1 (next 12)) (recipe 1 l)
        (rawProfile1 (.a (next 12) l))≤rawProfile1 (.p 12 l)) := by
  decide +kernel

theorem d_chunk_1_12 : ∀ j l : Fin 16, (12 : Fin 16)≤j → j<l →
    dCore 16 5003 profile1 (recipe 1 12) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 12 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 12 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_13 : ∀ j : Fin 16, (13 : Fin 16)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 13) (recipe 1 j)).eval profile1≤rawProfile1 (.a 13 j) := by
  decide +kernel

theorem other_chunk_1_13 :
    (∀ j : Fin 16, (13 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 1 13) (recipe 1 j)).eval profile1≤rawProfile1 (.b 13 j)) ∧
    (∀ j : Fin 16, (13 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 1 13) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 13 j)) ∧
    (∀ l : Fin 16, (13 : Fin 16)<l →
      pCore 16 caps.pcross profile1 (recipe 1 13) (recipe 1 (next 13)) (recipe 1 l)
        (rawProfile1 (.a (next 13) l))≤rawProfile1 (.p 13 l)) := by
  decide +kernel

theorem d_chunk_1_13 : ∀ j l : Fin 16, (13 : Fin 16)≤j → j<l →
    dCore 16 5003 profile1 (recipe 1 13) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 13 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 13 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_14 : ∀ j : Fin 16, (14 : Fin 16)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 14) (recipe 1 j)).eval profile1≤rawProfile1 (.a 14 j) := by
  decide +kernel

theorem other_chunk_1_14 :
    (∀ j : Fin 16, (14 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 1 14) (recipe 1 j)).eval profile1≤rawProfile1 (.b 14 j)) ∧
    (∀ j : Fin 16, (14 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 1 14) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 14 j)) ∧
    (∀ l : Fin 16, (14 : Fin 16)<l →
      pCore 16 caps.pcross profile1 (recipe 1 14) (recipe 1 (next 14)) (recipe 1 l)
        (rawProfile1 (.a (next 14) l))≤rawProfile1 (.p 14 l)) := by
  decide +kernel

theorem d_chunk_1_14 : ∀ j l : Fin 16, (14 : Fin 16)≤j → j<l →
    dCore 16 5003 profile1 (recipe 1 14) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 14 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 14 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_15 : ∀ j : Fin 16, (15 : Fin 16)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 1 15) (recipe 1 j)).eval profile1≤rawProfile1 (.a 15 j) := by
  decide +kernel

theorem other_chunk_1_15 :
    (∀ j : Fin 16, (15 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 1 15) (recipe 1 j)).eval profile1≤rawProfile1 (.b 15 j)) ∧
    (∀ j : Fin 16, (15 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 1 15) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 15 j)) ∧
    (∀ l : Fin 16, (15 : Fin 16)<l →
      pCore 16 caps.pcross profile1 (recipe 1 15) (recipe 1 (next 15)) (recipe 1 l)
        (rawProfile1 (.a (next 15) l))≤rawProfile1 (.p 15 l)) := by
  decide +kernel

theorem d_chunk_1_15 : ∀ j l : Fin 16, (15 : Fin 16)≤j → j<l →
    dCore 16 5003 profile1 (recipe 1 15) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 15 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 15 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_1_15


