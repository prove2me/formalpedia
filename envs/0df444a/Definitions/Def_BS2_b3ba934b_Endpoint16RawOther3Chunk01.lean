-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther3Chunk01
-- name    : BS2_b3ba934b_Endpoint16RawOther3Chunk01
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:31:11.069995+00:00
-- url     : https://prove2.me/theorems/22d513db-cd37-43b3-9e67-2cfdfe9267ca
-- title:
--   Sensitivity separation: Endpoint16RawOther3Chunk01 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther3Chunk01` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther3Chunk01.lean; original SHA-256 9f203a1f9eb2206d6217174ac9f87c42f2718288943d6a2808ce704e84370507; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_3_4 : ∀ j : Fin 16, (4 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 4) (recipe 3 j)).eval profile3≤rawProfile3 (.a 4 j) := by
  decide +kernel

theorem other_chunk_3_4 :
    (∀ j : Fin 16, (4 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 4) (recipe 3 j)).eval profile3≤rawProfile3 (.b 4 j)) ∧
    (∀ j : Fin 16, (4 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 4) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 4 j)) ∧
    (∀ l : Fin 16, (4 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 4) (recipe 3 (next 4)) (recipe 3 l)
        (rawProfile3 (.a (next 4) l))≤rawProfile3 (.p 4 l)) := by
  decide +kernel

theorem d_chunk_3_4 : ∀ j l : Fin 16, (4 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 4) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 4 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 4 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_5 : ∀ j : Fin 16, (5 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 5) (recipe 3 j)).eval profile3≤rawProfile3 (.a 5 j) := by
  decide +kernel

theorem other_chunk_3_5 :
    (∀ j : Fin 16, (5 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 5) (recipe 3 j)).eval profile3≤rawProfile3 (.b 5 j)) ∧
    (∀ j : Fin 16, (5 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 5) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 5 j)) ∧
    (∀ l : Fin 16, (5 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 5) (recipe 3 (next 5)) (recipe 3 l)
        (rawProfile3 (.a (next 5) l))≤rawProfile3 (.p 5 l)) := by
  decide +kernel

theorem d_chunk_3_5 : ∀ j l : Fin 16, (5 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 5) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 5 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 5 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_6 : ∀ j : Fin 16, (6 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 6) (recipe 3 j)).eval profile3≤rawProfile3 (.a 6 j) := by
  decide +kernel

theorem other_chunk_3_6 :
    (∀ j : Fin 16, (6 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 6) (recipe 3 j)).eval profile3≤rawProfile3 (.b 6 j)) ∧
    (∀ j : Fin 16, (6 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 6) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 6 j)) ∧
    (∀ l : Fin 16, (6 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 6) (recipe 3 (next 6)) (recipe 3 l)
        (rawProfile3 (.a (next 6) l))≤rawProfile3 (.p 6 l)) := by
  decide +kernel

theorem d_chunk_3_6 : ∀ j l : Fin 16, (6 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 6) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 6 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 6 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_7 : ∀ j : Fin 16, (7 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 7) (recipe 3 j)).eval profile3≤rawProfile3 (.a 7 j) := by
  decide +kernel

theorem other_chunk_3_7 :
    (∀ j : Fin 16, (7 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 7) (recipe 3 j)).eval profile3≤rawProfile3 (.b 7 j)) ∧
    (∀ j : Fin 16, (7 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 7) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 7 j)) ∧
    (∀ l : Fin 16, (7 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 7) (recipe 3 (next 7)) (recipe 3 l)
        (rawProfile3 (.a (next 7) l))≤rawProfile3 (.p 7 l)) := by
  decide +kernel

theorem d_chunk_3_7 : ∀ j l : Fin 16, (7 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 7) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 7 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 7 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_3_7


