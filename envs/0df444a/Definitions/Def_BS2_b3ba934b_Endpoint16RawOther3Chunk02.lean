-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther3Chunk02
-- name    : BS2_b3ba934b_Endpoint16RawOther3Chunk02
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:31:57.314726+00:00
-- url     : https://prove2.me/theorems/b76a2a26-1074-4668-9728-bf3d65a2ac99
-- title:
--   Sensitivity separation: Endpoint16RawOther3Chunk02 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther3Chunk02` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther3Chunk02.lean; original SHA-256 755e4408d958ed3ad31f893f093bbef2f27b7161a57bf2eaf52bf107c338b451; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_3_8 : ∀ j : Fin 16, (8 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 8) (recipe 3 j)).eval profile3≤rawProfile3 (.a 8 j) := by
  decide +kernel

theorem other_chunk_3_8 :
    (∀ j : Fin 16, (8 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 8) (recipe 3 j)).eval profile3≤rawProfile3 (.b 8 j)) ∧
    (∀ j : Fin 16, (8 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 8) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 8 j)) ∧
    (∀ l : Fin 16, (8 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 8) (recipe 3 (next 8)) (recipe 3 l)
        (rawProfile3 (.a (next 8) l))≤rawProfile3 (.p 8 l)) := by
  decide +kernel

theorem d_chunk_3_8 : ∀ j l : Fin 16, (8 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 8) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 8 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 8 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_9 : ∀ j : Fin 16, (9 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 9) (recipe 3 j)).eval profile3≤rawProfile3 (.a 9 j) := by
  decide +kernel

theorem other_chunk_3_9 :
    (∀ j : Fin 16, (9 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 9) (recipe 3 j)).eval profile3≤rawProfile3 (.b 9 j)) ∧
    (∀ j : Fin 16, (9 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 9) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 9 j)) ∧
    (∀ l : Fin 16, (9 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 9) (recipe 3 (next 9)) (recipe 3 l)
        (rawProfile3 (.a (next 9) l))≤rawProfile3 (.p 9 l)) := by
  decide +kernel

theorem d_chunk_3_9 : ∀ j l : Fin 16, (9 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 9) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 9 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 9 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_10 : ∀ j : Fin 16, (10 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 10) (recipe 3 j)).eval profile3≤rawProfile3 (.a 10 j) := by
  decide +kernel

theorem other_chunk_3_10 :
    (∀ j : Fin 16, (10 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 10) (recipe 3 j)).eval profile3≤rawProfile3 (.b 10 j)) ∧
    (∀ j : Fin 16, (10 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 10) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 10 j)) ∧
    (∀ l : Fin 16, (10 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 10) (recipe 3 (next 10)) (recipe 3 l)
        (rawProfile3 (.a (next 10) l))≤rawProfile3 (.p 10 l)) := by
  decide +kernel

theorem d_chunk_3_10 : ∀ j l : Fin 16, (10 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 10) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 10 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 10 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_11 : ∀ j : Fin 16, (11 : Fin 16)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 11) (recipe 3 j)).eval profile3≤rawProfile3 (.a 11 j) := by
  decide +kernel

theorem other_chunk_3_11 :
    (∀ j : Fin 16, (11 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 3 11) (recipe 3 j)).eval profile3≤rawProfile3 (.b 11 j)) ∧
    (∀ j : Fin 16, (11 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 3 11) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 11 j)) ∧
    (∀ l : Fin 16, (11 : Fin 16)<l →
      pCore 16 caps.pcross profile3 (recipe 3 11) (recipe 3 (next 11)) (recipe 3 l)
        (rawProfile3 (.a (next 11) l))≤rawProfile3 (.p 11 l)) := by
  decide +kernel

theorem d_chunk_3_11 : ∀ j l : Fin 16, (11 : Fin 16)≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 11) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 11 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 11 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_3_11


