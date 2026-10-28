-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther0Chunk02
-- name    : BS2_b3ba934b_Endpoint16RawOther0Chunk02
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:29:06.521582+00:00
-- url     : https://prove2.me/theorems/8aa8479d-20b4-4a12-815a-5e0fd163f3f8
-- title:
--   Sensitivity separation: Endpoint16RawOther0Chunk02 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther0Chunk02` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther0Chunk02.lean; original SHA-256 3b398677455c92b68562e3267fa686a728870bf39f47d75f8199ef2dd9ac0bf1; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_0_8 : ∀ j : Fin 16, (8 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 8) (recipe 0 j)).eval profile0≤rawProfile0 (.a 8 j) := by
  decide +kernel

theorem other_chunk_0_8 :
    (∀ j : Fin 16, (8 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 8) (recipe 0 j)).eval profile0≤rawProfile0 (.b 8 j)) ∧
    (∀ j : Fin 16, (8 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 8) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 8 j)) ∧
    (∀ l : Fin 16, (8 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 8) (recipe 0 (next 8)) (recipe 0 l)
        (rawProfile0 (.a (next 8) l))≤rawProfile0 (.p 8 l)) := by
  decide +kernel

theorem d_chunk_0_8 : ∀ j l : Fin 16, (8 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 8) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 8 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 8 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_9 : ∀ j : Fin 16, (9 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 9) (recipe 0 j)).eval profile0≤rawProfile0 (.a 9 j) := by
  decide +kernel

theorem other_chunk_0_9 :
    (∀ j : Fin 16, (9 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 9) (recipe 0 j)).eval profile0≤rawProfile0 (.b 9 j)) ∧
    (∀ j : Fin 16, (9 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 9) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 9 j)) ∧
    (∀ l : Fin 16, (9 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 9) (recipe 0 (next 9)) (recipe 0 l)
        (rawProfile0 (.a (next 9) l))≤rawProfile0 (.p 9 l)) := by
  decide +kernel

theorem d_chunk_0_9 : ∀ j l : Fin 16, (9 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 9) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 9 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 9 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_10 : ∀ j : Fin 16, (10 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 10) (recipe 0 j)).eval profile0≤rawProfile0 (.a 10 j) := by
  decide +kernel

theorem other_chunk_0_10 :
    (∀ j : Fin 16, (10 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 10) (recipe 0 j)).eval profile0≤rawProfile0 (.b 10 j)) ∧
    (∀ j : Fin 16, (10 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 10) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 10 j)) ∧
    (∀ l : Fin 16, (10 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 10) (recipe 0 (next 10)) (recipe 0 l)
        (rawProfile0 (.a (next 10) l))≤rawProfile0 (.p 10 l)) := by
  decide +kernel

theorem d_chunk_0_10 : ∀ j l : Fin 16, (10 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 10) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 10 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 10 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_11 : ∀ j : Fin 16, (11 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 11) (recipe 0 j)).eval profile0≤rawProfile0 (.a 11 j) := by
  decide +kernel

theorem other_chunk_0_11 :
    (∀ j : Fin 16, (11 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 11) (recipe 0 j)).eval profile0≤rawProfile0 (.b 11 j)) ∧
    (∀ j : Fin 16, (11 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 11) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 11 j)) ∧
    (∀ l : Fin 16, (11 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 11) (recipe 0 (next 11)) (recipe 0 l)
        (rawProfile0 (.a (next 11) l))≤rawProfile0 (.p 11 l)) := by
  decide +kernel

theorem d_chunk_0_11 : ∀ j l : Fin 16, (11 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 11) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 11 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 11 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_0_11


