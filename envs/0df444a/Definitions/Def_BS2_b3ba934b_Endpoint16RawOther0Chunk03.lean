-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther0Chunk03
-- name    : BS2_b3ba934b_Endpoint16RawOther0Chunk03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:29:12.188173+00:00
-- url     : https://prove2.me/theorems/6d2c8828-d91b-47ee-9ed1-86746dfe531a
-- title:
--   Sensitivity separation: Endpoint16RawOther0Chunk03 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther0Chunk03` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther0Chunk03.lean; original SHA-256 a73f63d9509474fb9fc118e6f7f63d7dab6d5b09c3a1fe43dbf05b05cca8fbc8; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_MinmaxCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_chunk_0_12 : ∀ j : Fin 16, (12 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 12) (recipe 0 j)).eval profile0≤rawProfile0 (.a 12 j) := by
  decide +kernel

theorem other_chunk_0_12 :
    (∀ j : Fin 16, (12 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 12) (recipe 0 j)).eval profile0≤rawProfile0 (.b 12 j)) ∧
    (∀ j : Fin 16, (12 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 12) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 12 j)) ∧
    (∀ l : Fin 16, (12 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 12) (recipe 0 (next 12)) (recipe 0 l)
        (rawProfile0 (.a (next 12) l))≤rawProfile0 (.p 12 l)) := by
  decide +kernel

theorem d_chunk_0_12 : ∀ j l : Fin 16, (12 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 12) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 12 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 12 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_13 : ∀ j : Fin 16, (13 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 13) (recipe 0 j)).eval profile0≤rawProfile0 (.a 13 j) := by
  decide +kernel

theorem other_chunk_0_13 :
    (∀ j : Fin 16, (13 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 13) (recipe 0 j)).eval profile0≤rawProfile0 (.b 13 j)) ∧
    (∀ j : Fin 16, (13 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 13) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 13 j)) ∧
    (∀ l : Fin 16, (13 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 13) (recipe 0 (next 13)) (recipe 0 l)
        (rawProfile0 (.a (next 13) l))≤rawProfile0 (.p 13 l)) := by
  decide +kernel

theorem d_chunk_0_13 : ∀ j l : Fin 16, (13 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 13) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 13 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 13 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_14 : ∀ j : Fin 16, (14 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 14) (recipe 0 j)).eval profile0≤rawProfile0 (.a 14 j) := by
  decide +kernel

theorem other_chunk_0_14 :
    (∀ j : Fin 16, (14 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 14) (recipe 0 j)).eval profile0≤rawProfile0 (.b 14 j)) ∧
    (∀ j : Fin 16, (14 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 14) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 14 j)) ∧
    (∀ l : Fin 16, (14 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 14) (recipe 0 (next 14)) (recipe 0 l)
        (rawProfile0 (.a (next 14) l))≤rawProfile0 (.p 14 l)) := by
  decide +kernel

theorem d_chunk_0_14 : ∀ j l : Fin 16, (14 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 14) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 14 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 14 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_15 : ∀ j : Fin 16, (15 : Fin 16)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 15) (recipe 0 j)).eval profile0≤rawProfile0 (.a 15 j) := by
  decide +kernel

theorem other_chunk_0_15 :
    (∀ j : Fin 16, (15 : Fin 16)≤j →
      (rawBExpr 16 5003 (recipe 0 15) (recipe 0 j)).eval profile0≤rawProfile0 (.b 15 j)) ∧
    (∀ j : Fin 16, (15 : Fin 16)≤j → j.val+1<16 →
      (rawMExpr 16 5003 (recipe 0 15) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 15 j)) ∧
    (∀ l : Fin 16, (15 : Fin 16)<l →
      pCore 16 caps.pcross profile0 (recipe 0 15) (recipe 0 (next 15)) (recipe 0 l)
        (rawProfile0 (.a (next 15) l))≤rawProfile0 (.p 15 l)) := by
  decide +kernel

theorem d_chunk_0_15 : ∀ j l : Fin 16, (15 : Fin 16)≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 15) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 15 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 15 j l) := by
  decide +kernel

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.d_chunk_0_15


