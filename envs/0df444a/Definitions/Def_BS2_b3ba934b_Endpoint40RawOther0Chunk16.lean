-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk16
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk16
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:19:43.475574+00:00
-- url     : https://prove2.me/theorems/107b804c-d5ed-423a-ae28-8f75b1562238
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk16 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk16` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk16.lean; original SHA-256 9d8350208e71c104440cf2319adb0cf81abbfdbbb1693ceda83aae67d552a70e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_32 : ∀ j : Fin 40, (32 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 32) (recipe 0 j)≤rawProfile0 (.a 32 j) := by
  decide +kernel

theorem other_chunk_0_32 :
    (∀ j : Fin 40, (32 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 32) (recipe 0 j)).eval profile0≤rawProfile0 (.b 32 j)) ∧
    (∀ j : Fin 40, (32 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 32) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 32 j)) ∧
    (∀ l : Fin 40, (32 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 32) (recipe 0 (next 32)) (recipe 0 l)
        (rawProfile0 (.a (next 32) l))≤rawProfile0 (.p 32 l)) := by
  decide +kernel

theorem d_chunk_0_32 : ∀ j l : Fin 40, (32 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 32) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 32 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 32 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_33 : ∀ j : Fin 40, (33 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 33) (recipe 0 j)≤rawProfile0 (.a 33 j) := by
  decide +kernel

theorem other_chunk_0_33 :
    (∀ j : Fin 40, (33 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 33) (recipe 0 j)).eval profile0≤rawProfile0 (.b 33 j)) ∧
    (∀ j : Fin 40, (33 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 33) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 33 j)) ∧
    (∀ l : Fin 40, (33 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 33) (recipe 0 (next 33)) (recipe 0 l)
        (rawProfile0 (.a (next 33) l))≤rawProfile0 (.p 33 l)) := by
  decide +kernel

theorem d_chunk_0_33 : ∀ j l : Fin 40, (33 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 33) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 33 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 33 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_33


