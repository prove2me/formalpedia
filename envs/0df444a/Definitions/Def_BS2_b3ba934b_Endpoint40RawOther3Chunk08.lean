-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk08
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk08
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:18:11.91898+00:00
-- url     : https://prove2.me/theorems/8bdf18fc-0b94-4203-9022-a0b8b9262be4
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk08 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk08` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk08.lean; original SHA-256 e85139fe05e055309cf2a8d50124667a3f5cf60701ef43ef38a50ec9f208c582; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_16 : ∀ j : Fin 40, (16 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 16) (recipe 3 j)≤rawProfile3 (.a 16 j) := by
  decide +kernel

theorem other_chunk_3_16 :
    (∀ j : Fin 40, (16 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 16) (recipe 3 j)).eval profile3≤rawProfile3 (.b 16 j)) ∧
    (∀ j : Fin 40, (16 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 16) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 16 j)) ∧
    (∀ l : Fin 40, (16 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 16) (recipe 3 (next 16)) (recipe 3 l)
        (rawProfile3 (.a (next 16) l))≤rawProfile3 (.p 16 l)) := by
  decide +kernel

theorem d_chunk_3_16 : ∀ j l : Fin 40, (16 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 16) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 16 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 16 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_17 : ∀ j : Fin 40, (17 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 17) (recipe 3 j)≤rawProfile3 (.a 17 j) := by
  decide +kernel

theorem other_chunk_3_17 :
    (∀ j : Fin 40, (17 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 17) (recipe 3 j)).eval profile3≤rawProfile3 (.b 17 j)) ∧
    (∀ j : Fin 40, (17 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 17) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 17 j)) ∧
    (∀ l : Fin 40, (17 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 17) (recipe 3 (next 17)) (recipe 3 l)
        (rawProfile3 (.a (next 17) l))≤rawProfile3 (.p 17 l)) := by
  decide +kernel

theorem d_chunk_3_17 : ∀ j l : Fin 40, (17 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 17) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 17 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 17 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_17


