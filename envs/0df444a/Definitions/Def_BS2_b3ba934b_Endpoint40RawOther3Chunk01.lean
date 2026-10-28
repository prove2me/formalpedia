-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk01
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk01
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:13:03.136896+00:00
-- url     : https://prove2.me/theorems/977d1ec6-5858-4b0e-91a5-d725ee2c9805
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk01 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk01` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk01.lean; original SHA-256 2c1509af93765ac481966afef82465b7db137f58e29d435f95dd0d58a279501a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_2 : ∀ j : Fin 40, (2 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 2) (recipe 3 j)≤rawProfile3 (.a 2 j) := by
  decide +kernel

theorem other_chunk_3_2 :
    (∀ j : Fin 40, (2 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 2) (recipe 3 j)).eval profile3≤rawProfile3 (.b 2 j)) ∧
    (∀ j : Fin 40, (2 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 2) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 2 j)) ∧
    (∀ l : Fin 40, (2 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 2) (recipe 3 (next 2)) (recipe 3 l)
        (rawProfile3 (.a (next 2) l))≤rawProfile3 (.p 2 l)) := by
  decide +kernel

theorem d_chunk_3_2 : ∀ j l : Fin 40, (2 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 2) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 2 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 2 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_3 : ∀ j : Fin 40, (3 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 3) (recipe 3 j)≤rawProfile3 (.a 3 j) := by
  decide +kernel

theorem other_chunk_3_3 :
    (∀ j : Fin 40, (3 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 3) (recipe 3 j)).eval profile3≤rawProfile3 (.b 3 j)) ∧
    (∀ j : Fin 40, (3 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 3) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 3 j)) ∧
    (∀ l : Fin 40, (3 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 3) (recipe 3 (next 3)) (recipe 3 l)
        (rawProfile3 (.a (next 3) l))≤rawProfile3 (.p 3 l)) := by
  decide +kernel

theorem d_chunk_3_3 : ∀ j l : Fin 40, (3 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 3) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 3 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 3 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_3


