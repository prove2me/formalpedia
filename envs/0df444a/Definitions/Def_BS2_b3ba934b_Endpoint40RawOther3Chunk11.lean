-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk11
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk11
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:20:28.633031+00:00
-- url     : https://prove2.me/theorems/da2ef934-3cf5-4102-933f-a1b9cd0298df
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk11 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk11` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk11.lean; original SHA-256 0742d989b144d4cef8cdc0e587e1a37e1c2cfec7a3931dc73f69c0553d6a51c9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_22 : ∀ j : Fin 40, (22 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 22) (recipe 3 j)≤rawProfile3 (.a 22 j) := by
  decide +kernel

theorem other_chunk_3_22 :
    (∀ j : Fin 40, (22 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 22) (recipe 3 j)).eval profile3≤rawProfile3 (.b 22 j)) ∧
    (∀ j : Fin 40, (22 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 22) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 22 j)) ∧
    (∀ l : Fin 40, (22 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 22) (recipe 3 (next 22)) (recipe 3 l)
        (rawProfile3 (.a (next 22) l))≤rawProfile3 (.p 22 l)) := by
  decide +kernel

theorem d_chunk_3_22 : ∀ j l : Fin 40, (22 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 22) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 22 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 22 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_23 : ∀ j : Fin 40, (23 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 23) (recipe 3 j)≤rawProfile3 (.a 23 j) := by
  decide +kernel

theorem other_chunk_3_23 :
    (∀ j : Fin 40, (23 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 23) (recipe 3 j)).eval profile3≤rawProfile3 (.b 23 j)) ∧
    (∀ j : Fin 40, (23 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 23) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 23 j)) ∧
    (∀ l : Fin 40, (23 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 23) (recipe 3 (next 23)) (recipe 3 l)
        (rawProfile3 (.a (next 23) l))≤rawProfile3 (.p 23 l)) := by
  decide +kernel

theorem d_chunk_3_23 : ∀ j l : Fin 40, (23 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 23) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 23 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 23 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_23


