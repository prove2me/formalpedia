-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk09
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk09
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:11:09.600975+00:00
-- url     : https://prove2.me/theorems/fdb6eb0a-54f9-4f72-9787-712e3197f2c0
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk09 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk09` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk09.lean; original SHA-256 4aa0a8deabcb784e19370bb97ff7f42a2df798cf03225d2c4f9efea38351b096; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_18 : ∀ j : Fin 40, (18 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 18) (recipe 2 j)≤rawProfile2 (.a 18 j) := by
  decide +kernel

theorem other_chunk_2_18 :
    (∀ j : Fin 40, (18 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 18) (recipe 2 j)).eval profile2≤rawProfile2 (.b 18 j)) ∧
    (∀ j : Fin 40, (18 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 18) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 18 j)) ∧
    (∀ l : Fin 40, (18 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 18) (recipe 2 (next 18)) (recipe 2 l)
        (rawProfile2 (.a (next 18) l))≤rawProfile2 (.p 18 l)) := by
  decide +kernel

theorem d_chunk_2_18 : ∀ j l : Fin 40, (18 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 18) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 18 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 18 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_19 : ∀ j : Fin 40, (19 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 19) (recipe 2 j)≤rawProfile2 (.a 19 j) := by
  decide +kernel

theorem other_chunk_2_19 :
    (∀ j : Fin 40, (19 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 19) (recipe 2 j)).eval profile2≤rawProfile2 (.b 19 j)) ∧
    (∀ j : Fin 40, (19 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 19) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 19 j)) ∧
    (∀ l : Fin 40, (19 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 19) (recipe 2 (next 19)) (recipe 2 l)
        (rawProfile2 (.a (next 19) l))≤rawProfile2 (.p 19 l)) := by
  decide +kernel

theorem d_chunk_2_19 : ∀ j l : Fin 40, (19 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 19) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 19 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 19 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_19


