-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk19
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk19
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:25:11.171931+00:00
-- url     : https://prove2.me/theorems/990192ec-204d-44ca-b7f5-22bb35506d02
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk19 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk19` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk19.lean; original SHA-256 e0b5838b8c92c4f5cbef5e1eddc2f7e6f8e75cc9c9eec5714c935386e557d253; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_38 : ∀ j : Fin 40, (38 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 38) (recipe 3 j)≤rawProfile3 (.a 38 j) := by
  decide +kernel

theorem other_chunk_3_38 :
    (∀ j : Fin 40, (38 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 38) (recipe 3 j)).eval profile3≤rawProfile3 (.b 38 j)) ∧
    (∀ j : Fin 40, (38 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 38) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 38 j)) ∧
    (∀ l : Fin 40, (38 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 38) (recipe 3 (next 38)) (recipe 3 l)
        (rawProfile3 (.a (next 38) l))≤rawProfile3 (.p 38 l)) := by
  decide +kernel

theorem d_chunk_3_38 : ∀ j l : Fin 40, (38 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 38) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 38 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 38 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_39 : ∀ j : Fin 40, (39 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 39) (recipe 3 j)≤rawProfile3 (.a 39 j) := by
  decide +kernel

theorem other_chunk_3_39 :
    (∀ j : Fin 40, (39 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 39) (recipe 3 j)).eval profile3≤rawProfile3 (.b 39 j)) ∧
    (∀ j : Fin 40, (39 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 39) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 39 j)) ∧
    (∀ l : Fin 40, (39 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 39) (recipe 3 (next 39)) (recipe 3 l)
        (rawProfile3 (.a (next 39) l))≤rawProfile3 (.p 39 l)) := by
  decide +kernel

theorem d_chunk_3_39 : ∀ j l : Fin 40, (39 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 39) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 39 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 39 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_39


