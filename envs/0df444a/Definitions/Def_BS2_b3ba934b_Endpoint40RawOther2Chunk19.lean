-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk19
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk19
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:23:58.887799+00:00
-- url     : https://prove2.me/theorems/cfe80ecd-f57b-4dcc-b744-1c5a1bff0c9d
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk19 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk19` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk19.lean; original SHA-256 6875993d89c999b017705def6e74a5e092153b7bbf013ff65417bb3af3d6b083; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_38 : ∀ j : Fin 40, (38 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 38) (recipe 2 j)≤rawProfile2 (.a 38 j) := by
  decide +kernel

theorem other_chunk_2_38 :
    (∀ j : Fin 40, (38 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 38) (recipe 2 j)).eval profile2≤rawProfile2 (.b 38 j)) ∧
    (∀ j : Fin 40, (38 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 38) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 38 j)) ∧
    (∀ l : Fin 40, (38 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 38) (recipe 2 (next 38)) (recipe 2 l)
        (rawProfile2 (.a (next 38) l))≤rawProfile2 (.p 38 l)) := by
  decide +kernel

theorem d_chunk_2_38 : ∀ j l : Fin 40, (38 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 38) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 38 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 38 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_39 : ∀ j : Fin 40, (39 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 39) (recipe 2 j)≤rawProfile2 (.a 39 j) := by
  decide +kernel

theorem other_chunk_2_39 :
    (∀ j : Fin 40, (39 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 39) (recipe 2 j)).eval profile2≤rawProfile2 (.b 39 j)) ∧
    (∀ j : Fin 40, (39 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 39) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 39 j)) ∧
    (∀ l : Fin 40, (39 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 39) (recipe 2 (next 39)) (recipe 2 l)
        (rawProfile2 (.a (next 39) l))≤rawProfile2 (.p 39 l)) := by
  decide +kernel

theorem d_chunk_2_39 : ∀ j l : Fin 40, (39 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 39) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 39 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 39 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_39


