-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk19
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk19
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:54:49.19561+00:00
-- url     : https://prove2.me/theorems/89e506bc-074c-401e-81ec-69eaeb38b591
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk19 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk19` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk19.lean; original SHA-256 d6157c5690ea076cbc9a9acfaba621f9b67aca799d370a85e5402ad6bbe70280; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_38 : ∀ j : Fin 40, (38 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 38) (recipe 1 j)≤rawProfile1 (.a 38 j) := by
  decide +kernel

theorem other_chunk_1_38 :
    (∀ j : Fin 40, (38 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 38) (recipe 1 j)).eval profile1≤rawProfile1 (.b 38 j)) ∧
    (∀ j : Fin 40, (38 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 38) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 38 j)) ∧
    (∀ l : Fin 40, (38 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 38) (recipe 1 (next 38)) (recipe 1 l)
        (rawProfile1 (.a (next 38) l))≤rawProfile1 (.p 38 l)) := by
  decide +kernel

theorem d_chunk_1_38 : ∀ j l : Fin 40, (38 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 38) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 38 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 38 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_39 : ∀ j : Fin 40, (39 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 39) (recipe 1 j)≤rawProfile1 (.a 39 j) := by
  decide +kernel

theorem other_chunk_1_39 :
    (∀ j : Fin 40, (39 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 39) (recipe 1 j)).eval profile1≤rawProfile1 (.b 39 j)) ∧
    (∀ j : Fin 40, (39 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 39) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 39 j)) ∧
    (∀ l : Fin 40, (39 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 39) (recipe 1 (next 39)) (recipe 1 l)
        (rawProfile1 (.a (next 39) l))≤rawProfile1 (.p 39 l)) := by
  decide +kernel

theorem d_chunk_1_39 : ∀ j l : Fin 40, (39 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 39) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 39 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 39 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_39


