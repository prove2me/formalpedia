-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk16
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk16
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:53:21.510701+00:00
-- url     : https://prove2.me/theorems/2594a8f6-f9ab-4583-ab44-3ce267f9deab
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk16 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk16` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk16.lean; original SHA-256 2ea56a846f8370dc98c7929bbaa7d02b65e3c997eaa1f735f2da7114fe6daa24; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_32 : ∀ j : Fin 40, (32 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 32) (recipe 1 j)≤rawProfile1 (.a 32 j) := by
  decide +kernel

theorem other_chunk_1_32 :
    (∀ j : Fin 40, (32 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 32) (recipe 1 j)).eval profile1≤rawProfile1 (.b 32 j)) ∧
    (∀ j : Fin 40, (32 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 32) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 32 j)) ∧
    (∀ l : Fin 40, (32 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 32) (recipe 1 (next 32)) (recipe 1 l)
        (rawProfile1 (.a (next 32) l))≤rawProfile1 (.p 32 l)) := by
  decide +kernel

theorem d_chunk_1_32 : ∀ j l : Fin 40, (32 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 32) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 32 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 32 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_33 : ∀ j : Fin 40, (33 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 33) (recipe 1 j)≤rawProfile1 (.a 33 j) := by
  decide +kernel

theorem other_chunk_1_33 :
    (∀ j : Fin 40, (33 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 33) (recipe 1 j)).eval profile1≤rawProfile1 (.b 33 j)) ∧
    (∀ j : Fin 40, (33 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 33) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 33 j)) ∧
    (∀ l : Fin 40, (33 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 33) (recipe 1 (next 33)) (recipe 1 l)
        (rawProfile1 (.a (next 33) l))≤rawProfile1 (.p 33 l)) := by
  decide +kernel

theorem d_chunk_1_33 : ∀ j l : Fin 40, (33 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 33) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 33 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 33 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_33


