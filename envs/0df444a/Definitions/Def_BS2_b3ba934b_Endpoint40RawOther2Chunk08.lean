-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk08
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk08
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:09:39.647511+00:00
-- url     : https://prove2.me/theorems/f45ea597-99f6-4733-b38c-2897b69082cb
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk08 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk08` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk08.lean; original SHA-256 03b27ce5361e25b39bcb77f41157393c39036d2794ce86cf379234d29cc1cff5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_16 : ∀ j : Fin 40, (16 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 16) (recipe 2 j)≤rawProfile2 (.a 16 j) := by
  decide +kernel

theorem other_chunk_2_16 :
    (∀ j : Fin 40, (16 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 16) (recipe 2 j)).eval profile2≤rawProfile2 (.b 16 j)) ∧
    (∀ j : Fin 40, (16 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 16) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 16 j)) ∧
    (∀ l : Fin 40, (16 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 16) (recipe 2 (next 16)) (recipe 2 l)
        (rawProfile2 (.a (next 16) l))≤rawProfile2 (.p 16 l)) := by
  decide +kernel

theorem d_chunk_2_16 : ∀ j l : Fin 40, (16 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 16) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 16 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 16 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_17 : ∀ j : Fin 40, (17 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 17) (recipe 2 j)≤rawProfile2 (.a 17 j) := by
  decide +kernel

theorem other_chunk_2_17 :
    (∀ j : Fin 40, (17 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 17) (recipe 2 j)).eval profile2≤rawProfile2 (.b 17 j)) ∧
    (∀ j : Fin 40, (17 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 17) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 17 j)) ∧
    (∀ l : Fin 40, (17 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 17) (recipe 2 (next 17)) (recipe 2 l)
        (rawProfile2 (.a (next 17) l))≤rawProfile2 (.p 17 l)) := by
  decide +kernel

theorem d_chunk_2_17 : ∀ j l : Fin 40, (17 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 17) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 17 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 17 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_17


