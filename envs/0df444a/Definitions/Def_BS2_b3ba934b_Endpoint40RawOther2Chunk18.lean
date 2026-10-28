-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk18
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk18
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:23:33.708987+00:00
-- url     : https://prove2.me/theorems/bf00eb45-eb4e-4225-ba4e-7aa96a79bc05
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk18 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk18` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk18.lean; original SHA-256 ce86b0549b9f29d39d25362e3c5223885a8148e1fdaae3e39c122060f8f90ca8; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_36 : ∀ j : Fin 40, (36 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 36) (recipe 2 j)≤rawProfile2 (.a 36 j) := by
  decide +kernel

theorem other_chunk_2_36 :
    (∀ j : Fin 40, (36 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 36) (recipe 2 j)).eval profile2≤rawProfile2 (.b 36 j)) ∧
    (∀ j : Fin 40, (36 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 36) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 36 j)) ∧
    (∀ l : Fin 40, (36 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 36) (recipe 2 (next 36)) (recipe 2 l)
        (rawProfile2 (.a (next 36) l))≤rawProfile2 (.p 36 l)) := by
  decide +kernel

theorem d_chunk_2_36 : ∀ j l : Fin 40, (36 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 36) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 36 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 36 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_37 : ∀ j : Fin 40, (37 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 37) (recipe 2 j)≤rawProfile2 (.a 37 j) := by
  decide +kernel

theorem other_chunk_2_37 :
    (∀ j : Fin 40, (37 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 37) (recipe 2 j)).eval profile2≤rawProfile2 (.b 37 j)) ∧
    (∀ j : Fin 40, (37 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 37) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 37 j)) ∧
    (∀ l : Fin 40, (37 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 37) (recipe 2 (next 37)) (recipe 2 l)
        (rawProfile2 (.a (next 37) l))≤rawProfile2 (.p 37 l)) := by
  decide +kernel

theorem d_chunk_2_37 : ∀ j l : Fin 40, (37 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 37) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 37 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 37 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_37


