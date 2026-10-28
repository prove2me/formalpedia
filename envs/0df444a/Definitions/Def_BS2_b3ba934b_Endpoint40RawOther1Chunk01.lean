-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk01
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk01
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:42:45.424726+00:00
-- url     : https://prove2.me/theorems/faf6a2c4-5e5b-4ac1-9eac-e69ed0e02b65
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk01 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk01` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk01.lean; original SHA-256 da2c4f2c43e75ff096bfe8587011dd6473c9fe02cec9b55494aebe6c48581ee9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_2 : ∀ j : Fin 40, (2 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 2) (recipe 1 j)≤rawProfile1 (.a 2 j) := by
  decide +kernel

theorem other_chunk_1_2 :
    (∀ j : Fin 40, (2 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 2) (recipe 1 j)).eval profile1≤rawProfile1 (.b 2 j)) ∧
    (∀ j : Fin 40, (2 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 2) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 2 j)) ∧
    (∀ l : Fin 40, (2 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 2) (recipe 1 (next 2)) (recipe 1 l)
        (rawProfile1 (.a (next 2) l))≤rawProfile1 (.p 2 l)) := by
  decide +kernel

theorem d_chunk_1_2 : ∀ j l : Fin 40, (2 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 2) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 2 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 2 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_3 : ∀ j : Fin 40, (3 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 3) (recipe 1 j)≤rawProfile1 (.a 3 j) := by
  decide +kernel

theorem other_chunk_1_3 :
    (∀ j : Fin 40, (3 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 3) (recipe 1 j)).eval profile1≤rawProfile1 (.b 3 j)) ∧
    (∀ j : Fin 40, (3 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 3) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 3 j)) ∧
    (∀ l : Fin 40, (3 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 3) (recipe 1 (next 3)) (recipe 1 l)
        (rawProfile1 (.a (next 3) l))≤rawProfile1 (.p 3 l)) := by
  decide +kernel

theorem d_chunk_1_3 : ∀ j l : Fin 40, (3 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 3) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 3 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 3 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_3


