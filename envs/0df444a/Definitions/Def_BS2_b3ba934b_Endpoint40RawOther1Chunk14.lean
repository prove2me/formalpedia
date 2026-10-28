-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk14
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk14
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:52:09.991281+00:00
-- url     : https://prove2.me/theorems/fada2afd-056c-41f4-a382-3e79f1a697d3
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk14 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk14` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk14.lean; original SHA-256 548687cde4606c669b9deb6a5d7b7174d0c2f3edeef0430fab0d8732dd930299; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_28 : ∀ j : Fin 40, (28 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 28) (recipe 1 j)≤rawProfile1 (.a 28 j) := by
  decide +kernel

theorem other_chunk_1_28 :
    (∀ j : Fin 40, (28 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 28) (recipe 1 j)).eval profile1≤rawProfile1 (.b 28 j)) ∧
    (∀ j : Fin 40, (28 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 28) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 28 j)) ∧
    (∀ l : Fin 40, (28 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 28) (recipe 1 (next 28)) (recipe 1 l)
        (rawProfile1 (.a (next 28) l))≤rawProfile1 (.p 28 l)) := by
  decide +kernel

theorem d_chunk_1_28 : ∀ j l : Fin 40, (28 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 28) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 28 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 28 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_29 : ∀ j : Fin 40, (29 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 29) (recipe 1 j)≤rawProfile1 (.a 29 j) := by
  decide +kernel

theorem other_chunk_1_29 :
    (∀ j : Fin 40, (29 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 29) (recipe 1 j)).eval profile1≤rawProfile1 (.b 29 j)) ∧
    (∀ j : Fin 40, (29 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 29) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 29 j)) ∧
    (∀ l : Fin 40, (29 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 29) (recipe 1 (next 29)) (recipe 1 l)
        (rawProfile1 (.a (next 29) l))≤rawProfile1 (.p 29 l)) := by
  decide +kernel

theorem d_chunk_1_29 : ∀ j l : Fin 40, (29 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 29) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 29 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 29 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_29


