-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk04
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk04
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:15:08.299324+00:00
-- url     : https://prove2.me/theorems/a07a40aa-9d69-441c-97da-7d1562c38c0d
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk04 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk04` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk04.lean; original SHA-256 f200fadd1c2b80509d6d0f385e9962709abc8520e39e9e505d8eb0f55ac61e50; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_8 : ∀ j : Fin 40, (8 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 8) (recipe 3 j)≤rawProfile3 (.a 8 j) := by
  decide +kernel

theorem other_chunk_3_8 :
    (∀ j : Fin 40, (8 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 8) (recipe 3 j)).eval profile3≤rawProfile3 (.b 8 j)) ∧
    (∀ j : Fin 40, (8 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 8) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 8 j)) ∧
    (∀ l : Fin 40, (8 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 8) (recipe 3 (next 8)) (recipe 3 l)
        (rawProfile3 (.a (next 8) l))≤rawProfile3 (.p 8 l)) := by
  decide +kernel

theorem d_chunk_3_8 : ∀ j l : Fin 40, (8 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 8) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 8 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 8 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_9 : ∀ j : Fin 40, (9 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 9) (recipe 3 j)≤rawProfile3 (.a 9 j) := by
  decide +kernel

theorem other_chunk_3_9 :
    (∀ j : Fin 40, (9 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 9) (recipe 3 j)).eval profile3≤rawProfile3 (.b 9 j)) ∧
    (∀ j : Fin 40, (9 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 9) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 9 j)) ∧
    (∀ l : Fin 40, (9 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 9) (recipe 3 (next 9)) (recipe 3 l)
        (rawProfile3 (.a (next 9) l))≤rawProfile3 (.p 9 l)) := by
  decide +kernel

theorem d_chunk_3_9 : ∀ j l : Fin 40, (9 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 9) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 9 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 9 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_9


