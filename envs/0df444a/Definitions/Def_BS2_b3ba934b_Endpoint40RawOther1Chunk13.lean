-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk13
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk13
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:51:33.86571+00:00
-- url     : https://prove2.me/theorems/d56ea73d-7204-41fd-9f17-548b6db196e1
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk13 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk13` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk13.lean; original SHA-256 7cbd11734b2f5aebcda6ffa5c92ec98c3a0aeec5653aa9eb5a6ea489819b8480; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_26 : ∀ j : Fin 40, (26 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 26) (recipe 1 j)≤rawProfile1 (.a 26 j) := by
  decide +kernel

theorem other_chunk_1_26 :
    (∀ j : Fin 40, (26 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 26) (recipe 1 j)).eval profile1≤rawProfile1 (.b 26 j)) ∧
    (∀ j : Fin 40, (26 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 26) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 26 j)) ∧
    (∀ l : Fin 40, (26 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 26) (recipe 1 (next 26)) (recipe 1 l)
        (rawProfile1 (.a (next 26) l))≤rawProfile1 (.p 26 l)) := by
  decide +kernel

theorem d_chunk_1_26 : ∀ j l : Fin 40, (26 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 26) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 26 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 26 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_27 : ∀ j : Fin 40, (27 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 27) (recipe 1 j)≤rawProfile1 (.a 27 j) := by
  decide +kernel

theorem other_chunk_1_27 :
    (∀ j : Fin 40, (27 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 27) (recipe 1 j)).eval profile1≤rawProfile1 (.b 27 j)) ∧
    (∀ j : Fin 40, (27 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 27) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 27 j)) ∧
    (∀ l : Fin 40, (27 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 27) (recipe 1 (next 27)) (recipe 1 l)
        (rawProfile1 (.a (next 27) l))≤rawProfile1 (.p 27 l)) := by
  decide +kernel

theorem d_chunk_1_27 : ∀ j l : Fin 40, (27 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 27) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 27 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 27 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_27


