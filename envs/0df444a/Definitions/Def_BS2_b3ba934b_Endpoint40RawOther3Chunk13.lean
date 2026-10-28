-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk13
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk13
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:21:43.367303+00:00
-- url     : https://prove2.me/theorems/c9ce5c15-3850-4baa-938a-208228b6a429
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk13 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk13` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk13.lean; original SHA-256 9a395df491dbb3a3329888540681fbb104eef88a7f4a089cb180d4325a71dafc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_26 : ∀ j : Fin 40, (26 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 26) (recipe 3 j)≤rawProfile3 (.a 26 j) := by
  decide +kernel

theorem other_chunk_3_26 :
    (∀ j : Fin 40, (26 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 26) (recipe 3 j)).eval profile3≤rawProfile3 (.b 26 j)) ∧
    (∀ j : Fin 40, (26 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 26) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 26 j)) ∧
    (∀ l : Fin 40, (26 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 26) (recipe 3 (next 26)) (recipe 3 l)
        (rawProfile3 (.a (next 26) l))≤rawProfile3 (.p 26 l)) := by
  decide +kernel

theorem d_chunk_3_26 : ∀ j l : Fin 40, (26 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 26) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 26 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 26 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_27 : ∀ j : Fin 40, (27 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 27) (recipe 3 j)≤rawProfile3 (.a 27 j) := by
  decide +kernel

theorem other_chunk_3_27 :
    (∀ j : Fin 40, (27 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 27) (recipe 3 j)).eval profile3≤rawProfile3 (.b 27 j)) ∧
    (∀ j : Fin 40, (27 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 27) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 27 j)) ∧
    (∀ l : Fin 40, (27 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 27) (recipe 3 (next 27)) (recipe 3 l)
        (rawProfile3 (.a (next 27) l))≤rawProfile3 (.p 27 l)) := by
  decide +kernel

theorem d_chunk_3_27 : ∀ j l : Fin 40, (27 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 27) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 27 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 27 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_27


