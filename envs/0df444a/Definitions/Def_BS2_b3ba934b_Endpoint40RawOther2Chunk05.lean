-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk05
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk05
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:08:13.256546+00:00
-- url     : https://prove2.me/theorems/adfe7c0a-7c01-4ac5-87fe-cf490b561a2e
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk05 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk05` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk05.lean; original SHA-256 c9b382245ccf68ff99c3551f7884b2501d2faea2369d304e94e858d7666b3b5d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_10 : ∀ j : Fin 40, (10 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 10) (recipe 2 j)≤rawProfile2 (.a 10 j) := by
  decide +kernel

theorem other_chunk_2_10 :
    (∀ j : Fin 40, (10 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 10) (recipe 2 j)).eval profile2≤rawProfile2 (.b 10 j)) ∧
    (∀ j : Fin 40, (10 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 10) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 10 j)) ∧
    (∀ l : Fin 40, (10 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 10) (recipe 2 (next 10)) (recipe 2 l)
        (rawProfile2 (.a (next 10) l))≤rawProfile2 (.p 10 l)) := by
  decide +kernel

theorem d_chunk_2_10 : ∀ j l : Fin 40, (10 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 10) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 10 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 10 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_11 : ∀ j : Fin 40, (11 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 11) (recipe 2 j)≤rawProfile2 (.a 11 j) := by
  decide +kernel

theorem other_chunk_2_11 :
    (∀ j : Fin 40, (11 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 11) (recipe 2 j)).eval profile2≤rawProfile2 (.b 11 j)) ∧
    (∀ j : Fin 40, (11 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 11) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 11 j)) ∧
    (∀ l : Fin 40, (11 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 11) (recipe 2 (next 11)) (recipe 2 l)
        (rawProfile2 (.a (next 11) l))≤rawProfile2 (.p 11 l)) := by
  decide +kernel

theorem d_chunk_2_11 : ∀ j l : Fin 40, (11 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 11) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 11 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 11 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_11


