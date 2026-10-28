-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk14
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk14
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:14:00.076781+00:00
-- url     : https://prove2.me/theorems/95e0af14-db44-4313-b26f-1bf11c93182e
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk14 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk14` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk14.lean; original SHA-256 da00ac6774c0ed5d6d6ba0f261e84652907b564ec2f3c2c14531cf8eff789ed9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_28 : ∀ j : Fin 40, (28 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 28) (recipe 2 j)≤rawProfile2 (.a 28 j) := by
  decide +kernel

theorem other_chunk_2_28 :
    (∀ j : Fin 40, (28 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 28) (recipe 2 j)).eval profile2≤rawProfile2 (.b 28 j)) ∧
    (∀ j : Fin 40, (28 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 28) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 28 j)) ∧
    (∀ l : Fin 40, (28 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 28) (recipe 2 (next 28)) (recipe 2 l)
        (rawProfile2 (.a (next 28) l))≤rawProfile2 (.p 28 l)) := by
  decide +kernel

theorem d_chunk_2_28 : ∀ j l : Fin 40, (28 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 28) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 28 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 28 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_29 : ∀ j : Fin 40, (29 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 29) (recipe 2 j)≤rawProfile2 (.a 29 j) := by
  decide +kernel

theorem other_chunk_2_29 :
    (∀ j : Fin 40, (29 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 29) (recipe 2 j)).eval profile2≤rawProfile2 (.b 29 j)) ∧
    (∀ j : Fin 40, (29 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 29) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 29 j)) ∧
    (∀ l : Fin 40, (29 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 29) (recipe 2 (next 29)) (recipe 2 l)
        (rawProfile2 (.a (next 29) l))≤rawProfile2 (.p 29 l)) := by
  decide +kernel

theorem d_chunk_2_29 : ∀ j l : Fin 40, (29 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 29) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 29 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 29 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_29


