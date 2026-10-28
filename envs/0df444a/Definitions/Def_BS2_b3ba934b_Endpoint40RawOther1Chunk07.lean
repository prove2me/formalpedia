-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk07
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk07
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:47:27.570219+00:00
-- url     : https://prove2.me/theorems/7507ed1d-2da1-4a56-a5b4-7ba5b1186f03
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk07 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk07` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk07.lean; original SHA-256 be790c6126fdabea125dee7d65026c8b4079e761fddfb05d4ea0fff0e5a6ebc7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_14 : ∀ j : Fin 40, (14 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 14) (recipe 1 j)≤rawProfile1 (.a 14 j) := by
  decide +kernel

theorem other_chunk_1_14 :
    (∀ j : Fin 40, (14 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 14) (recipe 1 j)).eval profile1≤rawProfile1 (.b 14 j)) ∧
    (∀ j : Fin 40, (14 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 14) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 14 j)) ∧
    (∀ l : Fin 40, (14 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 14) (recipe 1 (next 14)) (recipe 1 l)
        (rawProfile1 (.a (next 14) l))≤rawProfile1 (.p 14 l)) := by
  decide +kernel

theorem d_chunk_1_14 : ∀ j l : Fin 40, (14 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 14) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 14 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 14 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_15 : ∀ j : Fin 40, (15 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 15) (recipe 1 j)≤rawProfile1 (.a 15 j) := by
  decide +kernel

theorem other_chunk_1_15 :
    (∀ j : Fin 40, (15 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 15) (recipe 1 j)).eval profile1≤rawProfile1 (.b 15 j)) ∧
    (∀ j : Fin 40, (15 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 15) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 15 j)) ∧
    (∀ l : Fin 40, (15 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 15) (recipe 1 (next 15)) (recipe 1 l)
        (rawProfile1 (.a (next 15) l))≤rawProfile1 (.p 15 l)) := by
  decide +kernel

theorem d_chunk_1_15 : ∀ j l : Fin 40, (15 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 15) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 15 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 15 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_15


