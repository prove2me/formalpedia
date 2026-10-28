-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk02
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk02
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:43:33.324497+00:00
-- url     : https://prove2.me/theorems/3fdb4d58-83f0-426d-8cc0-2f13c35702b3
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk02 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk02` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk02.lean; original SHA-256 d172d2c1ddbdcc36453e1a081701dcf2fc0ea8182642b2ed1e3780b271d639ad; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_4 : ∀ j : Fin 40, (4 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 4) (recipe 1 j)≤rawProfile1 (.a 4 j) := by
  decide +kernel

theorem other_chunk_1_4 :
    (∀ j : Fin 40, (4 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 4) (recipe 1 j)).eval profile1≤rawProfile1 (.b 4 j)) ∧
    (∀ j : Fin 40, (4 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 4) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 4 j)) ∧
    (∀ l : Fin 40, (4 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 4) (recipe 1 (next 4)) (recipe 1 l)
        (rawProfile1 (.a (next 4) l))≤rawProfile1 (.p 4 l)) := by
  decide +kernel

theorem d_chunk_1_4 : ∀ j l : Fin 40, (4 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 4) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 4 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 4 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_5 : ∀ j : Fin 40, (5 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 5) (recipe 1 j)≤rawProfile1 (.a 5 j) := by
  decide +kernel

theorem other_chunk_1_5 :
    (∀ j : Fin 40, (5 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 5) (recipe 1 j)).eval profile1≤rawProfile1 (.b 5 j)) ∧
    (∀ j : Fin 40, (5 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 5) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 5 j)) ∧
    (∀ l : Fin 40, (5 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 5) (recipe 1 (next 5)) (recipe 1 l)
        (rawProfile1 (.a (next 5) l))≤rawProfile1 (.p 5 l)) := by
  decide +kernel

theorem d_chunk_1_5 : ∀ j l : Fin 40, (5 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 5) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 5 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 5 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_5


