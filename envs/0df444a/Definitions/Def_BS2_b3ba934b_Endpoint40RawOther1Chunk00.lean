-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk00
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:42:04.764991+00:00
-- url     : https://prove2.me/theorems/ec45b27b-23d0-43f0-ab39-d081ce5dba93
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk00 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk00` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk00.lean; original SHA-256 138a9c8fe8f9d636e2c3c360617c43a04912c9fdeead97969dc565025b0e3abb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_0 : ∀ j : Fin 40, (0 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 0) (recipe 1 j)≤rawProfile1 (.a 0 j) := by
  decide +kernel

theorem other_chunk_1_0 :
    (∀ j : Fin 40, (0 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 0) (recipe 1 j)).eval profile1≤rawProfile1 (.b 0 j)) ∧
    (∀ j : Fin 40, (0 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 0) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 0 j)) ∧
    (∀ l : Fin 40, (0 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 0) (recipe 1 (next 0)) (recipe 1 l)
        (rawProfile1 (.a (next 0) l))≤rawProfile1 (.p 0 l)) := by
  decide +kernel

theorem d_chunk_1_0 : ∀ j l : Fin 40, (0 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 0) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 0 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 0 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_1 : ∀ j : Fin 40, (1 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 1) (recipe 1 j)≤rawProfile1 (.a 1 j) := by
  decide +kernel

theorem other_chunk_1_1 :
    (∀ j : Fin 40, (1 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 1) (recipe 1 j)).eval profile1≤rawProfile1 (.b 1 j)) ∧
    (∀ j : Fin 40, (1 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 1) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 1 j)) ∧
    (∀ l : Fin 40, (1 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 1) (recipe 1 (next 1)) (recipe 1 l)
        (rawProfile1 (.a (next 1) l))≤rawProfile1 (.p 1 l)) := by
  decide +kernel

theorem d_chunk_1_1 : ∀ j l : Fin 40, (1 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 1) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 1 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 1 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_1


