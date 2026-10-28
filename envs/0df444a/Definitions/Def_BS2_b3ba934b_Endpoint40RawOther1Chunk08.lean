-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk08
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk08
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:48:03.937966+00:00
-- url     : https://prove2.me/theorems/da271095-fc4e-4e3a-abce-8656e91f33d4
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk08 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk08` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk08.lean; original SHA-256 42f09ccb0ad268a01f82d5c5dfbaf75329a7536fda70812222ad888b5e31b90d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_16 : ∀ j : Fin 40, (16 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 16) (recipe 1 j)≤rawProfile1 (.a 16 j) := by
  decide +kernel

theorem other_chunk_1_16 :
    (∀ j : Fin 40, (16 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 16) (recipe 1 j)).eval profile1≤rawProfile1 (.b 16 j)) ∧
    (∀ j : Fin 40, (16 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 16) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 16 j)) ∧
    (∀ l : Fin 40, (16 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 16) (recipe 1 (next 16)) (recipe 1 l)
        (rawProfile1 (.a (next 16) l))≤rawProfile1 (.p 16 l)) := by
  decide +kernel

theorem d_chunk_1_16 : ∀ j l : Fin 40, (16 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 16) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 16 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 16 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_17 : ∀ j : Fin 40, (17 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 17) (recipe 1 j)≤rawProfile1 (.a 17 j) := by
  decide +kernel

theorem other_chunk_1_17 :
    (∀ j : Fin 40, (17 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 17) (recipe 1 j)).eval profile1≤rawProfile1 (.b 17 j)) ∧
    (∀ j : Fin 40, (17 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 17) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 17 j)) ∧
    (∀ l : Fin 40, (17 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 17) (recipe 1 (next 17)) (recipe 1 l)
        (rawProfile1 (.a (next 17) l))≤rawProfile1 (.p 17 l)) := by
  decide +kernel

theorem d_chunk_1_17 : ∀ j l : Fin 40, (17 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 17) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 17 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 17 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_17


