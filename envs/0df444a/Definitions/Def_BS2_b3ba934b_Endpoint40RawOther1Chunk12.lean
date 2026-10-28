-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk12
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk12
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:50:49.937406+00:00
-- url     : https://prove2.me/theorems/9d66696d-88bb-4e0e-ba61-6b37f54072e2
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk12 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk12` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk12.lean; original SHA-256 0295ee9b97c845d549cc25462b7f656dab0316e8d9bb06819c2c0e173b58ea1e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_24 : ∀ j : Fin 40, (24 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 24) (recipe 1 j)≤rawProfile1 (.a 24 j) := by
  decide +kernel

theorem other_chunk_1_24 :
    (∀ j : Fin 40, (24 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 24) (recipe 1 j)).eval profile1≤rawProfile1 (.b 24 j)) ∧
    (∀ j : Fin 40, (24 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 24) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 24 j)) ∧
    (∀ l : Fin 40, (24 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 24) (recipe 1 (next 24)) (recipe 1 l)
        (rawProfile1 (.a (next 24) l))≤rawProfile1 (.p 24 l)) := by
  decide +kernel

theorem d_chunk_1_24 : ∀ j l : Fin 40, (24 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 24) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 24 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 24 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_25 : ∀ j : Fin 40, (25 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 25) (recipe 1 j)≤rawProfile1 (.a 25 j) := by
  decide +kernel

theorem other_chunk_1_25 :
    (∀ j : Fin 40, (25 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 25) (recipe 1 j)).eval profile1≤rawProfile1 (.b 25 j)) ∧
    (∀ j : Fin 40, (25 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 25) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 25 j)) ∧
    (∀ l : Fin 40, (25 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 25) (recipe 1 (next 25)) (recipe 1 l)
        (rawProfile1 (.a (next 25) l))≤rawProfile1 (.p 25 l)) := by
  decide +kernel

theorem d_chunk_1_25 : ∀ j l : Fin 40, (25 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 25) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 25 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 25 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_25


