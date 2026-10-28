-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk17
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk17
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:53:52.358023+00:00
-- url     : https://prove2.me/theorems/21a6c394-9013-407f-8b0f-38cfe17e70c7
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk17 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk17` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk17.lean; original SHA-256 08be602edb75b2eee3457b708252004871791fc78cef2b315d53f6fd77663b5b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_34 : ∀ j : Fin 40, (34 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 34) (recipe 1 j)≤rawProfile1 (.a 34 j) := by
  decide +kernel

theorem other_chunk_1_34 :
    (∀ j : Fin 40, (34 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 34) (recipe 1 j)).eval profile1≤rawProfile1 (.b 34 j)) ∧
    (∀ j : Fin 40, (34 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 34) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 34 j)) ∧
    (∀ l : Fin 40, (34 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 34) (recipe 1 (next 34)) (recipe 1 l)
        (rawProfile1 (.a (next 34) l))≤rawProfile1 (.p 34 l)) := by
  decide +kernel

theorem d_chunk_1_34 : ∀ j l : Fin 40, (34 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 34) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 34 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 34 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_35 : ∀ j : Fin 40, (35 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 35) (recipe 1 j)≤rawProfile1 (.a 35 j) := by
  decide +kernel

theorem other_chunk_1_35 :
    (∀ j : Fin 40, (35 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 35) (recipe 1 j)).eval profile1≤rawProfile1 (.b 35 j)) ∧
    (∀ j : Fin 40, (35 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 35) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 35 j)) ∧
    (∀ l : Fin 40, (35 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 35) (recipe 1 (next 35)) (recipe 1 l)
        (rawProfile1 (.a (next 35) l))≤rawProfile1 (.p 35 l)) := by
  decide +kernel

theorem d_chunk_1_35 : ∀ j l : Fin 40, (35 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 35) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 35 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 35 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_35


