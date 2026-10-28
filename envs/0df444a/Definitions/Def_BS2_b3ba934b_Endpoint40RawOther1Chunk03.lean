-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk03
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:44:42.334919+00:00
-- url     : https://prove2.me/theorems/a95a50f7-edde-419a-91de-d8937fbad159
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk03 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk03` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk03.lean; original SHA-256 aa4edbc932e417461573ea9f392633a7c57155737a2a0c9caefed759457b8930; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_6 : ∀ j : Fin 40, (6 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 6) (recipe 1 j)≤rawProfile1 (.a 6 j) := by
  decide +kernel

theorem other_chunk_1_6 :
    (∀ j : Fin 40, (6 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 6) (recipe 1 j)).eval profile1≤rawProfile1 (.b 6 j)) ∧
    (∀ j : Fin 40, (6 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 6) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 6 j)) ∧
    (∀ l : Fin 40, (6 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 6) (recipe 1 (next 6)) (recipe 1 l)
        (rawProfile1 (.a (next 6) l))≤rawProfile1 (.p 6 l)) := by
  decide +kernel

theorem d_chunk_1_6 : ∀ j l : Fin 40, (6 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 6) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 6 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 6 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_7 : ∀ j : Fin 40, (7 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 7) (recipe 1 j)≤rawProfile1 (.a 7 j) := by
  decide +kernel

theorem other_chunk_1_7 :
    (∀ j : Fin 40, (7 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 7) (recipe 1 j)).eval profile1≤rawProfile1 (.b 7 j)) ∧
    (∀ j : Fin 40, (7 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 7) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 7 j)) ∧
    (∀ l : Fin 40, (7 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 7) (recipe 1 (next 7)) (recipe 1 l)
        (rawProfile1 (.a (next 7) l))≤rawProfile1 (.p 7 l)) := by
  decide +kernel

theorem d_chunk_1_7 : ∀ j l : Fin 40, (7 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 7) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 7 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 7 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_7


