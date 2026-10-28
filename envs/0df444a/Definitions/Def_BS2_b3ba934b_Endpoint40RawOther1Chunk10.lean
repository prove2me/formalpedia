-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk10
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk10
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:49:25.159233+00:00
-- url     : https://prove2.me/theorems/798ed867-57d9-4ac3-8cd1-886738d6a855
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk10 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk10` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk10.lean; original SHA-256 c3b32af60e0c81988492b0d9a53f842059d6821bb73f69c3983292822ca54d17; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_20 : ∀ j : Fin 40, (20 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 20) (recipe 1 j)≤rawProfile1 (.a 20 j) := by
  decide +kernel

theorem other_chunk_1_20 :
    (∀ j : Fin 40, (20 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 20) (recipe 1 j)).eval profile1≤rawProfile1 (.b 20 j)) ∧
    (∀ j : Fin 40, (20 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 20) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 20 j)) ∧
    (∀ l : Fin 40, (20 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 20) (recipe 1 (next 20)) (recipe 1 l)
        (rawProfile1 (.a (next 20) l))≤rawProfile1 (.p 20 l)) := by
  decide +kernel

theorem d_chunk_1_20 : ∀ j l : Fin 40, (20 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 20) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 20 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 20 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_21 : ∀ j : Fin 40, (21 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 21) (recipe 1 j)≤rawProfile1 (.a 21 j) := by
  decide +kernel

theorem other_chunk_1_21 :
    (∀ j : Fin 40, (21 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 21) (recipe 1 j)).eval profile1≤rawProfile1 (.b 21 j)) ∧
    (∀ j : Fin 40, (21 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 21) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 21 j)) ∧
    (∀ l : Fin 40, (21 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 21) (recipe 1 (next 21)) (recipe 1 l)
        (rawProfile1 (.a (next 21) l))≤rawProfile1 (.p 21 l)) := by
  decide +kernel

theorem d_chunk_1_21 : ∀ j l : Fin 40, (21 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 21) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 21 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 21 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_21


