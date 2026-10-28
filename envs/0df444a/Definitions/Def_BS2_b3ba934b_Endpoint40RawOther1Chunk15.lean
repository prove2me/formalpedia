-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk15
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk15
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:52:51.05108+00:00
-- url     : https://prove2.me/theorems/c6ec2a42-24f1-4820-ae7c-9243b6b9f899
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk15 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk15` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk15.lean; original SHA-256 b76a250b12453eae9065a5516612c804cb3305468a88e10b8a3ec57db57d5da9; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_30 : ∀ j : Fin 40, (30 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 30) (recipe 1 j)≤rawProfile1 (.a 30 j) := by
  decide +kernel

theorem other_chunk_1_30 :
    (∀ j : Fin 40, (30 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 30) (recipe 1 j)).eval profile1≤rawProfile1 (.b 30 j)) ∧
    (∀ j : Fin 40, (30 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 30) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 30 j)) ∧
    (∀ l : Fin 40, (30 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 30) (recipe 1 (next 30)) (recipe 1 l)
        (rawProfile1 (.a (next 30) l))≤rawProfile1 (.p 30 l)) := by
  decide +kernel

theorem d_chunk_1_30 : ∀ j l : Fin 40, (30 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 30) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 30 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 30 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_31 : ∀ j : Fin 40, (31 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 31) (recipe 1 j)≤rawProfile1 (.a 31 j) := by
  decide +kernel

theorem other_chunk_1_31 :
    (∀ j : Fin 40, (31 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 31) (recipe 1 j)).eval profile1≤rawProfile1 (.b 31 j)) ∧
    (∀ j : Fin 40, (31 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 31) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 31 j)) ∧
    (∀ l : Fin 40, (31 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 31) (recipe 1 (next 31)) (recipe 1 l)
        (rawProfile1 (.a (next 31) l))≤rawProfile1 (.p 31 l)) := by
  decide +kernel

theorem d_chunk_1_31 : ∀ j l : Fin 40, (31 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 31) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 31 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 31 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_31


