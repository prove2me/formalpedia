-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk11
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk11
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:50:15.979765+00:00
-- url     : https://prove2.me/theorems/fffc2aa0-4e1f-4dda-b9f1-f776fa0aed02
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk11 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk11` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk11.lean; original SHA-256 8ba9411130d256e9e68d6459fd7bfb5bddb54cb5a4b23b2b09b4b8cc563ddae0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_22 : ∀ j : Fin 40, (22 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 22) (recipe 1 j)≤rawProfile1 (.a 22 j) := by
  decide +kernel

theorem other_chunk_1_22 :
    (∀ j : Fin 40, (22 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 22) (recipe 1 j)).eval profile1≤rawProfile1 (.b 22 j)) ∧
    (∀ j : Fin 40, (22 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 22) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 22 j)) ∧
    (∀ l : Fin 40, (22 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 22) (recipe 1 (next 22)) (recipe 1 l)
        (rawProfile1 (.a (next 22) l))≤rawProfile1 (.p 22 l)) := by
  decide +kernel

theorem d_chunk_1_22 : ∀ j l : Fin 40, (22 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 22) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 22 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 22 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_23 : ∀ j : Fin 40, (23 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 23) (recipe 1 j)≤rawProfile1 (.a 23 j) := by
  decide +kernel

theorem other_chunk_1_23 :
    (∀ j : Fin 40, (23 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 23) (recipe 1 j)).eval profile1≤rawProfile1 (.b 23 j)) ∧
    (∀ j : Fin 40, (23 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 23) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 23 j)) ∧
    (∀ l : Fin 40, (23 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 23) (recipe 1 (next 23)) (recipe 1 l)
        (rawProfile1 (.a (next 23) l))≤rawProfile1 (.p 23 l)) := by
  decide +kernel

theorem d_chunk_1_23 : ∀ j l : Fin 40, (23 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 23) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 23 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 23 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_23


