-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk11
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk11
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:16:39.342347+00:00
-- url     : https://prove2.me/theorems/8c683bd8-c718-441e-abf9-cbc692ed3811
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk11 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk11` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk11.lean; original SHA-256 7763ac2f6f491c35110e58c90bb2fdc91b657ea2d007e060d3a1f1dafe0a7555; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_22 : ∀ j : Fin 40, (22 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 22) (recipe 0 j)≤rawProfile0 (.a 22 j) := by
  decide +kernel

theorem other_chunk_0_22 :
    (∀ j : Fin 40, (22 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 22) (recipe 0 j)).eval profile0≤rawProfile0 (.b 22 j)) ∧
    (∀ j : Fin 40, (22 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 22) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 22 j)) ∧
    (∀ l : Fin 40, (22 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 22) (recipe 0 (next 22)) (recipe 0 l)
        (rawProfile0 (.a (next 22) l))≤rawProfile0 (.p 22 l)) := by
  decide +kernel

theorem d_chunk_0_22 : ∀ j l : Fin 40, (22 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 22) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 22 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 22 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_23 : ∀ j : Fin 40, (23 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 23) (recipe 0 j)≤rawProfile0 (.a 23 j) := by
  decide +kernel

theorem other_chunk_0_23 :
    (∀ j : Fin 40, (23 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 23) (recipe 0 j)).eval profile0≤rawProfile0 (.b 23 j)) ∧
    (∀ j : Fin 40, (23 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 23) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 23 j)) ∧
    (∀ l : Fin 40, (23 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 23) (recipe 0 (next 23)) (recipe 0 l)
        (rawProfile0 (.a (next 23) l))≤rawProfile0 (.p 23 l)) := by
  decide +kernel

theorem d_chunk_0_23 : ∀ j l : Fin 40, (23 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 23) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 23 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 23 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_23


