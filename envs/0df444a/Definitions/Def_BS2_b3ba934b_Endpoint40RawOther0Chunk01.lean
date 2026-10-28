-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk01
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk01
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:00:55.932514+00:00
-- url     : https://prove2.me/theorems/49e0b46f-8139-4b86-a834-7cc3119aae04
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk01 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk01` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk01.lean; original SHA-256 df9b03e122af8cf118a028b59f2863a9b64b37080f77bf1aa0be2a0d7a623c7f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_2 : ∀ j : Fin 40, (2 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 2) (recipe 0 j)≤rawProfile0 (.a 2 j) := by
  decide +kernel

theorem other_chunk_0_2 :
    (∀ j : Fin 40, (2 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 2) (recipe 0 j)).eval profile0≤rawProfile0 (.b 2 j)) ∧
    (∀ j : Fin 40, (2 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 2) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 2 j)) ∧
    (∀ l : Fin 40, (2 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 2) (recipe 0 (next 2)) (recipe 0 l)
        (rawProfile0 (.a (next 2) l))≤rawProfile0 (.p 2 l)) := by
  decide +kernel

theorem d_chunk_0_2 : ∀ j l : Fin 40, (2 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 2) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 2 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 2 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_3 : ∀ j : Fin 40, (3 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 3) (recipe 0 j)≤rawProfile0 (.a 3 j) := by
  decide +kernel

theorem other_chunk_0_3 :
    (∀ j : Fin 40, (3 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 3) (recipe 0 j)).eval profile0≤rawProfile0 (.b 3 j)) ∧
    (∀ j : Fin 40, (3 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 3) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 3 j)) ∧
    (∀ l : Fin 40, (3 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 3) (recipe 0 (next 3)) (recipe 0 l)
        (rawProfile0 (.a (next 3) l))≤rawProfile0 (.p 3 l)) := by
  decide +kernel

theorem d_chunk_0_3 : ∀ j l : Fin 40, (3 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 3) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 3 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 3 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_3


