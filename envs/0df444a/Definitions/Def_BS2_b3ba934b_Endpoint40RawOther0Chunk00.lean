-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk00
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:59:36.523475+00:00
-- url     : https://prove2.me/theorems/48f97822-2e3a-4335-a094-0de296ebe584
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk00 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk00` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk00.lean; original SHA-256 be29e24a398b912aa03bb73e5d6716517b17ea6e32ad3afb07720dd9faf8e9f2; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_0 : ∀ j : Fin 40, (0 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 0) (recipe 0 j)≤rawProfile0 (.a 0 j) := by
  decide +kernel

theorem other_chunk_0_0 :
    (∀ j : Fin 40, (0 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 0) (recipe 0 j)).eval profile0≤rawProfile0 (.b 0 j)) ∧
    (∀ j : Fin 40, (0 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 0) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 0 j)) ∧
    (∀ l : Fin 40, (0 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 0) (recipe 0 (next 0)) (recipe 0 l)
        (rawProfile0 (.a (next 0) l))≤rawProfile0 (.p 0 l)) := by
  decide +kernel

theorem d_chunk_0_0 : ∀ j l : Fin 40, (0 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 0) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 0 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 0 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_1 : ∀ j : Fin 40, (1 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 1) (recipe 0 j)≤rawProfile0 (.a 1 j) := by
  decide +kernel

theorem other_chunk_0_1 :
    (∀ j : Fin 40, (1 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 1) (recipe 0 j)).eval profile0≤rawProfile0 (.b 1 j)) ∧
    (∀ j : Fin 40, (1 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 1) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 1 j)) ∧
    (∀ l : Fin 40, (1 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 1) (recipe 0 (next 1)) (recipe 0 l)
        (rawProfile0 (.a (next 1) l))≤rawProfile0 (.p 1 l)) := by
  decide +kernel

theorem d_chunk_0_1 : ∀ j l : Fin 40, (1 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 1) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 1 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 1 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_1


