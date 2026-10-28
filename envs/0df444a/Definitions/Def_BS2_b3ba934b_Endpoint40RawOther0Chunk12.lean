-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk12
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk12
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:17:44.347286+00:00
-- url     : https://prove2.me/theorems/c32eeaf8-fea6-40b5-9295-b304fd8e6a6d
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk12 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk12` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk12.lean; original SHA-256 9c17d9b15feabfb63049a3d5ea516f158f0fb72c183b51c54fef7bd64093bd3b; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_24 : ∀ j : Fin 40, (24 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 24) (recipe 0 j)≤rawProfile0 (.a 24 j) := by
  decide +kernel

theorem other_chunk_0_24 :
    (∀ j : Fin 40, (24 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 24) (recipe 0 j)).eval profile0≤rawProfile0 (.b 24 j)) ∧
    (∀ j : Fin 40, (24 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 24) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 24 j)) ∧
    (∀ l : Fin 40, (24 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 24) (recipe 0 (next 24)) (recipe 0 l)
        (rawProfile0 (.a (next 24) l))≤rawProfile0 (.p 24 l)) := by
  decide +kernel

theorem d_chunk_0_24 : ∀ j l : Fin 40, (24 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 24) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 24 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 24 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_25 : ∀ j : Fin 40, (25 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 25) (recipe 0 j)≤rawProfile0 (.a 25 j) := by
  decide +kernel

theorem other_chunk_0_25 :
    (∀ j : Fin 40, (25 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 25) (recipe 0 j)).eval profile0≤rawProfile0 (.b 25 j)) ∧
    (∀ j : Fin 40, (25 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 25) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 25 j)) ∧
    (∀ l : Fin 40, (25 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 25) (recipe 0 (next 25)) (recipe 0 l)
        (rawProfile0 (.a (next 25) l))≤rawProfile0 (.p 25 l)) := by
  decide +kernel

theorem d_chunk_0_25 : ∀ j l : Fin 40, (25 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 25) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 25 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 25 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_25


