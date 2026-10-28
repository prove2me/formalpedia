-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk13
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk13
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:17:37.068418+00:00
-- url     : https://prove2.me/theorems/cb399074-7e5e-4ba2-bc7d-e4c7a45b864d
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk13 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk13` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk13.lean; original SHA-256 8c3feecb77cae1ef24d54d44e95e8e8781eed87eee56307dc6a9f5f32a355586; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_26 : ∀ j : Fin 40, (26 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 26) (recipe 0 j)≤rawProfile0 (.a 26 j) := by
  decide +kernel

theorem other_chunk_0_26 :
    (∀ j : Fin 40, (26 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 26) (recipe 0 j)).eval profile0≤rawProfile0 (.b 26 j)) ∧
    (∀ j : Fin 40, (26 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 26) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 26 j)) ∧
    (∀ l : Fin 40, (26 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 26) (recipe 0 (next 26)) (recipe 0 l)
        (rawProfile0 (.a (next 26) l))≤rawProfile0 (.p 26 l)) := by
  decide +kernel

theorem d_chunk_0_26 : ∀ j l : Fin 40, (26 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 26) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 26 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 26 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_27 : ∀ j : Fin 40, (27 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 27) (recipe 0 j)≤rawProfile0 (.a 27 j) := by
  decide +kernel

theorem other_chunk_0_27 :
    (∀ j : Fin 40, (27 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 27) (recipe 0 j)).eval profile0≤rawProfile0 (.b 27 j)) ∧
    (∀ j : Fin 40, (27 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 27) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 27 j)) ∧
    (∀ l : Fin 40, (27 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 27) (recipe 0 (next 27)) (recipe 0 l)
        (rawProfile0 (.a (next 27) l))≤rawProfile0 (.p 27 l)) := by
  decide +kernel

theorem d_chunk_0_27 : ∀ j l : Fin 40, (27 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 27) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 27 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 27 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_27


