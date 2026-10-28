-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk03
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:02:37.713315+00:00
-- url     : https://prove2.me/theorems/2a4af906-039b-4913-87a0-db62e9c5f280
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk03 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk03` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk03.lean; original SHA-256 7723579957d4afec816a8412771dc5fc7a78269f4e420400e1dd8fcd5f59f648; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_6 : ∀ j : Fin 40, (6 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 6) (recipe 0 j)≤rawProfile0 (.a 6 j) := by
  decide +kernel

theorem other_chunk_0_6 :
    (∀ j : Fin 40, (6 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 6) (recipe 0 j)).eval profile0≤rawProfile0 (.b 6 j)) ∧
    (∀ j : Fin 40, (6 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 6) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 6 j)) ∧
    (∀ l : Fin 40, (6 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 6) (recipe 0 (next 6)) (recipe 0 l)
        (rawProfile0 (.a (next 6) l))≤rawProfile0 (.p 6 l)) := by
  decide +kernel

theorem d_chunk_0_6 : ∀ j l : Fin 40, (6 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 6) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 6 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 6 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_7 : ∀ j : Fin 40, (7 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 7) (recipe 0 j)≤rawProfile0 (.a 7 j) := by
  decide +kernel

theorem other_chunk_0_7 :
    (∀ j : Fin 40, (7 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 7) (recipe 0 j)).eval profile0≤rawProfile0 (.b 7 j)) ∧
    (∀ j : Fin 40, (7 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 7) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 7 j)) ∧
    (∀ l : Fin 40, (7 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 7) (recipe 0 (next 7)) (recipe 0 l)
        (rawProfile0 (.a (next 7) l))≤rawProfile0 (.p 7 l)) := by
  decide +kernel

theorem d_chunk_0_7 : ∀ j l : Fin 40, (7 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 7) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 7 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 7 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_7


