-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk06
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk06
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:05:52.844512+00:00
-- url     : https://prove2.me/theorems/779c72a7-9832-4c78-9137-607e827929aa
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk06 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk06` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk06.lean; original SHA-256 ca5a6a27b78ced3da1a43543ece1682bf16aaff62fb32eb7f137f0984579b6f3; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_12 : ∀ j : Fin 40, (12 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 12) (recipe 0 j)≤rawProfile0 (.a 12 j) := by
  decide +kernel

theorem other_chunk_0_12 :
    (∀ j : Fin 40, (12 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 12) (recipe 0 j)).eval profile0≤rawProfile0 (.b 12 j)) ∧
    (∀ j : Fin 40, (12 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 12) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 12 j)) ∧
    (∀ l : Fin 40, (12 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 12) (recipe 0 (next 12)) (recipe 0 l)
        (rawProfile0 (.a (next 12) l))≤rawProfile0 (.p 12 l)) := by
  decide +kernel

theorem d_chunk_0_12 : ∀ j l : Fin 40, (12 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 12) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 12 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 12 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_13 : ∀ j : Fin 40, (13 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 13) (recipe 0 j)≤rawProfile0 (.a 13 j) := by
  decide +kernel

theorem other_chunk_0_13 :
    (∀ j : Fin 40, (13 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 13) (recipe 0 j)).eval profile0≤rawProfile0 (.b 13 j)) ∧
    (∀ j : Fin 40, (13 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 13) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 13 j)) ∧
    (∀ l : Fin 40, (13 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 13) (recipe 0 (next 13)) (recipe 0 l)
        (rawProfile0 (.a (next 13) l))≤rawProfile0 (.p 13 l)) := by
  decide +kernel

theorem d_chunk_0_13 : ∀ j l : Fin 40, (13 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 13) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 13 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 13 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_13


