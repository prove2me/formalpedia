-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk10
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk10
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:16:55.583037+00:00
-- url     : https://prove2.me/theorems/12c001ae-3c30-42a3-9165-cf060486ab9f
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk10 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk10` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk10.lean; original SHA-256 289b1db5dfecc26cfeb6cb433dc1370e8a637796e04a8e561b11808b77bd9239; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_20 : ∀ j : Fin 40, (20 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 20) (recipe 0 j)≤rawProfile0 (.a 20 j) := by
  decide +kernel

theorem other_chunk_0_20 :
    (∀ j : Fin 40, (20 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 20) (recipe 0 j)).eval profile0≤rawProfile0 (.b 20 j)) ∧
    (∀ j : Fin 40, (20 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 20) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 20 j)) ∧
    (∀ l : Fin 40, (20 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 20) (recipe 0 (next 20)) (recipe 0 l)
        (rawProfile0 (.a (next 20) l))≤rawProfile0 (.p 20 l)) := by
  decide +kernel

theorem d_chunk_0_20 : ∀ j l : Fin 40, (20 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 20) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 20 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 20 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_21 : ∀ j : Fin 40, (21 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 21) (recipe 0 j)≤rawProfile0 (.a 21 j) := by
  decide +kernel

theorem other_chunk_0_21 :
    (∀ j : Fin 40, (21 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 21) (recipe 0 j)).eval profile0≤rawProfile0 (.b 21 j)) ∧
    (∀ j : Fin 40, (21 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 21) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 21 j)) ∧
    (∀ l : Fin 40, (21 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 21) (recipe 0 (next 21)) (recipe 0 l)
        (rawProfile0 (.a (next 21) l))≤rawProfile0 (.p 21 l)) := by
  decide +kernel

theorem d_chunk_0_21 : ∀ j l : Fin 40, (21 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 21) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 21 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 21 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_21


