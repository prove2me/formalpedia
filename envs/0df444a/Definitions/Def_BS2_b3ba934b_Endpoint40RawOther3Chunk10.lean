-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk10
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk10
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:19:41.486009+00:00
-- url     : https://prove2.me/theorems/98594812-69e5-4aec-8fc4-0f5721744ea4
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk10 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk10` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk10.lean; original SHA-256 f1e22c8a0df6e9ade9e2e4c0173c4a9c5e6e027cd2d43cab72c6d5ffd2bba865; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_20 : ∀ j : Fin 40, (20 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 20) (recipe 3 j)≤rawProfile3 (.a 20 j) := by
  decide +kernel

theorem other_chunk_3_20 :
    (∀ j : Fin 40, (20 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 20) (recipe 3 j)).eval profile3≤rawProfile3 (.b 20 j)) ∧
    (∀ j : Fin 40, (20 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 20) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 20 j)) ∧
    (∀ l : Fin 40, (20 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 20) (recipe 3 (next 20)) (recipe 3 l)
        (rawProfile3 (.a (next 20) l))≤rawProfile3 (.p 20 l)) := by
  decide +kernel

theorem d_chunk_3_20 : ∀ j l : Fin 40, (20 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 20) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 20 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 20 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_21 : ∀ j : Fin 40, (21 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 21) (recipe 3 j)≤rawProfile3 (.a 21 j) := by
  decide +kernel

theorem other_chunk_3_21 :
    (∀ j : Fin 40, (21 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 21) (recipe 3 j)).eval profile3≤rawProfile3 (.b 21 j)) ∧
    (∀ j : Fin 40, (21 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 21) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 21 j)) ∧
    (∀ l : Fin 40, (21 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 21) (recipe 3 (next 21)) (recipe 3 l)
        (rawProfile3 (.a (next 21) l))≤rawProfile3 (.p 21 l)) := by
  decide +kernel

theorem d_chunk_3_21 : ∀ j l : Fin 40, (21 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 21) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 21 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 21 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_21


