-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk00
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk00
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:12:19.393608+00:00
-- url     : https://prove2.me/theorems/25225af5-a7b7-400f-b079-f5098640ce08
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk00 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk00` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk00.lean; original SHA-256 beca008d40c7114c22e837d762f84d30d72720627285369d167c5f2e609f22dc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_0 : ∀ j : Fin 40, (0 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 0) (recipe 3 j)≤rawProfile3 (.a 0 j) := by
  decide +kernel

theorem other_chunk_3_0 :
    (∀ j : Fin 40, (0 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 0) (recipe 3 j)).eval profile3≤rawProfile3 (.b 0 j)) ∧
    (∀ j : Fin 40, (0 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 0) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 0 j)) ∧
    (∀ l : Fin 40, (0 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 0) (recipe 3 (next 0)) (recipe 3 l)
        (rawProfile3 (.a (next 0) l))≤rawProfile3 (.p 0 l)) := by
  decide +kernel

theorem d_chunk_3_0 : ∀ j l : Fin 40, (0 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 0) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 0 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 0 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_1 : ∀ j : Fin 40, (1 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 1) (recipe 3 j)≤rawProfile3 (.a 1 j) := by
  decide +kernel

theorem other_chunk_3_1 :
    (∀ j : Fin 40, (1 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 1) (recipe 3 j)).eval profile3≤rawProfile3 (.b 1 j)) ∧
    (∀ j : Fin 40, (1 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 1) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 1 j)) ∧
    (∀ l : Fin 40, (1 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 1) (recipe 3 (next 1)) (recipe 3 l)
        (rawProfile3 (.a (next 1) l))≤rawProfile3 (.p 1 l)) := by
  decide +kernel

theorem d_chunk_3_1 : ∀ j l : Fin 40, (1 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 1) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 1 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 1 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_1


