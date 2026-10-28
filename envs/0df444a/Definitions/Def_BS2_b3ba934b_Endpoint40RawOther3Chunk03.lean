-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk03
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:14:29.134673+00:00
-- url     : https://prove2.me/theorems/4e80c9df-153c-4107-9642-a9aed04c2daf
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk03 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk03` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk03.lean; original SHA-256 9878e7259c16f005c2731577ec31f7fde3d28d5e5903642a682689ea3fb2b445; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_6 : ∀ j : Fin 40, (6 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 6) (recipe 3 j)≤rawProfile3 (.a 6 j) := by
  decide +kernel

theorem other_chunk_3_6 :
    (∀ j : Fin 40, (6 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 6) (recipe 3 j)).eval profile3≤rawProfile3 (.b 6 j)) ∧
    (∀ j : Fin 40, (6 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 6) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 6 j)) ∧
    (∀ l : Fin 40, (6 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 6) (recipe 3 (next 6)) (recipe 3 l)
        (rawProfile3 (.a (next 6) l))≤rawProfile3 (.p 6 l)) := by
  decide +kernel

theorem d_chunk_3_6 : ∀ j l : Fin 40, (6 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 6) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 6 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 6 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_7 : ∀ j : Fin 40, (7 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 7) (recipe 3 j)≤rawProfile3 (.a 7 j) := by
  decide +kernel

theorem other_chunk_3_7 :
    (∀ j : Fin 40, (7 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 7) (recipe 3 j)).eval profile3≤rawProfile3 (.b 7 j)) ∧
    (∀ j : Fin 40, (7 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 7) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 7 j)) ∧
    (∀ l : Fin 40, (7 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 7) (recipe 3 (next 7)) (recipe 3 l)
        (rawProfile3 (.a (next 7) l))≤rawProfile3 (.p 7 l)) := by
  decide +kernel

theorem d_chunk_3_7 : ∀ j l : Fin 40, (7 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 7) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 7 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 7 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_7


