-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk02
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk02
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:13:41.874085+00:00
-- url     : https://prove2.me/theorems/abcbff88-f126-41bc-bc55-500c7002db96
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk02 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk02` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk02.lean; original SHA-256 65ff5a70bd20b8b6e73f0c0194f8fd54ffdb1f18a53c16653a7a0a22997dc07d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_4 : ∀ j : Fin 40, (4 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 4) (recipe 3 j)≤rawProfile3 (.a 4 j) := by
  decide +kernel

theorem other_chunk_3_4 :
    (∀ j : Fin 40, (4 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 4) (recipe 3 j)).eval profile3≤rawProfile3 (.b 4 j)) ∧
    (∀ j : Fin 40, (4 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 4) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 4 j)) ∧
    (∀ l : Fin 40, (4 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 4) (recipe 3 (next 4)) (recipe 3 l)
        (rawProfile3 (.a (next 4) l))≤rawProfile3 (.p 4 l)) := by
  decide +kernel

theorem d_chunk_3_4 : ∀ j l : Fin 40, (4 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 4) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 4 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 4 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_5 : ∀ j : Fin 40, (5 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 5) (recipe 3 j)≤rawProfile3 (.a 5 j) := by
  decide +kernel

theorem other_chunk_3_5 :
    (∀ j : Fin 40, (5 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 5) (recipe 3 j)).eval profile3≤rawProfile3 (.b 5 j)) ∧
    (∀ j : Fin 40, (5 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 5) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 5 j)) ∧
    (∀ l : Fin 40, (5 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 5) (recipe 3 (next 5)) (recipe 3 l)
        (rawProfile3 (.a (next 5) l))≤rawProfile3 (.p 5 l)) := by
  decide +kernel

theorem d_chunk_3_5 : ∀ j l : Fin 40, (5 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 5) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 5 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 5 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_5


