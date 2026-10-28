-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk18
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk18
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:24:40.491037+00:00
-- url     : https://prove2.me/theorems/ec983650-b455-4871-8d7f-319af961dcf1
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk18 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk18` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk18.lean; original SHA-256 5dc1a583bf237b51ac6fbb95baa2847932eda730c3ec342b3d54a1453a3ac44a; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_36 : ∀ j : Fin 40, (36 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 36) (recipe 3 j)≤rawProfile3 (.a 36 j) := by
  decide +kernel

theorem other_chunk_3_36 :
    (∀ j : Fin 40, (36 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 36) (recipe 3 j)).eval profile3≤rawProfile3 (.b 36 j)) ∧
    (∀ j : Fin 40, (36 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 36) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 36 j)) ∧
    (∀ l : Fin 40, (36 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 36) (recipe 3 (next 36)) (recipe 3 l)
        (rawProfile3 (.a (next 36) l))≤rawProfile3 (.p 36 l)) := by
  decide +kernel

theorem d_chunk_3_36 : ∀ j l : Fin 40, (36 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 36) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 36 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 36 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_37 : ∀ j : Fin 40, (37 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 37) (recipe 3 j)≤rawProfile3 (.a 37 j) := by
  decide +kernel

theorem other_chunk_3_37 :
    (∀ j : Fin 40, (37 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 37) (recipe 3 j)).eval profile3≤rawProfile3 (.b 37 j)) ∧
    (∀ j : Fin 40, (37 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 37) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 37 j)) ∧
    (∀ l : Fin 40, (37 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 37) (recipe 3 (next 37)) (recipe 3 l)
        (rawProfile3 (.a (next 37) l))≤rawProfile3 (.p 37 l)) := by
  decide +kernel

theorem d_chunk_3_37 : ∀ j l : Fin 40, (37 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 37) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 37 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 37 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_37


