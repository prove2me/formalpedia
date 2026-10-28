-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk05
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk05
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:15:50.221503+00:00
-- url     : https://prove2.me/theorems/03a4b25f-937f-4020-8d6d-c5ef05cbc340
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk05 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk05` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk05.lean; original SHA-256 5981942dec69a73a04555e81500c8325304109daa7bdce16c8fbcb7da5b9f352; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_10 : ∀ j : Fin 40, (10 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 10) (recipe 3 j)≤rawProfile3 (.a 10 j) := by
  decide +kernel

theorem other_chunk_3_10 :
    (∀ j : Fin 40, (10 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 10) (recipe 3 j)).eval profile3≤rawProfile3 (.b 10 j)) ∧
    (∀ j : Fin 40, (10 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 10) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 10 j)) ∧
    (∀ l : Fin 40, (10 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 10) (recipe 3 (next 10)) (recipe 3 l)
        (rawProfile3 (.a (next 10) l))≤rawProfile3 (.p 10 l)) := by
  decide +kernel

theorem d_chunk_3_10 : ∀ j l : Fin 40, (10 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 10) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 10 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 10 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_11 : ∀ j : Fin 40, (11 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 11) (recipe 3 j)≤rawProfile3 (.a 11 j) := by
  decide +kernel

theorem other_chunk_3_11 :
    (∀ j : Fin 40, (11 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 11) (recipe 3 j)).eval profile3≤rawProfile3 (.b 11 j)) ∧
    (∀ j : Fin 40, (11 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 11) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 11 j)) ∧
    (∀ l : Fin 40, (11 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 11) (recipe 3 (next 11)) (recipe 3 l)
        (rawProfile3 (.a (next 11) l))≤rawProfile3 (.p 11 l)) := by
  decide +kernel

theorem d_chunk_3_11 : ∀ j l : Fin 40, (11 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 11) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 11 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 11 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_11


