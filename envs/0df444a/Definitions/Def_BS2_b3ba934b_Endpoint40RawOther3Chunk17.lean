-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk17
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk17
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:24:07.545594+00:00
-- url     : https://prove2.me/theorems/c31e0d03-ae87-469b-9591-6ca505fa230d
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk17 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk17` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk17.lean; original SHA-256 4d28f14abf20c33331c78af233391422ea4b0e9d18cfa05a0ac3fa9da3dc91d8; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_34 : ∀ j : Fin 40, (34 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 34) (recipe 3 j)≤rawProfile3 (.a 34 j) := by
  decide +kernel

theorem other_chunk_3_34 :
    (∀ j : Fin 40, (34 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 34) (recipe 3 j)).eval profile3≤rawProfile3 (.b 34 j)) ∧
    (∀ j : Fin 40, (34 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 34) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 34 j)) ∧
    (∀ l : Fin 40, (34 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 34) (recipe 3 (next 34)) (recipe 3 l)
        (rawProfile3 (.a (next 34) l))≤rawProfile3 (.p 34 l)) := by
  decide +kernel

theorem d_chunk_3_34 : ∀ j l : Fin 40, (34 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 34) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 34 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 34 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_35 : ∀ j : Fin 40, (35 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 35) (recipe 3 j)≤rawProfile3 (.a 35 j) := by
  decide +kernel

theorem other_chunk_3_35 :
    (∀ j : Fin 40, (35 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 35) (recipe 3 j)).eval profile3≤rawProfile3 (.b 35 j)) ∧
    (∀ j : Fin 40, (35 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 35) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 35 j)) ∧
    (∀ l : Fin 40, (35 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 35) (recipe 3 (next 35)) (recipe 3 l)
        (rawProfile3 (.a (next 35) l))≤rawProfile3 (.p 35 l)) := by
  decide +kernel

theorem d_chunk_3_35 : ∀ j l : Fin 40, (35 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 35) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 35 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 35 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_35


