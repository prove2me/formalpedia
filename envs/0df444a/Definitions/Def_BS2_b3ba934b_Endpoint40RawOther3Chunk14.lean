-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk14
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk14
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:22:22.365015+00:00
-- url     : https://prove2.me/theorems/60741bab-b83c-4593-9a66-30dfa1bf5322
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk14 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk14` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk14.lean; original SHA-256 7dbc82297450b60750239b10c44c22f62f0e15df93ee20beb81de24e572948e7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_28 : ∀ j : Fin 40, (28 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 28) (recipe 3 j)≤rawProfile3 (.a 28 j) := by
  decide +kernel

theorem other_chunk_3_28 :
    (∀ j : Fin 40, (28 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 28) (recipe 3 j)).eval profile3≤rawProfile3 (.b 28 j)) ∧
    (∀ j : Fin 40, (28 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 28) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 28 j)) ∧
    (∀ l : Fin 40, (28 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 28) (recipe 3 (next 28)) (recipe 3 l)
        (rawProfile3 (.a (next 28) l))≤rawProfile3 (.p 28 l)) := by
  decide +kernel

theorem d_chunk_3_28 : ∀ j l : Fin 40, (28 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 28) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 28 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 28 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_29 : ∀ j : Fin 40, (29 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 29) (recipe 3 j)≤rawProfile3 (.a 29 j) := by
  decide +kernel

theorem other_chunk_3_29 :
    (∀ j : Fin 40, (29 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 29) (recipe 3 j)).eval profile3≤rawProfile3 (.b 29 j)) ∧
    (∀ j : Fin 40, (29 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 29) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 29 j)) ∧
    (∀ l : Fin 40, (29 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 29) (recipe 3 (next 29)) (recipe 3 l)
        (rawProfile3 (.a (next 29) l))≤rawProfile3 (.p 29 l)) := by
  decide +kernel

theorem d_chunk_3_29 : ∀ j l : Fin 40, (29 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 29) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 29 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 29 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_29


