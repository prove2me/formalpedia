-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk12
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk12
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:21:08.962556+00:00
-- url     : https://prove2.me/theorems/e3ee259a-9225-4362-ac16-8166c2dc5ff4
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk12 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk12` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk12.lean; original SHA-256 43c51faa0c288b59bb983f6c03f73022ba4251129de111abcd24bedd98122585; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_24 : ∀ j : Fin 40, (24 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 24) (recipe 3 j)≤rawProfile3 (.a 24 j) := by
  decide +kernel

theorem other_chunk_3_24 :
    (∀ j : Fin 40, (24 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 24) (recipe 3 j)).eval profile3≤rawProfile3 (.b 24 j)) ∧
    (∀ j : Fin 40, (24 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 24) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 24 j)) ∧
    (∀ l : Fin 40, (24 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 24) (recipe 3 (next 24)) (recipe 3 l)
        (rawProfile3 (.a (next 24) l))≤rawProfile3 (.p 24 l)) := by
  decide +kernel

theorem d_chunk_3_24 : ∀ j l : Fin 40, (24 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 24) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 24 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 24 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_25 : ∀ j : Fin 40, (25 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 25) (recipe 3 j)≤rawProfile3 (.a 25 j) := by
  decide +kernel

theorem other_chunk_3_25 :
    (∀ j : Fin 40, (25 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 25) (recipe 3 j)).eval profile3≤rawProfile3 (.b 25 j)) ∧
    (∀ j : Fin 40, (25 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 25) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 25 j)) ∧
    (∀ l : Fin 40, (25 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 25) (recipe 3 (next 25)) (recipe 3 l)
        (rawProfile3 (.a (next 25) l))≤rawProfile3 (.p 25 l)) := by
  decide +kernel

theorem d_chunk_3_25 : ∀ j l : Fin 40, (25 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 25) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 25 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 25 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_25


