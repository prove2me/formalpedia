-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk12
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk12
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:12:56.733021+00:00
-- url     : https://prove2.me/theorems/09455dbc-6303-42ff-b6c7-0d534f84cd74
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk12 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk12` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk12.lean; original SHA-256 bc08437208665a63e4f8d52b653279cf2cc3d549d25afe640e873cc7b78de1ec; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_24 : ∀ j : Fin 40, (24 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 24) (recipe 2 j)≤rawProfile2 (.a 24 j) := by
  decide +kernel

theorem other_chunk_2_24 :
    (∀ j : Fin 40, (24 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 24) (recipe 2 j)).eval profile2≤rawProfile2 (.b 24 j)) ∧
    (∀ j : Fin 40, (24 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 24) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 24 j)) ∧
    (∀ l : Fin 40, (24 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 24) (recipe 2 (next 24)) (recipe 2 l)
        (rawProfile2 (.a (next 24) l))≤rawProfile2 (.p 24 l)) := by
  decide +kernel

theorem d_chunk_2_24 : ∀ j l : Fin 40, (24 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 24) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 24 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 24 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_25 : ∀ j : Fin 40, (25 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 25) (recipe 2 j)≤rawProfile2 (.a 25 j) := by
  decide +kernel

theorem other_chunk_2_25 :
    (∀ j : Fin 40, (25 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 25) (recipe 2 j)).eval profile2≤rawProfile2 (.b 25 j)) ∧
    (∀ j : Fin 40, (25 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 25) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 25 j)) ∧
    (∀ l : Fin 40, (25 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 25) (recipe 2 (next 25)) (recipe 2 l)
        (rawProfile2 (.a (next 25) l))≤rawProfile2 (.p 25 l)) := by
  decide +kernel

theorem d_chunk_2_25 : ∀ j l : Fin 40, (25 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 25) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 25 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 25 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_25


