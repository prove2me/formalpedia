-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk06
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk06
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:16:42.023819+00:00
-- url     : https://prove2.me/theorems/069d9f61-4f1a-4852-a77e-98a84a165850
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk06 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk06` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk06.lean; original SHA-256 fe93cbe1def37c487fc3404524f20f124367432201fdf193b046720d353d2a47; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_12 : ∀ j : Fin 40, (12 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 12) (recipe 3 j)≤rawProfile3 (.a 12 j) := by
  decide +kernel

theorem other_chunk_3_12 :
    (∀ j : Fin 40, (12 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 12) (recipe 3 j)).eval profile3≤rawProfile3 (.b 12 j)) ∧
    (∀ j : Fin 40, (12 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 12) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 12 j)) ∧
    (∀ l : Fin 40, (12 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 12) (recipe 3 (next 12)) (recipe 3 l)
        (rawProfile3 (.a (next 12) l))≤rawProfile3 (.p 12 l)) := by
  decide +kernel

theorem d_chunk_3_12 : ∀ j l : Fin 40, (12 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 12) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 12 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 12 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_13 : ∀ j : Fin 40, (13 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 13) (recipe 3 j)≤rawProfile3 (.a 13 j) := by
  decide +kernel

theorem other_chunk_3_13 :
    (∀ j : Fin 40, (13 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 13) (recipe 3 j)).eval profile3≤rawProfile3 (.b 13 j)) ∧
    (∀ j : Fin 40, (13 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 13) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 13 j)) ∧
    (∀ l : Fin 40, (13 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 13) (recipe 3 (next 13)) (recipe 3 l)
        (rawProfile3 (.a (next 13) l))≤rawProfile3 (.p 13 l)) := by
  decide +kernel

theorem d_chunk_3_13 : ∀ j l : Fin 40, (13 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 13) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 13 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 13 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_13


