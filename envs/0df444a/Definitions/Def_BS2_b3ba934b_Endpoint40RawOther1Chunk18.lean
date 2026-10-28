-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk18
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk18
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:54:21.784993+00:00
-- url     : https://prove2.me/theorems/20c075a6-7dbc-4a86-971e-0b5467b2ce02
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk18 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk18` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk18.lean; original SHA-256 3603c2921ee6d336a7672fe94e5496e82e21befae7afaec0bb3a302c2a0deeaa; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_36 : ∀ j : Fin 40, (36 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 36) (recipe 1 j)≤rawProfile1 (.a 36 j) := by
  decide +kernel

theorem other_chunk_1_36 :
    (∀ j : Fin 40, (36 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 36) (recipe 1 j)).eval profile1≤rawProfile1 (.b 36 j)) ∧
    (∀ j : Fin 40, (36 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 36) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 36 j)) ∧
    (∀ l : Fin 40, (36 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 36) (recipe 1 (next 36)) (recipe 1 l)
        (rawProfile1 (.a (next 36) l))≤rawProfile1 (.p 36 l)) := by
  decide +kernel

theorem d_chunk_1_36 : ∀ j l : Fin 40, (36 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 36) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 36 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 36 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_37 : ∀ j : Fin 40, (37 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 37) (recipe 1 j)≤rawProfile1 (.a 37 j) := by
  decide +kernel

theorem other_chunk_1_37 :
    (∀ j : Fin 40, (37 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 37) (recipe 1 j)).eval profile1≤rawProfile1 (.b 37 j)) ∧
    (∀ j : Fin 40, (37 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 37) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 37 j)) ∧
    (∀ l : Fin 40, (37 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 37) (recipe 1 (next 37)) (recipe 1 l)
        (rawProfile1 (.a (next 37) l))≤rawProfile1 (.p 37 l)) := by
  decide +kernel

theorem d_chunk_1_37 : ∀ j l : Fin 40, (37 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 37) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 37 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 37 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_37


