-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk06
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk06
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:46:38.852524+00:00
-- url     : https://prove2.me/theorems/cb568754-3a41-4722-bb6c-21bf01b5d269
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk06 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk06` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk06.lean; original SHA-256 c6a5aaaf2415c324e1b14a12fb39e14f465dae5559366e86ad09ac5f0b7fef60; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_12 : ∀ j : Fin 40, (12 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 12) (recipe 1 j)≤rawProfile1 (.a 12 j) := by
  decide +kernel

theorem other_chunk_1_12 :
    (∀ j : Fin 40, (12 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 12) (recipe 1 j)).eval profile1≤rawProfile1 (.b 12 j)) ∧
    (∀ j : Fin 40, (12 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 12) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 12 j)) ∧
    (∀ l : Fin 40, (12 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 12) (recipe 1 (next 12)) (recipe 1 l)
        (rawProfile1 (.a (next 12) l))≤rawProfile1 (.p 12 l)) := by
  decide +kernel

theorem d_chunk_1_12 : ∀ j l : Fin 40, (12 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 12) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 12 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 12 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_13 : ∀ j : Fin 40, (13 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 13) (recipe 1 j)≤rawProfile1 (.a 13 j) := by
  decide +kernel

theorem other_chunk_1_13 :
    (∀ j : Fin 40, (13 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 13) (recipe 1 j)).eval profile1≤rawProfile1 (.b 13 j)) ∧
    (∀ j : Fin 40, (13 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 13) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 13 j)) ∧
    (∀ l : Fin 40, (13 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 13) (recipe 1 (next 13)) (recipe 1 l)
        (rawProfile1 (.a (next 13) l))≤rawProfile1 (.p 13 l)) := by
  decide +kernel

theorem d_chunk_1_13 : ∀ j l : Fin 40, (13 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 13) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 13 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 13 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_13


