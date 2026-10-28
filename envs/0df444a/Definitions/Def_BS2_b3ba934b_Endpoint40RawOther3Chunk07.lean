-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk07
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk07
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:17:30.150251+00:00
-- url     : https://prove2.me/theorems/00745998-b00a-4250-9b3a-056908a16d84
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk07 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk07` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk07.lean; original SHA-256 bf8da1be9220a14b590e1459a0fa71953ca752f673898c8062e1df8da406db0d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_14 : ∀ j : Fin 40, (14 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 14) (recipe 3 j)≤rawProfile3 (.a 14 j) := by
  decide +kernel

theorem other_chunk_3_14 :
    (∀ j : Fin 40, (14 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 14) (recipe 3 j)).eval profile3≤rawProfile3 (.b 14 j)) ∧
    (∀ j : Fin 40, (14 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 14) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 14 j)) ∧
    (∀ l : Fin 40, (14 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 14) (recipe 3 (next 14)) (recipe 3 l)
        (rawProfile3 (.a (next 14) l))≤rawProfile3 (.p 14 l)) := by
  decide +kernel

theorem d_chunk_3_14 : ∀ j l : Fin 40, (14 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 14) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 14 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 14 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_15 : ∀ j : Fin 40, (15 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 15) (recipe 3 j)≤rawProfile3 (.a 15 j) := by
  decide +kernel

theorem other_chunk_3_15 :
    (∀ j : Fin 40, (15 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 15) (recipe 3 j)).eval profile3≤rawProfile3 (.b 15 j)) ∧
    (∀ j : Fin 40, (15 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 15) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 15 j)) ∧
    (∀ l : Fin 40, (15 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 15) (recipe 3 (next 15)) (recipe 3 l)
        (rawProfile3 (.a (next 15) l))≤rawProfile3 (.p 15 l)) := by
  decide +kernel

theorem d_chunk_3_15 : ∀ j l : Fin 40, (15 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 15) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 15 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 15 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_15


