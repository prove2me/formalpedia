-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk04
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk04
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:03:04.657068+00:00
-- url     : https://prove2.me/theorems/bb9cbed0-be42-49bc-b36a-a02e58678d22
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk04 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk04` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk04.lean; original SHA-256 414b50e660e630b2166692937767a995d4712edd7fd157dc359533339ddaacd7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_8 : ∀ j : Fin 40, (8 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 8) (recipe 0 j)≤rawProfile0 (.a 8 j) := by
  decide +kernel

theorem other_chunk_0_8 :
    (∀ j : Fin 40, (8 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 8) (recipe 0 j)).eval profile0≤rawProfile0 (.b 8 j)) ∧
    (∀ j : Fin 40, (8 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 8) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 8 j)) ∧
    (∀ l : Fin 40, (8 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 8) (recipe 0 (next 8)) (recipe 0 l)
        (rawProfile0 (.a (next 8) l))≤rawProfile0 (.p 8 l)) := by
  decide +kernel

theorem d_chunk_0_8 : ∀ j l : Fin 40, (8 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 8) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 8 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 8 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_9 : ∀ j : Fin 40, (9 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 9) (recipe 0 j)≤rawProfile0 (.a 9 j) := by
  decide +kernel

theorem other_chunk_0_9 :
    (∀ j : Fin 40, (9 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 9) (recipe 0 j)).eval profile0≤rawProfile0 (.b 9 j)) ∧
    (∀ j : Fin 40, (9 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 9) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 9 j)) ∧
    (∀ l : Fin 40, (9 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 9) (recipe 0 (next 9)) (recipe 0 l)
        (rawProfile0 (.a (next 9) l))≤rawProfile0 (.p 9 l)) := by
  decide +kernel

theorem d_chunk_0_9 : ∀ j l : Fin 40, (9 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 9) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 9 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 9 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_9


