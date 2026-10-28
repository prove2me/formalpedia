-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk18
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk18
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:20:24.65776+00:00
-- url     : https://prove2.me/theorems/975af064-1757-4283-99be-821886403dc3
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk18 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk18` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk18.lean; original SHA-256 b86e1774bee22c973a8c7ba73b71d3698e921b87fda8e659a20e201dca78b8c7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_36 : ∀ j : Fin 40, (36 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 36) (recipe 0 j)≤rawProfile0 (.a 36 j) := by
  decide +kernel

theorem other_chunk_0_36 :
    (∀ j : Fin 40, (36 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 36) (recipe 0 j)).eval profile0≤rawProfile0 (.b 36 j)) ∧
    (∀ j : Fin 40, (36 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 36) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 36 j)) ∧
    (∀ l : Fin 40, (36 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 36) (recipe 0 (next 36)) (recipe 0 l)
        (rawProfile0 (.a (next 36) l))≤rawProfile0 (.p 36 l)) := by
  decide +kernel

theorem d_chunk_0_36 : ∀ j l : Fin 40, (36 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 36) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 36 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 36 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_37 : ∀ j : Fin 40, (37 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 37) (recipe 0 j)≤rawProfile0 (.a 37 j) := by
  decide +kernel

theorem other_chunk_0_37 :
    (∀ j : Fin 40, (37 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 37) (recipe 0 j)).eval profile0≤rawProfile0 (.b 37 j)) ∧
    (∀ j : Fin 40, (37 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 37) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 37 j)) ∧
    (∀ l : Fin 40, (37 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 37) (recipe 0 (next 37)) (recipe 0 l)
        (rawProfile0 (.a (next 37) l))≤rawProfile0 (.p 37 l)) := by
  decide +kernel

theorem d_chunk_0_37 : ∀ j l : Fin 40, (37 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 37) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 37 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 37 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_37


