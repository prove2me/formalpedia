-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk09
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk09
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:19:00.044952+00:00
-- url     : https://prove2.me/theorems/69e3eb26-7f21-4c72-8a33-2b000066a6ee
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk09 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk09` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk09.lean; original SHA-256 be5574d3d8a74bdb3e8df0237ed7a085494c2a3ff6e6b13a7331faf821c81292; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_18 : ∀ j : Fin 40, (18 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 18) (recipe 3 j)≤rawProfile3 (.a 18 j) := by
  decide +kernel

theorem other_chunk_3_18 :
    (∀ j : Fin 40, (18 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 18) (recipe 3 j)).eval profile3≤rawProfile3 (.b 18 j)) ∧
    (∀ j : Fin 40, (18 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 18) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 18 j)) ∧
    (∀ l : Fin 40, (18 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 18) (recipe 3 (next 18)) (recipe 3 l)
        (rawProfile3 (.a (next 18) l))≤rawProfile3 (.p 18 l)) := by
  decide +kernel

theorem d_chunk_3_18 : ∀ j l : Fin 40, (18 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 18) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 18 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 18 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_19 : ∀ j : Fin 40, (19 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 19) (recipe 3 j)≤rawProfile3 (.a 19 j) := by
  decide +kernel

theorem other_chunk_3_19 :
    (∀ j : Fin 40, (19 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 19) (recipe 3 j)).eval profile3≤rawProfile3 (.b 19 j)) ∧
    (∀ j : Fin 40, (19 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 19) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 19 j)) ∧
    (∀ l : Fin 40, (19 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 19) (recipe 3 (next 19)) (recipe 3 l)
        (rawProfile3 (.a (next 19) l))≤rawProfile3 (.p 19 l)) := by
  decide +kernel

theorem d_chunk_3_19 : ∀ j l : Fin 40, (19 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 19) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 19 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 19 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_19


