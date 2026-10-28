-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk14
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk14
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:18:29.658789+00:00
-- url     : https://prove2.me/theorems/0b13bfbf-b598-4d62-a6c1-d6114b153192
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk14 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk14` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk14.lean; original SHA-256 a7176c139c283392e1eba294e1a9910e4b84a427189811eeab058ac55a89141c; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_28 : ∀ j : Fin 40, (28 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 28) (recipe 0 j)≤rawProfile0 (.a 28 j) := by
  decide +kernel

theorem other_chunk_0_28 :
    (∀ j : Fin 40, (28 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 28) (recipe 0 j)).eval profile0≤rawProfile0 (.b 28 j)) ∧
    (∀ j : Fin 40, (28 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 28) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 28 j)) ∧
    (∀ l : Fin 40, (28 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 28) (recipe 0 (next 28)) (recipe 0 l)
        (rawProfile0 (.a (next 28) l))≤rawProfile0 (.p 28 l)) := by
  decide +kernel

theorem d_chunk_0_28 : ∀ j l : Fin 40, (28 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 28) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 28 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 28 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_29 : ∀ j : Fin 40, (29 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 29) (recipe 0 j)≤rawProfile0 (.a 29 j) := by
  decide +kernel

theorem other_chunk_0_29 :
    (∀ j : Fin 40, (29 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 29) (recipe 0 j)).eval profile0≤rawProfile0 (.b 29 j)) ∧
    (∀ j : Fin 40, (29 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 29) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 29 j)) ∧
    (∀ l : Fin 40, (29 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 29) (recipe 0 (next 29)) (recipe 0 l)
        (rawProfile0 (.a (next 29) l))≤rawProfile0 (.p 29 l)) := by
  decide +kernel

theorem d_chunk_0_29 : ∀ j l : Fin 40, (29 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 29) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 29 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 29 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_29


