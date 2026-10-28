-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk05
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk05
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:04:49.335411+00:00
-- url     : https://prove2.me/theorems/0a4528cf-60cf-4830-8803-d7bc95de227e
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk05 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk05` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk05.lean; original SHA-256 62f3d588101ae173a06d28019cd76a7a261180367a57b54caeebada521d9d37f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_10 : ∀ j : Fin 40, (10 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 10) (recipe 0 j)≤rawProfile0 (.a 10 j) := by
  decide +kernel

theorem other_chunk_0_10 :
    (∀ j : Fin 40, (10 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 10) (recipe 0 j)).eval profile0≤rawProfile0 (.b 10 j)) ∧
    (∀ j : Fin 40, (10 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 10) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 10 j)) ∧
    (∀ l : Fin 40, (10 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 10) (recipe 0 (next 10)) (recipe 0 l)
        (rawProfile0 (.a (next 10) l))≤rawProfile0 (.p 10 l)) := by
  decide +kernel

theorem d_chunk_0_10 : ∀ j l : Fin 40, (10 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 10) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 10 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 10 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_11 : ∀ j : Fin 40, (11 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 11) (recipe 0 j)≤rawProfile0 (.a 11 j) := by
  decide +kernel

theorem other_chunk_0_11 :
    (∀ j : Fin 40, (11 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 11) (recipe 0 j)).eval profile0≤rawProfile0 (.b 11 j)) ∧
    (∀ j : Fin 40, (11 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 11) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 11 j)) ∧
    (∀ l : Fin 40, (11 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 11) (recipe 0 (next 11)) (recipe 0 l)
        (rawProfile0 (.a (next 11) l))≤rawProfile0 (.p 11 l)) := by
  decide +kernel

theorem d_chunk_0_11 : ∀ j l : Fin 40, (11 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 11) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 11 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 11 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_11


