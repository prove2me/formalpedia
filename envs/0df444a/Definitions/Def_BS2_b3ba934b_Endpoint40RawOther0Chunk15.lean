-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk15
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk15
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:19:10.614621+00:00
-- url     : https://prove2.me/theorems/804c5658-6b0d-47c8-b102-6c18d8bcf1e6
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk15 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk15` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk15.lean; original SHA-256 43a3ba21629dacf3dc810b8aa2380777c0432228d0db6cb5e2b322db5c644c98; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_30 : ∀ j : Fin 40, (30 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 30) (recipe 0 j)≤rawProfile0 (.a 30 j) := by
  decide +kernel

theorem other_chunk_0_30 :
    (∀ j : Fin 40, (30 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 30) (recipe 0 j)).eval profile0≤rawProfile0 (.b 30 j)) ∧
    (∀ j : Fin 40, (30 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 30) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 30 j)) ∧
    (∀ l : Fin 40, (30 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 30) (recipe 0 (next 30)) (recipe 0 l)
        (rawProfile0 (.a (next 30) l))≤rawProfile0 (.p 30 l)) := by
  decide +kernel

theorem d_chunk_0_30 : ∀ j l : Fin 40, (30 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 30) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 30 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 30 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_31 : ∀ j : Fin 40, (31 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 31) (recipe 0 j)≤rawProfile0 (.a 31 j) := by
  decide +kernel

theorem other_chunk_0_31 :
    (∀ j : Fin 40, (31 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 31) (recipe 0 j)).eval profile0≤rawProfile0 (.b 31 j)) ∧
    (∀ j : Fin 40, (31 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 31) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 31 j)) ∧
    (∀ l : Fin 40, (31 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 31) (recipe 0 (next 31)) (recipe 0 l)
        (rawProfile0 (.a (next 31) l))≤rawProfile0 (.p 31 l)) := by
  decide +kernel

theorem d_chunk_0_31 : ∀ j l : Fin 40, (31 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 31) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 31 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 31 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_31


