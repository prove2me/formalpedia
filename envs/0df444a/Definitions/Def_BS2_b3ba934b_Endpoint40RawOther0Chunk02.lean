-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk02
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk02
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:00:24.309659+00:00
-- url     : https://prove2.me/theorems/f87581ec-f741-4621-8dd6-63c128883acf
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk02 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk02` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk02.lean; original SHA-256 596aaf88f236eb6b7fa9e86a4c93196c535c43d238276c22803acb5bb8c7ace6; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_4 : ∀ j : Fin 40, (4 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 4) (recipe 0 j)≤rawProfile0 (.a 4 j) := by
  decide +kernel

theorem other_chunk_0_4 :
    (∀ j : Fin 40, (4 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 4) (recipe 0 j)).eval profile0≤rawProfile0 (.b 4 j)) ∧
    (∀ j : Fin 40, (4 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 4) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 4 j)) ∧
    (∀ l : Fin 40, (4 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 4) (recipe 0 (next 4)) (recipe 0 l)
        (rawProfile0 (.a (next 4) l))≤rawProfile0 (.p 4 l)) := by
  decide +kernel

theorem d_chunk_0_4 : ∀ j l : Fin 40, (4 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 4) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 4 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 4 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_5 : ∀ j : Fin 40, (5 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 5) (recipe 0 j)≤rawProfile0 (.a 5 j) := by
  decide +kernel

theorem other_chunk_0_5 :
    (∀ j : Fin 40, (5 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 5) (recipe 0 j)).eval profile0≤rawProfile0 (.b 5 j)) ∧
    (∀ j : Fin 40, (5 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 5) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 5 j)) ∧
    (∀ l : Fin 40, (5 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 5) (recipe 0 (next 5)) (recipe 0 l)
        (rawProfile0 (.a (next 5) l))≤rawProfile0 (.p 5 l)) := by
  decide +kernel

theorem d_chunk_0_5 : ∀ j l : Fin 40, (5 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 5) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 5 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 5 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_5


