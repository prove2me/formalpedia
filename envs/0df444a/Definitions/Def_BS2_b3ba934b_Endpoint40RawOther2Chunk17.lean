-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk17
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk17
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:22:57.166124+00:00
-- url     : https://prove2.me/theorems/9a88f8b8-51d7-4a95-97f5-baab61f77d2a
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk17 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk17` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk17.lean; original SHA-256 0bb113e411473d82781184ffccc15d99090c86663b9711dd8c24d0208134ee6d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_34 : ∀ j : Fin 40, (34 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 34) (recipe 2 j)≤rawProfile2 (.a 34 j) := by
  decide +kernel

theorem other_chunk_2_34 :
    (∀ j : Fin 40, (34 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 34) (recipe 2 j)).eval profile2≤rawProfile2 (.b 34 j)) ∧
    (∀ j : Fin 40, (34 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 34) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 34 j)) ∧
    (∀ l : Fin 40, (34 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 34) (recipe 2 (next 34)) (recipe 2 l)
        (rawProfile2 (.a (next 34) l))≤rawProfile2 (.p 34 l)) := by
  decide +kernel

theorem d_chunk_2_34 : ∀ j l : Fin 40, (34 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 34) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 34 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 34 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_35 : ∀ j : Fin 40, (35 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 35) (recipe 2 j)≤rawProfile2 (.a 35 j) := by
  decide +kernel

theorem other_chunk_2_35 :
    (∀ j : Fin 40, (35 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 35) (recipe 2 j)).eval profile2≤rawProfile2 (.b 35 j)) ∧
    (∀ j : Fin 40, (35 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 35) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 35 j)) ∧
    (∀ l : Fin 40, (35 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 35) (recipe 2 (next 35)) (recipe 2 l)
        (rawProfile2 (.a (next 35) l))≤rawProfile2 (.p 35 l)) := by
  decide +kernel

theorem d_chunk_2_35 : ∀ j l : Fin 40, (35 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 35) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 35 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 35 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_35


