-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk07
-- name    : BS2_b3ba934b_Endpoint40RawOther2Chunk07
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:10:22.4961+00:00
-- url     : https://prove2.me/theorems/fd5d636d-974e-416f-9fc3-dded970e29c2
-- title:
--   Sensitivity separation: Endpoint40RawOther2Chunk07 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2Chunk07` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2Chunk07.lean; original SHA-256 5e61494bd61eca5749bffd5a616bfed1187b18574ad4bcd242ff3f8bc97feead; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_2_14 : ∀ j : Fin 40, (14 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 14) (recipe 2 j)≤rawProfile2 (.a 14 j) := by
  decide +kernel

theorem other_chunk_2_14 :
    (∀ j : Fin 40, (14 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 14) (recipe 2 j)).eval profile2≤rawProfile2 (.b 14 j)) ∧
    (∀ j : Fin 40, (14 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 14) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 14 j)) ∧
    (∀ l : Fin 40, (14 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 14) (recipe 2 (next 14)) (recipe 2 l)
        (rawProfile2 (.a (next 14) l))≤rawProfile2 (.p 14 l)) := by
  decide +kernel

theorem d_chunk_2_14 : ∀ j l : Fin 40, (14 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 14) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 14 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 14 j l) := by
  decide +kernel

theorem ordinaryA_chunk_2_15 : ∀ j : Fin 40, (15 : Fin 40)≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    rawAFast 40 profile2 caps records (recipe 2 15) (recipe 2 j)≤rawProfile2 (.a 15 j) := by
  decide +kernel

theorem other_chunk_2_15 :
    (∀ j : Fin 40, (15 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 2 15) (recipe 2 j)).eval profile2≤rawProfile2 (.b 15 j)) ∧
    (∀ j : Fin 40, (15 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 2 15) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m 15 j)) ∧
    (∀ l : Fin 40, (15 : Fin 40)<l →
      pCore 40 profile2 caps (recipe 2 15) (recipe 2 (next 15)) (recipe 2 l)
        (rawProfile2 (.a (next 15) l))≤rawProfile2 (.p 15 l)) := by
  decide +kernel

theorem d_chunk_2_15 : ∀ j l : Fin 40, (15 : Fin 40)≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 15) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m 15 j)+rawProfile2 (.p j l))≤rawProfile2 (.d 15 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_2_15


