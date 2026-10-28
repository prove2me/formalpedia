-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk15
-- name    : BS2_b3ba934b_Endpoint40RawOther3Chunk15
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:22:57.793674+00:00
-- url     : https://prove2.me/theorems/7a041fc0-af4f-414d-a7c9-efd6db6a08b9
-- title:
--   Sensitivity separation: Endpoint40RawOther3Chunk15 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3Chunk15` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3Chunk15.lean; original SHA-256 62041d57d7f74b03333c4eaa15b7ee2dadf1ee243fd2d6e3bbda35caea9c99b1; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_3_30 : ∀ j : Fin 40, (30 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 30) (recipe 3 j)≤rawProfile3 (.a 30 j) := by
  decide +kernel

theorem other_chunk_3_30 :
    (∀ j : Fin 40, (30 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 30) (recipe 3 j)).eval profile3≤rawProfile3 (.b 30 j)) ∧
    (∀ j : Fin 40, (30 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 30) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 30 j)) ∧
    (∀ l : Fin 40, (30 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 30) (recipe 3 (next 30)) (recipe 3 l)
        (rawProfile3 (.a (next 30) l))≤rawProfile3 (.p 30 l)) := by
  decide +kernel

theorem d_chunk_3_30 : ∀ j l : Fin 40, (30 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 30) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 30 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 30 j l) := by
  decide +kernel

theorem ordinaryA_chunk_3_31 : ∀ j : Fin 40, (31 : Fin 40)≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    rawAFast 40 profile3 caps records (recipe 3 31) (recipe 3 j)≤rawProfile3 (.a 31 j) := by
  decide +kernel

theorem other_chunk_3_31 :
    (∀ j : Fin 40, (31 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 3 31) (recipe 3 j)).eval profile3≤rawProfile3 (.b 31 j)) ∧
    (∀ j : Fin 40, (31 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 3 31) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m 31 j)) ∧
    (∀ l : Fin 40, (31 : Fin 40)<l →
      pCore 40 profile3 caps (recipe 3 31) (recipe 3 (next 31)) (recipe 3 l)
        (rawProfile3 (.a (next 31) l))≤rawProfile3 (.p 31 l)) := by
  decide +kernel

theorem d_chunk_3_31 : ∀ j l : Fin 40, (31 : Fin 40)≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 31) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m 31 j)+rawProfile3 (.p j l))≤rawProfile3 (.d 31 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_3_31


