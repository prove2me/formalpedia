-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk19
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk19
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:20:31.370155+00:00
-- url     : https://prove2.me/theorems/26f2de96-6440-49ea-a96e-abc792136edd
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk19 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk19` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk19.lean; original SHA-256 6ab54344821e0a2caa12ec64dbf9ff0279e31c4ff6ecd2795f8f99015273c564; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_38 : ∀ j : Fin 40, (38 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 38) (recipe 0 j)≤rawProfile0 (.a 38 j) := by
  decide +kernel

theorem other_chunk_0_38 :
    (∀ j : Fin 40, (38 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 38) (recipe 0 j)).eval profile0≤rawProfile0 (.b 38 j)) ∧
    (∀ j : Fin 40, (38 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 38) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 38 j)) ∧
    (∀ l : Fin 40, (38 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 38) (recipe 0 (next 38)) (recipe 0 l)
        (rawProfile0 (.a (next 38) l))≤rawProfile0 (.p 38 l)) := by
  decide +kernel

theorem d_chunk_0_38 : ∀ j l : Fin 40, (38 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 38) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 38 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 38 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_39 : ∀ j : Fin 40, (39 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 39) (recipe 0 j)≤rawProfile0 (.a 39 j) := by
  decide +kernel

theorem other_chunk_0_39 :
    (∀ j : Fin 40, (39 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 39) (recipe 0 j)).eval profile0≤rawProfile0 (.b 39 j)) ∧
    (∀ j : Fin 40, (39 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 39) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 39 j)) ∧
    (∀ l : Fin 40, (39 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 39) (recipe 0 (next 39)) (recipe 0 l)
        (rawProfile0 (.a (next 39) l))≤rawProfile0 (.p 39 l)) := by
  decide +kernel

theorem d_chunk_0_39 : ∀ j l : Fin 40, (39 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 39) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 39 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 39 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_39


