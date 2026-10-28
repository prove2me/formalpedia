-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk17
-- name    : BS2_b3ba934b_Endpoint40RawOther0Chunk17
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:19:52.001326+00:00
-- url     : https://prove2.me/theorems/cfb83471-9363-4886-81a7-c47b353ee319
-- title:
--   Sensitivity separation: Endpoint40RawOther0Chunk17 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0Chunk17` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0Chunk17.lean; original SHA-256 19bbc9a4967b4bd76ef998ee23c2bbc8a1b56d13b1e908a7c3296802d7a93be4; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_0_34 : ∀ j : Fin 40, (34 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 34) (recipe 0 j)≤rawProfile0 (.a 34 j) := by
  decide +kernel

theorem other_chunk_0_34 :
    (∀ j : Fin 40, (34 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 34) (recipe 0 j)).eval profile0≤rawProfile0 (.b 34 j)) ∧
    (∀ j : Fin 40, (34 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 34) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 34 j)) ∧
    (∀ l : Fin 40, (34 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 34) (recipe 0 (next 34)) (recipe 0 l)
        (rawProfile0 (.a (next 34) l))≤rawProfile0 (.p 34 l)) := by
  decide +kernel

theorem d_chunk_0_34 : ∀ j l : Fin 40, (34 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 34) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 34 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 34 j l) := by
  decide +kernel

theorem ordinaryA_chunk_0_35 : ∀ j : Fin 40, (35 : Fin 40)≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    rawAFast 40 profile0 caps records (recipe 0 35) (recipe 0 j)≤rawProfile0 (.a 35 j) := by
  decide +kernel

theorem other_chunk_0_35 :
    (∀ j : Fin 40, (35 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 0 35) (recipe 0 j)).eval profile0≤rawProfile0 (.b 35 j)) ∧
    (∀ j : Fin 40, (35 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 0 35) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m 35 j)) ∧
    (∀ l : Fin 40, (35 : Fin 40)<l →
      pCore 40 profile0 caps (recipe 0 35) (recipe 0 (next 35)) (recipe 0 l)
        (rawProfile0 (.a (next 35) l))≤rawProfile0 (.p 35 l)) := by
  decide +kernel

theorem d_chunk_0_35 : ∀ j l : Fin 40, (35 : Fin 40)≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 35) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m 35 j)+rawProfile0 (.p j l))≤rawProfile0 (.d 35 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_0_35


