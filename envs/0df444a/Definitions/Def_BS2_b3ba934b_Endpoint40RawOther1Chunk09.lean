-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk09
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk09
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:48:41.973987+00:00
-- url     : https://prove2.me/theorems/8250fbef-17bb-4272-a582-82ef309cc237
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk09 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk09` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk09.lean; original SHA-256 44a184e0761accd20c71f61b7adf8b15255cd920d57eed84ba6ba486b6105cd5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_18 : ∀ j : Fin 40, (18 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 18) (recipe 1 j)≤rawProfile1 (.a 18 j) := by
  decide +kernel

theorem other_chunk_1_18 :
    (∀ j : Fin 40, (18 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 18) (recipe 1 j)).eval profile1≤rawProfile1 (.b 18 j)) ∧
    (∀ j : Fin 40, (18 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 18) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 18 j)) ∧
    (∀ l : Fin 40, (18 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 18) (recipe 1 (next 18)) (recipe 1 l)
        (rawProfile1 (.a (next 18) l))≤rawProfile1 (.p 18 l)) := by
  decide +kernel

theorem d_chunk_1_18 : ∀ j l : Fin 40, (18 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 18) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 18 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 18 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_19 : ∀ j : Fin 40, (19 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 19) (recipe 1 j)≤rawProfile1 (.a 19 j) := by
  decide +kernel

theorem other_chunk_1_19 :
    (∀ j : Fin 40, (19 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 19) (recipe 1 j)).eval profile1≤rawProfile1 (.b 19 j)) ∧
    (∀ j : Fin 40, (19 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 19) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 19 j)) ∧
    (∀ l : Fin 40, (19 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 19) (recipe 1 (next 19)) (recipe 1 l)
        (rawProfile1 (.a (next 19) l))≤rawProfile1 (.p 19 l)) := by
  decide +kernel

theorem d_chunk_1_19 : ∀ j l : Fin 40, (19 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 19) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 19 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 19 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_19


