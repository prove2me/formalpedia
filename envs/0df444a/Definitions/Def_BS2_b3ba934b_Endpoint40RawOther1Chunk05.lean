-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk05
-- name    : BS2_b3ba934b_Endpoint40RawOther1Chunk05
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:46:01.27299+00:00
-- url     : https://prove2.me/theorems/8dd93d62-295e-4636-8466-4f0a1333a7ba
-- title:
--   Sensitivity separation: Endpoint40RawOther1Chunk05 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1Chunk05` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1Chunk05.lean; original SHA-256 7d506e711c49615354ec2ad2c00b1eadefa661cd2fd1f0d59725db515edc9a99; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_RawCoreBounds
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_chunk_1_10 : ∀ j : Fin 40, (10 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 10) (recipe 1 j)≤rawProfile1 (.a 10 j) := by
  decide +kernel

theorem other_chunk_1_10 :
    (∀ j : Fin 40, (10 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 10) (recipe 1 j)).eval profile1≤rawProfile1 (.b 10 j)) ∧
    (∀ j : Fin 40, (10 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 10) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 10 j)) ∧
    (∀ l : Fin 40, (10 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 10) (recipe 1 (next 10)) (recipe 1 l)
        (rawProfile1 (.a (next 10) l))≤rawProfile1 (.p 10 l)) := by
  decide +kernel

theorem d_chunk_1_10 : ∀ j l : Fin 40, (10 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 10) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 10 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 10 j l) := by
  decide +kernel

theorem ordinaryA_chunk_1_11 : ∀ j : Fin 40, (11 : Fin 40)≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    rawAFast 40 profile1 caps records (recipe 1 11) (recipe 1 j)≤rawProfile1 (.a 11 j) := by
  decide +kernel

theorem other_chunk_1_11 :
    (∀ j : Fin 40, (11 : Fin 40)≤j →
      (rawBExpr 40 5003 (recipe 1 11) (recipe 1 j)).eval profile1≤rawProfile1 (.b 11 j)) ∧
    (∀ j : Fin 40, (11 : Fin 40)≤j → j.val+1<40 →
      (rawMExpr 40 5003 (recipe 1 11) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m 11 j)) ∧
    (∀ l : Fin 40, (11 : Fin 40)<l →
      pCore 40 profile1 caps (recipe 1 11) (recipe 1 (next 11)) (recipe 1 l)
        (rawProfile1 (.a (next 11) l))≤rawProfile1 (.p 11 l)) := by
  decide +kernel

theorem d_chunk_1_11 : ∀ j l : Fin 40, (11 : Fin 40)≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 11) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m 11 j)+rawProfile1 (.p j l))≤rawProfile1 (.d 11 j l) := by
  decide +kernel

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.d_chunk_1_11


