-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther2
-- name    : BS2_b3ba934b_Endpoint16RawOther2
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:33:07.347974+00:00
-- url     : https://prove2.me/theorems/fb4025b6-51e3-4e8f-9af9-0e66c029fa96
-- title:
--   Sensitivity separation: Endpoint16RawOther2 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther2` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther2.lean; original SHA-256 a7410d5856ea725b45f942ccd5e7ef82da342bcbde32982e075648c16417cc55; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther2Chunk00
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther2Chunk01
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther2Chunk02
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther2Chunk03

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_checked2 : ∀ i j : Fin 16, i≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j) := by
  intro i
  fin_cases i
  · exact ordinaryA_chunk_2_0
  · exact ordinaryA_chunk_2_1
  · exact ordinaryA_chunk_2_2
  · exact ordinaryA_chunk_2_3
  · exact ordinaryA_chunk_2_4
  · exact ordinaryA_chunk_2_5
  · exact ordinaryA_chunk_2_6
  · exact ordinaryA_chunk_2_7
  · exact ordinaryA_chunk_2_8
  · exact ordinaryA_chunk_2_9
  · exact ordinaryA_chunk_2_10
  · exact ordinaryA_chunk_2_11
  · exact ordinaryA_chunk_2_12
  · exact ordinaryA_chunk_2_13
  · exact ordinaryA_chunk_2_14
  · exact ordinaryA_chunk_2_15

theorem b_checked2 : ∀ i j : Fin 16, i≤j →
    (rawBExpr 16 5003 (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.b i j) := by
  intro i
  fin_cases i
  · exact other_chunk_2_0.1
  · exact other_chunk_2_1.1
  · exact other_chunk_2_2.1
  · exact other_chunk_2_3.1
  · exact other_chunk_2_4.1
  · exact other_chunk_2_5.1
  · exact other_chunk_2_6.1
  · exact other_chunk_2_7.1
  · exact other_chunk_2_8.1
  · exact other_chunk_2_9.1
  · exact other_chunk_2_10.1
  · exact other_chunk_2_11.1
  · exact other_chunk_2_12.1
  · exact other_chunk_2_13.1
  · exact other_chunk_2_14.1
  · exact other_chunk_2_15.1

theorem m_checked2 : ∀ i j : Fin 16, i≤j → j.val+1<16 →
    (rawMExpr 16 5003 (recipe 2 i) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m i j) := by
  intro i
  fin_cases i
  · exact other_chunk_2_0.2.1
  · exact other_chunk_2_1.2.1
  · exact other_chunk_2_2.2.1
  · exact other_chunk_2_3.2.1
  · exact other_chunk_2_4.2.1
  · exact other_chunk_2_5.2.1
  · exact other_chunk_2_6.2.1
  · exact other_chunk_2_7.2.1
  · exact other_chunk_2_8.2.1
  · exact other_chunk_2_9.2.1
  · exact other_chunk_2_10.2.1
  · exact other_chunk_2_11.2.1
  · exact other_chunk_2_12.2.1
  · exact other_chunk_2_13.2.1
  · exact other_chunk_2_14.2.1
  · exact other_chunk_2_15.2.1

theorem p_core_checked2 : ∀ j l : Fin 16, j<l →
    pCore 16 caps.pcross profile2 (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.a (next j) l))≤rawProfile2 (.p j l) := by
  intro i
  fin_cases i
  · exact other_chunk_2_0.2.2
  · exact other_chunk_2_1.2.2
  · exact other_chunk_2_2.2.2
  · exact other_chunk_2_3.2.2
  · exact other_chunk_2_4.2.2
  · exact other_chunk_2_5.2.2
  · exact other_chunk_2_6.2.2
  · exact other_chunk_2_7.2.2
  · exact other_chunk_2_8.2.2
  · exact other_chunk_2_9.2.2
  · exact other_chunk_2_10.2.2
  · exact other_chunk_2_11.2.2
  · exact other_chunk_2_12.2.2
  · exact other_chunk_2_13.2.2
  · exact other_chunk_2_14.2.2
  · exact other_chunk_2_15.2.2

theorem d_core_checked2 : ∀ i j l : Fin 16, i≤j → j<l →
    dCore 16 5003 profile2 (recipe 2 i) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.m i j)+rawProfile2 (.p j l))≤rawProfile2 (.d i j l) := by
  intro i
  fin_cases i
  · exact d_chunk_2_0
  · exact d_chunk_2_1
  · exact d_chunk_2_2
  · exact d_chunk_2_3
  · exact d_chunk_2_4
  · exact d_chunk_2_5
  · exact d_chunk_2_6
  · exact d_chunk_2_7
  · exact d_chunk_2_8
  · exact d_chunk_2_9
  · exact d_chunk_2_10
  · exact d_chunk_2_11
  · exact d_chunk_2_12
  · exact d_chunk_2_13
  · exact d_chunk_2_14
  · exact d_chunk_2_15

theorem raw_numerical_of_A2
    (ha : ∀ i j : Fin 16, i≤j →
      (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j)) :
    ∀ coord : Coord 16, valid coord → raw 2 profile2 coord≤rawProfile2 coord := by
  have hp : ∀ j l : Fin 16, j<l →
      (rawPExpr 16 caps.pcross (ThreeBoundMinmaxA.rawAExpr 16 caps records)
        (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)).eval profile2≤rawProfile2 (.p j l) := by
    intro j l hjl
    exact rawP_bound_from_A 16 caps.pcross profile2 (ThreeBoundMinmaxA.rawAExpr 16 caps records)
      (recipe 2 j) (recipe 2 (next j)) (recipe 2 l) _ _
      (ha (next j) l (next_le_of_lt j l hjl)) (p_core_checked2 j l hjl)
  intro coord hc
  cases coord with
  | a i j => exact ha i j hc
  | b i j => exact b_checked2 i j hc
  | m i j => exact m_checked2 i j hc.1 hc.2
  | p j l => exact hp j l hc
  | d i j l =>
      exact rawD_bound_from_MP 16 5003 caps.pcross profile2 (ThreeBoundMinmaxA.rawAExpr 16 caps records)
        (recipe 2 i) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l) _ _ _
        (m_checked2 i j hc.1 (next_lt_n_of_lt j l hc.2)) (hp j l hc.2)
        (d_core_checked2 i j l hc.1 hc.2)

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.raw_numerical_of_A2


