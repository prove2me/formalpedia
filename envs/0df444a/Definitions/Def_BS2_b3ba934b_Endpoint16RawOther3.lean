-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther3
-- name    : BS2_b3ba934b_Endpoint16RawOther3
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:33:34.103535+00:00
-- url     : https://prove2.me/theorems/5f715883-1bf4-4f81-bcb0-4a9b7f7bf634
-- title:
--   Sensitivity separation: Endpoint16RawOther3 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther3` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther3.lean; original SHA-256 750533425cf29d19b5907b9cfe1f4a069e79ccecaec5771fcceb68f05d5f7786; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther3Chunk00
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther3Chunk01
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther3Chunk02
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther3Chunk03

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_checked3 : ∀ i j : Fin 16, i≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j) := by
  intro i
  fin_cases i
  · exact ordinaryA_chunk_3_0
  · exact ordinaryA_chunk_3_1
  · exact ordinaryA_chunk_3_2
  · exact ordinaryA_chunk_3_3
  · exact ordinaryA_chunk_3_4
  · exact ordinaryA_chunk_3_5
  · exact ordinaryA_chunk_3_6
  · exact ordinaryA_chunk_3_7
  · exact ordinaryA_chunk_3_8
  · exact ordinaryA_chunk_3_9
  · exact ordinaryA_chunk_3_10
  · exact ordinaryA_chunk_3_11
  · exact ordinaryA_chunk_3_12
  · exact ordinaryA_chunk_3_13
  · exact ordinaryA_chunk_3_14
  · exact ordinaryA_chunk_3_15

theorem b_checked3 : ∀ i j : Fin 16, i≤j →
    (rawBExpr 16 5003 (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.b i j) := by
  intro i
  fin_cases i
  · exact other_chunk_3_0.1
  · exact other_chunk_3_1.1
  · exact other_chunk_3_2.1
  · exact other_chunk_3_3.1
  · exact other_chunk_3_4.1
  · exact other_chunk_3_5.1
  · exact other_chunk_3_6.1
  · exact other_chunk_3_7.1
  · exact other_chunk_3_8.1
  · exact other_chunk_3_9.1
  · exact other_chunk_3_10.1
  · exact other_chunk_3_11.1
  · exact other_chunk_3_12.1
  · exact other_chunk_3_13.1
  · exact other_chunk_3_14.1
  · exact other_chunk_3_15.1

theorem m_checked3 : ∀ i j : Fin 16, i≤j → j.val+1<16 →
    (rawMExpr 16 5003 (recipe 3 i) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m i j) := by
  intro i
  fin_cases i
  · exact other_chunk_3_0.2.1
  · exact other_chunk_3_1.2.1
  · exact other_chunk_3_2.2.1
  · exact other_chunk_3_3.2.1
  · exact other_chunk_3_4.2.1
  · exact other_chunk_3_5.2.1
  · exact other_chunk_3_6.2.1
  · exact other_chunk_3_7.2.1
  · exact other_chunk_3_8.2.1
  · exact other_chunk_3_9.2.1
  · exact other_chunk_3_10.2.1
  · exact other_chunk_3_11.2.1
  · exact other_chunk_3_12.2.1
  · exact other_chunk_3_13.2.1
  · exact other_chunk_3_14.2.1
  · exact other_chunk_3_15.2.1

theorem p_core_checked3 : ∀ j l : Fin 16, j<l →
    pCore 16 caps.pcross profile3 (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.a (next j) l))≤rawProfile3 (.p j l) := by
  intro i
  fin_cases i
  · exact other_chunk_3_0.2.2
  · exact other_chunk_3_1.2.2
  · exact other_chunk_3_2.2.2
  · exact other_chunk_3_3.2.2
  · exact other_chunk_3_4.2.2
  · exact other_chunk_3_5.2.2
  · exact other_chunk_3_6.2.2
  · exact other_chunk_3_7.2.2
  · exact other_chunk_3_8.2.2
  · exact other_chunk_3_9.2.2
  · exact other_chunk_3_10.2.2
  · exact other_chunk_3_11.2.2
  · exact other_chunk_3_12.2.2
  · exact other_chunk_3_13.2.2
  · exact other_chunk_3_14.2.2
  · exact other_chunk_3_15.2.2

theorem d_core_checked3 : ∀ i j l : Fin 16, i≤j → j<l →
    dCore 16 5003 profile3 (recipe 3 i) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.m i j)+rawProfile3 (.p j l))≤rawProfile3 (.d i j l) := by
  intro i
  fin_cases i
  · exact d_chunk_3_0
  · exact d_chunk_3_1
  · exact d_chunk_3_2
  · exact d_chunk_3_3
  · exact d_chunk_3_4
  · exact d_chunk_3_5
  · exact d_chunk_3_6
  · exact d_chunk_3_7
  · exact d_chunk_3_8
  · exact d_chunk_3_9
  · exact d_chunk_3_10
  · exact d_chunk_3_11
  · exact d_chunk_3_12
  · exact d_chunk_3_13
  · exact d_chunk_3_14
  · exact d_chunk_3_15

theorem raw_numerical_of_A3
    (ha : ∀ i j : Fin 16, i≤j →
      (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j)) :
    ∀ coord : Coord 16, valid coord → raw 3 profile3 coord≤rawProfile3 coord := by
  have hp : ∀ j l : Fin 16, j<l →
      (rawPExpr 16 caps.pcross (ThreeBoundMinmaxA.rawAExpr 16 caps records)
        (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)).eval profile3≤rawProfile3 (.p j l) := by
    intro j l hjl
    exact rawP_bound_from_A 16 caps.pcross profile3 (ThreeBoundMinmaxA.rawAExpr 16 caps records)
      (recipe 3 j) (recipe 3 (next j)) (recipe 3 l) _ _
      (ha (next j) l (next_le_of_lt j l hjl)) (p_core_checked3 j l hjl)
  intro coord hc
  cases coord with
  | a i j => exact ha i j hc
  | b i j => exact b_checked3 i j hc
  | m i j => exact m_checked3 i j hc.1 hc.2
  | p j l => exact hp j l hc
  | d i j l =>
      exact rawD_bound_from_MP 16 5003 caps.pcross profile3 (ThreeBoundMinmaxA.rawAExpr 16 caps records)
        (recipe 3 i) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l) _ _ _
        (m_checked3 i j hc.1 (next_lt_n_of_lt j l hc.2)) (hp j l hc.2)
        (d_core_checked3 i j l hc.1 hc.2)

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.raw_numerical_of_A3


