-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16RawOther0
-- name    : BS2_b3ba934b_Endpoint16RawOther0
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:32:24.997565+00:00
-- url     : https://prove2.me/theorems/db9a0fde-290f-467a-8ea9-93bd0fbce539
-- title:
--   Sensitivity separation: Endpoint16RawOther0 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16RawOther0` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawOther0.lean; original SHA-256 e43c2c2d430e35a551e1096410b440e5cea661e02b2ff0db634f9823f369d6ad; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther0Chunk00
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther0Chunk01
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther0Chunk02
import Definitions.Def_BS2_b3ba934b_Endpoint16RawOther0Chunk03

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundMinmaxNumeric.Endpoint16
open ThreeBoundNumeric ThreeBoundFullProfile

theorem ordinaryA_checked0 : ∀ i j : Fin 16, i≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j) := by
  intro i
  fin_cases i
  · exact ordinaryA_chunk_0_0
  · exact ordinaryA_chunk_0_1
  · exact ordinaryA_chunk_0_2
  · exact ordinaryA_chunk_0_3
  · exact ordinaryA_chunk_0_4
  · exact ordinaryA_chunk_0_5
  · exact ordinaryA_chunk_0_6
  · exact ordinaryA_chunk_0_7
  · exact ordinaryA_chunk_0_8
  · exact ordinaryA_chunk_0_9
  · exact ordinaryA_chunk_0_10
  · exact ordinaryA_chunk_0_11
  · exact ordinaryA_chunk_0_12
  · exact ordinaryA_chunk_0_13
  · exact ordinaryA_chunk_0_14
  · exact ordinaryA_chunk_0_15

theorem b_checked0 : ∀ i j : Fin 16, i≤j →
    (rawBExpr 16 5003 (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.b i j) := by
  intro i
  fin_cases i
  · exact other_chunk_0_0.1
  · exact other_chunk_0_1.1
  · exact other_chunk_0_2.1
  · exact other_chunk_0_3.1
  · exact other_chunk_0_4.1
  · exact other_chunk_0_5.1
  · exact other_chunk_0_6.1
  · exact other_chunk_0_7.1
  · exact other_chunk_0_8.1
  · exact other_chunk_0_9.1
  · exact other_chunk_0_10.1
  · exact other_chunk_0_11.1
  · exact other_chunk_0_12.1
  · exact other_chunk_0_13.1
  · exact other_chunk_0_14.1
  · exact other_chunk_0_15.1

theorem m_checked0 : ∀ i j : Fin 16, i≤j → j.val+1<16 →
    (rawMExpr 16 5003 (recipe 0 i) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m i j) := by
  intro i
  fin_cases i
  · exact other_chunk_0_0.2.1
  · exact other_chunk_0_1.2.1
  · exact other_chunk_0_2.2.1
  · exact other_chunk_0_3.2.1
  · exact other_chunk_0_4.2.1
  · exact other_chunk_0_5.2.1
  · exact other_chunk_0_6.2.1
  · exact other_chunk_0_7.2.1
  · exact other_chunk_0_8.2.1
  · exact other_chunk_0_9.2.1
  · exact other_chunk_0_10.2.1
  · exact other_chunk_0_11.2.1
  · exact other_chunk_0_12.2.1
  · exact other_chunk_0_13.2.1
  · exact other_chunk_0_14.2.1
  · exact other_chunk_0_15.2.1

theorem p_core_checked0 : ∀ j l : Fin 16, j<l →
    pCore 16 caps.pcross profile0 (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.a (next j) l))≤rawProfile0 (.p j l) := by
  intro i
  fin_cases i
  · exact other_chunk_0_0.2.2
  · exact other_chunk_0_1.2.2
  · exact other_chunk_0_2.2.2
  · exact other_chunk_0_3.2.2
  · exact other_chunk_0_4.2.2
  · exact other_chunk_0_5.2.2
  · exact other_chunk_0_6.2.2
  · exact other_chunk_0_7.2.2
  · exact other_chunk_0_8.2.2
  · exact other_chunk_0_9.2.2
  · exact other_chunk_0_10.2.2
  · exact other_chunk_0_11.2.2
  · exact other_chunk_0_12.2.2
  · exact other_chunk_0_13.2.2
  · exact other_chunk_0_14.2.2
  · exact other_chunk_0_15.2.2

theorem d_core_checked0 : ∀ i j l : Fin 16, i≤j → j<l →
    dCore 16 5003 profile0 (recipe 0 i) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.m i j)+rawProfile0 (.p j l))≤rawProfile0 (.d i j l) := by
  intro i
  fin_cases i
  · exact d_chunk_0_0
  · exact d_chunk_0_1
  · exact d_chunk_0_2
  · exact d_chunk_0_3
  · exact d_chunk_0_4
  · exact d_chunk_0_5
  · exact d_chunk_0_6
  · exact d_chunk_0_7
  · exact d_chunk_0_8
  · exact d_chunk_0_9
  · exact d_chunk_0_10
  · exact d_chunk_0_11
  · exact d_chunk_0_12
  · exact d_chunk_0_13
  · exact d_chunk_0_14
  · exact d_chunk_0_15

theorem raw_numerical_of_A0
    (ha : ∀ i j : Fin 16, i≤j →
      (ThreeBoundMinmaxA.rawAExpr 16 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j)) :
    ∀ coord : Coord 16, valid coord → raw 0 profile0 coord≤rawProfile0 coord := by
  have hp : ∀ j l : Fin 16, j<l →
      (rawPExpr 16 caps.pcross (ThreeBoundMinmaxA.rawAExpr 16 caps records)
        (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)).eval profile0≤rawProfile0 (.p j l) := by
    intro j l hjl
    exact rawP_bound_from_A 16 caps.pcross profile0 (ThreeBoundMinmaxA.rawAExpr 16 caps records)
      (recipe 0 j) (recipe 0 (next j)) (recipe 0 l) _ _
      (ha (next j) l (next_le_of_lt j l hjl)) (p_core_checked0 j l hjl)
  intro coord hc
  cases coord with
  | a i j => exact ha i j hc
  | b i j => exact b_checked0 i j hc
  | m i j => exact m_checked0 i j hc.1 hc.2
  | p j l => exact hp j l hc
  | d i j l =>
      exact rawD_bound_from_MP 16 5003 caps.pcross profile0 (ThreeBoundMinmaxA.rawAExpr 16 caps records)
        (recipe 0 i) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l) _ _ _
        (m_checked0 i j hc.1 (next_lt_n_of_lt j l hc.2)) (hp j l hc.2)
        (d_core_checked0 i j l hc.1 hc.2)

end ThreeBoundMinmaxNumeric.Endpoint16

#print axioms ThreeBoundMinmaxNumeric.Endpoint16.raw_numerical_of_A0


