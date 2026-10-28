-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3
-- name    : BS2_b3ba934b_Endpoint40RawOther3
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T07:26:46.133992+00:00
-- url     : https://prove2.me/theorems/dfa43574-eb28-4ae7-84d4-50f3b070fd92
-- title:
--   Sensitivity separation: Endpoint40RawOther3 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther3` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther3.lean; original SHA-256 688770f8c78517daf4ca8613d7835919a93003fe068a5e5ce8edd6224aa521eb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk00
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk01
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk02
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk03
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk04
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk05
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk06
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk07
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk08
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk09
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk10
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk11
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk12
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk13
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk14
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk15
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk16
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk17
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk18
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther3Chunk19

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_checked3 : ∀ i j : Fin 40, i≤j →
    ((recipe 3 j).tolerance=0 ∨ 3≤(recipe 3 j).tolerance) →
    (rawAExpr 40 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j) := by
  intro i j hij hq
  rw [← rawAFast_eq]
  fin_cases i
  · exact ordinaryA_chunk_3_0 j hij hq
  · exact ordinaryA_chunk_3_1 j hij hq
  · exact ordinaryA_chunk_3_2 j hij hq
  · exact ordinaryA_chunk_3_3 j hij hq
  · exact ordinaryA_chunk_3_4 j hij hq
  · exact ordinaryA_chunk_3_5 j hij hq
  · exact ordinaryA_chunk_3_6 j hij hq
  · exact ordinaryA_chunk_3_7 j hij hq
  · exact ordinaryA_chunk_3_8 j hij hq
  · exact ordinaryA_chunk_3_9 j hij hq
  · exact ordinaryA_chunk_3_10 j hij hq
  · exact ordinaryA_chunk_3_11 j hij hq
  · exact ordinaryA_chunk_3_12 j hij hq
  · exact ordinaryA_chunk_3_13 j hij hq
  · exact ordinaryA_chunk_3_14 j hij hq
  · exact ordinaryA_chunk_3_15 j hij hq
  · exact ordinaryA_chunk_3_16 j hij hq
  · exact ordinaryA_chunk_3_17 j hij hq
  · exact ordinaryA_chunk_3_18 j hij hq
  · exact ordinaryA_chunk_3_19 j hij hq
  · exact ordinaryA_chunk_3_20 j hij hq
  · exact ordinaryA_chunk_3_21 j hij hq
  · exact ordinaryA_chunk_3_22 j hij hq
  · exact ordinaryA_chunk_3_23 j hij hq
  · exact ordinaryA_chunk_3_24 j hij hq
  · exact ordinaryA_chunk_3_25 j hij hq
  · exact ordinaryA_chunk_3_26 j hij hq
  · exact ordinaryA_chunk_3_27 j hij hq
  · exact ordinaryA_chunk_3_28 j hij hq
  · exact ordinaryA_chunk_3_29 j hij hq
  · exact ordinaryA_chunk_3_30 j hij hq
  · exact ordinaryA_chunk_3_31 j hij hq
  · exact ordinaryA_chunk_3_32 j hij hq
  · exact ordinaryA_chunk_3_33 j hij hq
  · exact ordinaryA_chunk_3_34 j hij hq
  · exact ordinaryA_chunk_3_35 j hij hq
  · exact ordinaryA_chunk_3_36 j hij hq
  · exact ordinaryA_chunk_3_37 j hij hq
  · exact ordinaryA_chunk_3_38 j hij hq
  · exact ordinaryA_chunk_3_39 j hij hq

theorem b_checked3 : ∀ i j : Fin 40, i≤j →
    (rawBExpr 40 5003 (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.b i j) := by
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
  · exact other_chunk_3_16.1
  · exact other_chunk_3_17.1
  · exact other_chunk_3_18.1
  · exact other_chunk_3_19.1
  · exact other_chunk_3_20.1
  · exact other_chunk_3_21.1
  · exact other_chunk_3_22.1
  · exact other_chunk_3_23.1
  · exact other_chunk_3_24.1
  · exact other_chunk_3_25.1
  · exact other_chunk_3_26.1
  · exact other_chunk_3_27.1
  · exact other_chunk_3_28.1
  · exact other_chunk_3_29.1
  · exact other_chunk_3_30.1
  · exact other_chunk_3_31.1
  · exact other_chunk_3_32.1
  · exact other_chunk_3_33.1
  · exact other_chunk_3_34.1
  · exact other_chunk_3_35.1
  · exact other_chunk_3_36.1
  · exact other_chunk_3_37.1
  · exact other_chunk_3_38.1
  · exact other_chunk_3_39.1
theorem m_checked3 : ∀ i j : Fin 40, i≤j → j.val+1<40 →
    (rawMExpr 40 5003 (recipe 3 i) (recipe 3 j) (recipe 3 (next j))).eval profile3≤rawProfile3 (.m i j) := by
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
  · exact other_chunk_3_16.2.1
  · exact other_chunk_3_17.2.1
  · exact other_chunk_3_18.2.1
  · exact other_chunk_3_19.2.1
  · exact other_chunk_3_20.2.1
  · exact other_chunk_3_21.2.1
  · exact other_chunk_3_22.2.1
  · exact other_chunk_3_23.2.1
  · exact other_chunk_3_24.2.1
  · exact other_chunk_3_25.2.1
  · exact other_chunk_3_26.2.1
  · exact other_chunk_3_27.2.1
  · exact other_chunk_3_28.2.1
  · exact other_chunk_3_29.2.1
  · exact other_chunk_3_30.2.1
  · exact other_chunk_3_31.2.1
  · exact other_chunk_3_32.2.1
  · exact other_chunk_3_33.2.1
  · exact other_chunk_3_34.2.1
  · exact other_chunk_3_35.2.1
  · exact other_chunk_3_36.2.1
  · exact other_chunk_3_37.2.1
  · exact other_chunk_3_38.2.1
  · exact other_chunk_3_39.2.1
theorem p_core_checked3 : ∀ j l : Fin 40, j<l →
    pCore 40 profile3 caps (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
      (rawProfile3 (.a (next j) l))≤rawProfile3 (.p j l) := by
  intro j
  fin_cases j
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
  · exact other_chunk_3_16.2.2
  · exact other_chunk_3_17.2.2
  · exact other_chunk_3_18.2.2
  · exact other_chunk_3_19.2.2
  · exact other_chunk_3_20.2.2
  · exact other_chunk_3_21.2.2
  · exact other_chunk_3_22.2.2
  · exact other_chunk_3_23.2.2
  · exact other_chunk_3_24.2.2
  · exact other_chunk_3_25.2.2
  · exact other_chunk_3_26.2.2
  · exact other_chunk_3_27.2.2
  · exact other_chunk_3_28.2.2
  · exact other_chunk_3_29.2.2
  · exact other_chunk_3_30.2.2
  · exact other_chunk_3_31.2.2
  · exact other_chunk_3_32.2.2
  · exact other_chunk_3_33.2.2
  · exact other_chunk_3_34.2.2
  · exact other_chunk_3_35.2.2
  · exact other_chunk_3_36.2.2
  · exact other_chunk_3_37.2.2
  · exact other_chunk_3_38.2.2
  · exact other_chunk_3_39.2.2
theorem d_core_checked3 : ∀ i j l : Fin 40, i≤j → j<l →
    dCore 40 5003 profile3 (recipe 3 i) (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)
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
  · exact d_chunk_3_16
  · exact d_chunk_3_17
  · exact d_chunk_3_18
  · exact d_chunk_3_19
  · exact d_chunk_3_20
  · exact d_chunk_3_21
  · exact d_chunk_3_22
  · exact d_chunk_3_23
  · exact d_chunk_3_24
  · exact d_chunk_3_25
  · exact d_chunk_3_26
  · exact d_chunk_3_27
  · exact d_chunk_3_28
  · exact d_chunk_3_29
  · exact d_chunk_3_30
  · exact d_chunk_3_31
  · exact d_chunk_3_32
  · exact d_chunk_3_33
  · exact d_chunk_3_34
  · exact d_chunk_3_35
  · exact d_chunk_3_36
  · exact d_chunk_3_37
  · exact d_chunk_3_38
  · exact d_chunk_3_39

theorem raw_numerical_of_A3
    (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 3 i) (recipe 3 j)).eval profile3≤rawProfile3 (.a i j)) :
    ∀ coord : Coord 40, valid coord → raw 3 profile3 coord≤rawProfile3 coord := by
  have hp : ∀ j l : Fin 40, j<l →
      (rawPExpr 40 5003 caps records (recipe 3 j) (recipe 3 (next j)) (recipe 3 l)).eval profile3≤
        rawProfile3 (.p j l) := by
    intro j l hjl
    exact rawP_bound_from_A 40 5003 profile3 caps records (recipe 3 j) (recipe 3 (next j))
      (recipe 3 l) _ _ (ha (next j) l (next_le_of_lt j l hjl)) (p_core_checked3 j l hjl)
  intro coord hc
  cases coord with
  | a i j => exact ha i j hc
  | b i j => exact b_checked3 i j hc
  | m i j => exact m_checked3 i j hc.1 hc.2
  | p j l => exact hp j l hc
  | d i j l =>
      exact rawD_bound_from_MP 40 5003 profile3 caps records (recipe 3 i) (recipe 3 j)
        (recipe 3 (next j)) (recipe 3 l) _ _ _
        (m_checked3 i j hc.1 (next_lt_n_of_lt j l hc.2)) (hp j l hc.2)
        (d_core_checked3 i j l hc.1 hc.2)

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.raw_numerical_of_A3


