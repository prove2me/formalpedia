-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2
-- name    : BS2_b3ba934b_Endpoint40RawOther2
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T06:26:00.202167+00:00
-- url     : https://prove2.me/theorems/9e750227-ba4f-47b4-bb94-897acefe6a76
-- title:
--   Sensitivity separation: Endpoint40RawOther2 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther2` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther2.lean; original SHA-256 6522282cdeb9874123a393494ec676ca3c96e1cf3653d9d2b1a0c2a5503dc3cf; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk00
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk01
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk02
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk03
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk04
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk05
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk06
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk07
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk08
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk09
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk10
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk11
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk12
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk13
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk14
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk15
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk16
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk17
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk18
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther2Chunk19

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_checked2 : ∀ i j : Fin 40, i≤j →
    ((recipe 2 j).tolerance=0 ∨ 3≤(recipe 2 j).tolerance) →
    (rawAExpr 40 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j) := by
  intro i j hij hq
  rw [← rawAFast_eq]
  fin_cases i
  · exact ordinaryA_chunk_2_0 j hij hq
  · exact ordinaryA_chunk_2_1 j hij hq
  · exact ordinaryA_chunk_2_2 j hij hq
  · exact ordinaryA_chunk_2_3 j hij hq
  · exact ordinaryA_chunk_2_4 j hij hq
  · exact ordinaryA_chunk_2_5 j hij hq
  · exact ordinaryA_chunk_2_6 j hij hq
  · exact ordinaryA_chunk_2_7 j hij hq
  · exact ordinaryA_chunk_2_8 j hij hq
  · exact ordinaryA_chunk_2_9 j hij hq
  · exact ordinaryA_chunk_2_10 j hij hq
  · exact ordinaryA_chunk_2_11 j hij hq
  · exact ordinaryA_chunk_2_12 j hij hq
  · exact ordinaryA_chunk_2_13 j hij hq
  · exact ordinaryA_chunk_2_14 j hij hq
  · exact ordinaryA_chunk_2_15 j hij hq
  · exact ordinaryA_chunk_2_16 j hij hq
  · exact ordinaryA_chunk_2_17 j hij hq
  · exact ordinaryA_chunk_2_18 j hij hq
  · exact ordinaryA_chunk_2_19 j hij hq
  · exact ordinaryA_chunk_2_20 j hij hq
  · exact ordinaryA_chunk_2_21 j hij hq
  · exact ordinaryA_chunk_2_22 j hij hq
  · exact ordinaryA_chunk_2_23 j hij hq
  · exact ordinaryA_chunk_2_24 j hij hq
  · exact ordinaryA_chunk_2_25 j hij hq
  · exact ordinaryA_chunk_2_26 j hij hq
  · exact ordinaryA_chunk_2_27 j hij hq
  · exact ordinaryA_chunk_2_28 j hij hq
  · exact ordinaryA_chunk_2_29 j hij hq
  · exact ordinaryA_chunk_2_30 j hij hq
  · exact ordinaryA_chunk_2_31 j hij hq
  · exact ordinaryA_chunk_2_32 j hij hq
  · exact ordinaryA_chunk_2_33 j hij hq
  · exact ordinaryA_chunk_2_34 j hij hq
  · exact ordinaryA_chunk_2_35 j hij hq
  · exact ordinaryA_chunk_2_36 j hij hq
  · exact ordinaryA_chunk_2_37 j hij hq
  · exact ordinaryA_chunk_2_38 j hij hq
  · exact ordinaryA_chunk_2_39 j hij hq

theorem b_checked2 : ∀ i j : Fin 40, i≤j →
    (rawBExpr 40 5003 (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.b i j) := by
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
  · exact other_chunk_2_16.1
  · exact other_chunk_2_17.1
  · exact other_chunk_2_18.1
  · exact other_chunk_2_19.1
  · exact other_chunk_2_20.1
  · exact other_chunk_2_21.1
  · exact other_chunk_2_22.1
  · exact other_chunk_2_23.1
  · exact other_chunk_2_24.1
  · exact other_chunk_2_25.1
  · exact other_chunk_2_26.1
  · exact other_chunk_2_27.1
  · exact other_chunk_2_28.1
  · exact other_chunk_2_29.1
  · exact other_chunk_2_30.1
  · exact other_chunk_2_31.1
  · exact other_chunk_2_32.1
  · exact other_chunk_2_33.1
  · exact other_chunk_2_34.1
  · exact other_chunk_2_35.1
  · exact other_chunk_2_36.1
  · exact other_chunk_2_37.1
  · exact other_chunk_2_38.1
  · exact other_chunk_2_39.1
theorem m_checked2 : ∀ i j : Fin 40, i≤j → j.val+1<40 →
    (rawMExpr 40 5003 (recipe 2 i) (recipe 2 j) (recipe 2 (next j))).eval profile2≤rawProfile2 (.m i j) := by
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
  · exact other_chunk_2_16.2.1
  · exact other_chunk_2_17.2.1
  · exact other_chunk_2_18.2.1
  · exact other_chunk_2_19.2.1
  · exact other_chunk_2_20.2.1
  · exact other_chunk_2_21.2.1
  · exact other_chunk_2_22.2.1
  · exact other_chunk_2_23.2.1
  · exact other_chunk_2_24.2.1
  · exact other_chunk_2_25.2.1
  · exact other_chunk_2_26.2.1
  · exact other_chunk_2_27.2.1
  · exact other_chunk_2_28.2.1
  · exact other_chunk_2_29.2.1
  · exact other_chunk_2_30.2.1
  · exact other_chunk_2_31.2.1
  · exact other_chunk_2_32.2.1
  · exact other_chunk_2_33.2.1
  · exact other_chunk_2_34.2.1
  · exact other_chunk_2_35.2.1
  · exact other_chunk_2_36.2.1
  · exact other_chunk_2_37.2.1
  · exact other_chunk_2_38.2.1
  · exact other_chunk_2_39.2.1
theorem p_core_checked2 : ∀ j l : Fin 40, j<l →
    pCore 40 profile2 caps (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
      (rawProfile2 (.a (next j) l))≤rawProfile2 (.p j l) := by
  intro j
  fin_cases j
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
  · exact other_chunk_2_16.2.2
  · exact other_chunk_2_17.2.2
  · exact other_chunk_2_18.2.2
  · exact other_chunk_2_19.2.2
  · exact other_chunk_2_20.2.2
  · exact other_chunk_2_21.2.2
  · exact other_chunk_2_22.2.2
  · exact other_chunk_2_23.2.2
  · exact other_chunk_2_24.2.2
  · exact other_chunk_2_25.2.2
  · exact other_chunk_2_26.2.2
  · exact other_chunk_2_27.2.2
  · exact other_chunk_2_28.2.2
  · exact other_chunk_2_29.2.2
  · exact other_chunk_2_30.2.2
  · exact other_chunk_2_31.2.2
  · exact other_chunk_2_32.2.2
  · exact other_chunk_2_33.2.2
  · exact other_chunk_2_34.2.2
  · exact other_chunk_2_35.2.2
  · exact other_chunk_2_36.2.2
  · exact other_chunk_2_37.2.2
  · exact other_chunk_2_38.2.2
  · exact other_chunk_2_39.2.2
theorem d_core_checked2 : ∀ i j l : Fin 40, i≤j → j<l →
    dCore 40 5003 profile2 (recipe 2 i) (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)
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
  · exact d_chunk_2_16
  · exact d_chunk_2_17
  · exact d_chunk_2_18
  · exact d_chunk_2_19
  · exact d_chunk_2_20
  · exact d_chunk_2_21
  · exact d_chunk_2_22
  · exact d_chunk_2_23
  · exact d_chunk_2_24
  · exact d_chunk_2_25
  · exact d_chunk_2_26
  · exact d_chunk_2_27
  · exact d_chunk_2_28
  · exact d_chunk_2_29
  · exact d_chunk_2_30
  · exact d_chunk_2_31
  · exact d_chunk_2_32
  · exact d_chunk_2_33
  · exact d_chunk_2_34
  · exact d_chunk_2_35
  · exact d_chunk_2_36
  · exact d_chunk_2_37
  · exact d_chunk_2_38
  · exact d_chunk_2_39

theorem raw_numerical_of_A2
    (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 2 i) (recipe 2 j)).eval profile2≤rawProfile2 (.a i j)) :
    ∀ coord : Coord 40, valid coord → raw 2 profile2 coord≤rawProfile2 coord := by
  have hp : ∀ j l : Fin 40, j<l →
      (rawPExpr 40 5003 caps records (recipe 2 j) (recipe 2 (next j)) (recipe 2 l)).eval profile2≤
        rawProfile2 (.p j l) := by
    intro j l hjl
    exact rawP_bound_from_A 40 5003 profile2 caps records (recipe 2 j) (recipe 2 (next j))
      (recipe 2 l) _ _ (ha (next j) l (next_le_of_lt j l hjl)) (p_core_checked2 j l hjl)
  intro coord hc
  cases coord with
  | a i j => exact ha i j hc
  | b i j => exact b_checked2 i j hc
  | m i j => exact m_checked2 i j hc.1 hc.2
  | p j l => exact hp j l hc
  | d i j l =>
      exact rawD_bound_from_MP 40 5003 profile2 caps records (recipe 2 i) (recipe 2 j)
        (recipe 2 (next j)) (recipe 2 l) _ _ _
        (m_checked2 i j hc.1 (next_lt_n_of_lt j l hc.2)) (hp j l hc.2)
        (d_core_checked2 i j l hc.1 hc.2)

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.raw_numerical_of_A2


