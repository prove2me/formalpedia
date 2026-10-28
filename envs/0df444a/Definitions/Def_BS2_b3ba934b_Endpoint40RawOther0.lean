-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0
-- name    : BS2_b3ba934b_Endpoint40RawOther0
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:22:14.301595+00:00
-- url     : https://prove2.me/theorems/145fcb4f-e0e9-49d3-a58e-a2182d994475
-- title:
--   Sensitivity separation: Endpoint40RawOther0 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther0` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0.lean; original SHA-256 d53272d11f47d3bc685ee8a7a6f661d9f2352a5e749d43135fd15aa3fa6a4d93; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk00
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk01
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk02
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk03
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk04
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk05
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk06
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk07
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk08
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk09
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk10
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk11
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk12
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk13
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk14
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk15
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk16
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk17
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk18
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther0Chunk19

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_checked0 : ∀ i j : Fin 40, i≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (rawAExpr 40 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j) := by
  intro i j hij hq
  rw [← rawAFast_eq]
  fin_cases i
  · exact ordinaryA_chunk_0_0 j hij hq
  · exact ordinaryA_chunk_0_1 j hij hq
  · exact ordinaryA_chunk_0_2 j hij hq
  · exact ordinaryA_chunk_0_3 j hij hq
  · exact ordinaryA_chunk_0_4 j hij hq
  · exact ordinaryA_chunk_0_5 j hij hq
  · exact ordinaryA_chunk_0_6 j hij hq
  · exact ordinaryA_chunk_0_7 j hij hq
  · exact ordinaryA_chunk_0_8 j hij hq
  · exact ordinaryA_chunk_0_9 j hij hq
  · exact ordinaryA_chunk_0_10 j hij hq
  · exact ordinaryA_chunk_0_11 j hij hq
  · exact ordinaryA_chunk_0_12 j hij hq
  · exact ordinaryA_chunk_0_13 j hij hq
  · exact ordinaryA_chunk_0_14 j hij hq
  · exact ordinaryA_chunk_0_15 j hij hq
  · exact ordinaryA_chunk_0_16 j hij hq
  · exact ordinaryA_chunk_0_17 j hij hq
  · exact ordinaryA_chunk_0_18 j hij hq
  · exact ordinaryA_chunk_0_19 j hij hq
  · exact ordinaryA_chunk_0_20 j hij hq
  · exact ordinaryA_chunk_0_21 j hij hq
  · exact ordinaryA_chunk_0_22 j hij hq
  · exact ordinaryA_chunk_0_23 j hij hq
  · exact ordinaryA_chunk_0_24 j hij hq
  · exact ordinaryA_chunk_0_25 j hij hq
  · exact ordinaryA_chunk_0_26 j hij hq
  · exact ordinaryA_chunk_0_27 j hij hq
  · exact ordinaryA_chunk_0_28 j hij hq
  · exact ordinaryA_chunk_0_29 j hij hq
  · exact ordinaryA_chunk_0_30 j hij hq
  · exact ordinaryA_chunk_0_31 j hij hq
  · exact ordinaryA_chunk_0_32 j hij hq
  · exact ordinaryA_chunk_0_33 j hij hq
  · exact ordinaryA_chunk_0_34 j hij hq
  · exact ordinaryA_chunk_0_35 j hij hq
  · exact ordinaryA_chunk_0_36 j hij hq
  · exact ordinaryA_chunk_0_37 j hij hq
  · exact ordinaryA_chunk_0_38 j hij hq
  · exact ordinaryA_chunk_0_39 j hij hq

theorem b_checked0 : ∀ i j : Fin 40, i≤j →
    (rawBExpr 40 5003 (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.b i j) := by
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
  · exact other_chunk_0_16.1
  · exact other_chunk_0_17.1
  · exact other_chunk_0_18.1
  · exact other_chunk_0_19.1
  · exact other_chunk_0_20.1
  · exact other_chunk_0_21.1
  · exact other_chunk_0_22.1
  · exact other_chunk_0_23.1
  · exact other_chunk_0_24.1
  · exact other_chunk_0_25.1
  · exact other_chunk_0_26.1
  · exact other_chunk_0_27.1
  · exact other_chunk_0_28.1
  · exact other_chunk_0_29.1
  · exact other_chunk_0_30.1
  · exact other_chunk_0_31.1
  · exact other_chunk_0_32.1
  · exact other_chunk_0_33.1
  · exact other_chunk_0_34.1
  · exact other_chunk_0_35.1
  · exact other_chunk_0_36.1
  · exact other_chunk_0_37.1
  · exact other_chunk_0_38.1
  · exact other_chunk_0_39.1
theorem m_checked0 : ∀ i j : Fin 40, i≤j → j.val+1<40 →
    (rawMExpr 40 5003 (recipe 0 i) (recipe 0 j) (recipe 0 (next j))).eval profile0≤rawProfile0 (.m i j) := by
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
  · exact other_chunk_0_16.2.1
  · exact other_chunk_0_17.2.1
  · exact other_chunk_0_18.2.1
  · exact other_chunk_0_19.2.1
  · exact other_chunk_0_20.2.1
  · exact other_chunk_0_21.2.1
  · exact other_chunk_0_22.2.1
  · exact other_chunk_0_23.2.1
  · exact other_chunk_0_24.2.1
  · exact other_chunk_0_25.2.1
  · exact other_chunk_0_26.2.1
  · exact other_chunk_0_27.2.1
  · exact other_chunk_0_28.2.1
  · exact other_chunk_0_29.2.1
  · exact other_chunk_0_30.2.1
  · exact other_chunk_0_31.2.1
  · exact other_chunk_0_32.2.1
  · exact other_chunk_0_33.2.1
  · exact other_chunk_0_34.2.1
  · exact other_chunk_0_35.2.1
  · exact other_chunk_0_36.2.1
  · exact other_chunk_0_37.2.1
  · exact other_chunk_0_38.2.1
  · exact other_chunk_0_39.2.1
theorem p_core_checked0 : ∀ j l : Fin 40, j<l →
    pCore 40 profile0 caps (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
      (rawProfile0 (.a (next j) l))≤rawProfile0 (.p j l) := by
  intro j
  fin_cases j
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
  · exact other_chunk_0_16.2.2
  · exact other_chunk_0_17.2.2
  · exact other_chunk_0_18.2.2
  · exact other_chunk_0_19.2.2
  · exact other_chunk_0_20.2.2
  · exact other_chunk_0_21.2.2
  · exact other_chunk_0_22.2.2
  · exact other_chunk_0_23.2.2
  · exact other_chunk_0_24.2.2
  · exact other_chunk_0_25.2.2
  · exact other_chunk_0_26.2.2
  · exact other_chunk_0_27.2.2
  · exact other_chunk_0_28.2.2
  · exact other_chunk_0_29.2.2
  · exact other_chunk_0_30.2.2
  · exact other_chunk_0_31.2.2
  · exact other_chunk_0_32.2.2
  · exact other_chunk_0_33.2.2
  · exact other_chunk_0_34.2.2
  · exact other_chunk_0_35.2.2
  · exact other_chunk_0_36.2.2
  · exact other_chunk_0_37.2.2
  · exact other_chunk_0_38.2.2
  · exact other_chunk_0_39.2.2
theorem d_core_checked0 : ∀ i j l : Fin 40, i≤j → j<l →
    dCore 40 5003 profile0 (recipe 0 i) (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)
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
  · exact d_chunk_0_16
  · exact d_chunk_0_17
  · exact d_chunk_0_18
  · exact d_chunk_0_19
  · exact d_chunk_0_20
  · exact d_chunk_0_21
  · exact d_chunk_0_22
  · exact d_chunk_0_23
  · exact d_chunk_0_24
  · exact d_chunk_0_25
  · exact d_chunk_0_26
  · exact d_chunk_0_27
  · exact d_chunk_0_28
  · exact d_chunk_0_29
  · exact d_chunk_0_30
  · exact d_chunk_0_31
  · exact d_chunk_0_32
  · exact d_chunk_0_33
  · exact d_chunk_0_34
  · exact d_chunk_0_35
  · exact d_chunk_0_36
  · exact d_chunk_0_37
  · exact d_chunk_0_38
  · exact d_chunk_0_39

theorem raw_numerical_of_A0
    (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j)) :
    ∀ coord : Coord 40, valid coord → raw 0 profile0 coord≤rawProfile0 coord := by
  have hp : ∀ j l : Fin 40, j<l →
      (rawPExpr 40 5003 caps records (recipe 0 j) (recipe 0 (next j)) (recipe 0 l)).eval profile0≤
        rawProfile0 (.p j l) := by
    intro j l hjl
    exact rawP_bound_from_A 40 5003 profile0 caps records (recipe 0 j) (recipe 0 (next j))
      (recipe 0 l) _ _ (ha (next j) l (next_le_of_lt j l hjl)) (p_core_checked0 j l hjl)
  intro coord hc
  cases coord with
  | a i j => exact ha i j hc
  | b i j => exact b_checked0 i j hc
  | m i j => exact m_checked0 i j hc.1 hc.2
  | p j l => exact hp j l hc
  | d i j l =>
      exact rawD_bound_from_MP 40 5003 profile0 caps records (recipe 0 i) (recipe 0 j)
        (recipe 0 (next j)) (recipe 0 l) _ _ _
        (m_checked0 i j hc.1 (next_lt_n_of_lt j l hc.2)) (hp j l hc.2)
        (d_core_checked0 i j l hc.1 hc.2)

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.raw_numerical_of_A0


