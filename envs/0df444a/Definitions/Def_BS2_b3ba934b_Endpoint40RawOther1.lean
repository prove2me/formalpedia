-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1
-- name    : BS2_b3ba934b_Endpoint40RawOther1
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T04:56:54.019057+00:00
-- url     : https://prove2.me/theorems/4dda7456-171e-41e1-bcb4-1d21d337f02e
-- title:
--   Sensitivity separation: Endpoint40RawOther1 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawOther1` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1.lean; original SHA-256 15710e6c55ee11e4a046b5b89fe298fcb02fbaa6201d2071ad28fe7e0bd697eb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk00
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk01
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk02
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk03
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk04
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk05
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk06
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk07
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk08
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk09
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk10
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk11
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk12
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk13
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk14
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk15
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk16
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk17
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk18
import Definitions.Def_BS2_b3ba934b_Endpoint40RawOther1Chunk19

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundFullProfile

theorem ordinaryA_checked1 : ∀ i j : Fin 40, i≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (rawAExpr 40 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j) := by
  intro i j hij hq
  rw [← rawAFast_eq]
  fin_cases i
  · exact ordinaryA_chunk_1_0 j hij hq
  · exact ordinaryA_chunk_1_1 j hij hq
  · exact ordinaryA_chunk_1_2 j hij hq
  · exact ordinaryA_chunk_1_3 j hij hq
  · exact ordinaryA_chunk_1_4 j hij hq
  · exact ordinaryA_chunk_1_5 j hij hq
  · exact ordinaryA_chunk_1_6 j hij hq
  · exact ordinaryA_chunk_1_7 j hij hq
  · exact ordinaryA_chunk_1_8 j hij hq
  · exact ordinaryA_chunk_1_9 j hij hq
  · exact ordinaryA_chunk_1_10 j hij hq
  · exact ordinaryA_chunk_1_11 j hij hq
  · exact ordinaryA_chunk_1_12 j hij hq
  · exact ordinaryA_chunk_1_13 j hij hq
  · exact ordinaryA_chunk_1_14 j hij hq
  · exact ordinaryA_chunk_1_15 j hij hq
  · exact ordinaryA_chunk_1_16 j hij hq
  · exact ordinaryA_chunk_1_17 j hij hq
  · exact ordinaryA_chunk_1_18 j hij hq
  · exact ordinaryA_chunk_1_19 j hij hq
  · exact ordinaryA_chunk_1_20 j hij hq
  · exact ordinaryA_chunk_1_21 j hij hq
  · exact ordinaryA_chunk_1_22 j hij hq
  · exact ordinaryA_chunk_1_23 j hij hq
  · exact ordinaryA_chunk_1_24 j hij hq
  · exact ordinaryA_chunk_1_25 j hij hq
  · exact ordinaryA_chunk_1_26 j hij hq
  · exact ordinaryA_chunk_1_27 j hij hq
  · exact ordinaryA_chunk_1_28 j hij hq
  · exact ordinaryA_chunk_1_29 j hij hq
  · exact ordinaryA_chunk_1_30 j hij hq
  · exact ordinaryA_chunk_1_31 j hij hq
  · exact ordinaryA_chunk_1_32 j hij hq
  · exact ordinaryA_chunk_1_33 j hij hq
  · exact ordinaryA_chunk_1_34 j hij hq
  · exact ordinaryA_chunk_1_35 j hij hq
  · exact ordinaryA_chunk_1_36 j hij hq
  · exact ordinaryA_chunk_1_37 j hij hq
  · exact ordinaryA_chunk_1_38 j hij hq
  · exact ordinaryA_chunk_1_39 j hij hq

theorem b_checked1 : ∀ i j : Fin 40, i≤j →
    (rawBExpr 40 5003 (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.b i j) := by
  intro i
  fin_cases i
  · exact other_chunk_1_0.1
  · exact other_chunk_1_1.1
  · exact other_chunk_1_2.1
  · exact other_chunk_1_3.1
  · exact other_chunk_1_4.1
  · exact other_chunk_1_5.1
  · exact other_chunk_1_6.1
  · exact other_chunk_1_7.1
  · exact other_chunk_1_8.1
  · exact other_chunk_1_9.1
  · exact other_chunk_1_10.1
  · exact other_chunk_1_11.1
  · exact other_chunk_1_12.1
  · exact other_chunk_1_13.1
  · exact other_chunk_1_14.1
  · exact other_chunk_1_15.1
  · exact other_chunk_1_16.1
  · exact other_chunk_1_17.1
  · exact other_chunk_1_18.1
  · exact other_chunk_1_19.1
  · exact other_chunk_1_20.1
  · exact other_chunk_1_21.1
  · exact other_chunk_1_22.1
  · exact other_chunk_1_23.1
  · exact other_chunk_1_24.1
  · exact other_chunk_1_25.1
  · exact other_chunk_1_26.1
  · exact other_chunk_1_27.1
  · exact other_chunk_1_28.1
  · exact other_chunk_1_29.1
  · exact other_chunk_1_30.1
  · exact other_chunk_1_31.1
  · exact other_chunk_1_32.1
  · exact other_chunk_1_33.1
  · exact other_chunk_1_34.1
  · exact other_chunk_1_35.1
  · exact other_chunk_1_36.1
  · exact other_chunk_1_37.1
  · exact other_chunk_1_38.1
  · exact other_chunk_1_39.1
theorem m_checked1 : ∀ i j : Fin 40, i≤j → j.val+1<40 →
    (rawMExpr 40 5003 (recipe 1 i) (recipe 1 j) (recipe 1 (next j))).eval profile1≤rawProfile1 (.m i j) := by
  intro i
  fin_cases i
  · exact other_chunk_1_0.2.1
  · exact other_chunk_1_1.2.1
  · exact other_chunk_1_2.2.1
  · exact other_chunk_1_3.2.1
  · exact other_chunk_1_4.2.1
  · exact other_chunk_1_5.2.1
  · exact other_chunk_1_6.2.1
  · exact other_chunk_1_7.2.1
  · exact other_chunk_1_8.2.1
  · exact other_chunk_1_9.2.1
  · exact other_chunk_1_10.2.1
  · exact other_chunk_1_11.2.1
  · exact other_chunk_1_12.2.1
  · exact other_chunk_1_13.2.1
  · exact other_chunk_1_14.2.1
  · exact other_chunk_1_15.2.1
  · exact other_chunk_1_16.2.1
  · exact other_chunk_1_17.2.1
  · exact other_chunk_1_18.2.1
  · exact other_chunk_1_19.2.1
  · exact other_chunk_1_20.2.1
  · exact other_chunk_1_21.2.1
  · exact other_chunk_1_22.2.1
  · exact other_chunk_1_23.2.1
  · exact other_chunk_1_24.2.1
  · exact other_chunk_1_25.2.1
  · exact other_chunk_1_26.2.1
  · exact other_chunk_1_27.2.1
  · exact other_chunk_1_28.2.1
  · exact other_chunk_1_29.2.1
  · exact other_chunk_1_30.2.1
  · exact other_chunk_1_31.2.1
  · exact other_chunk_1_32.2.1
  · exact other_chunk_1_33.2.1
  · exact other_chunk_1_34.2.1
  · exact other_chunk_1_35.2.1
  · exact other_chunk_1_36.2.1
  · exact other_chunk_1_37.2.1
  · exact other_chunk_1_38.2.1
  · exact other_chunk_1_39.2.1
theorem p_core_checked1 : ∀ j l : Fin 40, j<l →
    pCore 40 profile1 caps (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.a (next j) l))≤rawProfile1 (.p j l) := by
  intro j
  fin_cases j
  · exact other_chunk_1_0.2.2
  · exact other_chunk_1_1.2.2
  · exact other_chunk_1_2.2.2
  · exact other_chunk_1_3.2.2
  · exact other_chunk_1_4.2.2
  · exact other_chunk_1_5.2.2
  · exact other_chunk_1_6.2.2
  · exact other_chunk_1_7.2.2
  · exact other_chunk_1_8.2.2
  · exact other_chunk_1_9.2.2
  · exact other_chunk_1_10.2.2
  · exact other_chunk_1_11.2.2
  · exact other_chunk_1_12.2.2
  · exact other_chunk_1_13.2.2
  · exact other_chunk_1_14.2.2
  · exact other_chunk_1_15.2.2
  · exact other_chunk_1_16.2.2
  · exact other_chunk_1_17.2.2
  · exact other_chunk_1_18.2.2
  · exact other_chunk_1_19.2.2
  · exact other_chunk_1_20.2.2
  · exact other_chunk_1_21.2.2
  · exact other_chunk_1_22.2.2
  · exact other_chunk_1_23.2.2
  · exact other_chunk_1_24.2.2
  · exact other_chunk_1_25.2.2
  · exact other_chunk_1_26.2.2
  · exact other_chunk_1_27.2.2
  · exact other_chunk_1_28.2.2
  · exact other_chunk_1_29.2.2
  · exact other_chunk_1_30.2.2
  · exact other_chunk_1_31.2.2
  · exact other_chunk_1_32.2.2
  · exact other_chunk_1_33.2.2
  · exact other_chunk_1_34.2.2
  · exact other_chunk_1_35.2.2
  · exact other_chunk_1_36.2.2
  · exact other_chunk_1_37.2.2
  · exact other_chunk_1_38.2.2
  · exact other_chunk_1_39.2.2
theorem d_core_checked1 : ∀ i j l : Fin 40, i≤j → j<l →
    dCore 40 5003 profile1 (recipe 1 i) (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)
      (rawProfile1 (.m i j)+rawProfile1 (.p j l))≤rawProfile1 (.d i j l) := by
  intro i
  fin_cases i
  · exact d_chunk_1_0
  · exact d_chunk_1_1
  · exact d_chunk_1_2
  · exact d_chunk_1_3
  · exact d_chunk_1_4
  · exact d_chunk_1_5
  · exact d_chunk_1_6
  · exact d_chunk_1_7
  · exact d_chunk_1_8
  · exact d_chunk_1_9
  · exact d_chunk_1_10
  · exact d_chunk_1_11
  · exact d_chunk_1_12
  · exact d_chunk_1_13
  · exact d_chunk_1_14
  · exact d_chunk_1_15
  · exact d_chunk_1_16
  · exact d_chunk_1_17
  · exact d_chunk_1_18
  · exact d_chunk_1_19
  · exact d_chunk_1_20
  · exact d_chunk_1_21
  · exact d_chunk_1_22
  · exact d_chunk_1_23
  · exact d_chunk_1_24
  · exact d_chunk_1_25
  · exact d_chunk_1_26
  · exact d_chunk_1_27
  · exact d_chunk_1_28
  · exact d_chunk_1_29
  · exact d_chunk_1_30
  · exact d_chunk_1_31
  · exact d_chunk_1_32
  · exact d_chunk_1_33
  · exact d_chunk_1_34
  · exact d_chunk_1_35
  · exact d_chunk_1_36
  · exact d_chunk_1_37
  · exact d_chunk_1_38
  · exact d_chunk_1_39

theorem raw_numerical_of_A1
    (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j)) :
    ∀ coord : Coord 40, valid coord → raw 1 profile1 coord≤rawProfile1 coord := by
  have hp : ∀ j l : Fin 40, j<l →
      (rawPExpr 40 5003 caps records (recipe 1 j) (recipe 1 (next j)) (recipe 1 l)).eval profile1≤
        rawProfile1 (.p j l) := by
    intro j l hjl
    exact rawP_bound_from_A 40 5003 profile1 caps records (recipe 1 j) (recipe 1 (next j))
      (recipe 1 l) _ _ (ha (next j) l (next_le_of_lt j l hjl)) (p_core_checked1 j l hjl)
  intro coord hc
  cases coord with
  | a i j => exact ha i j hc
  | b i j => exact b_checked1 i j hc
  | m i j => exact m_checked1 i j hc.1 hc.2
  | p j l => exact hp j l hc
  | d i j l =>
      exact rawD_bound_from_MP 40 5003 profile1 caps records (recipe 1 i) (recipe 1 j)
        (recipe 1 (next j)) (recipe 1 l) _ _ _
        (m_checked1 i j hc.1 (next_lt_n_of_lt j l hc.2)) (hp j l hc.2)
        (d_core_checked1 i j l hc.1 hc.2)

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.raw_numerical_of_A1


