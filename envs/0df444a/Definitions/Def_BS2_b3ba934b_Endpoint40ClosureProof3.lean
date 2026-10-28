-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40ClosureProof3
-- name    : BS2_b3ba934b_Endpoint40ClosureProof3
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:41:27.117898+00:00
-- url     : https://prove2.me/theorems/361cfccf-41a6-4954-8bb2-ae958b25f460
-- title:
--   Sensitivity separation: Endpoint40ClosureProof3 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40ClosureProof3` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40ClosureProof3.lean; original SHA-256 3115a03fc0dff3c81568977734e27aa1dc5d324e6437b45296487c5eb9e29a59; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40ClosureData3
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundProfiles ThreeBoundFullProfile ClosureCertificate

private theorem node_chunk_3_0 :
    checkInterval (checkNode rawProfile3 nodes3) 13860 13980=true := by decide +kernel

private theorem node_chunk_3_1 :
    checkInterval (checkNode rawProfile3 nodes3) 13980 14100=true := by decide +kernel

private theorem node_chunk_3_2 :
    checkInterval (checkNode rawProfile3 nodes3) 14100 14220=true := by decide +kernel

private theorem node_chunk_3_3 :
    checkInterval (checkNode rawProfile3 nodes3) 14220 14340=true := by decide +kernel

private theorem node_chunk_3_4 :
    checkInterval (checkNode rawProfile3 nodes3) 14340 14460=true := by decide +kernel

private theorem node_chunk_3_5 :
    checkInterval (checkNode rawProfile3 nodes3) 14460 14580=true := by decide +kernel

private theorem node_chunk_3_6 :
    checkInterval (checkNode rawProfile3 nodes3) 14580 14700=true := by decide +kernel

private theorem node_chunk_3_7 :
    checkInterval (checkNode rawProfile3 nodes3) 14700 14820=true := by decide +kernel

private theorem node_chunk_3_8 :
    checkInterval (checkNode rawProfile3 nodes3) 14820 14940=true := by decide +kernel

private theorem node_chunk_3_9 :
    checkInterval (checkNode rawProfile3 nodes3) 14940 15060=true := by decide +kernel

private theorem node_chunk_3_10 :
    checkInterval (checkNode rawProfile3 nodes3) 15060 15180=true := by decide +kernel

private theorem node_chunk_3_11 :
    checkInterval (checkNode rawProfile3 nodes3) 15180 15300=true := by decide +kernel

private theorem node_chunk_3_12 :
    checkInterval (checkNode rawProfile3 nodes3) 15300 15420=true := by decide +kernel

theorem new_nodes_checked3 :
    checkInterval (checkNode rawProfile3 nodes3) 13860 nodeCount3=true :=
  (checkInterval_join _ 13860 14580 15420 (checkInterval_join _ 13860 14220 14580 (checkInterval_join _ 13860 13980 14220 node_chunk_3_0 (checkInterval_join _ 13980 14100 14220 node_chunk_3_1 node_chunk_3_2)) (checkInterval_join _ 14220 14340 14580 node_chunk_3_3 (checkInterval_join _ 14340 14460 14580 node_chunk_3_4 node_chunk_3_5))) (checkInterval_join _ 14580 14940 15420 (checkInterval_join _ 14580 14700 14940 node_chunk_3_6 (checkInterval_join _ 14700 14820 14940 node_chunk_3_7 node_chunk_3_8)) (checkInterval_join _ 14940 15180 15420 (checkInterval_join _ 14940 15060 15180 node_chunk_3_9 node_chunk_3_10) (checkInterval_join _ 15180 15300 15420 node_chunk_3_11 node_chunk_3_12))))

theorem nodes_pointwise_checked3 (k : ℕ) (hk : k<nodeCount3) :
    checkNode rawProfile3 nodes3 k=true := by
  by_cases hbase : k<13860
  · simp [checkNode,nodes3,hbase]
  · exact checkInterval_sound _ _ _ new_nodes_checked3 k (by omega) hk

private theorem ab_chunk_3_0 : ∀ j : Fin 40, (0 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 0 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 0 j)=true := by
  decide +kernel

private theorem ab_chunk_3_1 : ∀ j : Fin 40, (1 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 1 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 1 j)=true := by
  decide +kernel

private theorem ab_chunk_3_2 : ∀ j : Fin 40, (2 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 2 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 2 j)=true := by
  decide +kernel

private theorem ab_chunk_3_3 : ∀ j : Fin 40, (3 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 3 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 3 j)=true := by
  decide +kernel

private theorem ab_chunk_3_4 : ∀ j : Fin 40, (4 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 4 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 4 j)=true := by
  decide +kernel

private theorem ab_chunk_3_5 : ∀ j : Fin 40, (5 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 5 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 5 j)=true := by
  decide +kernel

private theorem ab_chunk_3_6 : ∀ j : Fin 40, (6 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 6 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 6 j)=true := by
  decide +kernel

private theorem ab_chunk_3_7 : ∀ j : Fin 40, (7 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 7 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 7 j)=true := by
  decide +kernel

private theorem ab_chunk_3_8 : ∀ j : Fin 40, (8 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 8 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 8 j)=true := by
  decide +kernel

private theorem ab_chunk_3_9 : ∀ j : Fin 40, (9 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 9 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 9 j)=true := by
  decide +kernel

private theorem ab_chunk_3_10 : ∀ j : Fin 40, (10 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 10 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 10 j)=true := by
  decide +kernel

private theorem ab_chunk_3_11 : ∀ j : Fin 40, (11 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 11 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 11 j)=true := by
  decide +kernel

private theorem ab_chunk_3_12 : ∀ j : Fin 40, (12 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 12 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 12 j)=true := by
  decide +kernel

private theorem ab_chunk_3_13 : ∀ j : Fin 40, (13 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 13 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 13 j)=true := by
  decide +kernel

private theorem ab_chunk_3_14 : ∀ j : Fin 40, (14 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 14 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 14 j)=true := by
  decide +kernel

private theorem ab_chunk_3_15 : ∀ j : Fin 40, (15 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 15 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 15 j)=true := by
  decide +kernel

private theorem ab_chunk_3_16 : ∀ j : Fin 40, (16 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 16 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 16 j)=true := by
  decide +kernel

private theorem ab_chunk_3_17 : ∀ j : Fin 40, (17 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 17 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 17 j)=true := by
  decide +kernel

private theorem ab_chunk_3_18 : ∀ j : Fin 40, (18 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 18 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 18 j)=true := by
  decide +kernel

private theorem ab_chunk_3_19 : ∀ j : Fin 40, (19 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 19 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 19 j)=true := by
  decide +kernel

private theorem ab_chunk_3_20 : ∀ j : Fin 40, (20 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 20 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 20 j)=true := by
  decide +kernel

private theorem ab_chunk_3_21 : ∀ j : Fin 40, (21 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 21 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 21 j)=true := by
  decide +kernel

private theorem ab_chunk_3_22 : ∀ j : Fin 40, (22 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 22 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 22 j)=true := by
  decide +kernel

private theorem ab_chunk_3_23 : ∀ j : Fin 40, (23 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 23 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 23 j)=true := by
  decide +kernel

private theorem ab_chunk_3_24 : ∀ j : Fin 40, (24 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 24 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 24 j)=true := by
  decide +kernel

private theorem ab_chunk_3_25 : ∀ j : Fin 40, (25 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 25 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 25 j)=true := by
  decide +kernel

private theorem ab_chunk_3_26 : ∀ j : Fin 40, (26 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 26 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 26 j)=true := by
  decide +kernel

private theorem ab_chunk_3_27 : ∀ j : Fin 40, (27 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 27 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 27 j)=true := by
  decide +kernel

private theorem ab_chunk_3_28 : ∀ j : Fin 40, (28 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 28 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 28 j)=true := by
  decide +kernel

private theorem ab_chunk_3_29 : ∀ j : Fin 40, (29 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 29 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 29 j)=true := by
  decide +kernel

private theorem ab_chunk_3_30 : ∀ j : Fin 40, (30 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 30 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 30 j)=true := by
  decide +kernel

private theorem ab_chunk_3_31 : ∀ j : Fin 40, (31 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 31 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 31 j)=true := by
  decide +kernel

private theorem ab_chunk_3_32 : ∀ j : Fin 40, (32 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 32 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 32 j)=true := by
  decide +kernel

private theorem ab_chunk_3_33 : ∀ j : Fin 40, (33 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 33 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 33 j)=true := by
  decide +kernel

private theorem ab_chunk_3_34 : ∀ j : Fin 40, (34 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 34 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 34 j)=true := by
  decide +kernel

private theorem ab_chunk_3_35 : ∀ j : Fin 40, (35 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 35 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 35 j)=true := by
  decide +kernel

private theorem ab_chunk_3_36 : ∀ j : Fin 40, (36 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 36 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 36 j)=true := by
  decide +kernel

private theorem ab_chunk_3_37 : ∀ j : Fin 40, (37 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 37 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 37 j)=true := by
  decide +kernel

private theorem ab_chunk_3_38 : ∀ j : Fin 40, (38 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 38 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 38 j)=true := by
  decide +kernel

private theorem ab_chunk_3_39 : ∀ j : Fin 40, (39 : Fin 40)≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a 39 j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b 39 j)=true := by
  decide +kernel

theorem ab_checked3 : ∀ i j : Fin 40, i≤j →
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.a i j)=true ∧
    checkOutputAt nodes3 nodeCount3 outputIndex3 profile4 (.b i j)=true := by
  intro i
  fin_cases i
  · exact ab_chunk_3_0
  · exact ab_chunk_3_1
  · exact ab_chunk_3_2
  · exact ab_chunk_3_3
  · exact ab_chunk_3_4
  · exact ab_chunk_3_5
  · exact ab_chunk_3_6
  · exact ab_chunk_3_7
  · exact ab_chunk_3_8
  · exact ab_chunk_3_9
  · exact ab_chunk_3_10
  · exact ab_chunk_3_11
  · exact ab_chunk_3_12
  · exact ab_chunk_3_13
  · exact ab_chunk_3_14
  · exact ab_chunk_3_15
  · exact ab_chunk_3_16
  · exact ab_chunk_3_17
  · exact ab_chunk_3_18
  · exact ab_chunk_3_19
  · exact ab_chunk_3_20
  · exact ab_chunk_3_21
  · exact ab_chunk_3_22
  · exact ab_chunk_3_23
  · exact ab_chunk_3_24
  · exact ab_chunk_3_25
  · exact ab_chunk_3_26
  · exact ab_chunk_3_27
  · exact ab_chunk_3_28
  · exact ab_chunk_3_29
  · exact ab_chunk_3_30
  · exact ab_chunk_3_31
  · exact ab_chunk_3_32
  · exact ab_chunk_3_33
  · exact ab_chunk_3_34
  · exact ab_chunk_3_35
  · exact ab_chunk_3_36
  · exact ab_chunk_3_37
  · exact ab_chunk_3_38
  · exact ab_chunk_3_39

theorem gap_share3 (coord : Coord 40) (h : 1640≤flatIndex coord) :
    profile4 coord=rawProfile3 coord := by
  change (if flatIndex coord<1640 then _ else gapTable4.get (flatIndex coord)) =
    (if flatIndex coord<1640 then _ else gapTable4.get (flatIndex coord))
  simp only [if_neg (Nat.not_lt_of_ge h)]

theorem closure3_sound {I : Type} [Fintype I]
    (F : Fin 40 → (I → Bool) → Bool) (hF : Nested F) (c : ℕ)
    (hi : Upper F (scale c rawProfile3)) : Upper F (scale c profile4) := by
  intro coord
  cases coord with
  | a i j =>
      intro hij
      exact outputAt_sound F hF rawProfile3 profile4 nodes3 nodeCount3 c
        outputIndex3 (.a i j) hi nodes_pointwise_checked3 (ab_checked3 i j hij).1 hij
  | b i j =>
      intro hij
      exact outputAt_sound F hF rawProfile3 profile4 nodes3 nodeCount3 c
        outputIndex3 (.b i j) hi nodes_pointwise_checked3 (ab_checked3 i j hij).2 hij
  | m i j =>
      have hidx : 1640≤flatIndex (Coord.m i j) := by simp only [flatIndex,mIndex]; omega
      simpa only [scale,gap_share3 _ hidx] using hi (.m i j)
  | p j l =>
      have hidx : 1640≤flatIndex (Coord.p j l) := by simp only [flatIndex,pIndex]; omega
      simpa only [scale,gap_share3 _ hidx] using hi (.p j l)
  | d i j l =>
      have hidx : 1640≤flatIndex (Coord.d i j l) := by simp only [flatIndex,dIndex]; omega
      simpa only [scale,gap_share3 _ hidx] using hi (.d i j l)

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.new_nodes_checked3
#print axioms ThreeBoundNumeric.Endpoint40.ab_checked3
#print axioms ThreeBoundNumeric.Endpoint40.closure3_sound


