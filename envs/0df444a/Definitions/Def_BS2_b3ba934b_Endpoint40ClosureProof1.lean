-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40ClosureProof1
-- name    : BS2_b3ba934b_Endpoint40ClosureProof1
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:44:52.791974+00:00
-- url     : https://prove2.me/theorems/1ab844e5-d5d0-4e6a-b882-f78ac9cec940
-- title:
--   Sensitivity separation: Endpoint40ClosureProof1 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40ClosureProof1` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40ClosureProof1.lean; original SHA-256 66e012f47a8ce74c9199d547b75d4d2c659982f8f171c10fa65bf382b80d8936; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40ClosureData1
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundProfiles ThreeBoundFullProfile ClosureCertificate

private theorem node_chunk_1_0 :
    checkInterval (checkNode rawProfile1 nodes1) 13860 13980=true := by decide +kernel

private theorem node_chunk_1_1 :
    checkInterval (checkNode rawProfile1 nodes1) 13980 14100=true := by decide +kernel

private theorem node_chunk_1_2 :
    checkInterval (checkNode rawProfile1 nodes1) 14100 14220=true := by decide +kernel

private theorem node_chunk_1_3 :
    checkInterval (checkNode rawProfile1 nodes1) 14220 14340=true := by decide +kernel

private theorem node_chunk_1_4 :
    checkInterval (checkNode rawProfile1 nodes1) 14340 14460=true := by decide +kernel

private theorem node_chunk_1_5 :
    checkInterval (checkNode rawProfile1 nodes1) 14460 14580=true := by decide +kernel

private theorem node_chunk_1_6 :
    checkInterval (checkNode rawProfile1 nodes1) 14580 14700=true := by decide +kernel

private theorem node_chunk_1_7 :
    checkInterval (checkNode rawProfile1 nodes1) 14700 14820=true := by decide +kernel

private theorem node_chunk_1_8 :
    checkInterval (checkNode rawProfile1 nodes1) 14820 14940=true := by decide +kernel

private theorem node_chunk_1_9 :
    checkInterval (checkNode rawProfile1 nodes1) 14940 15060=true := by decide +kernel

private theorem node_chunk_1_10 :
    checkInterval (checkNode rawProfile1 nodes1) 15060 15180=true := by decide +kernel

private theorem node_chunk_1_11 :
    checkInterval (checkNode rawProfile1 nodes1) 15180 15300=true := by decide +kernel

private theorem node_chunk_1_12 :
    checkInterval (checkNode rawProfile1 nodes1) 15300 15420=true := by decide +kernel

theorem new_nodes_checked1 :
    checkInterval (checkNode rawProfile1 nodes1) 13860 nodeCount1=true :=
  (checkInterval_join _ 13860 14580 15420 (checkInterval_join _ 13860 14220 14580 (checkInterval_join _ 13860 13980 14220 node_chunk_1_0 (checkInterval_join _ 13980 14100 14220 node_chunk_1_1 node_chunk_1_2)) (checkInterval_join _ 14220 14340 14580 node_chunk_1_3 (checkInterval_join _ 14340 14460 14580 node_chunk_1_4 node_chunk_1_5))) (checkInterval_join _ 14580 14940 15420 (checkInterval_join _ 14580 14700 14940 node_chunk_1_6 (checkInterval_join _ 14700 14820 14940 node_chunk_1_7 node_chunk_1_8)) (checkInterval_join _ 14940 15180 15420 (checkInterval_join _ 14940 15060 15180 node_chunk_1_9 node_chunk_1_10) (checkInterval_join _ 15180 15300 15420 node_chunk_1_11 node_chunk_1_12))))

theorem nodes_pointwise_checked1 (k : ℕ) (hk : k<nodeCount1) :
    checkNode rawProfile1 nodes1 k=true := by
  by_cases hbase : k<13860
  · simp [checkNode,nodes1,hbase]
  · exact checkInterval_sound _ _ _ new_nodes_checked1 k (by omega) hk

private theorem ab_chunk_1_0 : ∀ j : Fin 40, (0 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 0 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 0 j)=true := by
  decide +kernel

private theorem ab_chunk_1_1 : ∀ j : Fin 40, (1 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 1 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 1 j)=true := by
  decide +kernel

private theorem ab_chunk_1_2 : ∀ j : Fin 40, (2 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 2 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 2 j)=true := by
  decide +kernel

private theorem ab_chunk_1_3 : ∀ j : Fin 40, (3 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 3 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 3 j)=true := by
  decide +kernel

private theorem ab_chunk_1_4 : ∀ j : Fin 40, (4 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 4 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 4 j)=true := by
  decide +kernel

private theorem ab_chunk_1_5 : ∀ j : Fin 40, (5 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 5 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 5 j)=true := by
  decide +kernel

private theorem ab_chunk_1_6 : ∀ j : Fin 40, (6 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 6 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 6 j)=true := by
  decide +kernel

private theorem ab_chunk_1_7 : ∀ j : Fin 40, (7 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 7 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 7 j)=true := by
  decide +kernel

private theorem ab_chunk_1_8 : ∀ j : Fin 40, (8 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 8 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 8 j)=true := by
  decide +kernel

private theorem ab_chunk_1_9 : ∀ j : Fin 40, (9 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 9 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 9 j)=true := by
  decide +kernel

private theorem ab_chunk_1_10 : ∀ j : Fin 40, (10 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 10 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 10 j)=true := by
  decide +kernel

private theorem ab_chunk_1_11 : ∀ j : Fin 40, (11 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 11 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 11 j)=true := by
  decide +kernel

private theorem ab_chunk_1_12 : ∀ j : Fin 40, (12 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 12 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 12 j)=true := by
  decide +kernel

private theorem ab_chunk_1_13 : ∀ j : Fin 40, (13 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 13 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 13 j)=true := by
  decide +kernel

private theorem ab_chunk_1_14 : ∀ j : Fin 40, (14 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 14 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 14 j)=true := by
  decide +kernel

private theorem ab_chunk_1_15 : ∀ j : Fin 40, (15 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 15 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 15 j)=true := by
  decide +kernel

private theorem ab_chunk_1_16 : ∀ j : Fin 40, (16 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 16 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 16 j)=true := by
  decide +kernel

private theorem ab_chunk_1_17 : ∀ j : Fin 40, (17 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 17 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 17 j)=true := by
  decide +kernel

private theorem ab_chunk_1_18 : ∀ j : Fin 40, (18 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 18 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 18 j)=true := by
  decide +kernel

private theorem ab_chunk_1_19 : ∀ j : Fin 40, (19 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 19 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 19 j)=true := by
  decide +kernel

private theorem ab_chunk_1_20 : ∀ j : Fin 40, (20 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 20 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 20 j)=true := by
  decide +kernel

private theorem ab_chunk_1_21 : ∀ j : Fin 40, (21 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 21 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 21 j)=true := by
  decide +kernel

private theorem ab_chunk_1_22 : ∀ j : Fin 40, (22 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 22 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 22 j)=true := by
  decide +kernel

private theorem ab_chunk_1_23 : ∀ j : Fin 40, (23 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 23 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 23 j)=true := by
  decide +kernel

private theorem ab_chunk_1_24 : ∀ j : Fin 40, (24 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 24 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 24 j)=true := by
  decide +kernel

private theorem ab_chunk_1_25 : ∀ j : Fin 40, (25 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 25 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 25 j)=true := by
  decide +kernel

private theorem ab_chunk_1_26 : ∀ j : Fin 40, (26 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 26 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 26 j)=true := by
  decide +kernel

private theorem ab_chunk_1_27 : ∀ j : Fin 40, (27 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 27 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 27 j)=true := by
  decide +kernel

private theorem ab_chunk_1_28 : ∀ j : Fin 40, (28 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 28 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 28 j)=true := by
  decide +kernel

private theorem ab_chunk_1_29 : ∀ j : Fin 40, (29 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 29 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 29 j)=true := by
  decide +kernel

private theorem ab_chunk_1_30 : ∀ j : Fin 40, (30 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 30 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 30 j)=true := by
  decide +kernel

private theorem ab_chunk_1_31 : ∀ j : Fin 40, (31 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 31 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 31 j)=true := by
  decide +kernel

private theorem ab_chunk_1_32 : ∀ j : Fin 40, (32 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 32 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 32 j)=true := by
  decide +kernel

private theorem ab_chunk_1_33 : ∀ j : Fin 40, (33 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 33 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 33 j)=true := by
  decide +kernel

private theorem ab_chunk_1_34 : ∀ j : Fin 40, (34 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 34 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 34 j)=true := by
  decide +kernel

private theorem ab_chunk_1_35 : ∀ j : Fin 40, (35 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 35 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 35 j)=true := by
  decide +kernel

private theorem ab_chunk_1_36 : ∀ j : Fin 40, (36 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 36 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 36 j)=true := by
  decide +kernel

private theorem ab_chunk_1_37 : ∀ j : Fin 40, (37 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 37 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 37 j)=true := by
  decide +kernel

private theorem ab_chunk_1_38 : ∀ j : Fin 40, (38 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 38 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 38 j)=true := by
  decide +kernel

private theorem ab_chunk_1_39 : ∀ j : Fin 40, (39 : Fin 40)≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a 39 j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b 39 j)=true := by
  decide +kernel

theorem ab_checked1 : ∀ i j : Fin 40, i≤j →
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.a i j)=true ∧
    checkOutputAt nodes1 nodeCount1 outputIndex1 profile2 (.b i j)=true := by
  intro i
  fin_cases i
  · exact ab_chunk_1_0
  · exact ab_chunk_1_1
  · exact ab_chunk_1_2
  · exact ab_chunk_1_3
  · exact ab_chunk_1_4
  · exact ab_chunk_1_5
  · exact ab_chunk_1_6
  · exact ab_chunk_1_7
  · exact ab_chunk_1_8
  · exact ab_chunk_1_9
  · exact ab_chunk_1_10
  · exact ab_chunk_1_11
  · exact ab_chunk_1_12
  · exact ab_chunk_1_13
  · exact ab_chunk_1_14
  · exact ab_chunk_1_15
  · exact ab_chunk_1_16
  · exact ab_chunk_1_17
  · exact ab_chunk_1_18
  · exact ab_chunk_1_19
  · exact ab_chunk_1_20
  · exact ab_chunk_1_21
  · exact ab_chunk_1_22
  · exact ab_chunk_1_23
  · exact ab_chunk_1_24
  · exact ab_chunk_1_25
  · exact ab_chunk_1_26
  · exact ab_chunk_1_27
  · exact ab_chunk_1_28
  · exact ab_chunk_1_29
  · exact ab_chunk_1_30
  · exact ab_chunk_1_31
  · exact ab_chunk_1_32
  · exact ab_chunk_1_33
  · exact ab_chunk_1_34
  · exact ab_chunk_1_35
  · exact ab_chunk_1_36
  · exact ab_chunk_1_37
  · exact ab_chunk_1_38
  · exact ab_chunk_1_39

theorem gap_share1 (coord : Coord 40) (h : 1640≤flatIndex coord) :
    profile2 coord=rawProfile1 coord := by
  change (if flatIndex coord<1640 then _ else gapTable2.get (flatIndex coord)) =
    (if flatIndex coord<1640 then _ else gapTable2.get (flatIndex coord))
  simp only [if_neg (Nat.not_lt_of_ge h)]

theorem closure1_sound {I : Type} [Fintype I]
    (F : Fin 40 → (I → Bool) → Bool) (hF : Nested F) (c : ℕ)
    (hi : Upper F (scale c rawProfile1)) : Upper F (scale c profile2) := by
  intro coord
  cases coord with
  | a i j =>
      intro hij
      exact outputAt_sound F hF rawProfile1 profile2 nodes1 nodeCount1 c
        outputIndex1 (.a i j) hi nodes_pointwise_checked1 (ab_checked1 i j hij).1 hij
  | b i j =>
      intro hij
      exact outputAt_sound F hF rawProfile1 profile2 nodes1 nodeCount1 c
        outputIndex1 (.b i j) hi nodes_pointwise_checked1 (ab_checked1 i j hij).2 hij
  | m i j =>
      have hidx : 1640≤flatIndex (Coord.m i j) := by simp only [flatIndex,mIndex]; omega
      simpa only [scale,gap_share1 _ hidx] using hi (.m i j)
  | p j l =>
      have hidx : 1640≤flatIndex (Coord.p j l) := by simp only [flatIndex,pIndex]; omega
      simpa only [scale,gap_share1 _ hidx] using hi (.p j l)
  | d i j l =>
      have hidx : 1640≤flatIndex (Coord.d i j l) := by simp only [flatIndex,dIndex]; omega
      simpa only [scale,gap_share1 _ hidx] using hi (.d i j l)

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.new_nodes_checked1
#print axioms ThreeBoundNumeric.Endpoint40.ab_checked1
#print axioms ThreeBoundNumeric.Endpoint40.closure1_sound


