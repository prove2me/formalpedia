-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40Invariant
-- name    : BS2_b3ba934b_Endpoint40Invariant
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:26:37.207671+00:00
-- url     : https://prove2.me/theorems/e204964a-4fa3-4243-914d-eb55bafe95dd
-- title:
--   Sensitivity separation: Endpoint40Invariant (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40Invariant` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40Invariant.lean; original SHA-256 b86f99609b8ea2ff336ae3f9fa88998cd3d076a3c9fd80eda7357bb0ec7e4e72; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_NatTableChecks
import Definitions.Def_BS2_b3ba934b_NumericAdmissibility
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40
open ThreeBoundProfiles ThreeBoundFullProfile

def initialABTable : NatTable := match profileTable0 with
  | .leaf v => .leaf v
  | .branch _ left _ => left

theorem base_ab_table : NatTable.lowerCheck 1 initialABTable=true := by decide +kernel

theorem period_table : NatTable.dominates 31739938 profileTable4 profileTable0=true := by
  decide +kernel

theorem period_inequality (coord : Coord 40) : profile4 coord≤31739938*profile0 coord :=
  NatTable.dominates_sound 31739938 profileTable4 profileTable0 period_table (flatIndex coord)

theorem base_ab_indices : ∀ i j : Fin 40,
    flatIndex (Coord.a i j)<1640 ∧ flatIndex (Coord.b i j)<1640 := by decide +kernel

theorem base_positive : BasePositive profile0 := by
  have htable := NatTable.lowerCheck_sound 1 initialABTable base_ab_table
  intro i j hij
  constructor
  · change 1≤(if flatIndex (Coord.a i j)<1640 then initialABTable.get (flatIndex (.a i j)) else _)
    rw [if_pos (base_ab_indices i j).1]
    exact htable _
  · change 1≤(if flatIndex (Coord.b i j)<1640 then initialABTable.get (flatIndex (.b i j)) else _)
    rw [if_pos (base_ab_indices i j).2]
    exact htable _

theorem actual_base_upper : Upper (Sensitivity10007Endpoint40.family 0) profile0 :=
  oneBit_upper profile0 base_positive

private theorem admissible_chunk_0_0 :
    (∀ j : Fin 40, (0 : Fin 40)<j →
      profile0 (.a 0 j)≤profile0 (.a (next 0) j) ∧
      profile0 (.a 0 j)≤profile0 (.a 0 (prev j)) ∧
      profile0 (.b 0 j)≤profile0 (.b (next 0) j) ∧
      profile0 (.b 0 j)≤profile0 (.b 0 (prev j))) ∧
    (∀ j : Fin 40, (0 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 0).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_1 :
    (∀ j : Fin 40, (1 : Fin 40)<j →
      profile0 (.a 1 j)≤profile0 (.a (next 1) j) ∧
      profile0 (.a 1 j)≤profile0 (.a 1 (prev j)) ∧
      profile0 (.b 1 j)≤profile0 (.b (next 1) j) ∧
      profile0 (.b 1 j)≤profile0 (.b 1 (prev j))) ∧
    (∀ j : Fin 40, (1 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 1).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_2 :
    (∀ j : Fin 40, (2 : Fin 40)<j →
      profile0 (.a 2 j)≤profile0 (.a (next 2) j) ∧
      profile0 (.a 2 j)≤profile0 (.a 2 (prev j)) ∧
      profile0 (.b 2 j)≤profile0 (.b (next 2) j) ∧
      profile0 (.b 2 j)≤profile0 (.b 2 (prev j))) ∧
    (∀ j : Fin 40, (2 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 2).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_3 :
    (∀ j : Fin 40, (3 : Fin 40)<j →
      profile0 (.a 3 j)≤profile0 (.a (next 3) j) ∧
      profile0 (.a 3 j)≤profile0 (.a 3 (prev j)) ∧
      profile0 (.b 3 j)≤profile0 (.b (next 3) j) ∧
      profile0 (.b 3 j)≤profile0 (.b 3 (prev j))) ∧
    (∀ j : Fin 40, (3 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 3).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_4 :
    (∀ j : Fin 40, (4 : Fin 40)<j →
      profile0 (.a 4 j)≤profile0 (.a (next 4) j) ∧
      profile0 (.a 4 j)≤profile0 (.a 4 (prev j)) ∧
      profile0 (.b 4 j)≤profile0 (.b (next 4) j) ∧
      profile0 (.b 4 j)≤profile0 (.b 4 (prev j))) ∧
    (∀ j : Fin 40, (4 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 4).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_5 :
    (∀ j : Fin 40, (5 : Fin 40)<j →
      profile0 (.a 5 j)≤profile0 (.a (next 5) j) ∧
      profile0 (.a 5 j)≤profile0 (.a 5 (prev j)) ∧
      profile0 (.b 5 j)≤profile0 (.b (next 5) j) ∧
      profile0 (.b 5 j)≤profile0 (.b 5 (prev j))) ∧
    (∀ j : Fin 40, (5 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 5).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_6 :
    (∀ j : Fin 40, (6 : Fin 40)<j →
      profile0 (.a 6 j)≤profile0 (.a (next 6) j) ∧
      profile0 (.a 6 j)≤profile0 (.a 6 (prev j)) ∧
      profile0 (.b 6 j)≤profile0 (.b (next 6) j) ∧
      profile0 (.b 6 j)≤profile0 (.b 6 (prev j))) ∧
    (∀ j : Fin 40, (6 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 6).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_7 :
    (∀ j : Fin 40, (7 : Fin 40)<j →
      profile0 (.a 7 j)≤profile0 (.a (next 7) j) ∧
      profile0 (.a 7 j)≤profile0 (.a 7 (prev j)) ∧
      profile0 (.b 7 j)≤profile0 (.b (next 7) j) ∧
      profile0 (.b 7 j)≤profile0 (.b 7 (prev j))) ∧
    (∀ j : Fin 40, (7 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 7).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_8 :
    (∀ j : Fin 40, (8 : Fin 40)<j →
      profile0 (.a 8 j)≤profile0 (.a (next 8) j) ∧
      profile0 (.a 8 j)≤profile0 (.a 8 (prev j)) ∧
      profile0 (.b 8 j)≤profile0 (.b (next 8) j) ∧
      profile0 (.b 8 j)≤profile0 (.b 8 (prev j))) ∧
    (∀ j : Fin 40, (8 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 8).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_9 :
    (∀ j : Fin 40, (9 : Fin 40)<j →
      profile0 (.a 9 j)≤profile0 (.a (next 9) j) ∧
      profile0 (.a 9 j)≤profile0 (.a 9 (prev j)) ∧
      profile0 (.b 9 j)≤profile0 (.b (next 9) j) ∧
      profile0 (.b 9 j)≤profile0 (.b 9 (prev j))) ∧
    (∀ j : Fin 40, (9 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 9).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_10 :
    (∀ j : Fin 40, (10 : Fin 40)<j →
      profile0 (.a 10 j)≤profile0 (.a (next 10) j) ∧
      profile0 (.a 10 j)≤profile0 (.a 10 (prev j)) ∧
      profile0 (.b 10 j)≤profile0 (.b (next 10) j) ∧
      profile0 (.b 10 j)≤profile0 (.b 10 (prev j))) ∧
    (∀ j : Fin 40, (10 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 10).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_11 :
    (∀ j : Fin 40, (11 : Fin 40)<j →
      profile0 (.a 11 j)≤profile0 (.a (next 11) j) ∧
      profile0 (.a 11 j)≤profile0 (.a 11 (prev j)) ∧
      profile0 (.b 11 j)≤profile0 (.b (next 11) j) ∧
      profile0 (.b 11 j)≤profile0 (.b 11 (prev j))) ∧
    (∀ j : Fin 40, (11 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 11).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_12 :
    (∀ j : Fin 40, (12 : Fin 40)<j →
      profile0 (.a 12 j)≤profile0 (.a (next 12) j) ∧
      profile0 (.a 12 j)≤profile0 (.a 12 (prev j)) ∧
      profile0 (.b 12 j)≤profile0 (.b (next 12) j) ∧
      profile0 (.b 12 j)≤profile0 (.b 12 (prev j))) ∧
    (∀ j : Fin 40, (12 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 12).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_13 :
    (∀ j : Fin 40, (13 : Fin 40)<j →
      profile0 (.a 13 j)≤profile0 (.a (next 13) j) ∧
      profile0 (.a 13 j)≤profile0 (.a 13 (prev j)) ∧
      profile0 (.b 13 j)≤profile0 (.b (next 13) j) ∧
      profile0 (.b 13 j)≤profile0 (.b 13 (prev j))) ∧
    (∀ j : Fin 40, (13 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 13).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_14 :
    (∀ j : Fin 40, (14 : Fin 40)<j →
      profile0 (.a 14 j)≤profile0 (.a (next 14) j) ∧
      profile0 (.a 14 j)≤profile0 (.a 14 (prev j)) ∧
      profile0 (.b 14 j)≤profile0 (.b (next 14) j) ∧
      profile0 (.b 14 j)≤profile0 (.b 14 (prev j))) ∧
    (∀ j : Fin 40, (14 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 14).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_15 :
    (∀ j : Fin 40, (15 : Fin 40)<j →
      profile0 (.a 15 j)≤profile0 (.a (next 15) j) ∧
      profile0 (.a 15 j)≤profile0 (.a 15 (prev j)) ∧
      profile0 (.b 15 j)≤profile0 (.b (next 15) j) ∧
      profile0 (.b 15 j)≤profile0 (.b 15 (prev j))) ∧
    (∀ j : Fin 40, (15 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 15).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_16 :
    (∀ j : Fin 40, (16 : Fin 40)<j →
      profile0 (.a 16 j)≤profile0 (.a (next 16) j) ∧
      profile0 (.a 16 j)≤profile0 (.a 16 (prev j)) ∧
      profile0 (.b 16 j)≤profile0 (.b (next 16) j) ∧
      profile0 (.b 16 j)≤profile0 (.b 16 (prev j))) ∧
    (∀ j : Fin 40, (16 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 16).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_17 :
    (∀ j : Fin 40, (17 : Fin 40)<j →
      profile0 (.a 17 j)≤profile0 (.a (next 17) j) ∧
      profile0 (.a 17 j)≤profile0 (.a 17 (prev j)) ∧
      profile0 (.b 17 j)≤profile0 (.b (next 17) j) ∧
      profile0 (.b 17 j)≤profile0 (.b 17 (prev j))) ∧
    (∀ j : Fin 40, (17 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 17).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_18 :
    (∀ j : Fin 40, (18 : Fin 40)<j →
      profile0 (.a 18 j)≤profile0 (.a (next 18) j) ∧
      profile0 (.a 18 j)≤profile0 (.a 18 (prev j)) ∧
      profile0 (.b 18 j)≤profile0 (.b (next 18) j) ∧
      profile0 (.b 18 j)≤profile0 (.b 18 (prev j))) ∧
    (∀ j : Fin 40, (18 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 18).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_19 :
    (∀ j : Fin 40, (19 : Fin 40)<j →
      profile0 (.a 19 j)≤profile0 (.a (next 19) j) ∧
      profile0 (.a 19 j)≤profile0 (.a 19 (prev j)) ∧
      profile0 (.b 19 j)≤profile0 (.b (next 19) j) ∧
      profile0 (.b 19 j)≤profile0 (.b 19 (prev j))) ∧
    (∀ j : Fin 40, (19 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 19).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_20 :
    (∀ j : Fin 40, (20 : Fin 40)<j →
      profile0 (.a 20 j)≤profile0 (.a (next 20) j) ∧
      profile0 (.a 20 j)≤profile0 (.a 20 (prev j)) ∧
      profile0 (.b 20 j)≤profile0 (.b (next 20) j) ∧
      profile0 (.b 20 j)≤profile0 (.b 20 (prev j))) ∧
    (∀ j : Fin 40, (20 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 20).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_21 :
    (∀ j : Fin 40, (21 : Fin 40)<j →
      profile0 (.a 21 j)≤profile0 (.a (next 21) j) ∧
      profile0 (.a 21 j)≤profile0 (.a 21 (prev j)) ∧
      profile0 (.b 21 j)≤profile0 (.b (next 21) j) ∧
      profile0 (.b 21 j)≤profile0 (.b 21 (prev j))) ∧
    (∀ j : Fin 40, (21 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 21).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_22 :
    (∀ j : Fin 40, (22 : Fin 40)<j →
      profile0 (.a 22 j)≤profile0 (.a (next 22) j) ∧
      profile0 (.a 22 j)≤profile0 (.a 22 (prev j)) ∧
      profile0 (.b 22 j)≤profile0 (.b (next 22) j) ∧
      profile0 (.b 22 j)≤profile0 (.b 22 (prev j))) ∧
    (∀ j : Fin 40, (22 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 22).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_23 :
    (∀ j : Fin 40, (23 : Fin 40)<j →
      profile0 (.a 23 j)≤profile0 (.a (next 23) j) ∧
      profile0 (.a 23 j)≤profile0 (.a 23 (prev j)) ∧
      profile0 (.b 23 j)≤profile0 (.b (next 23) j) ∧
      profile0 (.b 23 j)≤profile0 (.b 23 (prev j))) ∧
    (∀ j : Fin 40, (23 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 23).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_24 :
    (∀ j : Fin 40, (24 : Fin 40)<j →
      profile0 (.a 24 j)≤profile0 (.a (next 24) j) ∧
      profile0 (.a 24 j)≤profile0 (.a 24 (prev j)) ∧
      profile0 (.b 24 j)≤profile0 (.b (next 24) j) ∧
      profile0 (.b 24 j)≤profile0 (.b 24 (prev j))) ∧
    (∀ j : Fin 40, (24 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 24).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_25 :
    (∀ j : Fin 40, (25 : Fin 40)<j →
      profile0 (.a 25 j)≤profile0 (.a (next 25) j) ∧
      profile0 (.a 25 j)≤profile0 (.a 25 (prev j)) ∧
      profile0 (.b 25 j)≤profile0 (.b (next 25) j) ∧
      profile0 (.b 25 j)≤profile0 (.b 25 (prev j))) ∧
    (∀ j : Fin 40, (25 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 25).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_26 :
    (∀ j : Fin 40, (26 : Fin 40)<j →
      profile0 (.a 26 j)≤profile0 (.a (next 26) j) ∧
      profile0 (.a 26 j)≤profile0 (.a 26 (prev j)) ∧
      profile0 (.b 26 j)≤profile0 (.b (next 26) j) ∧
      profile0 (.b 26 j)≤profile0 (.b 26 (prev j))) ∧
    (∀ j : Fin 40, (26 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 26).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_27 :
    (∀ j : Fin 40, (27 : Fin 40)<j →
      profile0 (.a 27 j)≤profile0 (.a (next 27) j) ∧
      profile0 (.a 27 j)≤profile0 (.a 27 (prev j)) ∧
      profile0 (.b 27 j)≤profile0 (.b (next 27) j) ∧
      profile0 (.b 27 j)≤profile0 (.b 27 (prev j))) ∧
    (∀ j : Fin 40, (27 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 27).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_28 :
    (∀ j : Fin 40, (28 : Fin 40)<j →
      profile0 (.a 28 j)≤profile0 (.a (next 28) j) ∧
      profile0 (.a 28 j)≤profile0 (.a 28 (prev j)) ∧
      profile0 (.b 28 j)≤profile0 (.b (next 28) j) ∧
      profile0 (.b 28 j)≤profile0 (.b 28 (prev j))) ∧
    (∀ j : Fin 40, (28 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 28).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_29 :
    (∀ j : Fin 40, (29 : Fin 40)<j →
      profile0 (.a 29 j)≤profile0 (.a (next 29) j) ∧
      profile0 (.a 29 j)≤profile0 (.a 29 (prev j)) ∧
      profile0 (.b 29 j)≤profile0 (.b (next 29) j) ∧
      profile0 (.b 29 j)≤profile0 (.b 29 (prev j))) ∧
    (∀ j : Fin 40, (29 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 29).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_30 :
    (∀ j : Fin 40, (30 : Fin 40)<j →
      profile0 (.a 30 j)≤profile0 (.a (next 30) j) ∧
      profile0 (.a 30 j)≤profile0 (.a 30 (prev j)) ∧
      profile0 (.b 30 j)≤profile0 (.b (next 30) j) ∧
      profile0 (.b 30 j)≤profile0 (.b 30 (prev j))) ∧
    (∀ j : Fin 40, (30 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 30).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_31 :
    (∀ j : Fin 40, (31 : Fin 40)<j →
      profile0 (.a 31 j)≤profile0 (.a (next 31) j) ∧
      profile0 (.a 31 j)≤profile0 (.a 31 (prev j)) ∧
      profile0 (.b 31 j)≤profile0 (.b (next 31) j) ∧
      profile0 (.b 31 j)≤profile0 (.b 31 (prev j))) ∧
    (∀ j : Fin 40, (31 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 31).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_32 :
    (∀ j : Fin 40, (32 : Fin 40)<j →
      profile0 (.a 32 j)≤profile0 (.a (next 32) j) ∧
      profile0 (.a 32 j)≤profile0 (.a 32 (prev j)) ∧
      profile0 (.b 32 j)≤profile0 (.b (next 32) j) ∧
      profile0 (.b 32 j)≤profile0 (.b 32 (prev j))) ∧
    (∀ j : Fin 40, (32 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 32).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_33 :
    (∀ j : Fin 40, (33 : Fin 40)<j →
      profile0 (.a 33 j)≤profile0 (.a (next 33) j) ∧
      profile0 (.a 33 j)≤profile0 (.a 33 (prev j)) ∧
      profile0 (.b 33 j)≤profile0 (.b (next 33) j) ∧
      profile0 (.b 33 j)≤profile0 (.b 33 (prev j))) ∧
    (∀ j : Fin 40, (33 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 33).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_34 :
    (∀ j : Fin 40, (34 : Fin 40)<j →
      profile0 (.a 34 j)≤profile0 (.a (next 34) j) ∧
      profile0 (.a 34 j)≤profile0 (.a 34 (prev j)) ∧
      profile0 (.b 34 j)≤profile0 (.b (next 34) j) ∧
      profile0 (.b 34 j)≤profile0 (.b 34 (prev j))) ∧
    (∀ j : Fin 40, (34 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 34).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_35 :
    (∀ j : Fin 40, (35 : Fin 40)<j →
      profile0 (.a 35 j)≤profile0 (.a (next 35) j) ∧
      profile0 (.a 35 j)≤profile0 (.a 35 (prev j)) ∧
      profile0 (.b 35 j)≤profile0 (.b (next 35) j) ∧
      profile0 (.b 35 j)≤profile0 (.b 35 (prev j))) ∧
    (∀ j : Fin 40, (35 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 35).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_36 :
    (∀ j : Fin 40, (36 : Fin 40)<j →
      profile0 (.a 36 j)≤profile0 (.a (next 36) j) ∧
      profile0 (.a 36 j)≤profile0 (.a 36 (prev j)) ∧
      profile0 (.b 36 j)≤profile0 (.b (next 36) j) ∧
      profile0 (.b 36 j)≤profile0 (.b 36 (prev j))) ∧
    (∀ j : Fin 40, (36 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 36).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_37 :
    (∀ j : Fin 40, (37 : Fin 40)<j →
      profile0 (.a 37 j)≤profile0 (.a (next 37) j) ∧
      profile0 (.a 37 j)≤profile0 (.a 37 (prev j)) ∧
      profile0 (.b 37 j)≤profile0 (.b (next 37) j) ∧
      profile0 (.b 37 j)≤profile0 (.b 37 (prev j))) ∧
    (∀ j : Fin 40, (37 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 37).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_38 :
    (∀ j : Fin 40, (38 : Fin 40)<j →
      profile0 (.a 38 j)≤profile0 (.a (next 38) j) ∧
      profile0 (.a 38 j)≤profile0 (.a 38 (prev j)) ∧
      profile0 (.b 38 j)≤profile0 (.b (next 38) j) ∧
      profile0 (.b 38 j)≤profile0 (.b 38 (prev j))) ∧
    (∀ j : Fin 40, (38 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 38).guard).eval profile0) := by decide +kernel

private theorem admissible_chunk_0_39 :
    (∀ j : Fin 40, (39 : Fin 40)<j →
      profile0 (.a 39 j)≤profile0 (.a (next 39) j) ∧
      profile0 (.a 39 j)≤profile0 (.a 39 (prev j)) ∧
      profile0 (.b 39 j)≤profile0 (.b (next 39) j) ∧
      profile0 (.b 39 j)≤profile0 (.b 39 (prev j))) ∧
    (∀ j : Fin 40, (39 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 0 j).tolerance →
      (bExpr 40 (recipe 0 j).guard ((recipe 0 j).threshold k.val)).eval profile0 ≤
      (bExpr 40 (recipe 0 j).guard (recipe 0 39).guard).eval profile0) := by decide +kernel

theorem admissible0 : Admissible (recipe 0) profile0 := by
  constructor
  · intro i
    fin_cases i
    · exact admissible_chunk_0_0.1
    · exact admissible_chunk_0_1.1
    · exact admissible_chunk_0_2.1
    · exact admissible_chunk_0_3.1
    · exact admissible_chunk_0_4.1
    · exact admissible_chunk_0_5.1
    · exact admissible_chunk_0_6.1
    · exact admissible_chunk_0_7.1
    · exact admissible_chunk_0_8.1
    · exact admissible_chunk_0_9.1
    · exact admissible_chunk_0_10.1
    · exact admissible_chunk_0_11.1
    · exact admissible_chunk_0_12.1
    · exact admissible_chunk_0_13.1
    · exact admissible_chunk_0_14.1
    · exact admissible_chunk_0_15.1
    · exact admissible_chunk_0_16.1
    · exact admissible_chunk_0_17.1
    · exact admissible_chunk_0_18.1
    · exact admissible_chunk_0_19.1
    · exact admissible_chunk_0_20.1
    · exact admissible_chunk_0_21.1
    · exact admissible_chunk_0_22.1
    · exact admissible_chunk_0_23.1
    · exact admissible_chunk_0_24.1
    · exact admissible_chunk_0_25.1
    · exact admissible_chunk_0_26.1
    · exact admissible_chunk_0_27.1
    · exact admissible_chunk_0_28.1
    · exact admissible_chunk_0_29.1
    · exact admissible_chunk_0_30.1
    · exact admissible_chunk_0_31.1
    · exact admissible_chunk_0_32.1
    · exact admissible_chunk_0_33.1
    · exact admissible_chunk_0_34.1
    · exact admissible_chunk_0_35.1
    · exact admissible_chunk_0_36.1
    · exact admissible_chunk_0_37.1
    · exact admissible_chunk_0_38.1
    · exact admissible_chunk_0_39.1
  · intro i
    fin_cases i
    · exact admissible_chunk_0_0.2
    · exact admissible_chunk_0_1.2
    · exact admissible_chunk_0_2.2
    · exact admissible_chunk_0_3.2
    · exact admissible_chunk_0_4.2
    · exact admissible_chunk_0_5.2
    · exact admissible_chunk_0_6.2
    · exact admissible_chunk_0_7.2
    · exact admissible_chunk_0_8.2
    · exact admissible_chunk_0_9.2
    · exact admissible_chunk_0_10.2
    · exact admissible_chunk_0_11.2
    · exact admissible_chunk_0_12.2
    · exact admissible_chunk_0_13.2
    · exact admissible_chunk_0_14.2
    · exact admissible_chunk_0_15.2
    · exact admissible_chunk_0_16.2
    · exact admissible_chunk_0_17.2
    · exact admissible_chunk_0_18.2
    · exact admissible_chunk_0_19.2
    · exact admissible_chunk_0_20.2
    · exact admissible_chunk_0_21.2
    · exact admissible_chunk_0_22.2
    · exact admissible_chunk_0_23.2
    · exact admissible_chunk_0_24.2
    · exact admissible_chunk_0_25.2
    · exact admissible_chunk_0_26.2
    · exact admissible_chunk_0_27.2
    · exact admissible_chunk_0_28.2
    · exact admissible_chunk_0_29.2
    · exact admissible_chunk_0_30.2
    · exact admissible_chunk_0_31.2
    · exact admissible_chunk_0_32.2
    · exact admissible_chunk_0_33.2
    · exact admissible_chunk_0_34.2
    · exact admissible_chunk_0_35.2
    · exact admissible_chunk_0_36.2
    · exact admissible_chunk_0_37.2
    · exact admissible_chunk_0_38.2
    · exact admissible_chunk_0_39.2
private theorem admissible_chunk_1_0 :
    (∀ j : Fin 40, (0 : Fin 40)<j →
      profile1 (.a 0 j)≤profile1 (.a (next 0) j) ∧
      profile1 (.a 0 j)≤profile1 (.a 0 (prev j)) ∧
      profile1 (.b 0 j)≤profile1 (.b (next 0) j) ∧
      profile1 (.b 0 j)≤profile1 (.b 0 (prev j))) ∧
    (∀ j : Fin 40, (0 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 0).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_1 :
    (∀ j : Fin 40, (1 : Fin 40)<j →
      profile1 (.a 1 j)≤profile1 (.a (next 1) j) ∧
      profile1 (.a 1 j)≤profile1 (.a 1 (prev j)) ∧
      profile1 (.b 1 j)≤profile1 (.b (next 1) j) ∧
      profile1 (.b 1 j)≤profile1 (.b 1 (prev j))) ∧
    (∀ j : Fin 40, (1 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 1).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_2 :
    (∀ j : Fin 40, (2 : Fin 40)<j →
      profile1 (.a 2 j)≤profile1 (.a (next 2) j) ∧
      profile1 (.a 2 j)≤profile1 (.a 2 (prev j)) ∧
      profile1 (.b 2 j)≤profile1 (.b (next 2) j) ∧
      profile1 (.b 2 j)≤profile1 (.b 2 (prev j))) ∧
    (∀ j : Fin 40, (2 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 2).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_3 :
    (∀ j : Fin 40, (3 : Fin 40)<j →
      profile1 (.a 3 j)≤profile1 (.a (next 3) j) ∧
      profile1 (.a 3 j)≤profile1 (.a 3 (prev j)) ∧
      profile1 (.b 3 j)≤profile1 (.b (next 3) j) ∧
      profile1 (.b 3 j)≤profile1 (.b 3 (prev j))) ∧
    (∀ j : Fin 40, (3 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 3).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_4 :
    (∀ j : Fin 40, (4 : Fin 40)<j →
      profile1 (.a 4 j)≤profile1 (.a (next 4) j) ∧
      profile1 (.a 4 j)≤profile1 (.a 4 (prev j)) ∧
      profile1 (.b 4 j)≤profile1 (.b (next 4) j) ∧
      profile1 (.b 4 j)≤profile1 (.b 4 (prev j))) ∧
    (∀ j : Fin 40, (4 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 4).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_5 :
    (∀ j : Fin 40, (5 : Fin 40)<j →
      profile1 (.a 5 j)≤profile1 (.a (next 5) j) ∧
      profile1 (.a 5 j)≤profile1 (.a 5 (prev j)) ∧
      profile1 (.b 5 j)≤profile1 (.b (next 5) j) ∧
      profile1 (.b 5 j)≤profile1 (.b 5 (prev j))) ∧
    (∀ j : Fin 40, (5 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 5).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_6 :
    (∀ j : Fin 40, (6 : Fin 40)<j →
      profile1 (.a 6 j)≤profile1 (.a (next 6) j) ∧
      profile1 (.a 6 j)≤profile1 (.a 6 (prev j)) ∧
      profile1 (.b 6 j)≤profile1 (.b (next 6) j) ∧
      profile1 (.b 6 j)≤profile1 (.b 6 (prev j))) ∧
    (∀ j : Fin 40, (6 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 6).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_7 :
    (∀ j : Fin 40, (7 : Fin 40)<j →
      profile1 (.a 7 j)≤profile1 (.a (next 7) j) ∧
      profile1 (.a 7 j)≤profile1 (.a 7 (prev j)) ∧
      profile1 (.b 7 j)≤profile1 (.b (next 7) j) ∧
      profile1 (.b 7 j)≤profile1 (.b 7 (prev j))) ∧
    (∀ j : Fin 40, (7 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 7).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_8 :
    (∀ j : Fin 40, (8 : Fin 40)<j →
      profile1 (.a 8 j)≤profile1 (.a (next 8) j) ∧
      profile1 (.a 8 j)≤profile1 (.a 8 (prev j)) ∧
      profile1 (.b 8 j)≤profile1 (.b (next 8) j) ∧
      profile1 (.b 8 j)≤profile1 (.b 8 (prev j))) ∧
    (∀ j : Fin 40, (8 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 8).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_9 :
    (∀ j : Fin 40, (9 : Fin 40)<j →
      profile1 (.a 9 j)≤profile1 (.a (next 9) j) ∧
      profile1 (.a 9 j)≤profile1 (.a 9 (prev j)) ∧
      profile1 (.b 9 j)≤profile1 (.b (next 9) j) ∧
      profile1 (.b 9 j)≤profile1 (.b 9 (prev j))) ∧
    (∀ j : Fin 40, (9 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 9).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_10 :
    (∀ j : Fin 40, (10 : Fin 40)<j →
      profile1 (.a 10 j)≤profile1 (.a (next 10) j) ∧
      profile1 (.a 10 j)≤profile1 (.a 10 (prev j)) ∧
      profile1 (.b 10 j)≤profile1 (.b (next 10) j) ∧
      profile1 (.b 10 j)≤profile1 (.b 10 (prev j))) ∧
    (∀ j : Fin 40, (10 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 10).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_11 :
    (∀ j : Fin 40, (11 : Fin 40)<j →
      profile1 (.a 11 j)≤profile1 (.a (next 11) j) ∧
      profile1 (.a 11 j)≤profile1 (.a 11 (prev j)) ∧
      profile1 (.b 11 j)≤profile1 (.b (next 11) j) ∧
      profile1 (.b 11 j)≤profile1 (.b 11 (prev j))) ∧
    (∀ j : Fin 40, (11 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 11).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_12 :
    (∀ j : Fin 40, (12 : Fin 40)<j →
      profile1 (.a 12 j)≤profile1 (.a (next 12) j) ∧
      profile1 (.a 12 j)≤profile1 (.a 12 (prev j)) ∧
      profile1 (.b 12 j)≤profile1 (.b (next 12) j) ∧
      profile1 (.b 12 j)≤profile1 (.b 12 (prev j))) ∧
    (∀ j : Fin 40, (12 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 12).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_13 :
    (∀ j : Fin 40, (13 : Fin 40)<j →
      profile1 (.a 13 j)≤profile1 (.a (next 13) j) ∧
      profile1 (.a 13 j)≤profile1 (.a 13 (prev j)) ∧
      profile1 (.b 13 j)≤profile1 (.b (next 13) j) ∧
      profile1 (.b 13 j)≤profile1 (.b 13 (prev j))) ∧
    (∀ j : Fin 40, (13 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 13).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_14 :
    (∀ j : Fin 40, (14 : Fin 40)<j →
      profile1 (.a 14 j)≤profile1 (.a (next 14) j) ∧
      profile1 (.a 14 j)≤profile1 (.a 14 (prev j)) ∧
      profile1 (.b 14 j)≤profile1 (.b (next 14) j) ∧
      profile1 (.b 14 j)≤profile1 (.b 14 (prev j))) ∧
    (∀ j : Fin 40, (14 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 14).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_15 :
    (∀ j : Fin 40, (15 : Fin 40)<j →
      profile1 (.a 15 j)≤profile1 (.a (next 15) j) ∧
      profile1 (.a 15 j)≤profile1 (.a 15 (prev j)) ∧
      profile1 (.b 15 j)≤profile1 (.b (next 15) j) ∧
      profile1 (.b 15 j)≤profile1 (.b 15 (prev j))) ∧
    (∀ j : Fin 40, (15 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 15).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_16 :
    (∀ j : Fin 40, (16 : Fin 40)<j →
      profile1 (.a 16 j)≤profile1 (.a (next 16) j) ∧
      profile1 (.a 16 j)≤profile1 (.a 16 (prev j)) ∧
      profile1 (.b 16 j)≤profile1 (.b (next 16) j) ∧
      profile1 (.b 16 j)≤profile1 (.b 16 (prev j))) ∧
    (∀ j : Fin 40, (16 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 16).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_17 :
    (∀ j : Fin 40, (17 : Fin 40)<j →
      profile1 (.a 17 j)≤profile1 (.a (next 17) j) ∧
      profile1 (.a 17 j)≤profile1 (.a 17 (prev j)) ∧
      profile1 (.b 17 j)≤profile1 (.b (next 17) j) ∧
      profile1 (.b 17 j)≤profile1 (.b 17 (prev j))) ∧
    (∀ j : Fin 40, (17 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 17).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_18 :
    (∀ j : Fin 40, (18 : Fin 40)<j →
      profile1 (.a 18 j)≤profile1 (.a (next 18) j) ∧
      profile1 (.a 18 j)≤profile1 (.a 18 (prev j)) ∧
      profile1 (.b 18 j)≤profile1 (.b (next 18) j) ∧
      profile1 (.b 18 j)≤profile1 (.b 18 (prev j))) ∧
    (∀ j : Fin 40, (18 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 18).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_19 :
    (∀ j : Fin 40, (19 : Fin 40)<j →
      profile1 (.a 19 j)≤profile1 (.a (next 19) j) ∧
      profile1 (.a 19 j)≤profile1 (.a 19 (prev j)) ∧
      profile1 (.b 19 j)≤profile1 (.b (next 19) j) ∧
      profile1 (.b 19 j)≤profile1 (.b 19 (prev j))) ∧
    (∀ j : Fin 40, (19 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 19).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_20 :
    (∀ j : Fin 40, (20 : Fin 40)<j →
      profile1 (.a 20 j)≤profile1 (.a (next 20) j) ∧
      profile1 (.a 20 j)≤profile1 (.a 20 (prev j)) ∧
      profile1 (.b 20 j)≤profile1 (.b (next 20) j) ∧
      profile1 (.b 20 j)≤profile1 (.b 20 (prev j))) ∧
    (∀ j : Fin 40, (20 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 20).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_21 :
    (∀ j : Fin 40, (21 : Fin 40)<j →
      profile1 (.a 21 j)≤profile1 (.a (next 21) j) ∧
      profile1 (.a 21 j)≤profile1 (.a 21 (prev j)) ∧
      profile1 (.b 21 j)≤profile1 (.b (next 21) j) ∧
      profile1 (.b 21 j)≤profile1 (.b 21 (prev j))) ∧
    (∀ j : Fin 40, (21 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 21).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_22 :
    (∀ j : Fin 40, (22 : Fin 40)<j →
      profile1 (.a 22 j)≤profile1 (.a (next 22) j) ∧
      profile1 (.a 22 j)≤profile1 (.a 22 (prev j)) ∧
      profile1 (.b 22 j)≤profile1 (.b (next 22) j) ∧
      profile1 (.b 22 j)≤profile1 (.b 22 (prev j))) ∧
    (∀ j : Fin 40, (22 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 22).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_23 :
    (∀ j : Fin 40, (23 : Fin 40)<j →
      profile1 (.a 23 j)≤profile1 (.a (next 23) j) ∧
      profile1 (.a 23 j)≤profile1 (.a 23 (prev j)) ∧
      profile1 (.b 23 j)≤profile1 (.b (next 23) j) ∧
      profile1 (.b 23 j)≤profile1 (.b 23 (prev j))) ∧
    (∀ j : Fin 40, (23 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 23).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_24 :
    (∀ j : Fin 40, (24 : Fin 40)<j →
      profile1 (.a 24 j)≤profile1 (.a (next 24) j) ∧
      profile1 (.a 24 j)≤profile1 (.a 24 (prev j)) ∧
      profile1 (.b 24 j)≤profile1 (.b (next 24) j) ∧
      profile1 (.b 24 j)≤profile1 (.b 24 (prev j))) ∧
    (∀ j : Fin 40, (24 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 24).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_25 :
    (∀ j : Fin 40, (25 : Fin 40)<j →
      profile1 (.a 25 j)≤profile1 (.a (next 25) j) ∧
      profile1 (.a 25 j)≤profile1 (.a 25 (prev j)) ∧
      profile1 (.b 25 j)≤profile1 (.b (next 25) j) ∧
      profile1 (.b 25 j)≤profile1 (.b 25 (prev j))) ∧
    (∀ j : Fin 40, (25 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 25).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_26 :
    (∀ j : Fin 40, (26 : Fin 40)<j →
      profile1 (.a 26 j)≤profile1 (.a (next 26) j) ∧
      profile1 (.a 26 j)≤profile1 (.a 26 (prev j)) ∧
      profile1 (.b 26 j)≤profile1 (.b (next 26) j) ∧
      profile1 (.b 26 j)≤profile1 (.b 26 (prev j))) ∧
    (∀ j : Fin 40, (26 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 26).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_27 :
    (∀ j : Fin 40, (27 : Fin 40)<j →
      profile1 (.a 27 j)≤profile1 (.a (next 27) j) ∧
      profile1 (.a 27 j)≤profile1 (.a 27 (prev j)) ∧
      profile1 (.b 27 j)≤profile1 (.b (next 27) j) ∧
      profile1 (.b 27 j)≤profile1 (.b 27 (prev j))) ∧
    (∀ j : Fin 40, (27 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 27).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_28 :
    (∀ j : Fin 40, (28 : Fin 40)<j →
      profile1 (.a 28 j)≤profile1 (.a (next 28) j) ∧
      profile1 (.a 28 j)≤profile1 (.a 28 (prev j)) ∧
      profile1 (.b 28 j)≤profile1 (.b (next 28) j) ∧
      profile1 (.b 28 j)≤profile1 (.b 28 (prev j))) ∧
    (∀ j : Fin 40, (28 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 28).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_29 :
    (∀ j : Fin 40, (29 : Fin 40)<j →
      profile1 (.a 29 j)≤profile1 (.a (next 29) j) ∧
      profile1 (.a 29 j)≤profile1 (.a 29 (prev j)) ∧
      profile1 (.b 29 j)≤profile1 (.b (next 29) j) ∧
      profile1 (.b 29 j)≤profile1 (.b 29 (prev j))) ∧
    (∀ j : Fin 40, (29 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 29).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_30 :
    (∀ j : Fin 40, (30 : Fin 40)<j →
      profile1 (.a 30 j)≤profile1 (.a (next 30) j) ∧
      profile1 (.a 30 j)≤profile1 (.a 30 (prev j)) ∧
      profile1 (.b 30 j)≤profile1 (.b (next 30) j) ∧
      profile1 (.b 30 j)≤profile1 (.b 30 (prev j))) ∧
    (∀ j : Fin 40, (30 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 30).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_31 :
    (∀ j : Fin 40, (31 : Fin 40)<j →
      profile1 (.a 31 j)≤profile1 (.a (next 31) j) ∧
      profile1 (.a 31 j)≤profile1 (.a 31 (prev j)) ∧
      profile1 (.b 31 j)≤profile1 (.b (next 31) j) ∧
      profile1 (.b 31 j)≤profile1 (.b 31 (prev j))) ∧
    (∀ j : Fin 40, (31 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 31).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_32 :
    (∀ j : Fin 40, (32 : Fin 40)<j →
      profile1 (.a 32 j)≤profile1 (.a (next 32) j) ∧
      profile1 (.a 32 j)≤profile1 (.a 32 (prev j)) ∧
      profile1 (.b 32 j)≤profile1 (.b (next 32) j) ∧
      profile1 (.b 32 j)≤profile1 (.b 32 (prev j))) ∧
    (∀ j : Fin 40, (32 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 32).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_33 :
    (∀ j : Fin 40, (33 : Fin 40)<j →
      profile1 (.a 33 j)≤profile1 (.a (next 33) j) ∧
      profile1 (.a 33 j)≤profile1 (.a 33 (prev j)) ∧
      profile1 (.b 33 j)≤profile1 (.b (next 33) j) ∧
      profile1 (.b 33 j)≤profile1 (.b 33 (prev j))) ∧
    (∀ j : Fin 40, (33 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 33).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_34 :
    (∀ j : Fin 40, (34 : Fin 40)<j →
      profile1 (.a 34 j)≤profile1 (.a (next 34) j) ∧
      profile1 (.a 34 j)≤profile1 (.a 34 (prev j)) ∧
      profile1 (.b 34 j)≤profile1 (.b (next 34) j) ∧
      profile1 (.b 34 j)≤profile1 (.b 34 (prev j))) ∧
    (∀ j : Fin 40, (34 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 34).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_35 :
    (∀ j : Fin 40, (35 : Fin 40)<j →
      profile1 (.a 35 j)≤profile1 (.a (next 35) j) ∧
      profile1 (.a 35 j)≤profile1 (.a 35 (prev j)) ∧
      profile1 (.b 35 j)≤profile1 (.b (next 35) j) ∧
      profile1 (.b 35 j)≤profile1 (.b 35 (prev j))) ∧
    (∀ j : Fin 40, (35 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 35).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_36 :
    (∀ j : Fin 40, (36 : Fin 40)<j →
      profile1 (.a 36 j)≤profile1 (.a (next 36) j) ∧
      profile1 (.a 36 j)≤profile1 (.a 36 (prev j)) ∧
      profile1 (.b 36 j)≤profile1 (.b (next 36) j) ∧
      profile1 (.b 36 j)≤profile1 (.b 36 (prev j))) ∧
    (∀ j : Fin 40, (36 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 36).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_37 :
    (∀ j : Fin 40, (37 : Fin 40)<j →
      profile1 (.a 37 j)≤profile1 (.a (next 37) j) ∧
      profile1 (.a 37 j)≤profile1 (.a 37 (prev j)) ∧
      profile1 (.b 37 j)≤profile1 (.b (next 37) j) ∧
      profile1 (.b 37 j)≤profile1 (.b 37 (prev j))) ∧
    (∀ j : Fin 40, (37 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 37).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_38 :
    (∀ j : Fin 40, (38 : Fin 40)<j →
      profile1 (.a 38 j)≤profile1 (.a (next 38) j) ∧
      profile1 (.a 38 j)≤profile1 (.a 38 (prev j)) ∧
      profile1 (.b 38 j)≤profile1 (.b (next 38) j) ∧
      profile1 (.b 38 j)≤profile1 (.b 38 (prev j))) ∧
    (∀ j : Fin 40, (38 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 38).guard).eval profile1) := by decide +kernel

private theorem admissible_chunk_1_39 :
    (∀ j : Fin 40, (39 : Fin 40)<j →
      profile1 (.a 39 j)≤profile1 (.a (next 39) j) ∧
      profile1 (.a 39 j)≤profile1 (.a 39 (prev j)) ∧
      profile1 (.b 39 j)≤profile1 (.b (next 39) j) ∧
      profile1 (.b 39 j)≤profile1 (.b 39 (prev j))) ∧
    (∀ j : Fin 40, (39 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 1 j).tolerance →
      (bExpr 40 (recipe 1 j).guard ((recipe 1 j).threshold k.val)).eval profile1 ≤
      (bExpr 40 (recipe 1 j).guard (recipe 1 39).guard).eval profile1) := by decide +kernel

theorem admissible1 : Admissible (recipe 1) profile1 := by
  constructor
  · intro i
    fin_cases i
    · exact admissible_chunk_1_0.1
    · exact admissible_chunk_1_1.1
    · exact admissible_chunk_1_2.1
    · exact admissible_chunk_1_3.1
    · exact admissible_chunk_1_4.1
    · exact admissible_chunk_1_5.1
    · exact admissible_chunk_1_6.1
    · exact admissible_chunk_1_7.1
    · exact admissible_chunk_1_8.1
    · exact admissible_chunk_1_9.1
    · exact admissible_chunk_1_10.1
    · exact admissible_chunk_1_11.1
    · exact admissible_chunk_1_12.1
    · exact admissible_chunk_1_13.1
    · exact admissible_chunk_1_14.1
    · exact admissible_chunk_1_15.1
    · exact admissible_chunk_1_16.1
    · exact admissible_chunk_1_17.1
    · exact admissible_chunk_1_18.1
    · exact admissible_chunk_1_19.1
    · exact admissible_chunk_1_20.1
    · exact admissible_chunk_1_21.1
    · exact admissible_chunk_1_22.1
    · exact admissible_chunk_1_23.1
    · exact admissible_chunk_1_24.1
    · exact admissible_chunk_1_25.1
    · exact admissible_chunk_1_26.1
    · exact admissible_chunk_1_27.1
    · exact admissible_chunk_1_28.1
    · exact admissible_chunk_1_29.1
    · exact admissible_chunk_1_30.1
    · exact admissible_chunk_1_31.1
    · exact admissible_chunk_1_32.1
    · exact admissible_chunk_1_33.1
    · exact admissible_chunk_1_34.1
    · exact admissible_chunk_1_35.1
    · exact admissible_chunk_1_36.1
    · exact admissible_chunk_1_37.1
    · exact admissible_chunk_1_38.1
    · exact admissible_chunk_1_39.1
  · intro i
    fin_cases i
    · exact admissible_chunk_1_0.2
    · exact admissible_chunk_1_1.2
    · exact admissible_chunk_1_2.2
    · exact admissible_chunk_1_3.2
    · exact admissible_chunk_1_4.2
    · exact admissible_chunk_1_5.2
    · exact admissible_chunk_1_6.2
    · exact admissible_chunk_1_7.2
    · exact admissible_chunk_1_8.2
    · exact admissible_chunk_1_9.2
    · exact admissible_chunk_1_10.2
    · exact admissible_chunk_1_11.2
    · exact admissible_chunk_1_12.2
    · exact admissible_chunk_1_13.2
    · exact admissible_chunk_1_14.2
    · exact admissible_chunk_1_15.2
    · exact admissible_chunk_1_16.2
    · exact admissible_chunk_1_17.2
    · exact admissible_chunk_1_18.2
    · exact admissible_chunk_1_19.2
    · exact admissible_chunk_1_20.2
    · exact admissible_chunk_1_21.2
    · exact admissible_chunk_1_22.2
    · exact admissible_chunk_1_23.2
    · exact admissible_chunk_1_24.2
    · exact admissible_chunk_1_25.2
    · exact admissible_chunk_1_26.2
    · exact admissible_chunk_1_27.2
    · exact admissible_chunk_1_28.2
    · exact admissible_chunk_1_29.2
    · exact admissible_chunk_1_30.2
    · exact admissible_chunk_1_31.2
    · exact admissible_chunk_1_32.2
    · exact admissible_chunk_1_33.2
    · exact admissible_chunk_1_34.2
    · exact admissible_chunk_1_35.2
    · exact admissible_chunk_1_36.2
    · exact admissible_chunk_1_37.2
    · exact admissible_chunk_1_38.2
    · exact admissible_chunk_1_39.2
private theorem admissible_chunk_2_0 :
    (∀ j : Fin 40, (0 : Fin 40)<j →
      profile2 (.a 0 j)≤profile2 (.a (next 0) j) ∧
      profile2 (.a 0 j)≤profile2 (.a 0 (prev j)) ∧
      profile2 (.b 0 j)≤profile2 (.b (next 0) j) ∧
      profile2 (.b 0 j)≤profile2 (.b 0 (prev j))) ∧
    (∀ j : Fin 40, (0 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 0).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_1 :
    (∀ j : Fin 40, (1 : Fin 40)<j →
      profile2 (.a 1 j)≤profile2 (.a (next 1) j) ∧
      profile2 (.a 1 j)≤profile2 (.a 1 (prev j)) ∧
      profile2 (.b 1 j)≤profile2 (.b (next 1) j) ∧
      profile2 (.b 1 j)≤profile2 (.b 1 (prev j))) ∧
    (∀ j : Fin 40, (1 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 1).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_2 :
    (∀ j : Fin 40, (2 : Fin 40)<j →
      profile2 (.a 2 j)≤profile2 (.a (next 2) j) ∧
      profile2 (.a 2 j)≤profile2 (.a 2 (prev j)) ∧
      profile2 (.b 2 j)≤profile2 (.b (next 2) j) ∧
      profile2 (.b 2 j)≤profile2 (.b 2 (prev j))) ∧
    (∀ j : Fin 40, (2 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 2).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_3 :
    (∀ j : Fin 40, (3 : Fin 40)<j →
      profile2 (.a 3 j)≤profile2 (.a (next 3) j) ∧
      profile2 (.a 3 j)≤profile2 (.a 3 (prev j)) ∧
      profile2 (.b 3 j)≤profile2 (.b (next 3) j) ∧
      profile2 (.b 3 j)≤profile2 (.b 3 (prev j))) ∧
    (∀ j : Fin 40, (3 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 3).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_4 :
    (∀ j : Fin 40, (4 : Fin 40)<j →
      profile2 (.a 4 j)≤profile2 (.a (next 4) j) ∧
      profile2 (.a 4 j)≤profile2 (.a 4 (prev j)) ∧
      profile2 (.b 4 j)≤profile2 (.b (next 4) j) ∧
      profile2 (.b 4 j)≤profile2 (.b 4 (prev j))) ∧
    (∀ j : Fin 40, (4 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 4).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_5 :
    (∀ j : Fin 40, (5 : Fin 40)<j →
      profile2 (.a 5 j)≤profile2 (.a (next 5) j) ∧
      profile2 (.a 5 j)≤profile2 (.a 5 (prev j)) ∧
      profile2 (.b 5 j)≤profile2 (.b (next 5) j) ∧
      profile2 (.b 5 j)≤profile2 (.b 5 (prev j))) ∧
    (∀ j : Fin 40, (5 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 5).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_6 :
    (∀ j : Fin 40, (6 : Fin 40)<j →
      profile2 (.a 6 j)≤profile2 (.a (next 6) j) ∧
      profile2 (.a 6 j)≤profile2 (.a 6 (prev j)) ∧
      profile2 (.b 6 j)≤profile2 (.b (next 6) j) ∧
      profile2 (.b 6 j)≤profile2 (.b 6 (prev j))) ∧
    (∀ j : Fin 40, (6 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 6).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_7 :
    (∀ j : Fin 40, (7 : Fin 40)<j →
      profile2 (.a 7 j)≤profile2 (.a (next 7) j) ∧
      profile2 (.a 7 j)≤profile2 (.a 7 (prev j)) ∧
      profile2 (.b 7 j)≤profile2 (.b (next 7) j) ∧
      profile2 (.b 7 j)≤profile2 (.b 7 (prev j))) ∧
    (∀ j : Fin 40, (7 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 7).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_8 :
    (∀ j : Fin 40, (8 : Fin 40)<j →
      profile2 (.a 8 j)≤profile2 (.a (next 8) j) ∧
      profile2 (.a 8 j)≤profile2 (.a 8 (prev j)) ∧
      profile2 (.b 8 j)≤profile2 (.b (next 8) j) ∧
      profile2 (.b 8 j)≤profile2 (.b 8 (prev j))) ∧
    (∀ j : Fin 40, (8 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 8).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_9 :
    (∀ j : Fin 40, (9 : Fin 40)<j →
      profile2 (.a 9 j)≤profile2 (.a (next 9) j) ∧
      profile2 (.a 9 j)≤profile2 (.a 9 (prev j)) ∧
      profile2 (.b 9 j)≤profile2 (.b (next 9) j) ∧
      profile2 (.b 9 j)≤profile2 (.b 9 (prev j))) ∧
    (∀ j : Fin 40, (9 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 9).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_10 :
    (∀ j : Fin 40, (10 : Fin 40)<j →
      profile2 (.a 10 j)≤profile2 (.a (next 10) j) ∧
      profile2 (.a 10 j)≤profile2 (.a 10 (prev j)) ∧
      profile2 (.b 10 j)≤profile2 (.b (next 10) j) ∧
      profile2 (.b 10 j)≤profile2 (.b 10 (prev j))) ∧
    (∀ j : Fin 40, (10 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 10).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_11 :
    (∀ j : Fin 40, (11 : Fin 40)<j →
      profile2 (.a 11 j)≤profile2 (.a (next 11) j) ∧
      profile2 (.a 11 j)≤profile2 (.a 11 (prev j)) ∧
      profile2 (.b 11 j)≤profile2 (.b (next 11) j) ∧
      profile2 (.b 11 j)≤profile2 (.b 11 (prev j))) ∧
    (∀ j : Fin 40, (11 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 11).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_12 :
    (∀ j : Fin 40, (12 : Fin 40)<j →
      profile2 (.a 12 j)≤profile2 (.a (next 12) j) ∧
      profile2 (.a 12 j)≤profile2 (.a 12 (prev j)) ∧
      profile2 (.b 12 j)≤profile2 (.b (next 12) j) ∧
      profile2 (.b 12 j)≤profile2 (.b 12 (prev j))) ∧
    (∀ j : Fin 40, (12 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 12).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_13 :
    (∀ j : Fin 40, (13 : Fin 40)<j →
      profile2 (.a 13 j)≤profile2 (.a (next 13) j) ∧
      profile2 (.a 13 j)≤profile2 (.a 13 (prev j)) ∧
      profile2 (.b 13 j)≤profile2 (.b (next 13) j) ∧
      profile2 (.b 13 j)≤profile2 (.b 13 (prev j))) ∧
    (∀ j : Fin 40, (13 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 13).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_14 :
    (∀ j : Fin 40, (14 : Fin 40)<j →
      profile2 (.a 14 j)≤profile2 (.a (next 14) j) ∧
      profile2 (.a 14 j)≤profile2 (.a 14 (prev j)) ∧
      profile2 (.b 14 j)≤profile2 (.b (next 14) j) ∧
      profile2 (.b 14 j)≤profile2 (.b 14 (prev j))) ∧
    (∀ j : Fin 40, (14 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 14).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_15 :
    (∀ j : Fin 40, (15 : Fin 40)<j →
      profile2 (.a 15 j)≤profile2 (.a (next 15) j) ∧
      profile2 (.a 15 j)≤profile2 (.a 15 (prev j)) ∧
      profile2 (.b 15 j)≤profile2 (.b (next 15) j) ∧
      profile2 (.b 15 j)≤profile2 (.b 15 (prev j))) ∧
    (∀ j : Fin 40, (15 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 15).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_16 :
    (∀ j : Fin 40, (16 : Fin 40)<j →
      profile2 (.a 16 j)≤profile2 (.a (next 16) j) ∧
      profile2 (.a 16 j)≤profile2 (.a 16 (prev j)) ∧
      profile2 (.b 16 j)≤profile2 (.b (next 16) j) ∧
      profile2 (.b 16 j)≤profile2 (.b 16 (prev j))) ∧
    (∀ j : Fin 40, (16 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 16).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_17 :
    (∀ j : Fin 40, (17 : Fin 40)<j →
      profile2 (.a 17 j)≤profile2 (.a (next 17) j) ∧
      profile2 (.a 17 j)≤profile2 (.a 17 (prev j)) ∧
      profile2 (.b 17 j)≤profile2 (.b (next 17) j) ∧
      profile2 (.b 17 j)≤profile2 (.b 17 (prev j))) ∧
    (∀ j : Fin 40, (17 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 17).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_18 :
    (∀ j : Fin 40, (18 : Fin 40)<j →
      profile2 (.a 18 j)≤profile2 (.a (next 18) j) ∧
      profile2 (.a 18 j)≤profile2 (.a 18 (prev j)) ∧
      profile2 (.b 18 j)≤profile2 (.b (next 18) j) ∧
      profile2 (.b 18 j)≤profile2 (.b 18 (prev j))) ∧
    (∀ j : Fin 40, (18 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 18).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_19 :
    (∀ j : Fin 40, (19 : Fin 40)<j →
      profile2 (.a 19 j)≤profile2 (.a (next 19) j) ∧
      profile2 (.a 19 j)≤profile2 (.a 19 (prev j)) ∧
      profile2 (.b 19 j)≤profile2 (.b (next 19) j) ∧
      profile2 (.b 19 j)≤profile2 (.b 19 (prev j))) ∧
    (∀ j : Fin 40, (19 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 19).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_20 :
    (∀ j : Fin 40, (20 : Fin 40)<j →
      profile2 (.a 20 j)≤profile2 (.a (next 20) j) ∧
      profile2 (.a 20 j)≤profile2 (.a 20 (prev j)) ∧
      profile2 (.b 20 j)≤profile2 (.b (next 20) j) ∧
      profile2 (.b 20 j)≤profile2 (.b 20 (prev j))) ∧
    (∀ j : Fin 40, (20 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 20).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_21 :
    (∀ j : Fin 40, (21 : Fin 40)<j →
      profile2 (.a 21 j)≤profile2 (.a (next 21) j) ∧
      profile2 (.a 21 j)≤profile2 (.a 21 (prev j)) ∧
      profile2 (.b 21 j)≤profile2 (.b (next 21) j) ∧
      profile2 (.b 21 j)≤profile2 (.b 21 (prev j))) ∧
    (∀ j : Fin 40, (21 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 21).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_22 :
    (∀ j : Fin 40, (22 : Fin 40)<j →
      profile2 (.a 22 j)≤profile2 (.a (next 22) j) ∧
      profile2 (.a 22 j)≤profile2 (.a 22 (prev j)) ∧
      profile2 (.b 22 j)≤profile2 (.b (next 22) j) ∧
      profile2 (.b 22 j)≤profile2 (.b 22 (prev j))) ∧
    (∀ j : Fin 40, (22 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 22).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_23 :
    (∀ j : Fin 40, (23 : Fin 40)<j →
      profile2 (.a 23 j)≤profile2 (.a (next 23) j) ∧
      profile2 (.a 23 j)≤profile2 (.a 23 (prev j)) ∧
      profile2 (.b 23 j)≤profile2 (.b (next 23) j) ∧
      profile2 (.b 23 j)≤profile2 (.b 23 (prev j))) ∧
    (∀ j : Fin 40, (23 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 23).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_24 :
    (∀ j : Fin 40, (24 : Fin 40)<j →
      profile2 (.a 24 j)≤profile2 (.a (next 24) j) ∧
      profile2 (.a 24 j)≤profile2 (.a 24 (prev j)) ∧
      profile2 (.b 24 j)≤profile2 (.b (next 24) j) ∧
      profile2 (.b 24 j)≤profile2 (.b 24 (prev j))) ∧
    (∀ j : Fin 40, (24 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 24).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_25 :
    (∀ j : Fin 40, (25 : Fin 40)<j →
      profile2 (.a 25 j)≤profile2 (.a (next 25) j) ∧
      profile2 (.a 25 j)≤profile2 (.a 25 (prev j)) ∧
      profile2 (.b 25 j)≤profile2 (.b (next 25) j) ∧
      profile2 (.b 25 j)≤profile2 (.b 25 (prev j))) ∧
    (∀ j : Fin 40, (25 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 25).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_26 :
    (∀ j : Fin 40, (26 : Fin 40)<j →
      profile2 (.a 26 j)≤profile2 (.a (next 26) j) ∧
      profile2 (.a 26 j)≤profile2 (.a 26 (prev j)) ∧
      profile2 (.b 26 j)≤profile2 (.b (next 26) j) ∧
      profile2 (.b 26 j)≤profile2 (.b 26 (prev j))) ∧
    (∀ j : Fin 40, (26 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 26).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_27 :
    (∀ j : Fin 40, (27 : Fin 40)<j →
      profile2 (.a 27 j)≤profile2 (.a (next 27) j) ∧
      profile2 (.a 27 j)≤profile2 (.a 27 (prev j)) ∧
      profile2 (.b 27 j)≤profile2 (.b (next 27) j) ∧
      profile2 (.b 27 j)≤profile2 (.b 27 (prev j))) ∧
    (∀ j : Fin 40, (27 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 27).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_28 :
    (∀ j : Fin 40, (28 : Fin 40)<j →
      profile2 (.a 28 j)≤profile2 (.a (next 28) j) ∧
      profile2 (.a 28 j)≤profile2 (.a 28 (prev j)) ∧
      profile2 (.b 28 j)≤profile2 (.b (next 28) j) ∧
      profile2 (.b 28 j)≤profile2 (.b 28 (prev j))) ∧
    (∀ j : Fin 40, (28 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 28).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_29 :
    (∀ j : Fin 40, (29 : Fin 40)<j →
      profile2 (.a 29 j)≤profile2 (.a (next 29) j) ∧
      profile2 (.a 29 j)≤profile2 (.a 29 (prev j)) ∧
      profile2 (.b 29 j)≤profile2 (.b (next 29) j) ∧
      profile2 (.b 29 j)≤profile2 (.b 29 (prev j))) ∧
    (∀ j : Fin 40, (29 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 29).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_30 :
    (∀ j : Fin 40, (30 : Fin 40)<j →
      profile2 (.a 30 j)≤profile2 (.a (next 30) j) ∧
      profile2 (.a 30 j)≤profile2 (.a 30 (prev j)) ∧
      profile2 (.b 30 j)≤profile2 (.b (next 30) j) ∧
      profile2 (.b 30 j)≤profile2 (.b 30 (prev j))) ∧
    (∀ j : Fin 40, (30 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 30).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_31 :
    (∀ j : Fin 40, (31 : Fin 40)<j →
      profile2 (.a 31 j)≤profile2 (.a (next 31) j) ∧
      profile2 (.a 31 j)≤profile2 (.a 31 (prev j)) ∧
      profile2 (.b 31 j)≤profile2 (.b (next 31) j) ∧
      profile2 (.b 31 j)≤profile2 (.b 31 (prev j))) ∧
    (∀ j : Fin 40, (31 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 31).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_32 :
    (∀ j : Fin 40, (32 : Fin 40)<j →
      profile2 (.a 32 j)≤profile2 (.a (next 32) j) ∧
      profile2 (.a 32 j)≤profile2 (.a 32 (prev j)) ∧
      profile2 (.b 32 j)≤profile2 (.b (next 32) j) ∧
      profile2 (.b 32 j)≤profile2 (.b 32 (prev j))) ∧
    (∀ j : Fin 40, (32 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 32).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_33 :
    (∀ j : Fin 40, (33 : Fin 40)<j →
      profile2 (.a 33 j)≤profile2 (.a (next 33) j) ∧
      profile2 (.a 33 j)≤profile2 (.a 33 (prev j)) ∧
      profile2 (.b 33 j)≤profile2 (.b (next 33) j) ∧
      profile2 (.b 33 j)≤profile2 (.b 33 (prev j))) ∧
    (∀ j : Fin 40, (33 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 33).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_34 :
    (∀ j : Fin 40, (34 : Fin 40)<j →
      profile2 (.a 34 j)≤profile2 (.a (next 34) j) ∧
      profile2 (.a 34 j)≤profile2 (.a 34 (prev j)) ∧
      profile2 (.b 34 j)≤profile2 (.b (next 34) j) ∧
      profile2 (.b 34 j)≤profile2 (.b 34 (prev j))) ∧
    (∀ j : Fin 40, (34 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 34).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_35 :
    (∀ j : Fin 40, (35 : Fin 40)<j →
      profile2 (.a 35 j)≤profile2 (.a (next 35) j) ∧
      profile2 (.a 35 j)≤profile2 (.a 35 (prev j)) ∧
      profile2 (.b 35 j)≤profile2 (.b (next 35) j) ∧
      profile2 (.b 35 j)≤profile2 (.b 35 (prev j))) ∧
    (∀ j : Fin 40, (35 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 35).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_36 :
    (∀ j : Fin 40, (36 : Fin 40)<j →
      profile2 (.a 36 j)≤profile2 (.a (next 36) j) ∧
      profile2 (.a 36 j)≤profile2 (.a 36 (prev j)) ∧
      profile2 (.b 36 j)≤profile2 (.b (next 36) j) ∧
      profile2 (.b 36 j)≤profile2 (.b 36 (prev j))) ∧
    (∀ j : Fin 40, (36 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 36).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_37 :
    (∀ j : Fin 40, (37 : Fin 40)<j →
      profile2 (.a 37 j)≤profile2 (.a (next 37) j) ∧
      profile2 (.a 37 j)≤profile2 (.a 37 (prev j)) ∧
      profile2 (.b 37 j)≤profile2 (.b (next 37) j) ∧
      profile2 (.b 37 j)≤profile2 (.b 37 (prev j))) ∧
    (∀ j : Fin 40, (37 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 37).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_38 :
    (∀ j : Fin 40, (38 : Fin 40)<j →
      profile2 (.a 38 j)≤profile2 (.a (next 38) j) ∧
      profile2 (.a 38 j)≤profile2 (.a 38 (prev j)) ∧
      profile2 (.b 38 j)≤profile2 (.b (next 38) j) ∧
      profile2 (.b 38 j)≤profile2 (.b 38 (prev j))) ∧
    (∀ j : Fin 40, (38 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 38).guard).eval profile2) := by decide +kernel

private theorem admissible_chunk_2_39 :
    (∀ j : Fin 40, (39 : Fin 40)<j →
      profile2 (.a 39 j)≤profile2 (.a (next 39) j) ∧
      profile2 (.a 39 j)≤profile2 (.a 39 (prev j)) ∧
      profile2 (.b 39 j)≤profile2 (.b (next 39) j) ∧
      profile2 (.b 39 j)≤profile2 (.b 39 (prev j))) ∧
    (∀ j : Fin 40, (39 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 2 j).tolerance →
      (bExpr 40 (recipe 2 j).guard ((recipe 2 j).threshold k.val)).eval profile2 ≤
      (bExpr 40 (recipe 2 j).guard (recipe 2 39).guard).eval profile2) := by decide +kernel

theorem admissible2 : Admissible (recipe 2) profile2 := by
  constructor
  · intro i
    fin_cases i
    · exact admissible_chunk_2_0.1
    · exact admissible_chunk_2_1.1
    · exact admissible_chunk_2_2.1
    · exact admissible_chunk_2_3.1
    · exact admissible_chunk_2_4.1
    · exact admissible_chunk_2_5.1
    · exact admissible_chunk_2_6.1
    · exact admissible_chunk_2_7.1
    · exact admissible_chunk_2_8.1
    · exact admissible_chunk_2_9.1
    · exact admissible_chunk_2_10.1
    · exact admissible_chunk_2_11.1
    · exact admissible_chunk_2_12.1
    · exact admissible_chunk_2_13.1
    · exact admissible_chunk_2_14.1
    · exact admissible_chunk_2_15.1
    · exact admissible_chunk_2_16.1
    · exact admissible_chunk_2_17.1
    · exact admissible_chunk_2_18.1
    · exact admissible_chunk_2_19.1
    · exact admissible_chunk_2_20.1
    · exact admissible_chunk_2_21.1
    · exact admissible_chunk_2_22.1
    · exact admissible_chunk_2_23.1
    · exact admissible_chunk_2_24.1
    · exact admissible_chunk_2_25.1
    · exact admissible_chunk_2_26.1
    · exact admissible_chunk_2_27.1
    · exact admissible_chunk_2_28.1
    · exact admissible_chunk_2_29.1
    · exact admissible_chunk_2_30.1
    · exact admissible_chunk_2_31.1
    · exact admissible_chunk_2_32.1
    · exact admissible_chunk_2_33.1
    · exact admissible_chunk_2_34.1
    · exact admissible_chunk_2_35.1
    · exact admissible_chunk_2_36.1
    · exact admissible_chunk_2_37.1
    · exact admissible_chunk_2_38.1
    · exact admissible_chunk_2_39.1
  · intro i
    fin_cases i
    · exact admissible_chunk_2_0.2
    · exact admissible_chunk_2_1.2
    · exact admissible_chunk_2_2.2
    · exact admissible_chunk_2_3.2
    · exact admissible_chunk_2_4.2
    · exact admissible_chunk_2_5.2
    · exact admissible_chunk_2_6.2
    · exact admissible_chunk_2_7.2
    · exact admissible_chunk_2_8.2
    · exact admissible_chunk_2_9.2
    · exact admissible_chunk_2_10.2
    · exact admissible_chunk_2_11.2
    · exact admissible_chunk_2_12.2
    · exact admissible_chunk_2_13.2
    · exact admissible_chunk_2_14.2
    · exact admissible_chunk_2_15.2
    · exact admissible_chunk_2_16.2
    · exact admissible_chunk_2_17.2
    · exact admissible_chunk_2_18.2
    · exact admissible_chunk_2_19.2
    · exact admissible_chunk_2_20.2
    · exact admissible_chunk_2_21.2
    · exact admissible_chunk_2_22.2
    · exact admissible_chunk_2_23.2
    · exact admissible_chunk_2_24.2
    · exact admissible_chunk_2_25.2
    · exact admissible_chunk_2_26.2
    · exact admissible_chunk_2_27.2
    · exact admissible_chunk_2_28.2
    · exact admissible_chunk_2_29.2
    · exact admissible_chunk_2_30.2
    · exact admissible_chunk_2_31.2
    · exact admissible_chunk_2_32.2
    · exact admissible_chunk_2_33.2
    · exact admissible_chunk_2_34.2
    · exact admissible_chunk_2_35.2
    · exact admissible_chunk_2_36.2
    · exact admissible_chunk_2_37.2
    · exact admissible_chunk_2_38.2
    · exact admissible_chunk_2_39.2
private theorem admissible_chunk_3_0 :
    (∀ j : Fin 40, (0 : Fin 40)<j →
      profile3 (.a 0 j)≤profile3 (.a (next 0) j) ∧
      profile3 (.a 0 j)≤profile3 (.a 0 (prev j)) ∧
      profile3 (.b 0 j)≤profile3 (.b (next 0) j) ∧
      profile3 (.b 0 j)≤profile3 (.b 0 (prev j))) ∧
    (∀ j : Fin 40, (0 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 0).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_1 :
    (∀ j : Fin 40, (1 : Fin 40)<j →
      profile3 (.a 1 j)≤profile3 (.a (next 1) j) ∧
      profile3 (.a 1 j)≤profile3 (.a 1 (prev j)) ∧
      profile3 (.b 1 j)≤profile3 (.b (next 1) j) ∧
      profile3 (.b 1 j)≤profile3 (.b 1 (prev j))) ∧
    (∀ j : Fin 40, (1 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 1).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_2 :
    (∀ j : Fin 40, (2 : Fin 40)<j →
      profile3 (.a 2 j)≤profile3 (.a (next 2) j) ∧
      profile3 (.a 2 j)≤profile3 (.a 2 (prev j)) ∧
      profile3 (.b 2 j)≤profile3 (.b (next 2) j) ∧
      profile3 (.b 2 j)≤profile3 (.b 2 (prev j))) ∧
    (∀ j : Fin 40, (2 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 2).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_3 :
    (∀ j : Fin 40, (3 : Fin 40)<j →
      profile3 (.a 3 j)≤profile3 (.a (next 3) j) ∧
      profile3 (.a 3 j)≤profile3 (.a 3 (prev j)) ∧
      profile3 (.b 3 j)≤profile3 (.b (next 3) j) ∧
      profile3 (.b 3 j)≤profile3 (.b 3 (prev j))) ∧
    (∀ j : Fin 40, (3 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 3).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_4 :
    (∀ j : Fin 40, (4 : Fin 40)<j →
      profile3 (.a 4 j)≤profile3 (.a (next 4) j) ∧
      profile3 (.a 4 j)≤profile3 (.a 4 (prev j)) ∧
      profile3 (.b 4 j)≤profile3 (.b (next 4) j) ∧
      profile3 (.b 4 j)≤profile3 (.b 4 (prev j))) ∧
    (∀ j : Fin 40, (4 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 4).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_5 :
    (∀ j : Fin 40, (5 : Fin 40)<j →
      profile3 (.a 5 j)≤profile3 (.a (next 5) j) ∧
      profile3 (.a 5 j)≤profile3 (.a 5 (prev j)) ∧
      profile3 (.b 5 j)≤profile3 (.b (next 5) j) ∧
      profile3 (.b 5 j)≤profile3 (.b 5 (prev j))) ∧
    (∀ j : Fin 40, (5 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 5).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_6 :
    (∀ j : Fin 40, (6 : Fin 40)<j →
      profile3 (.a 6 j)≤profile3 (.a (next 6) j) ∧
      profile3 (.a 6 j)≤profile3 (.a 6 (prev j)) ∧
      profile3 (.b 6 j)≤profile3 (.b (next 6) j) ∧
      profile3 (.b 6 j)≤profile3 (.b 6 (prev j))) ∧
    (∀ j : Fin 40, (6 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 6).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_7 :
    (∀ j : Fin 40, (7 : Fin 40)<j →
      profile3 (.a 7 j)≤profile3 (.a (next 7) j) ∧
      profile3 (.a 7 j)≤profile3 (.a 7 (prev j)) ∧
      profile3 (.b 7 j)≤profile3 (.b (next 7) j) ∧
      profile3 (.b 7 j)≤profile3 (.b 7 (prev j))) ∧
    (∀ j : Fin 40, (7 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 7).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_8 :
    (∀ j : Fin 40, (8 : Fin 40)<j →
      profile3 (.a 8 j)≤profile3 (.a (next 8) j) ∧
      profile3 (.a 8 j)≤profile3 (.a 8 (prev j)) ∧
      profile3 (.b 8 j)≤profile3 (.b (next 8) j) ∧
      profile3 (.b 8 j)≤profile3 (.b 8 (prev j))) ∧
    (∀ j : Fin 40, (8 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 8).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_9 :
    (∀ j : Fin 40, (9 : Fin 40)<j →
      profile3 (.a 9 j)≤profile3 (.a (next 9) j) ∧
      profile3 (.a 9 j)≤profile3 (.a 9 (prev j)) ∧
      profile3 (.b 9 j)≤profile3 (.b (next 9) j) ∧
      profile3 (.b 9 j)≤profile3 (.b 9 (prev j))) ∧
    (∀ j : Fin 40, (9 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 9).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_10 :
    (∀ j : Fin 40, (10 : Fin 40)<j →
      profile3 (.a 10 j)≤profile3 (.a (next 10) j) ∧
      profile3 (.a 10 j)≤profile3 (.a 10 (prev j)) ∧
      profile3 (.b 10 j)≤profile3 (.b (next 10) j) ∧
      profile3 (.b 10 j)≤profile3 (.b 10 (prev j))) ∧
    (∀ j : Fin 40, (10 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 10).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_11 :
    (∀ j : Fin 40, (11 : Fin 40)<j →
      profile3 (.a 11 j)≤profile3 (.a (next 11) j) ∧
      profile3 (.a 11 j)≤profile3 (.a 11 (prev j)) ∧
      profile3 (.b 11 j)≤profile3 (.b (next 11) j) ∧
      profile3 (.b 11 j)≤profile3 (.b 11 (prev j))) ∧
    (∀ j : Fin 40, (11 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 11).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_12 :
    (∀ j : Fin 40, (12 : Fin 40)<j →
      profile3 (.a 12 j)≤profile3 (.a (next 12) j) ∧
      profile3 (.a 12 j)≤profile3 (.a 12 (prev j)) ∧
      profile3 (.b 12 j)≤profile3 (.b (next 12) j) ∧
      profile3 (.b 12 j)≤profile3 (.b 12 (prev j))) ∧
    (∀ j : Fin 40, (12 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 12).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_13 :
    (∀ j : Fin 40, (13 : Fin 40)<j →
      profile3 (.a 13 j)≤profile3 (.a (next 13) j) ∧
      profile3 (.a 13 j)≤profile3 (.a 13 (prev j)) ∧
      profile3 (.b 13 j)≤profile3 (.b (next 13) j) ∧
      profile3 (.b 13 j)≤profile3 (.b 13 (prev j))) ∧
    (∀ j : Fin 40, (13 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 13).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_14 :
    (∀ j : Fin 40, (14 : Fin 40)<j →
      profile3 (.a 14 j)≤profile3 (.a (next 14) j) ∧
      profile3 (.a 14 j)≤profile3 (.a 14 (prev j)) ∧
      profile3 (.b 14 j)≤profile3 (.b (next 14) j) ∧
      profile3 (.b 14 j)≤profile3 (.b 14 (prev j))) ∧
    (∀ j : Fin 40, (14 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 14).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_15 :
    (∀ j : Fin 40, (15 : Fin 40)<j →
      profile3 (.a 15 j)≤profile3 (.a (next 15) j) ∧
      profile3 (.a 15 j)≤profile3 (.a 15 (prev j)) ∧
      profile3 (.b 15 j)≤profile3 (.b (next 15) j) ∧
      profile3 (.b 15 j)≤profile3 (.b 15 (prev j))) ∧
    (∀ j : Fin 40, (15 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 15).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_16 :
    (∀ j : Fin 40, (16 : Fin 40)<j →
      profile3 (.a 16 j)≤profile3 (.a (next 16) j) ∧
      profile3 (.a 16 j)≤profile3 (.a 16 (prev j)) ∧
      profile3 (.b 16 j)≤profile3 (.b (next 16) j) ∧
      profile3 (.b 16 j)≤profile3 (.b 16 (prev j))) ∧
    (∀ j : Fin 40, (16 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 16).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_17 :
    (∀ j : Fin 40, (17 : Fin 40)<j →
      profile3 (.a 17 j)≤profile3 (.a (next 17) j) ∧
      profile3 (.a 17 j)≤profile3 (.a 17 (prev j)) ∧
      profile3 (.b 17 j)≤profile3 (.b (next 17) j) ∧
      profile3 (.b 17 j)≤profile3 (.b 17 (prev j))) ∧
    (∀ j : Fin 40, (17 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 17).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_18 :
    (∀ j : Fin 40, (18 : Fin 40)<j →
      profile3 (.a 18 j)≤profile3 (.a (next 18) j) ∧
      profile3 (.a 18 j)≤profile3 (.a 18 (prev j)) ∧
      profile3 (.b 18 j)≤profile3 (.b (next 18) j) ∧
      profile3 (.b 18 j)≤profile3 (.b 18 (prev j))) ∧
    (∀ j : Fin 40, (18 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 18).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_19 :
    (∀ j : Fin 40, (19 : Fin 40)<j →
      profile3 (.a 19 j)≤profile3 (.a (next 19) j) ∧
      profile3 (.a 19 j)≤profile3 (.a 19 (prev j)) ∧
      profile3 (.b 19 j)≤profile3 (.b (next 19) j) ∧
      profile3 (.b 19 j)≤profile3 (.b 19 (prev j))) ∧
    (∀ j : Fin 40, (19 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 19).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_20 :
    (∀ j : Fin 40, (20 : Fin 40)<j →
      profile3 (.a 20 j)≤profile3 (.a (next 20) j) ∧
      profile3 (.a 20 j)≤profile3 (.a 20 (prev j)) ∧
      profile3 (.b 20 j)≤profile3 (.b (next 20) j) ∧
      profile3 (.b 20 j)≤profile3 (.b 20 (prev j))) ∧
    (∀ j : Fin 40, (20 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 20).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_21 :
    (∀ j : Fin 40, (21 : Fin 40)<j →
      profile3 (.a 21 j)≤profile3 (.a (next 21) j) ∧
      profile3 (.a 21 j)≤profile3 (.a 21 (prev j)) ∧
      profile3 (.b 21 j)≤profile3 (.b (next 21) j) ∧
      profile3 (.b 21 j)≤profile3 (.b 21 (prev j))) ∧
    (∀ j : Fin 40, (21 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 21).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_22 :
    (∀ j : Fin 40, (22 : Fin 40)<j →
      profile3 (.a 22 j)≤profile3 (.a (next 22) j) ∧
      profile3 (.a 22 j)≤profile3 (.a 22 (prev j)) ∧
      profile3 (.b 22 j)≤profile3 (.b (next 22) j) ∧
      profile3 (.b 22 j)≤profile3 (.b 22 (prev j))) ∧
    (∀ j : Fin 40, (22 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 22).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_23 :
    (∀ j : Fin 40, (23 : Fin 40)<j →
      profile3 (.a 23 j)≤profile3 (.a (next 23) j) ∧
      profile3 (.a 23 j)≤profile3 (.a 23 (prev j)) ∧
      profile3 (.b 23 j)≤profile3 (.b (next 23) j) ∧
      profile3 (.b 23 j)≤profile3 (.b 23 (prev j))) ∧
    (∀ j : Fin 40, (23 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 23).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_24 :
    (∀ j : Fin 40, (24 : Fin 40)<j →
      profile3 (.a 24 j)≤profile3 (.a (next 24) j) ∧
      profile3 (.a 24 j)≤profile3 (.a 24 (prev j)) ∧
      profile3 (.b 24 j)≤profile3 (.b (next 24) j) ∧
      profile3 (.b 24 j)≤profile3 (.b 24 (prev j))) ∧
    (∀ j : Fin 40, (24 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 24).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_25 :
    (∀ j : Fin 40, (25 : Fin 40)<j →
      profile3 (.a 25 j)≤profile3 (.a (next 25) j) ∧
      profile3 (.a 25 j)≤profile3 (.a 25 (prev j)) ∧
      profile3 (.b 25 j)≤profile3 (.b (next 25) j) ∧
      profile3 (.b 25 j)≤profile3 (.b 25 (prev j))) ∧
    (∀ j : Fin 40, (25 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 25).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_26 :
    (∀ j : Fin 40, (26 : Fin 40)<j →
      profile3 (.a 26 j)≤profile3 (.a (next 26) j) ∧
      profile3 (.a 26 j)≤profile3 (.a 26 (prev j)) ∧
      profile3 (.b 26 j)≤profile3 (.b (next 26) j) ∧
      profile3 (.b 26 j)≤profile3 (.b 26 (prev j))) ∧
    (∀ j : Fin 40, (26 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 26).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_27 :
    (∀ j : Fin 40, (27 : Fin 40)<j →
      profile3 (.a 27 j)≤profile3 (.a (next 27) j) ∧
      profile3 (.a 27 j)≤profile3 (.a 27 (prev j)) ∧
      profile3 (.b 27 j)≤profile3 (.b (next 27) j) ∧
      profile3 (.b 27 j)≤profile3 (.b 27 (prev j))) ∧
    (∀ j : Fin 40, (27 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 27).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_28 :
    (∀ j : Fin 40, (28 : Fin 40)<j →
      profile3 (.a 28 j)≤profile3 (.a (next 28) j) ∧
      profile3 (.a 28 j)≤profile3 (.a 28 (prev j)) ∧
      profile3 (.b 28 j)≤profile3 (.b (next 28) j) ∧
      profile3 (.b 28 j)≤profile3 (.b 28 (prev j))) ∧
    (∀ j : Fin 40, (28 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 28).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_29 :
    (∀ j : Fin 40, (29 : Fin 40)<j →
      profile3 (.a 29 j)≤profile3 (.a (next 29) j) ∧
      profile3 (.a 29 j)≤profile3 (.a 29 (prev j)) ∧
      profile3 (.b 29 j)≤profile3 (.b (next 29) j) ∧
      profile3 (.b 29 j)≤profile3 (.b 29 (prev j))) ∧
    (∀ j : Fin 40, (29 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 29).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_30 :
    (∀ j : Fin 40, (30 : Fin 40)<j →
      profile3 (.a 30 j)≤profile3 (.a (next 30) j) ∧
      profile3 (.a 30 j)≤profile3 (.a 30 (prev j)) ∧
      profile3 (.b 30 j)≤profile3 (.b (next 30) j) ∧
      profile3 (.b 30 j)≤profile3 (.b 30 (prev j))) ∧
    (∀ j : Fin 40, (30 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 30).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_31 :
    (∀ j : Fin 40, (31 : Fin 40)<j →
      profile3 (.a 31 j)≤profile3 (.a (next 31) j) ∧
      profile3 (.a 31 j)≤profile3 (.a 31 (prev j)) ∧
      profile3 (.b 31 j)≤profile3 (.b (next 31) j) ∧
      profile3 (.b 31 j)≤profile3 (.b 31 (prev j))) ∧
    (∀ j : Fin 40, (31 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 31).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_32 :
    (∀ j : Fin 40, (32 : Fin 40)<j →
      profile3 (.a 32 j)≤profile3 (.a (next 32) j) ∧
      profile3 (.a 32 j)≤profile3 (.a 32 (prev j)) ∧
      profile3 (.b 32 j)≤profile3 (.b (next 32) j) ∧
      profile3 (.b 32 j)≤profile3 (.b 32 (prev j))) ∧
    (∀ j : Fin 40, (32 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 32).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_33 :
    (∀ j : Fin 40, (33 : Fin 40)<j →
      profile3 (.a 33 j)≤profile3 (.a (next 33) j) ∧
      profile3 (.a 33 j)≤profile3 (.a 33 (prev j)) ∧
      profile3 (.b 33 j)≤profile3 (.b (next 33) j) ∧
      profile3 (.b 33 j)≤profile3 (.b 33 (prev j))) ∧
    (∀ j : Fin 40, (33 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 33).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_34 :
    (∀ j : Fin 40, (34 : Fin 40)<j →
      profile3 (.a 34 j)≤profile3 (.a (next 34) j) ∧
      profile3 (.a 34 j)≤profile3 (.a 34 (prev j)) ∧
      profile3 (.b 34 j)≤profile3 (.b (next 34) j) ∧
      profile3 (.b 34 j)≤profile3 (.b 34 (prev j))) ∧
    (∀ j : Fin 40, (34 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 34).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_35 :
    (∀ j : Fin 40, (35 : Fin 40)<j →
      profile3 (.a 35 j)≤profile3 (.a (next 35) j) ∧
      profile3 (.a 35 j)≤profile3 (.a 35 (prev j)) ∧
      profile3 (.b 35 j)≤profile3 (.b (next 35) j) ∧
      profile3 (.b 35 j)≤profile3 (.b 35 (prev j))) ∧
    (∀ j : Fin 40, (35 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 35).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_36 :
    (∀ j : Fin 40, (36 : Fin 40)<j →
      profile3 (.a 36 j)≤profile3 (.a (next 36) j) ∧
      profile3 (.a 36 j)≤profile3 (.a 36 (prev j)) ∧
      profile3 (.b 36 j)≤profile3 (.b (next 36) j) ∧
      profile3 (.b 36 j)≤profile3 (.b 36 (prev j))) ∧
    (∀ j : Fin 40, (36 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 36).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_37 :
    (∀ j : Fin 40, (37 : Fin 40)<j →
      profile3 (.a 37 j)≤profile3 (.a (next 37) j) ∧
      profile3 (.a 37 j)≤profile3 (.a 37 (prev j)) ∧
      profile3 (.b 37 j)≤profile3 (.b (next 37) j) ∧
      profile3 (.b 37 j)≤profile3 (.b 37 (prev j))) ∧
    (∀ j : Fin 40, (37 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 37).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_38 :
    (∀ j : Fin 40, (38 : Fin 40)<j →
      profile3 (.a 38 j)≤profile3 (.a (next 38) j) ∧
      profile3 (.a 38 j)≤profile3 (.a 38 (prev j)) ∧
      profile3 (.b 38 j)≤profile3 (.b (next 38) j) ∧
      profile3 (.b 38 j)≤profile3 (.b 38 (prev j))) ∧
    (∀ j : Fin 40, (38 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 38).guard).eval profile3) := by decide +kernel

private theorem admissible_chunk_3_39 :
    (∀ j : Fin 40, (39 : Fin 40)<j →
      profile3 (.a 39 j)≤profile3 (.a (next 39) j) ∧
      profile3 (.a 39 j)≤profile3 (.a 39 (prev j)) ∧
      profile3 (.b 39 j)≤profile3 (.b (next 39) j) ∧
      profile3 (.b 39 j)≤profile3 (.b 39 (prev j))) ∧
    (∀ j : Fin 40, (39 : Fin 40)≤j → ∀ k : Fin 9, k.val≤(recipe 3 j).tolerance →
      (bExpr 40 (recipe 3 j).guard ((recipe 3 j).threshold k.val)).eval profile3 ≤
      (bExpr 40 (recipe 3 j).guard (recipe 3 39).guard).eval profile3) := by decide +kernel

theorem admissible3 : Admissible (recipe 3) profile3 := by
  constructor
  · intro i
    fin_cases i
    · exact admissible_chunk_3_0.1
    · exact admissible_chunk_3_1.1
    · exact admissible_chunk_3_2.1
    · exact admissible_chunk_3_3.1
    · exact admissible_chunk_3_4.1
    · exact admissible_chunk_3_5.1
    · exact admissible_chunk_3_6.1
    · exact admissible_chunk_3_7.1
    · exact admissible_chunk_3_8.1
    · exact admissible_chunk_3_9.1
    · exact admissible_chunk_3_10.1
    · exact admissible_chunk_3_11.1
    · exact admissible_chunk_3_12.1
    · exact admissible_chunk_3_13.1
    · exact admissible_chunk_3_14.1
    · exact admissible_chunk_3_15.1
    · exact admissible_chunk_3_16.1
    · exact admissible_chunk_3_17.1
    · exact admissible_chunk_3_18.1
    · exact admissible_chunk_3_19.1
    · exact admissible_chunk_3_20.1
    · exact admissible_chunk_3_21.1
    · exact admissible_chunk_3_22.1
    · exact admissible_chunk_3_23.1
    · exact admissible_chunk_3_24.1
    · exact admissible_chunk_3_25.1
    · exact admissible_chunk_3_26.1
    · exact admissible_chunk_3_27.1
    · exact admissible_chunk_3_28.1
    · exact admissible_chunk_3_29.1
    · exact admissible_chunk_3_30.1
    · exact admissible_chunk_3_31.1
    · exact admissible_chunk_3_32.1
    · exact admissible_chunk_3_33.1
    · exact admissible_chunk_3_34.1
    · exact admissible_chunk_3_35.1
    · exact admissible_chunk_3_36.1
    · exact admissible_chunk_3_37.1
    · exact admissible_chunk_3_38.1
    · exact admissible_chunk_3_39.1
  · intro i
    fin_cases i
    · exact admissible_chunk_3_0.2
    · exact admissible_chunk_3_1.2
    · exact admissible_chunk_3_2.2
    · exact admissible_chunk_3_3.2
    · exact admissible_chunk_3_4.2
    · exact admissible_chunk_3_5.2
    · exact admissible_chunk_3_6.2
    · exact admissible_chunk_3_7.2
    · exact admissible_chunk_3_8.2
    · exact admissible_chunk_3_9.2
    · exact admissible_chunk_3_10.2
    · exact admissible_chunk_3_11.2
    · exact admissible_chunk_3_12.2
    · exact admissible_chunk_3_13.2
    · exact admissible_chunk_3_14.2
    · exact admissible_chunk_3_15.2
    · exact admissible_chunk_3_16.2
    · exact admissible_chunk_3_17.2
    · exact admissible_chunk_3_18.2
    · exact admissible_chunk_3_19.2
    · exact admissible_chunk_3_20.2
    · exact admissible_chunk_3_21.2
    · exact admissible_chunk_3_22.2
    · exact admissible_chunk_3_23.2
    · exact admissible_chunk_3_24.2
    · exact admissible_chunk_3_25.2
    · exact admissible_chunk_3_26.2
    · exact admissible_chunk_3_27.2
    · exact admissible_chunk_3_28.2
    · exact admissible_chunk_3_29.2
    · exact admissible_chunk_3_30.2
    · exact admissible_chunk_3_31.2
    · exact admissible_chunk_3_32.2
    · exact admissible_chunk_3_33.2
    · exact admissible_chunk_3_34.2
    · exact admissible_chunk_3_35.2
    · exact admissible_chunk_3_36.2
    · exact admissible_chunk_3_37.2
    · exact admissible_chunk_3_38.2
    · exact admissible_chunk_3_39.2

end ThreeBoundNumeric.Endpoint40

#print axioms ThreeBoundNumeric.Endpoint40.period_inequality
#print axioms ThreeBoundNumeric.Endpoint40.actual_base_upper
#print axioms ThreeBoundNumeric.Endpoint40.admissible0
#print axioms ThreeBoundNumeric.Endpoint40.admissible1
#print axioms ThreeBoundNumeric.Endpoint40.admissible2
#print axioms ThreeBoundNumeric.Endpoint40.admissible3


