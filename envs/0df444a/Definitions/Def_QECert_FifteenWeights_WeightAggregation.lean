-- Prove2me | Definitions.Def_QECert_FifteenWeights_WeightAggregation
-- name    : QECert_FifteenWeights_WeightAggregation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T01:02:57.877184+00:00
-- url     : https://prove2.me/theorems/6d902011-868f-4b64-8dc0-78a600625d22
-- title:
--   Code
-- statement:
--   Definitions and structural lemmas for Code, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Code.lean

import Definitions.Def_QECert_FifteenWeights_CountChunk0
import Definitions.Def_QECert_FifteenWeights_CountChunk1
import Definitions.Def_QECert_FifteenWeights_CountChunk2
import Definitions.Def_QECert_FifteenWeights_CountChunk3
import Definitions.Def_QECert_FifteenWeights_CountChunk4
import Definitions.Def_QECert_FifteenWeights_CountChunk5
import Definitions.Def_QECert_FifteenWeights_CountChunk6
import Definitions.Def_QECert_FifteenWeights_CountChunk7
import Definitions.Def_QECert_FifteenWeights_CountChunk8
import Definitions.Def_QECert_FifteenWeights_CountChunk9
import Definitions.Def_QECert_FifteenWeights_CountChunk10
import Definitions.Def_QECert_FifteenWeights_CountChunk11
import Definitions.Def_QECert_FifteenWeights_CountChunk12
import Definitions.Def_QECert_FifteenWeights_CountChunk13
import Definitions.Def_QECert_FifteenWeights_CountChunk14
import Definitions.Def_QECert_FifteenWeights_CountChunk15
import Definitions.Def_QECert_FifteenWeights_WeightChunk0
import Definitions.Def_QECert_FifteenWeights_WeightChunk1
import Definitions.Def_QECert_FifteenWeights_WeightChunk2
import Definitions.Def_QECert_FifteenWeights_WeightChunk3
import Definitions.Def_QECert_FifteenWeights_WeightChunk4
import Definitions.Def_QECert_FifteenWeights_WeightChunk5
import Definitions.Def_QECert_FifteenWeights_WeightChunk6
import Definitions.Def_QECert_FifteenWeights_WeightChunk7
import Definitions.Def_QECert_FifteenWeights_WeightChunk8
import Definitions.Def_QECert_FifteenWeights_WeightChunk9
import Definitions.Def_QECert_FifteenWeights_WeightChunk10
import Definitions.Def_QECert_FifteenWeights_WeightChunk11
import Definitions.Def_QECert_FifteenWeights_WeightChunk12
import Definitions.Def_QECert_FifteenWeights_WeightChunk13
import Definitions.Def_QECert_FifteenWeights_WeightChunk14
import Definitions.Def_QECert_FifteenWeights_WeightChunk15
set_option autoImplicit false
set_option maxHeartbeats 200000
open QEC QEC.Coding QEC.Distillation.BK15
open scoped BigOperators
namespace QEC.Distillation.BK15.CertifiedWeights
private theorem bitValue_injective {a b : Bool} (h : (if a then (1 : Bit) else 0) = (if b then (1 : Bit) else 0)) : a = b := by
  cases a <;> cases b <;> simp_all
private theorem coefficient_injective : Function.Injective (fun n : Fin 1024 => certificateCoefficient n.val) := by
  intro a b h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10
  · interval_cases i
    · exact bitValue_injective (congrFun h (Sum.inl (0 : Fin 4)))
    · exact bitValue_injective (congrFun h (Sum.inl (1 : Fin 4)))
    · exact bitValue_injective (congrFun h (Sum.inl (2 : Fin 4)))
    · exact bitValue_injective (congrFun h (Sum.inl (3 : Fin 4)))
    · apply bitValue_injective
      have hh := congrFun h ((Sum.inr ⟨(0, 1), by decide⟩) : Sum (Fin 4) QuadraticIndex)
      simpa [certificateCoefficient] using hh
    · apply bitValue_injective
      have hh := congrFun h ((Sum.inr ⟨(0, 2), by decide⟩) : Sum (Fin 4) QuadraticIndex)
      simpa [certificateCoefficient] using hh
    · apply bitValue_injective
      have hh := congrFun h ((Sum.inr ⟨(0, 3), by decide⟩) : Sum (Fin 4) QuadraticIndex)
      simpa [certificateCoefficient] using hh
    · apply bitValue_injective
      have hh := congrFun h ((Sum.inr ⟨(1, 2), by decide⟩) : Sum (Fin 4) QuadraticIndex)
      simpa [certificateCoefficient] using hh
    · apply bitValue_injective
      have hh := congrFun h ((Sum.inr ⟨(1, 3), by decide⟩) : Sum (Fin 4) QuadraticIndex)
      simpa [certificateCoefficient] using hh
    · apply bitValue_injective
      have hh := congrFun h ((Sum.inr ⟨(2, 3), by decide⟩) : Sum (Fin 4) QuadraticIndex)
      simpa [certificateCoefficient] using hh
  · have hle : 10 ≤ i := by omega
    have ha : a.val < 2 ^ i := lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) hle)
    have hb : b.val < 2 ^ i := lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) hle)
    rw [Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb]
private theorem coefficient_bijective : Function.Bijective (fun n : Fin 1024 => certificateCoefficient n.val) := by
  have hquad : Fintype.card QuadraticIndex = 6 := by decide +kernel
  have hcard : Fintype.card (Fin 1024) = Fintype.card (Sum (Fin 4) QuadraticIndex → Bit) := by
    simp [Fintype.card_fun, Fintype.card_sum, hquad, Bit]
  exact ⟨coefficient_injective, (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).1 coefficient_injective⟩
private theorem word_table_blocks (i : Fin 16) (j : Fin 64) : HammingWeight (l2CoefficientMap (certificateCoefficient (i.val * 64 + j.val))) = certificateWeightBlock i j := by
  fin_cases i
  · exact word_table_block_0 j
  · exact word_table_block_1 j
  · exact word_table_block_2 j
  · exact word_table_block_3 j
  · exact word_table_block_4 j
  · exact word_table_block_5 j
  · exact word_table_block_6 j
  · exact word_table_block_7 j
  · exact word_table_block_8 j
  · exact word_table_block_9 j
  · exact word_table_block_10 j
  · exact word_table_block_11 j
  · exact word_table_block_12 j
  · exact word_table_block_13 j
  · exact word_table_block_14 j
  · exact word_table_block_15 j
private theorem word_table (n : Fin 1024) : HammingWeight (l2CoefficientMap (certificateCoefficient n.val)) = certificateWeightBlock ⟨n.val / 64, by omega⟩ ⟨n.val % 64, Nat.mod_lt _ (by decide)⟩ := by
  let i : Fin 16 := ⟨n.val / 64, by omega⟩
  let j : Fin 64 := ⟨n.val % 64, Nat.mod_lt _ (by decide)⟩
  have hn : i.val * 64 + j.val = n.val := by dsimp [i, j]; omega
  have heq := word_table_blocks i j
  rw [hn] at heq
  exact heq
private theorem tables_same : certificateWeightBlock = certificateWeightBlock := rfl
private def blockGrid : Fin 1024 ≃ Fin 16 × Fin 64 where
  toFun n := (⟨n.val / 64, by omega⟩, ⟨n.val % 64, Nat.mod_lt _ (by decide)⟩)
  invFun p := ⟨p.1.val * 64 + p.2.val, by omega⟩
  left_inv n := by apply Fin.ext; dsimp; omega
  right_inv p := by
    apply Prod.ext
    · apply Fin.ext; dsimp; omega
    · apply Fin.ext; dsimp; omega
private theorem count_split (weight : Nat) :
    ((Finset.univ : Finset (Fin 1024)).filter (fun n => certificateWeightBlock (blockGrid n).1 (blockGrid n).2 = weight)).card =
      ∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = weight)).card := by
  rw [Finset.card_filter]
  calc
    _ = ∑ p : Fin 16 × Fin 64, if certificateWeightBlock p.1 p.2 = weight then 1 else 0 :=
      Fintype.sum_equiv blockGrid _ _ (fun _ => rfl)
    _ = ∑ i : Fin 16, ∑ j : Fin 64, if certificateWeightBlock i j = weight then 1 else 0 :=
      Fintype.sum_prod_type _
    _ = _ := by simp only [Finset.card_filter]
private theorem counts_0 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 0)).card = (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_0
  · exact block_count_1_0
  · exact block_count_2_0
  · exact block_count_3_0
  · exact block_count_4_0
  · exact block_count_5_0
  · exact block_count_6_0
  · exact block_count_7_0
  · exact block_count_8_0
  · exact block_count_9_0
  · exact block_count_10_0
  · exact block_count_11_0
  · exact block_count_12_0
  · exact block_count_13_0
  · exact block_count_14_0
  · exact block_count_15_0
private theorem total_0 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 0)).card) = 1 := by
  simp_rw [counts_0]
  decide +kernel
private theorem counts_1 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 1)).card = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_1
  · exact block_count_1_1
  · exact block_count_2_1
  · exact block_count_3_1
  · exact block_count_4_1
  · exact block_count_5_1
  · exact block_count_6_1
  · exact block_count_7_1
  · exact block_count_8_1
  · exact block_count_9_1
  · exact block_count_10_1
  · exact block_count_11_1
  · exact block_count_12_1
  · exact block_count_13_1
  · exact block_count_14_1
  · exact block_count_15_1
private theorem total_1 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 1)).card) = 0 := by
  simp_rw [counts_1]
  decide +kernel
private theorem counts_2 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 2)).card = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_2
  · exact block_count_1_2
  · exact block_count_2_2
  · exact block_count_3_2
  · exact block_count_4_2
  · exact block_count_5_2
  · exact block_count_6_2
  · exact block_count_7_2
  · exact block_count_8_2
  · exact block_count_9_2
  · exact block_count_10_2
  · exact block_count_11_2
  · exact block_count_12_2
  · exact block_count_13_2
  · exact block_count_14_2
  · exact block_count_15_2
private theorem total_2 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 2)).card) = 0 := by
  simp_rw [counts_2]
  decide +kernel
private theorem counts_3 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 3)).card = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_3
  · exact block_count_1_3
  · exact block_count_2_3
  · exact block_count_3_3
  · exact block_count_4_3
  · exact block_count_5_3
  · exact block_count_6_3
  · exact block_count_7_3
  · exact block_count_8_3
  · exact block_count_9_3
  · exact block_count_10_3
  · exact block_count_11_3
  · exact block_count_12_3
  · exact block_count_13_3
  · exact block_count_14_3
  · exact block_count_15_3
private theorem total_3 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 3)).card) = 0 := by
  simp_rw [counts_3]
  decide +kernel
private theorem counts_4 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 4)).card = (![9, 12, 12, 0, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_4
  · exact block_count_1_4
  · exact block_count_2_4
  · exact block_count_3_4
  · exact block_count_4_4
  · exact block_count_5_4
  · exact block_count_6_4
  · exact block_count_7_4
  · exact block_count_8_4
  · exact block_count_9_4
  · exact block_count_10_4
  · exact block_count_11_4
  · exact block_count_12_4
  · exact block_count_13_4
  · exact block_count_14_4
  · exact block_count_15_4
private theorem total_4 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 4)).card) = 105 := by
  simp_rw [counts_4]
  decide +kernel
private theorem counts_5 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 5)).card = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_5
  · exact block_count_1_5
  · exact block_count_2_5
  · exact block_count_3_5
  · exact block_count_4_5
  · exact block_count_5_5
  · exact block_count_6_5
  · exact block_count_7_5
  · exact block_count_8_5
  · exact block_count_9_5
  · exact block_count_10_5
  · exact block_count_11_5
  · exact block_count_12_5
  · exact block_count_13_5
  · exact block_count_14_5
  · exact block_count_15_5
private theorem total_5 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 5)).card) = 0 := by
  simp_rw [counts_5]
  decide +kernel
private theorem counts_6 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 6)).card = (![0, 0, 0, 40, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_6
  · exact block_count_1_6
  · exact block_count_2_6
  · exact block_count_3_6
  · exact block_count_4_6
  · exact block_count_5_6
  · exact block_count_6_6
  · exact block_count_7_6
  · exact block_count_8_6
  · exact block_count_9_6
  · exact block_count_10_6
  · exact block_count_11_6
  · exact block_count_12_6
  · exact block_count_13_6
  · exact block_count_14_6
  · exact block_count_15_6
private theorem total_6 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 6)).card) = 280 := by
  simp_rw [counts_6]
  decide +kernel
private theorem counts_7 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 7)).card = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_7
  · exact block_count_1_7
  · exact block_count_2_7
  · exact block_count_3_7
  · exact block_count_4_7
  · exact block_count_5_7
  · exact block_count_6_7
  · exact block_count_7_7
  · exact block_count_8_7
  · exact block_count_9_7
  · exact block_count_10_7
  · exact block_count_11_7
  · exact block_count_12_7
  · exact block_count_13_7
  · exact block_count_14_7
  · exact block_count_15_7
private theorem total_7 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 7)).card) = 0 := by
  simp_rw [counts_7]
  decide +kernel
private theorem counts_8 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 8)).card = (![51, 48, 48, 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_8
  · exact block_count_1_8
  · exact block_count_2_8
  · exact block_count_3_8
  · exact block_count_4_8
  · exact block_count_5_8
  · exact block_count_6_8
  · exact block_count_7_8
  · exact block_count_8_8
  · exact block_count_9_8
  · exact block_count_10_8
  · exact block_count_11_8
  · exact block_count_12_8
  · exact block_count_13_8
  · exact block_count_14_8
  · exact block_count_15_8
private theorem total_8 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 8)).card) = 435 := by
  simp_rw [counts_8]
  decide +kernel
private theorem counts_9 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 9)).card = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_9
  · exact block_count_1_9
  · exact block_count_2_9
  · exact block_count_3_9
  · exact block_count_4_9
  · exact block_count_5_9
  · exact block_count_6_9
  · exact block_count_7_9
  · exact block_count_8_9
  · exact block_count_9_9
  · exact block_count_10_9
  · exact block_count_11_9
  · exact block_count_12_9
  · exact block_count_13_9
  · exact block_count_14_9
  · exact block_count_15_9
private theorem total_9 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 9)).card) = 0 := by
  simp_rw [counts_9]
  decide +kernel
private theorem counts_10 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 10)).card = (![0, 0, 0, 24, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_10
  · exact block_count_1_10
  · exact block_count_2_10
  · exact block_count_3_10
  · exact block_count_4_10
  · exact block_count_5_10
  · exact block_count_6_10
  · exact block_count_7_10
  · exact block_count_8_10
  · exact block_count_9_10
  · exact block_count_10_10
  · exact block_count_11_10
  · exact block_count_12_10
  · exact block_count_13_10
  · exact block_count_14_10
  · exact block_count_15_10
private theorem total_10 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 10)).card) = 168 := by
  simp_rw [counts_10]
  decide +kernel
private theorem counts_11 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 11)).card = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_11
  · exact block_count_1_11
  · exact block_count_2_11
  · exact block_count_3_11
  · exact block_count_4_11
  · exact block_count_5_11
  · exact block_count_6_11
  · exact block_count_7_11
  · exact block_count_8_11
  · exact block_count_9_11
  · exact block_count_10_11
  · exact block_count_11_11
  · exact block_count_12_11
  · exact block_count_13_11
  · exact block_count_14_11
  · exact block_count_15_11
private theorem total_11 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 11)).card) = 0 := by
  simp_rw [counts_11]
  decide +kernel
private theorem counts_12 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 12)).card = (![3, 4, 4, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_12
  · exact block_count_1_12
  · exact block_count_2_12
  · exact block_count_3_12
  · exact block_count_4_12
  · exact block_count_5_12
  · exact block_count_6_12
  · exact block_count_7_12
  · exact block_count_8_12
  · exact block_count_9_12
  · exact block_count_10_12
  · exact block_count_11_12
  · exact block_count_12_12
  · exact block_count_13_12
  · exact block_count_14_12
  · exact block_count_15_12
private theorem total_12 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 12)).card) = 35 := by
  simp_rw [counts_12]
  decide +kernel
private theorem counts_13 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 13)).card = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_13
  · exact block_count_1_13
  · exact block_count_2_13
  · exact block_count_3_13
  · exact block_count_4_13
  · exact block_count_5_13
  · exact block_count_6_13
  · exact block_count_7_13
  · exact block_count_8_13
  · exact block_count_9_13
  · exact block_count_10_13
  · exact block_count_11_13
  · exact block_count_12_13
  · exact block_count_13_13
  · exact block_count_14_13
  · exact block_count_15_13
private theorem total_13 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 13)).card) = 0 := by
  simp_rw [counts_13]
  decide +kernel
private theorem counts_14 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 14)).card = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_14
  · exact block_count_1_14
  · exact block_count_2_14
  · exact block_count_3_14
  · exact block_count_4_14
  · exact block_count_5_14
  · exact block_count_6_14
  · exact block_count_7_14
  · exact block_count_8_14
  · exact block_count_9_14
  · exact block_count_10_14
  · exact block_count_11_14
  · exact block_count_12_14
  · exact block_count_13_14
  · exact block_count_14_14
  · exact block_count_15_14
private theorem total_14 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 14)).card) = 0 := by
  simp_rw [counts_14]
  decide +kernel
private theorem counts_15 (i : Fin 16) : ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 15)).card = (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 16 → Nat) i := by
  fin_cases i
  · exact block_count_0_15
  · exact block_count_1_15
  · exact block_count_2_15
  · exact block_count_3_15
  · exact block_count_4_15
  · exact block_count_5_15
  · exact block_count_6_15
  · exact block_count_7_15
  · exact block_count_8_15
  · exact block_count_9_15
  · exact block_count_10_15
  · exact block_count_11_15
  · exact block_count_12_15
  · exact block_count_13_15
  · exact block_count_14_15
  · exact block_count_15_15
private theorem total_15 : (∑ i : Fin 16, ((Finset.univ : Finset (Fin 64)).filter (fun j => certificateWeightBlock i j = 15)).card) = 0 := by
  simp_rw [counts_15]
  decide +kernel
private theorem table_enumerator (weight : Fin 16) : ((Finset.univ : Finset (Fin 1024)).filter (fun n => certificateWeightBlock (blockGrid n).1 (blockGrid n).2 = weight.val)).card = if weight = 0 then 1 else if weight = 4 then 105 else if weight = 6 then 280 else if weight = 8 then 435 else if weight = 10 then 168 else if weight = 12 then 35 else 0 := by
  rw [count_split]
  fin_cases weight
  · exact total_0
  · exact total_1
  · exact total_2
  · exact total_3
  · exact total_4
  · exact total_5
  · exact total_6
  · exact total_7
  · exact total_8
  · exact total_9
  · exact total_10
  · exact total_11
  · exact total_12
  · exact total_13
  · exact total_14
  · exact total_15
private theorem word_enumerator (weight : Fin 16) : ((Finset.univ : Finset (Fin 1024)).filter (fun n => HammingWeight (l2CoefficientMap (certificateCoefficient n.val)) = weight.val)).card = if weight = 0 then 1 else if weight = 4 then 105 else if weight = 6 then 280 else if weight = 8 then 435 else if weight = 10 then 168 else if weight = 12 then 35 else 0 := by
  simp_rw [word_table]
  exact table_enumerator weight

private theorem card_filter_transport {α β : Type} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Bijective f) (p : β → Prop) [DecidablePred p] :
    ((Finset.univ : Finset α).filter (fun a => p (f a))).card =
      ((Finset.univ : Finset β).filter p).card := by
  classical
  apply Finset.card_bij (fun a _ => f a)
  · intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  · intro a ha b hb hab
    exact hf.1 hab
  · intro b hb
    obtain ⟨a, rfl⟩ := hf.2 b
    exact ⟨a, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb, rfl⟩
private theorem bridge_coefficient_bijective :
    Function.Bijective (fun n : Fin 1024 => certificateCoefficient n.val) := coefficient_bijective
theorem coefficient_enumerator (weight : Fin 16) : ((Finset.univ : Finset (Sum (Fin 4) QuadraticIndex → Bit)).filter (fun a => HammingWeight (l2CoefficientMap a) = weight.val)).card = if weight = 0 then 1 else if weight = 4 then 105 else if weight = 6 then 280 else if weight = 8 then 435 else if weight = 10 then 168 else if weight = 12 then 35 else 0 := by
  have h := card_filter_transport (fun n : Fin 1024 => certificateCoefficient n.val) bridge_coefficient_bijective (fun a => HammingWeight (l2CoefficientMap a) = weight.val)
  exact h.symm.trans (word_enumerator weight)
private theorem binary_complement : ∀ b : Bit, b + 1 ≠ 0 ↔ b = 0 := by
  decide +kernel
private theorem support_complement (w : Word) :
    hammingSupport (w + allOnes) = Finset.univ \ hammingSupport w := by
  ext i
  simp [hammingSupport, allOnes, binary_complement]
private theorem weight_complement (w : Word) :
    HammingWeight (w + allOnes) = 15 - HammingWeight w := by
  unfold HammingWeight
  rw [support_complement, Finset.card_sdiff]
  simp
private theorem weight_le (w : Word) : HammingWeight w ≤ 15 := by
  unfold HammingWeight hammingSupport
  exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
theorem coset_coefficient_enumerator (weight : Fin 16) :
    ((Finset.univ : Finset (Sum (Fin 4) QuadraticIndex → Bit)).filter
      (fun a => HammingWeight (l2CoefficientMap a + allOnes) = weight.val)).card =
      if weight = 3 then 35 else if weight = 5 then 168 else
      if weight = 7 then 435 else if weight = 9 then 280 else
      if weight = 11 then 105 else if weight = 15 then 1 else 0 := by
  have hp (a : Sum (Fin 4) QuadraticIndex → Bit) :
      HammingWeight (l2CoefficientMap a + allOnes) = weight.val ↔
        HammingWeight (l2CoefficientMap a) = 15 - weight.val := by
    rw [weight_complement]
    have := weight_le (l2CoefficientMap a)
    have := weight.isLt
    omega
  have hf : ((Finset.univ : Finset (Sum (Fin 4) QuadraticIndex → Bit)).filter
      (fun a => HammingWeight (l2CoefficientMap a + allOnes) = weight.val)) =
      ((Finset.univ : Finset (Sum (Fin 4) QuadraticIndex → Bit)).filter
      (fun a => HammingWeight (l2CoefficientMap a) = 15 - weight.val)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp]
  rw [hf]
  have h := coefficient_enumerator (⟨15 - weight.val, by omega⟩ : Fin 16)
  fin_cases weight <;> exact h
private theorem sum_bit (f : Bit → Nat) : (∑ b : Bit, f b) = f 0 + f 1 := by
  have hu : (Finset.univ : Finset Bit) = {0, 1} := by decide +kernel
  rw [hu]
  simp
private theorem pair_bit_count {α : Type} [Fintype α] (f : α × Bit → Nat) (weight : Nat) :
    ((Finset.univ : Finset (α × Bit)).filter (fun x => f x = weight)).card =
      ((Finset.univ : Finset α).filter (fun a => f (a, 0) = weight)).card +
      ((Finset.univ : Finset α).filter (fun a => f (a, 1) = weight)).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp_rw [sum_bit]
  rw [Finset.sum_add_distrib]
  simp only [Finset.card_filter]
theorem dual_coefficient_enumerator (weight : Fin 16) :
    ((Finset.univ : Finset ((Sum (Fin 4) QuadraticIndex → Bit) × Bit)).filter
      (fun a => HammingWeight (l1DualCoefficientMap a) = weight.val)).card =
      if weight = 0 then 1 else if weight = 3 then 35 else
      if weight = 4 then 105 else if weight = 5 then 168 else
      if weight = 6 then 280 else if weight = 7 then 435 else
      if weight = 8 then 435 else if weight = 9 then 280 else
      if weight = 10 then 168 else if weight = 11 then 105 else
      if weight = 12 then 35 else if weight = 15 then 1 else 0 := by
  rw [pair_bit_count]
  simp only [l1DualCoefficientMap, LinearMap.coe_mk, AddHom.coe_mk,
    zero_smul, add_zero, one_smul]
  rw [coefficient_enumerator weight, coset_coefficient_enumerator weight]
  fin_cases weight <;> decide

end QEC.Distillation.BK15.CertifiedWeights


