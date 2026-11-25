-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_3
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54_3
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:36:25.93156+00:00
-- url     : https://prove2.me/theorems/8716991d-4026-5c66-a676-466f345b034a
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (3/11)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 3 of 11 (`harmBucketWork54_3`).
-- source:
--   Liu, Childs, Gottesman [LCG26], First and second quantization: reversible and quantum circuits (arXiv:2411.04019, Section IV.B–C); Krivcenko, Nguyen, de Wolf [KNW26] (arXiv:2609.40331, Theorem 5.4).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Comb
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Circs
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketHL54V2
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_1
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_2

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (3/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

lemma two_K_add_two_le_two_pow_lOf_sub_one {n K : ℕ} (h1n : 1 ≤ n) (_h1K : 1 ≤ K) :
    2 * K + 2 ≤ 2 ^ (lOf n K - 1) := by
  dsimp [lOf]
  have hle : 2 * K + 2 ≤ (K + 1) * (n + 1) + 2 := by nlinarith
  calc 2 * K + 2 ≤ (K + 1) * (n + 1) + 2 := hle
    _ ≤ 2 ^ Nat.clog 2 ((K + 1) * (n + 1) + 2) := Nat.le_pow_clog (by norm_num) _
    _ = 2 ^ (Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 - 1) := by simp

lemma clog_two_K_add_two_le {n K : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) :
    Nat.clog 2 (2 * K + 2) ≤ lOf n K - 1 := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  exact two_K_add_two_le_two_pow_lOf_sub_one h1n h1K

lemma one_le_dOccOf {K : ℕ} (h1K : 1 ≤ K) : 1 ≤ dOccOf K := by
  dsimp [dOccOf]
  have hnot : ¬ Nat.clog 2 (2 * K) ≤ 0 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    omega
  omega

lemma two_K_le_arity_dOcc {K : ℕ} : 2 * K ≤ arity (dOccOf K) := by
  rw [arity_eq_two_pow]
  exact Nat.le_pow_clog (by norm_num) _

lemma arity_dOcc_lt_four_K {K : ℕ} (h1K : 1 ≤ K) : arity (dOccOf K) < 4 * K := by
  have hd : 1 ≤ dOccOf K := one_le_dOccOf h1K
  have hnot : ¬ dOccOf K ≤ dOccOf K - 1 := by omega
  dsimp [dOccOf] at hnot
  rw [Nat.clog_le_iff_le_pow (by norm_num)] at hnot
  have hlt : 2 ^ (dOccOf K - 1) < 2 * K := by dsimp [dOccOf]; omega
  rw [arity_eq_two_pow]
  have hpow : 2 ^ dOccOf K = 2 * 2 ^ (dOccOf K - 1) := by
    conv_lhs => rw [show dOccOf K = (dOccOf K - 1) + 1 by omega]
    rw [pow_succ']
  omega

lemma dOcc_le_lOf {n K : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) : dOccOf K ≤ lOf n K := by
  have h1 : dOccOf K ≤ Nat.clog 2 (2 * K + 2) := Nat.clog_mono_right 2 (by omega)
  have h2 := clog_two_K_add_two_le h1n h1K
  omega

lemma two_le_clog_two_K_add_two {K : ℕ} (h1K : 1 ≤ K) : 2 ≤ Nat.clog 2 (2 * K + 2) := by
  have hnot : ¬ Nat.clog 2 (2 * K + 2) ≤ 1 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    omega
  omega

lemma three_le_dHbOf {K : ℕ} (h1K : 1 ≤ K) : 3 ≤ dHbOf K := by
  dsimp [dHbOf]
  have hc := two_le_clog_two_K_add_two h1K
  have hge : 6 ≤ 2 * K * Nat.clog 2 (2 * K + 2) + 2 := by nlinarith
  have hnot : ¬ Nat.clog 2 (2 * K * Nat.clog 2 (2 * K + 2) + 2) ≤ 2 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    omega
  omega

lemma two_K_lt_B2 {K : ℕ} (h1K : 1 ≤ K) : 2 * K < arity (dHbOf K) := by
  have hc := two_le_clog_two_K_add_two h1K
  have hle : 2 * K + 1 ≤ 2 * K * Nat.clog 2 (2 * K + 2) + 2 := by nlinarith
  have hpow := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * K * Nat.clog 2 (2 * K + 2) + 2)
  rw [arity_eq_two_pow]
  dsimp [dHbOf]
  omega

lemma bucketPairs_length_lt_B2 (comb : LcgSym54Comb) {K : ℕ} :
    (bucketPairs (2 * K)).length < arity (dHbOf K) := by
  have h1 := comb.bucketPairs_length (2 * K)
  have h2 := comb.harmonicBucketSum_le (2 * K)
  have hpow := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * K * Nat.clog 2 (2 * K + 2) + 2)
  rw [arity_eq_two_pow]
  dsimp [dHbOf]
  omega

lemma B2_le {n K : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) :
    arity (dHbOf K) ≤ 4 * K * lOf n K + 2 := by
  have hd : 3 ≤ Nat.clog 2 (2 * K * Nat.clog 2 (2 * K + 2) + 2) := three_le_dHbOf h1K
  set m := Nat.clog 2 (2 * K * Nat.clog 2 (2 * K + 2) + 2)
  have hnot : ¬ m ≤ m - 1 := by omega
  rw [Nat.clog_le_iff_le_pow (by norm_num)] at hnot
  have hlt : 2 ^ (m - 1) < 2 * K * Nat.clog 2 (2 * K + 2) + 2 := Nat.lt_of_not_ge hnot
  have hc := clog_two_K_add_two_le h1n h1K
  have hL := four_le_lOf h1n h1K
  have hclog_le : Nat.clog 2 (2 * K + 2) ≤ lOf n K := by omega
  have hmul : 2 * K * Nat.clog 2 (2 * K + 2) ≤ 2 * K * lOf n K :=
    Nat.mul_le_mul_left _ hclog_le
  have hbound : 2 ^ (m - 1) ≤ 2 * K * lOf n K + 1 :=
    Nat.le_of_lt_succ (lt_of_lt_of_le hlt (Nat.add_le_add_right hmul 2))
  rw [arity_eq_two_pow]
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have hm : 3 ≤ m := hd
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ']
  dsimp [dHbOf]
  rw [hpow]
  set P := 2 ^ (m - 1)
  set Q := 2 * K * lOf n K
  have hmulQ : 4 * K * lOf n K = 2 * Q := by dsimp [Q]; ring
  rw [hmulQ]
  omega

lemma add_one_le_two_pow {k : ℕ} (hk : 1 ≤ k) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0; norm_num
    · have ih' := ih (by omega)
      have hp : 1 ≤ 2 ^ k := Nat.two_pow_pos k
      rw [pow_succ, mul_two]
      omega

lemma dHb_le_two_mul_lOf {n K : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) :
    dHbOf K ≤ 2 * lOf n K := by
  dsimp [dHbOf]
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  have hL := four_le_lOf h1n h1K
  have h2K : 2 * K ≤ 2 ^ (lOf n K - 1) := by
    have := two_K_add_two_le_two_pow_lOf_sub_one h1n h1K; omega
  have hc : Nat.clog 2 (2 * K + 2) ≤ 2 ^ (lOf n K - 1) := by
    have h1 := clog_two_K_add_two_le h1n h1K
    have h2 := add_one_le_two_pow (k := lOf n K - 1) (by omega)
    omega
  have hpow_ge : 4 ≤ 2 ^ (lOf n K - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (lOf n K - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hprod : 2 * K * Nat.clog 2 (2 * K + 2) ≤ 2 ^ (lOf n K - 1) * 2 ^ (lOf n K - 1) :=
    Nat.mul_le_mul h2K hc
  have hsum_pow : 2 ^ (lOf n K - 1) * 2 ^ (lOf n K - 1) = 2 ^ (2 * lOf n K - 2) := by
    rw [← pow_add]; congr 1; omega
  have hbig : 2 ^ (2 * lOf n K) = 4 * 2 ^ (2 * lOf n K - 2) := by
    conv_lhs => rw [show 2 * lOf n K = (2 * lOf n K - 2) + 2 by omega]
    rw [pow_add]; ring
  have hpos : 2 ≤ 2 ^ (2 * lOf n K - 2) := by
    calc 2 ≤ 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * lOf n K - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma five_le_wOf {K : ℕ} (h1K : 1 ≤ K) : 5 ≤ wOf K := by
  have := three_le_dHbOf h1K
  dsimp [wOf]; omega

lemma wOf_le {n K : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) : wOf K ≤ 2 * lOf n K + 2 := by
  have := dHb_le_two_mul_lOf h1n h1K
  dsimp [wOf]; omega

lemma two_mul_B2_add_one_lt_two_pow_wOf {K : ℕ} (h1K : 1 ≤ K) :
    2 * arity (dHbOf K) + 1 < 2 ^ wOf K := by
  have hd : 3 ≤ Nat.clog 2 (2 * K * Nat.clog 2 (2 * K + 2) + 2) := three_le_dHbOf h1K
  have hB : 8 ≤ arity (dHbOf K) := by
    rw [arity_eq_two_pow]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ dHbOf K := Nat.pow_le_pow_right (by norm_num) hd
  dsimp only [wOf]
  have har := arity_eq_two_pow (dHbOf K)
  have hpow : 2 ^ (dHbOf K + 2) = 4 * arity (dHbOf K) := by
    rw [pow_add, har]; norm_num; ring
  rw [hpow]
  omega

/-! #### 5.2 Wire Layout (`harmBucketAncDef` & Block Embeddings) -/

abbrev wK1Occ (K : ℕ) : ℕ := 1 + wOf K + wOf K
abbrev wP1Occ (K : ℕ) : ℕ := wOf K
abbrev wR1Occ (K : ℕ) : ℕ := wK1Occ K + wP1Occ K

abbrev wK1Hb (K : ℕ) : ℕ := 1 + wOf K + wOf K + 2 + wOf K
abbrev wP1Hb (K : ℕ) : ℕ := 2 + wOf K + wOf K
abbrev wR1Hb (K : ℕ) : ℕ := wK1Hb K + wP1Hb K

abbrev wK2Hb (K : ℕ) : ℕ := 1 + wOf K + wOf K
abbrev wP2Hb (K : ℕ) : ℕ := 2 + wOf K
abbrev wR2Hb (K : ℕ) : ℕ := wK2Hb K + wP2Hb K

@[irreducible] def ancLen (n K _d ancAS : ℕ) (k : Fin 24) : ℕ :=
  match k.1 with
  | 0 => (2 * K) * wOf K                                -- 0: eM
  | 1 => (2 * K) * 1                                    -- 1: eAct
  | 2 => (2 * K) * wOf K                                -- 2: eOcc
  | 3 => arity (dOccOf K) * wR1Occ K                    -- 3: eRec1
  | 4 => sortTraceSize (dOccOf K)                       -- 4: eTr1
  | 5 => 1                                              -- 5: eEqFlag
  | 6 => 1                                              -- 6: eOne12
  | 7 => wK1Occ K                                       -- 7: eSort1Anc
  | 8 => 3                                              -- 8: eScanB
  | 9 => 1                                              -- 9: eScanCtrl
  | 10 => max (sOf n) (wOf K + 1)                       -- 10: eArith12
  | 11 => arity (dHbOf K + 1) * wR1Hb K                 -- 11: eRec2
  | 12 => sortTraceSize (dHbOf K + 1)                   -- 12: eTr2a
  | 13 => arity (dHbOf K + 1) * wR2Hb K                 -- 13: eRec3
  | 14 => sortTraceSize (dHbOf K + 1)                   -- 14: eTr2b
  | 15 => (2 * K) * wOf K                               -- 15: eD
  | 16 => wOf K                                         -- 16: eSubTmp
  | 17 => wK1Hb K                                       -- 17: eSort2aAnc
  | 18 => wK2Hb K                                       -- 18: eSort2bAnc
  | 19 => 4                                             -- 19: eSeqB
  | 20 => 1                                             -- 20: eSeqCtrl
  | 21 => 1                                             -- 21: eUnifCtrl
  | 22 => wOf K + 1                                     -- 22: eArith345
  | 23 => ancAS                                         -- 23: eAsAnc
  | _ => 0

lemma ancLen_0 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨0, by decide⟩ = (2 * K) * wOf K := by
  unfold ancLen; rfl
lemma ancLen_1 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨1, by decide⟩ = (2 * K) * 1 := by
  unfold ancLen; rfl
lemma ancLen_2 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨2, by decide⟩ = (2 * K) * wOf K := by
  unfold ancLen; rfl
lemma ancLen_3 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨3, by decide⟩ = arity (dOccOf K) * wR1Occ K := by
  unfold ancLen; rfl
lemma ancLen_4 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨4, by decide⟩ = sortTraceSize (dOccOf K) := by
  unfold ancLen; rfl
lemma ancLen_5 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨5, by decide⟩ = 1 := by
  unfold ancLen; rfl
lemma ancLen_6 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨6, by decide⟩ = 1 := by
  unfold ancLen; rfl
lemma ancLen_7 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨7, by decide⟩ = wK1Occ K := by
  unfold ancLen; rfl
lemma ancLen_8 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨8, by decide⟩ = 3 := by
  unfold ancLen; rfl
lemma ancLen_9 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨9, by decide⟩ = 1 := by
  unfold ancLen; rfl
lemma ancLen_10 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨10, by decide⟩ = max (sOf n) (wOf K + 1) := by
  unfold ancLen; rfl
lemma ancLen_11 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨11, by decide⟩ = arity (dHbOf K + 1) * wR1Hb K := by
  unfold ancLen; rfl
lemma ancLen_12 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨12, by decide⟩ = sortTraceSize (dHbOf K + 1) := by
  unfold ancLen; rfl
lemma ancLen_13 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨13, by decide⟩ = arity (dHbOf K + 1) * wR2Hb K := by
  unfold ancLen; rfl
lemma ancLen_14 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨14, by decide⟩ = sortTraceSize (dHbOf K + 1) := by
  unfold ancLen; rfl
lemma ancLen_15 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨15, by decide⟩ = (2 * K) * wOf K := by
  unfold ancLen; rfl
lemma ancLen_16 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨16, by decide⟩ = wOf K := by
  unfold ancLen; rfl
lemma ancLen_17 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨17, by decide⟩ = wK1Hb K := by
  unfold ancLen; rfl
lemma ancLen_18 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨18, by decide⟩ = wK2Hb K := by
  unfold ancLen; rfl
lemma ancLen_19 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨19, by decide⟩ = 4 := by
  unfold ancLen; rfl
lemma ancLen_20 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨20, by decide⟩ = 1 := by
  unfold ancLen; rfl
lemma ancLen_21 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨21, by decide⟩ = 1 := by
  unfold ancLen; rfl
lemma ancLen_22 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨22, by decide⟩ = wOf K + 1 := by
  unfold ancLen; rfl
lemma ancLen_23 (n K d ancAS : ℕ) : ancLen n K d ancAS ⟨23, by decide⟩ = ancAS := by
  unfold ancLen; rfl

@[irreducible] def ancOff (n K d ancAS : ℕ) (k : Fin 24) : ℕ :=
  ∑ j : Fin 24, if j.1 < k.1 then ancLen n K d ancAS j else 0

@[irreducible] def harmBucketAncDef (as : AlonsoSchottSil54) (n K d : ℕ) : ℕ :=
  ∑ j : Fin 24, ancLen n K d (as.alonsoSchottAnc (2 * K) d) j

abbrev totWiresDef (as : AlonsoSchottSil54) (n K d : ℕ) : ℕ :=
  (2 * K * sOf n + arity d * d) + harmBucketAncDef as n K d

lemma ancOff_add_ancLen_le_sum (n K d ancAS : ℕ) (k : Fin 24) :
    ancOff n K d ancAS k + ancLen n K d ancAS k ≤ ∑ j : Fin 24, ancLen n K d ancAS j := by
  unfold ancOff
  have hsum1 := Finset.sum_erase_add (Finset.univ : Finset (Fin 24))
    (fun j => if j.1 < k.1 then ancLen n K d ancAS j else 0) (Finset.mem_univ k)
  have hsum2 := Finset.sum_erase_add (Finset.univ : Finset (Fin 24))
    (fun j => if j.1 ≤ k.1 then ancLen n K d ancAS j else 0) (Finset.mem_univ k)
  calc (∑ j : Fin 24, if j.1 < k.1 then ancLen n K d ancAS j else 0) + ancLen n K d ancAS k
      = (∑ j ∈ Finset.univ.erase k, if j.1 < k.1 then ancLen n K d ancAS j else 0) +
          (if k.1 < k.1 then ancLen n K d ancAS k else 0) + ancLen n K d ancAS k := by
          rw [hsum1]
    _ = (∑ j ∈ Finset.univ.erase k, if j.1 ≤ k.1 then ancLen n K d ancAS j else 0) +
          (if k.1 ≤ k.1 then ancLen n K d ancAS k else 0) := by
          simp only [lt_self_iff_false, ↓reduceIte, le_refl, add_zero]
          congr 1
          refine Finset.sum_congr rfl fun j hj => ?_
          have hne : j ≠ k := (Finset.mem_erase.mp hj).1
          have hlt : j.1 < k.1 ↔ j.1 ≤ k.1 :=
            ⟨Nat.le_of_lt, fun hle => lt_of_le_of_ne hle (Fin.val_ne_of_ne hne)⟩
          simp [hlt]
    _ = ∑ j : Fin 24, if j.1 ≤ k.1 then ancLen n K d ancAS j else 0 := hsum2
    _ ≤ ∑ j : Fin 24, ancLen n K d ancAS j := by
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs <;> omega

lemma ancOff_add_ancLen_le_ancOff {n K d ancAS : ℕ} {k1 k2 : Fin 24} (h : k1.1 < k2.1) :
    ancOff n K d ancAS k1 + ancLen n K d ancAS k1 ≤ ancOff n K d ancAS k2 := by
  unfold ancOff
  have hsum2 := Finset.sum_erase_add (Finset.univ : Finset (Fin 24))
    (fun j => if j.1 < k2.1 then ancLen n K d ancAS j else 0) (Finset.mem_univ k1)
  have hsum1 := Finset.sum_erase_add (Finset.univ : Finset (Fin 24))
    (fun j => if j.1 < k1.1 then ancLen n K d ancAS j else 0) (Finset.mem_univ k1)
  have hle : (∑ j ∈ Finset.univ.erase k1, if j.1 < k1.1 then ancLen n K d ancAS j else 0) ≤
      ∑ j ∈ Finset.univ.erase k1, if j.1 < k2.1 then ancLen n K d ancAS j else 0 := by
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : j.1 < k1.1
    · have hj2 : j.1 < k2.1 := lt_trans hj h
      simp [hj, hj2]
    · simp [hj]
  rw [← hsum2, ← hsum1]
  simp only [lt_self_iff_false, ↓reduceIte, add_zero, h]
  omega

def eL (as : AlonsoSchottSil54) (n K d : ℕ) : Fin (2 * K * sOf n) ↪ Fin (totWiresDef as n K d) :=
  sliceEmb 0 (2 * K * sOf n) (by dsimp [totWiresDef]; omega)

def eOut (as : AlonsoSchottSil54) (n K d : ℕ) : Fin (arity d * d) ↪ Fin (totWiresDef as n K d) :=
  sliceEmb (2 * K * sOf n) (arity d * d) (by dsimp [totWiresDef]; omega)

def ancEmb (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) :
    Fin (ancLen n K d (as.alonsoSchottAnc (2 * K) d) k) ↪ Fin (totWiresDef as n K d) :=
  sliceEmb ((2 * K * sOf n + arity d * d) + ancOff n K d (as.alonsoSchottAnc (2 * K) d) k)
    (ancLen n K d (as.alonsoSchottAnc (2 * K) d) k)
    (by
      dsimp only [totWiresDef]
      unfold harmBucketAncDef
      have := ancOff_add_ancLen_le_sum n K d (as.alonsoSchottAnc (2 * K) d) k
      omega)

lemma eL_disjoint_eOut (as : AlonsoSchottSil54) (n K _d : ℕ) :
    ∀ i j, eL as n K _d i ≠ eOut as n K _d j :=
  sliceEmb_disjoint _ _ (Or.inl (by omega))

lemma eL_disjoint_anc (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) :
    ∀ i j, eL as n K d i ≠ ancEmb as n K d k j :=
  sliceEmb_disjoint _ _ (Or.inl (by omega))

lemma anc_disjoint_eL (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) :
    ∀ i j, ancEmb as n K d k i ≠ eL as n K d j :=
  fun i j h => eL_disjoint_anc as n K d k j i h.symm

lemma eOut_disjoint_anc (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) :
    ∀ i j, eOut as n K d i ≠ ancEmb as n K d k j :=
  sliceEmb_disjoint _ _ (Or.inl (by omega))

lemma anc_disjoint_eOut (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) :
    ∀ i j, ancEmb as n K d k i ≠ eOut as n K d j :=
  fun i j h => eOut_disjoint_anc as n K d k j i h.symm

lemma ancEmb_disjoint (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24} (hk : k1 ≠ k2) :
    ∀ i j, ancEmb as n K d k1 i ≠ ancEmb as n K d k2 j := by
  rcases Nat.lt_trichotomy k1.1 k2.1 with h12 | h12 | h21
  · exact sliceEmb_disjoint _ _ (Or.inl (by
      have := ancOff_add_ancLen_le_ancOff (n := n) (K := K) (d := d)
        (ancAS := as.alonsoSchottAnc (2 * K) d) h12
      omega))
  · exact absurd (Fin.ext h12) hk
  · exact sliceEmb_disjoint _ _ (Or.inr (by
      have := ancOff_add_ancLen_le_ancOff (n := n) (K := K) (d := d)
        (ancAS := as.alonsoSchottAnc (2 * K) d) h21
      omega))

/-! #### 5.3 Generic Array-Slot & Record-Field Helpers (No `Equiv.cast`) -/

def ancRegSlice (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r) :
    Fin (N_rec * w_r) ↪ Fin (totWiresDef as n K d) :=
  (sliceEmb 0 (N_rec * w_r) (by omega)).trans (ancEmb as n K d k)

lemma ancRegSlice_disjoint_anc (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N_rec * w_r) :
    ∀ i j, ancRegSlice as n K d k1 N_rec w_r hlen i ≠ ancEmb as n K d k2 j :=
  trans_disjoint_left (ancEmb_disjoint as n K d hk)

lemma anc_disjoint_ancRegSlice (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k2 ≠ k1) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N_rec * w_r) :
    ∀ i j, ancEmb as n K d k2 i ≠ ancRegSlice as n K d k1 N_rec w_r hlen j :=
  fun i j h => ancRegSlice_disjoint_anc as n K d hk.symm N_rec w_r hlen j i h.symm

def ancRegSlot (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r) (q : Fin N_rec) :
    Fin w_r ↪ Fin (totWiresDef as n K d) :=
  (slotInReg N_rec w_r q).trans (ancRegSlice as n K d k N_rec w_r hlen)

lemma ancRegSlot_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    {q1 q2 : Fin N_rec} (hq : q1 ≠ q2) :
    ∀ b1 b2, ancRegSlot as n K d k N_rec w_r hlen q1 b1 ≠
      ancRegSlot as n K d k N_rec w_r hlen q2 b2 := by
  intro b1 b2 h
  exact slotInReg_disjoint hq b1 b2 ((ancRegSlice as n K d k N_rec w_r hlen).injective h)

lemma ancRegSlot_disjoint_anc (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N_rec * w_r) (q : Fin N_rec) :
    ∀ i j, ancRegSlot as n K d k1 N_rec w_r hlen q i ≠ ancEmb as n K d k2 j :=
  trans_disjoint_left (ancRegSlice_disjoint_anc as n K d hk N_rec w_r hlen)

lemma anc_disjoint_ancRegSlot (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k2 ≠ k1) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N_rec * w_r) (q : Fin N_rec) :
    ∀ i j, ancEmb as n K d k2 i ≠ ancRegSlot as n K d k1 N_rec w_r hlen q j :=
  fun i j h => ancRegSlot_disjoint_anc as n K d hk.symm N_rec w_r hlen q j i h.symm

def ancRegField (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r) (q : Fin N_rec)
    (fOff fLen : ℕ) (hf : fOff + fLen ≤ w_r) :
    Fin fLen ↪ Fin (totWiresDef as n K d) :=
  (sliceEmb fOff fLen hf).trans (ancRegSlot as n K d k N_rec w_r hlen q)

lemma ancRegField_disjoint_field_same (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (N_rec w_r : ℕ) (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    (q : Fin N_rec) {o1 l1 o2 l2 : ℕ} (hf1 : o1 + l1 ≤ w_r) (hf2 : o2 + l2 ≤ w_r)
    (hdisj : o1 + l1 ≤ o2 ∨ o2 + l2 ≤ o1) :
    ∀ i j, ancRegField as n K d k N_rec w_r hlen q o1 l1 hf1 i ≠
      ancRegField as n K d k N_rec w_r hlen q o2 l2 hf2 j := by
  intro i j hij
  exact sliceEmb_disjoint hf1 hf2 hdisj i j ((ancRegSlot as n K d k N_rec w_r hlen q).injective hij)

lemma ancRegField_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (N_rec w_r : ℕ) (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    {q1 q2 : Fin N_rec} (hq : q1 ≠ q2) {o1 l1 o2 l2 : ℕ} (hf1 : o1 + l1 ≤ w_r) (hf2 : o2 + l2 ≤ w_r) :
    ∀ i j, ancRegField as n K d k N_rec w_r hlen q1 o1 l1 hf1 i ≠
      ancRegField as n K d k N_rec w_r hlen q2 o2 l2 hf2 j :=
  fun _ _ => ancRegSlot_disjoint_slot as n K d k N_rec w_r hlen hq _ _

lemma ancRegField_disjoint_anc (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N_rec * w_r) (q : Fin N_rec)
    (fOff fLen : ℕ) (hf : fOff + fLen ≤ w_r) :
    ∀ i j, ancRegField as n K d k1 N_rec w_r hlen q fOff fLen hf i ≠ ancEmb as n K d k2 j :=
  trans_disjoint_left (ancRegSlot_disjoint_anc as n K d hk N_rec w_r hlen q)

lemma anc_disjoint_ancRegField (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k2 ≠ k1) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N_rec * w_r) (q : Fin N_rec)
    (fOff fLen : ℕ) (hf : fOff + fLen ≤ w_r) :
    ∀ i j, ancEmb as n K d k2 i ≠ ancRegField as n K d k1 N_rec w_r hlen q fOff fLen hf j :=
  fun i j h => ancRegField_disjoint_anc as n K d hk.symm N_rec w_r hlen q fOff fLen hf j i h.symm

lemma comp_ancRegSlot (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    (z : Qubits (totWiresDef as n K d)) (arr : Fin N_rec → Qubits w_r)
    (hz : z ∘ ancRegSlice as n K d k N_rec w_r hlen = flatReg N_rec w_r arr)
    (q : Fin N_rec) :
    z ∘ ancRegSlot as n K d k N_rec w_r hlen q = arr q := by
  funext b
  have := congrFun hz (finProdFinEquiv (q, b))
  simpa [flatReg, ancRegSlot, Function.comp_apply] using this

lemma comp_ancRegField (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    (z : Qubits (totWiresDef as n K d)) (arr : Fin N_rec → Qubits w_r)
    (hz : z ∘ ancRegSlice as n K d k N_rec w_r hlen = flatReg N_rec w_r arr)
    (q : Fin N_rec) (fOff fLen : ℕ) (hf : fOff + fLen ≤ w_r) :
    z ∘ ancRegField as n K d k N_rec w_r hlen q fOff fLen hf =
      arr q ∘ sliceEmb fOff fLen hf := by
  funext i
  exact congrFun (comp_ancRegSlot as n K d k N_rec w_r hlen z arr hz q) (sliceEmb fOff fLen hf i)


end HarmBucketWork54


