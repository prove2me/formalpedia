-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_9
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54_9
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:52:59.671142+00:00
-- url     : https://prove2.me/theorems/26cdf244-853c-4182-acd0-727979b975bc
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (9/11)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 9 of 11 (`harmBucketWork54_9`).
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
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_3
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_4
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_5
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_6
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_7
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_8

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (9/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

def hbInitSlotCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (q : ℕ) (hq : q < arity (dHbOf K + 1)) : LayeredCircuit (totWiresDef as n K d) :=
  let qF : Fin (arity (dHbOf K + 1)) := ⟨q, hq⟩
  let w := wOf K
  if hq2 : q < 2 * K then
    let c1 := (arith.copyRegCircuit 1).mapWires
      (combineEmb (eActSlot as n K d ⟨q, hq2⟩) (eRec2Inact as n K d qF) (eActSlot_disjoint_eRec2Inact as n K d _ _))
    let c2 := (arith.setConstMSBCircuit 1 1).mapWires (eRec2Inact as n K d qF)
    let c3 := (arith.ctrlCopyRegCircuit w).mapWires
      (comb3 (eActSlot as n K d ⟨q, hq2⟩) (eMSlot as n K d ⟨q, hq2⟩) (eRec2M as n K d qF)
        (eActSlot_disjoint_eMSlot as n K d _ _)
        (eActSlot_disjoint_eRec2M as n K d _ _)
        (eMSlot_disjoint_eRec2M as n K d _ _))
    let c4 := (arith.ctrlCopyRegCircuit w).mapWires
      (comb3 (eActSlot as n K d ⟨q, hq2⟩) (eOccSlot as n K d ⟨q, hq2⟩) (eRec2Occ as n K d qF)
        (eActSlot_disjoint_eOccSlot as n K d _ _)
        (eActSlot_disjoint_eRec2Occ as n K d _ _)
        (eOccSlot_disjoint_eRec2Occ as n K d _ _))
    let c5 := (arith.setConstMSBCircuit 2 2).mapWires (eRec2KR1 as n K d qF)
    let c6 := (arith.ctrlConstXorMSBCircuit 2 2).mapWires
      (combineEmb (eActSlot as n K d ⟨q, hq2⟩) (eRec2KR1 as n K d qF) (eActSlot_disjoint_eRec2KR1 as n K d _ _))
    let c7 := (arith.setConstMSBCircuit w q).mapWires (eRec2Orig as n K d qF)
    let c8 := (arith.setConstMSBCircuit 2 3).mapWires (eRec2Kind as n K d qF)
    let c9 := (arith.ctrlConstXorMSBCircuit 2 3).mapWires
      (combineEmb (eActSlot as n K d ⟨q, hq2⟩) (eRec2Kind as n K d qF) (eActSlot_disjoint_eRec2Kind as n K d _ _))
    LayeredCircuit.seqList [c1, c2, c3, c4, c5, c6, c7, c8, c9]
  else if _hqB : q < arity (dHbOf K) then
    let c1 := (arith.setConstMSBCircuit 1 1).mapWires (eRec2Inact as n K d qF)
    let c2 := (arith.setConstMSBCircuit 2 2).mapWires (eRec2KR1 as n K d qF)
    let c3 := (arith.setConstMSBCircuit w q).mapWires (eRec2Orig as n K d qF)
    let c4 := (arith.setConstMSBCircuit 2 3).mapWires (eRec2Kind as n K d qF)
    LayeredCircuit.seqList [c1, c2, c3, c4]
  else
    let b := q - arity (dHbOf K)
    let pair := bucketPairs (2 * K)
    let mb := if hb : b < pair.length then pair[b].1 else 2 * K + 1 + b
    let occb := if hb : b < pair.length then pair[b].2 else 0
    let c1 := (arith.setConstMSBCircuit w mb).mapWires (eRec2M as n K d qF)
    let c2 := (arith.setConstMSBCircuit w occb).mapWires (eRec2Occ as n K d qF)
    let c3 := (arith.setConstMSBCircuit 2 1).mapWires (eRec2KR1 as n K d qF)
    let c4 := (arith.setConstMSBCircuit w q).mapWires (eRec2Orig as n K d qF)
    let c5 := (arith.setConstMSBCircuit 2 1).mapWires (eRec2Kind as n K d qF)
    let c6 := (arith.setConstMSBCircuit w b).mapWires (eRec2Dest as n K d qF)
    LayeredCircuit.seqList [c1, c2, c3, c4, c5, c6]

lemma hbInit_length {α : Type*} [LinearOrder α] (N B2 : ℕ) (l : Fin N → α) :
    (hbInit N B2 l).length = 2 * B2 := by
  dsimp [hbInit]; rw [List.length_append, List.length_map, List.length_map, List.length_finRange]; omega

noncomputable def hbInitArr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (q : Fin (arity (dHbOf K + 1))) :
    Qubits (wR1Hb K) :=
  hbRecToBits (wOf K)
    ((hbInit (2 * K) (arity (dHbOf K)) l)[q.1]'(by
      rw [hbInit_length]; exact Nat.lt_of_lt_of_eq q.isLt (arity_succ_eq _)))
    (fun _ => false)

lemma hbInit_getElem_lt_2K {n K : ℕ} (l : Fin (2 * K) → Fin (n + 1)) {q : ℕ}
    (hq2 : q < 2 * K) (hqB : q < arity (dHbOf K))
    (hqLen : q < (hbInit (2 * K) (arity (dHbOf K)) l).length) :
    (hbInit (2 * K) (arity (dHbOf K)) l)[q]'hqLen =
      if 2 ≤ runOffset l ⟨q, hq2⟩ then
        { kind := 0, m := runOffset l ⟨q, hq2⟩, occ := runOcc l ⟨q, hq2⟩, dest := 0, orig := q }
      else { kind := 3, m := 0, occ := 0, dest := 0, orig := q } := by
  revert hqLen; dsimp only [hbInit]; intro hqLen
  rw [List.getElem_append_left (by rw [List.length_map, List.length_finRange]; exact hqB),
    List.getElem_map, List.getElem_finRange]
  simp only [Fin.val_cast, dif_pos hq2]

lemma hbInit_getElem_mid {n K : ℕ} (l : Fin (2 * K) → Fin (n + 1)) {q : ℕ}
    (hq2 : ¬ q < 2 * K) (hqB : q < arity (dHbOf K))
    (hqLen : q < (hbInit (2 * K) (arity (dHbOf K)) l).length) :
    (hbInit (2 * K) (arity (dHbOf K)) l)[q]'hqLen =
      { kind := 3, m := 0, occ := 0, dest := 0, orig := q } := by
  revert hqLen; dsimp only [hbInit]; intro hqLen
  rw [List.getElem_append_left (by rw [List.length_map, List.length_finRange]; exact hqB),
    List.getElem_map, List.getElem_finRange]
  simp only [Fin.val_cast, dif_neg hq2]

lemma hbInit_getElem_ge_B2 {n K : ℕ} (l : Fin (2 * K) → Fin (n + 1)) {q : ℕ}
    (hqB : ¬ q < arity (dHbOf K)) (hqN : q < arity (dHbOf K + 1))
    (hqLen : q < (hbInit (2 * K) (arity (dHbOf K)) l).length) :
    (hbInit (2 * K) (arity (dHbOf K)) l)[q]'hqLen =
      if hb : q - arity (dHbOf K) < (bucketPairs (2 * K)).length then
        { kind := 1,
          m := ((bucketPairs (2 * K))[q - arity (dHbOf K)]'hb).1,
          occ := ((bucketPairs (2 * K))[q - arity (dHbOf K)]'hb).2,
          dest := q - arity (dHbOf K), orig := q }
      else
        { kind := 1, m := 2 * K + 1 + (q - arity (dHbOf K)), occ := 0,
          dest := q - arity (dHbOf K), orig := q } := by
  have hq_ge : arity (dHbOf K) ≤ q := by omega
  have hq_sub : q - arity (dHbOf K) < arity (dHbOf K) := by
    have := Nat.lt_of_lt_of_eq hqN (arity_succ_eq _); omega
  have hBadd : arity (dHbOf K) + (q - arity (dHbOf K)) = q := by omega
  revert hqLen; dsimp only [hbInit]; intro hqLen
  rw [List.getElem_append_right (by rw [List.length_map, List.length_finRange]; exact hq_ge),
    List.getElem_map, List.getElem_finRange]
  simp only [List.length_map, List.length_finRange, Fin.val_cast]
  by_cases hb : q - arity (dHbOf K) < (bucketPairs (2 * K)).length
  · rw [dif_pos hb, dif_pos hb, hBadd]
  · rw [dif_neg hb, dif_neg hb, hBadd]

lemma eRec2Slot_disjoint_eActSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) (i : Fin (2 * K)) :
    ∀ a b, ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q a ≠
      eActSlot as n K d i b :=
  trans_disjoint_right (trans_disjoint_right
    (ancRegSlot_disjoint_anc as n K d (k2 := ⟨1, by decide⟩) (by decide) _ _ (ancLen_11 n K d _) q))

lemma eRec2Slot_disjoint_eMSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) (i : Fin (2 * K)) :
    ∀ a b, ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q a ≠
      eMSlot as n K d i b :=
  trans_disjoint_right (trans_disjoint_right
    (ancRegSlot_disjoint_anc as n K d (k2 := ⟨0, by decide⟩) (by decide) _ _ (ancLen_11 n K d _) q))

lemma eRec2Slot_disjoint_eOccSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) (i : Fin (2 * K)) :
    ∀ a b, ancRegSlot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q a ≠
      eOccSlot as n K d i b :=
  trans_disjoint_right (trans_disjoint_right
    (ancRegSlot_disjoint_anc as n K d (k2 := ⟨2, by decide⟩) (by decide) _ _ (ancLen_11 n K d _) q))

def hbInitCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) :
    LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList ((List.range (arity (dHbOf K + 1))).map fun q =>
    if hq : q < arity (dHbOf K + 1) then hbInitSlotCirc as arith n K d q hq else LayeredCircuit.id _)

def sortHb1Circ (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ) :
    LayeredCircuit (totWiresDef as n K d) :=
  (br.bitonicSortKeyCircuit (dHbOf K + 1) (wK1Hb K) (wP1Hb K) true).mapWires
    (packDTA54Emb (eRec2 as n K d) (eTr2a as n K d) (eSort2aAnc as n K d)
      (eRec2_disjoint_eTr2a as n K d)
      (eRec2_disjoint_eSort2aAnc as n K d)
      (eTr2a_disjoint_eSort2aAnc as n K d))

noncomputable def rec2SortedArr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    Fin (arity (dHbOf K + 1)) → Qubits (wR1Hb K) :=
  sort (fun r => bitsToNat (recKey54 r)) (dHbOf K + 1) true (hbInitArr K l)

noncomputable def rec2SortTr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    Fin (sortTraceSize (dHbOf K + 1)) → Bool :=
  sortTrace (fun r => bitsToNat (recKey54 r)) (dHbOf K + 1) true (hbInitArr K l)

def hb1SortedList (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) : List HBRec :=
  (hbInit (2 * K) (arity (dHbOf K)) l).mergeSort (fun x y => decide (hbKey1 x ≤ hbKey1 y))

lemma hbInit_map_orig {α : Type*} [LinearOrder α] (N B2 : ℕ) (l : Fin N → α) :
    (hbInit N B2 l).map (·.orig) = List.range (2 * B2) := by
  dsimp [hbInit]
  rw [List.map_append, List.map_map, List.map_map]
  have h1 : (List.finRange B2).map ((fun r : HBRec => r.orig) ∘ fun i : Fin B2 =>
      if h : i.1 < N then
        if 2 ≤ runOffset l ⟨i.1, h⟩ then
          { kind := 0, m := runOffset l ⟨i.1, h⟩, occ := runOcc l ⟨i.1, h⟩, dest := 0, orig := i.1 }
        else { kind := 3, m := 0, occ := 0, dest := 0, orig := i.1 }
      else { kind := 3, m := 0, occ := 0, dest := 0, orig := i.1 }) = List.range B2 := by
    apply List.ext_getElem <;> simp
    intro i hi; split_ifs <;> rfl
  have h2 : (List.finRange B2).map ((fun r : HBRec => r.orig) ∘ fun b : Fin B2 =>
      if _hb : b.1 < (bucketPairs N).length then
        { kind := 1, m := (bucketPairs N)[b.1].1, occ := (bucketPairs N)[b.1].2, dest := b.1, orig := B2 + b.1 }
      else { kind := 1, m := N + 1 + b.1, occ := 0, dest := b.1, orig := B2 + b.1 }) =
      (List.range B2).map (B2 + ·) := by
    apply List.ext_getElem <;> simp
    intro i hi; split_ifs <;> rfl
  rw [h1, h2, show 2 * B2 = B2 + B2 by omega, List.range_add]

lemma hbInit_bounds (comb : LcgSym54Comb) {n K : ℕ} (h1K : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1)) :
    ∀ r ∈ hbInit (2 * K) (arity (dHbOf K)) l,
      r.kind ≤ 3 ∧ r.kind ≠ 2 ∧ (r.kind = 0 → r.dest = 0) ∧
      r.m < 2 ^ wOf K ∧ r.occ < 2 ^ wOf K ∧ r.dest < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K := by
  have h2KB2 := two_K_lt_B2 h1K
  have hw := two_mul_B2_add_one_lt_two_pow_wOf h1K
  have hw0 : 0 < 2 ^ wOf K := Nat.two_pow_pos (wOf K)
  intro r hr
  dsimp [hbInit] at hr
  simp only [List.mem_append, List.mem_map, List.mem_finRange] at hr
  rcases hr with ⟨i, _, hi⟩ | ⟨b, _, hb⟩
  · by_cases hi2K : i.1 < 2 * K
    · rw [dif_pos hi2K] at hi
      by_cases hact : 2 ≤ runOffset l ⟨i.1, hi2K⟩
      · rw [if_pos hact] at hi; subst hi
        have hm : runOffset l ⟨i.1, hi2K⟩ ≤ 2 * K := comb.runOffset_le_N l ⟨i.1, hi2K⟩
        have hocc : runOcc l ⟨i.1, hi2K⟩ < 2 * K := by
          dsimp [runOcc]
          have hlt : (Finset.univ.filter fun j : Fin (2 * K) =>
              j < ⟨i.1, hi2K⟩ ∧ runOffset l j = runOffset l ⟨i.1, hi2K⟩) ⊂ Finset.univ := by
            rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
            exact ⟨⟨i.1, hi2K⟩, Finset.mem_univ _, by simp⟩
          calc _ < (Finset.univ : Finset (Fin (2 * K))).card := Finset.card_lt_card hlt
            _ = 2 * K := Fintype.card_fin _
        dsimp only
        exact ⟨by omega, by omega, fun _ => rfl, by omega, by omega, hw0, by omega⟩
      · rw [if_neg hact] at hi; subst hi; dsimp only
        exact ⟨by omega, by omega, fun h => by omega, hw0, hw0, hw0, by omega⟩
    · rw [dif_neg hi2K] at hi; subst hi; dsimp only
      exact ⟨by omega, by omega, fun h => by omega, hw0, hw0, hw0, by omega⟩
  · by_cases hb_len : b.1 < (bucketPairs (2 * K)).length
    · rw [dif_pos hb_len] at hb; subst hb
      have hmem : (bucketPairs (2 * K))[b.1] ∈ bucketPairs (2 * K) := List.getElem_mem hb_len
      have hbp := (comb.mem_bucketPairs_iff (2 * K) _ _).mp hmem
      simp only [List.get_eq_getElem] at hbp
      have hdiv : 2 * K / (bucketPairs (2 * K))[b.1].1 ≤ 2 * K := Nat.div_le_self _ _
      dsimp only
      exact ⟨by omega, by omega, fun h => by omega, by omega, by omega, by omega, by omega⟩
    · rw [dif_neg hb_len] at hb; subst hb; dsimp only
      exact ⟨by omega, by omega, fun h => by omega, by omega, hw0, by omega, by omega⟩

def hb1ArrOfList (K : ℕ) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K)) :
    Fin (arity (dHbOf K + 1)) → Qubits (wR1Hb K) :=
  fun q => hbRecToBits (wOf K) (L[q.1]'(by omega)) (d_arr q)

lemma hbInitArr_eq_hb1ArrOfList (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    hbInitArr K l = hb1ArrOfList K (hbInit (2 * K) (arity (dHbOf K)) l)
      (by rw [hbInit_length, arity_succ_eq]) (fun _ _ => false) := rfl

lemma hb1SortedList_length (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    (hb1SortedList K l).length = arity (dHbOf K + 1) := by
  dsimp [hb1SortedList]
  rw [List.length_mergeSort, hbInit_length, arity_succ_eq]

lemma hb1SortedList_mem_iff (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (r : HBRec) :
    r ∈ hb1SortedList K l ↔ r ∈ hbInit (2 * K) (arity (dHbOf K)) l :=
  (List.mergeSort_perm _ _).mem_iff

lemma hb1SortedList_orig_nodup (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    ((hb1SortedList K l).map (·.orig)).Nodup := by
  have hp : List.Perm ((hb1SortedList K l).map (·.orig))
      ((hbInit (2 * K) (arity (dHbOf K)) l).map (·.orig)) :=
    (List.mergeSort_perm _ _).map _
  rw [hp.nodup_iff, hbInit_map_orig]
  exact List.nodup_range

lemma eRec2Kind_disjoint_eSeqBSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) (j : Fin 4) :
    ∀ a b, eRec2Kind as n K d q a ≠ eSeqBSlot as n K d j b :=
  trans_disjoint_right (ancRegField_disjoint_ancPrefix as n K d (by decide) _ _ (ancLen_11 n K d _) q _ 2 _ 4 _)

lemma eRec2Kind_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec2Kind as n K d q a ≠ eArith345 as n K d subLen hle b :=
  ancRegField_disjoint_ancPrefix as n K d (by decide) _ _ (ancLen_11 n K d _) q _ 2 _ subLen _

lemma eRec2M_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ)
    {q0 q1 : Fin (arity (dHbOf K + 1))} (hq : q0 ≠ q1) :
    ∀ a b, eRec2M as n K d q0 a ≠ eRec2M as n K d q1 b :=
  ancRegField_disjoint_slot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K)
    (ancLen_11 n K d _) hq _ _

lemma eRec2M_disjoint_eSeqBSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) (j : Fin 4) :
    ∀ a b, eRec2M as n K d q a ≠ eSeqBSlot as n K d j b :=
  trans_disjoint_right (ancRegField_disjoint_ancPrefix as n K d (by decide) _ _ (ancLen_11 n K d _) q _ (wOf K) _ 4 _)

lemma eRec2M_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec2M as n K d q a ≠ eArith345 as n K d subLen hle b :=
  ancRegField_disjoint_ancPrefix as n K d (by decide) _ _ (ancLen_11 n K d _) q _ (wOf K) _ subLen _

lemma eRec2Occ_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ)
    {q0 q1 : Fin (arity (dHbOf K + 1))} (hq : q0 ≠ q1) :
    ∀ a b, eRec2Occ as n K d q0 a ≠ eRec2Occ as n K d q1 b :=
  ancRegField_disjoint_slot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K)
    (ancLen_11 n K d _) hq _ _

lemma eRec2Occ_disjoint_eSeqBSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) (j : Fin 4) :
    ∀ a b, eRec2Occ as n K d q a ≠ eSeqBSlot as n K d j b :=
  trans_disjoint_right (ancRegField_disjoint_ancPrefix as n K d (by decide) _ _ (ancLen_11 n K d _) q _ (wOf K) _ 4 _)

lemma eRec2Occ_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec2Occ as n K d q a ≠ eArith345 as n K d subLen hle b :=
  ancRegField_disjoint_ancPrefix as n K d (by decide) _ _ (ancLen_11 n K d _) q _ (wOf K) _ subLen _

lemma eRec2Dest_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ)
    {q0 q1 : Fin (arity (dHbOf K + 1))} (hq : q0 ≠ q1) :
    ∀ a b, eRec2Dest as n K d q0 a ≠ eRec2Dest as n K d q1 b :=
  ancRegField_disjoint_slot as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K)
    (ancLen_11 n K d _) hq _ _

lemma eSeqCtrl_disjoint_eRec2Dest (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eSeqCtrl as n K d a ≠ eRec2Dest as n K d q b :=
  fun a b h => ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨20, by decide⟩)
    (by decide) _ _ (ancLen_11 n K d _) q _ (wOf K) _ 1 _ b a h.symm

lemma eSeqCtrl_disjoint_eRec2Kind (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eSeqCtrl as n K d a ≠ eRec2Kind as n K d q b :=
  fun a b h => ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨20, by decide⟩)
    (by decide) _ _ (ancLen_11 n K d _) q _ 2 _ 1 _ b a h.symm

lemma eRec2Kind_disjoint_eSeqCtrl (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec2Kind as n K d q a ≠ eSeqCtrl as n K d b :=
  fun a b h => eSeqCtrl_disjoint_eRec2Kind as n K d q b a h.symm

lemma eSeqCtrl_disjoint_eRec2KR1 (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eSeqCtrl as n K d a ≠ eRec2KR1 as n K d q b :=
  fun a b h => ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨20, by decide⟩)
    (by decide) _ _ (ancLen_11 n K d _) q _ 2 _ 1 _ b a h.symm

lemma eRec2Kind_disjoint_eRec2KR1 (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec2Kind as n K d q a ≠ eRec2KR1 as n K d q b :=
  ancRegField_disjoint_field_same as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K)
    (ancLen_11 n K d _) q _ _ (Or.inr (by dsimp [wK1Hb]; omega))

lemma eRec2KindMsb_disjoint_eRec3Group (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec2KindMsb as n K d q a ≠ eRec3Group as n K d q b :=
  trans_disjoint_left (ancRegField_disjoint_ancRegField as n K d (by decide)
    _ _ (ancLen_11 n K d _) q _ 2 _ _ _ (ancLen_13 n K d _) q _ 1 _)

lemma eRec2Dest_disjoint_eRec3Dest (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec2Dest as n K d q a ≠ eRec3Dest as n K d q b :=
  ancRegField_disjoint_ancRegField as n K d (by decide)
    _ _ (ancLen_11 n K d _) q _ (wOf K) _ _ _ (ancLen_13 n K d _) q _ (wOf K) _

lemma eRec2Orig_disjoint_eRec3Orig (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec2Orig as n K d q a ≠ eRec3Orig as n K d q b :=
  ancRegField_disjoint_ancRegField as n K d (by decide)
    _ _ (ancLen_11 n K d _) q _ (wOf K) _ _ _ (ancLen_13 n K d _) q _ (wOf K) _

lemma eRec2Kind_disjoint_eRec3Kind (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eRec2Kind as n K d q a ≠ eRec3Kind as n K d q b :=
  ancRegField_disjoint_ancRegField as n K d (by decide)
    _ _ (ancLen_11 n K d _) q _ 2 _ _ _ (ancLen_13 n K d _) q _ 2 _

lemma eRec3Slot_disjoint_eRec2KindMsb (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, ancRegSlot as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q a ≠
      eRec2KindMsb as n K d q b :=
  trans_disjoint_right (ancRegSlot_disjoint_ancRegField as n K d (by decide)
    _ _ (ancLen_13 n K d _) q _ _ (ancLen_11 n K d _) q _ 2 _)

lemma eRec3Slot_disjoint_eRec2Dest (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, ancRegSlot as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q a ≠
      eRec2Dest as n K d q b :=
  ancRegSlot_disjoint_ancRegField as n K d (by decide)
    _ _ (ancLen_13 n K d _) q _ _ (ancLen_11 n K d _) q _ (wOf K) _

lemma eRec3Slot_disjoint_eRec2Orig (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, ancRegSlot as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q a ≠
      eRec2Orig as n K d q b :=
  ancRegSlot_disjoint_ancRegField as n K d (by decide)
    _ _ (ancLen_13 n K d _) q _ _ (ancLen_11 n K d _) q _ (wOf K) _

lemma eRec3Slot_disjoint_eRec2Kind (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, ancRegSlot as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q a ≠
      eRec2Kind as n K d q b :=
  ancRegSlot_disjoint_ancRegField as n K d (by decide)
    _ _ (ancLen_13 n K d _) q _ _ (ancLen_11 n K d _) q _ 2 _

def hbSeqCmpCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (p : ℕ) (hp : p + 1 < arity (dHbOf K + 1)) : LayeredCircuit (totWiresDef as n K d) :=
  have h5w := five_le_wOf h1K
  let w := wOf K
  let q0 : Fin (arity (dHbOf K + 1)) := ⟨p, by omega⟩
  let q1 : Fin (arity (dHbOf K + 1)) := ⟨p + 1, hp⟩
  let anc2 := eArith345 as n K d 2 (by omega)
  let ancW := eArith345 as n K d w (by omega)
  let c0 := (arith.eqConstMSBCircuit 2 0).mapWires
    (comb3 (eRec2Kind as n K d q0) (eSeqBSlot as n K d ⟨0, by decide⟩) anc2
      (eRec2Kind_disjoint_eSeqBSlot as n K d _ _)
      (eRec2Kind_disjoint_eArith345 as n K d 2 (by omega) _)
      (eSeqBSlot_disjoint_eArith345 as n K d 2 (by omega) _))
  let c1 := (arith.eqConstMSBCircuit 2 1).mapWires
    (comb3 (eRec2Kind as n K d q1) (eSeqBSlot as n K d ⟨1, by decide⟩) anc2
      (eRec2Kind_disjoint_eSeqBSlot as n K d _ _)
      (eRec2Kind_disjoint_eArith345 as n K d 2 (by omega) _)
      (eSeqBSlot_disjoint_eArith345 as n K d 2 (by omega) _))
  let c2 := (arith.eqRegCircuit w).mapWires
    (comb4 (eRec2M as n K d q0) (eRec2M as n K d q1) (eSeqBSlot as n K d ⟨2, by decide⟩) ancW
      (eRec2M_disjoint_slot as n K d (by simp [q0, q1, Fin.ext_iff]))
      (eRec2M_disjoint_eSeqBSlot as n K d _ _)
      (eRec2M_disjoint_eSeqBSlot as n K d _ _)
      (eRec2M_disjoint_eArith345 as n K d w (by omega) _)
      (eRec2M_disjoint_eArith345 as n K d w (by omega) _)
      (eSeqBSlot_disjoint_eArith345 as n K d w (by omega) _))
  let c3 := (arith.eqRegCircuit w).mapWires
    (comb4 (eRec2Occ as n K d q0) (eRec2Occ as n K d q1) (eSeqBSlot as n K d ⟨3, by decide⟩) ancW
      (eRec2Occ_disjoint_slot as n K d (by simp [q0, q1, Fin.ext_iff]))
      (eRec2Occ_disjoint_eSeqBSlot as n K d _ _)
      (eRec2Occ_disjoint_eSeqBSlot as n K d _ _)
      (eRec2Occ_disjoint_eArith345 as n K d w (by omega) _)
      (eRec2Occ_disjoint_eArith345 as n K d w (by omega) _)
      (eSeqBSlot_disjoint_eArith345 as n K d w (by omega) _))
  LayeredCircuit.seqList [c0, c1, c2, c3]

lemma eSeqB_disjoint_eRec2Kind (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eSeqB as n K d a ≠ eRec2Kind as n K d q b :=
  trans_disjoint_left (anc_disjoint_ancRegField as n K d (by decide) _ _ (ancLen_11 n K d _) q _ 2 _)

lemma eSeqB_disjoint_eRec2M (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eSeqB as n K d a ≠ eRec2M as n K d q b :=
  trans_disjoint_left (anc_disjoint_ancRegField as n K d (by decide) _ _ (ancLen_11 n K d _) q _ (wOf K) _)

lemma eSeqB_disjoint_eRec2Occ (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eSeqB as n K d a ≠ eRec2Occ as n K d q b :=
  trans_disjoint_left (anc_disjoint_ancRegField as n K d (by decide) _ _ (ancLen_11 n K d _) q _ (wOf K) _)

lemma eTr2a_disjoint_eSeqB (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eTr2a as n K d a ≠ eSeqB as n K d b :=
  trans_disjoint_right (eTr2a_disjoint_anc_other as n K d ⟨19, by decide⟩ (by decide))


end HarmBucketWork54


