-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_10
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54_10
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:55:41.049288+00:00
-- url     : https://prove2.me/theorems/61fa1e09-a7ba-4572-8b92-38ae9fcb11c3
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (10/11)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 10 of 11 (`harmBucketWork54_10`).
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
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_9

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (10/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

lemma eTr2a_disjoint_eSeqCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eTr2a as n K d a ≠ eSeqCtrl as n K d b :=
  trans_disjoint_right (eTr2a_disjoint_anc_other as n K d ⟨20, by decide⟩ (by decide))

def hbSeqCmpBits (r0 r1 : HBRec) (j : Fin 4) : Bool :=
  match j.1 with
  | 0 => decide (r0.kind = 0)
  | 1 => decide (r1.kind = 1)
  | 2 => decide (r0.m = r1.m)
  | _ => decide (r0.occ = r1.occ)

lemma comp_eRec2Kind (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr))
    (q : Fin (arity (dHbOf K + 1))) :
    z ∘ eRec2Kind as n K d q = natToBits 2 (L[q.1]'(by omega)).kind := by
  dsimp only [eRec2Kind]
  rw [comp_ancRegField as n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z _ hz q]
  exact rec2SlotFn_comp_5 ..

lemma comp_eRec2M (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr))
    (q : Fin (arity (dHbOf K + 1))) :
    z ∘ eRec2M as n K d q = natToBits (wOf K) (L[q.1]'(by omega)).m := by
  dsimp only [eRec2M]
  rw [comp_ancRegField as n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z _ hz q]
  exact rec2SlotFn_comp_1 ..

lemma comp_eRec2Occ (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr))
    (q : Fin (arity (dHbOf K + 1))) :
    z ∘ eRec2Occ as n K d q = natToBits (wOf K) (L[q.1]'(by omega)).occ := by
  dsimp only [eRec2Occ]
  rw [comp_ancRegField as n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z _ hz q]
  exact rec2SlotFn_comp_2 ..

lemma comp_eRec2Dest (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr))
    (q : Fin (arity (dHbOf K + 1))) :
    z ∘ eRec2Dest as n K d q = natToBits (wOf K) (L[q.1]'(by omega)).dest := by
  dsimp only [eRec2Dest]
  rw [comp_ancRegField as n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z _ hz q]
  exact rec2SlotFn_comp_6 ..

lemma comp_eRec2KR1 (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K))
    (hz : z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K L hL d_arr))
    (q : Fin (arity (dHbOf K + 1))) :
    z ∘ eRec2KR1 as n K d q = natToBits 2 (hbKindRank1 (L[q.1]'(by omega))) := by
  dsimp only [eRec2KR1]
  rw [comp_ancRegField as n K d ⟨11, by decide⟩ _ _ (ancLen_11 n K d _) z _ hz q]
  exact rec2SlotFn_comp_3 ..

lemma updateOn_eSeqBSlot (as : AlonsoSchottSil54) (n K d : ℕ) (z : Qubits (totWiresDef as n K d))
    (bIn : Qubits 4) (hz : z ∘ eSeqB as n K d = bIn) (j : Fin 4) (v : Bool) :
    updateOn (eSeqBSlot as n K d j) z (fun _ => v) =
      updateOn (eSeqB as n K d) z (Function.update bIn j v) := by
  dsimp only [eSeqBSlot]
  rw [updateOn_trans_emb, ← hz]
  apply congrArg (updateOn (eSeqB as n K d) z)
  funext u
  by_cases hu : u = j
  · subst hu
    change updateOn (sliceEmb u.1 1 (by omega)) (z ∘ eSeqB as n K d) (fun _ => v)
      (sliceEmb u.1 1 (by omega) 0) = _
    rw [updateOn_apply_emb, Function.update_self]
  · have hnot : u ∉ Set.range (sliceEmb j.1 1 (by omega)) := by
      rintro ⟨i, hi⟩; have hv := congrArg Fin.val hi; simp [sliceEmb_apply] at hv
      exact hu (Fin.ext (by omega))
    rw [updateOn_apply_not_mem _ _ _ hnot, Function.update_of_ne hu]

def hbSeqStepCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (p : ℕ) (hp : p + 1 < arity (dHbOf K + 1)) : LayeredCircuit (totWiresDef as n K d) :=
  have h5w := five_le_wOf h1K
  let w := wOf K
  let q0 : Fin (arity (dHbOf K + 1)) := ⟨p, by omega⟩
  let q1 : Fin (arity (dHbOf K + 1)) := ⟨p + 1, hp⟩
  let ancCmp := hbSeqCmpCirc as arith n K d h1K p hp
  let c4 := (arith.eqConstMSBCircuit 4 (2 ^ 4 - 1)).mapWires
    (comb3 (eSeqB as n K d) (eSeqCtrl as n K d) (eArith345 as n K d 4 (by omega))
      (eSeqB_disjoint_eSeqCtrl as n K d)
      (eSeqB_disjoint_eArith345 as n K d 4 (by omega))
      (eSeqCtrl_disjoint_eArith345 as n K d 4 (by omega)))
  let c5 := (arith.ctrlCopyRegCircuit w).mapWires
    (comb3 (eSeqCtrl as n K d) (eRec2Dest as n K d q1) (eRec2Dest as n K d q0)
      (eSeqCtrl_disjoint_eRec2Dest as n K d _)
      (eSeqCtrl_disjoint_eRec2Dest as n K d _)
      (eRec2Dest_disjoint_slot as n K d (by simp [q0, q1, Fin.ext_iff])))
  let c6 := (arith.ctrlConstXorMSBCircuit 2 3).mapWires
    (combineEmb (eSeqCtrl as n K d) (eRec2Kind as n K d q1) (eSeqCtrl_disjoint_eRec2Kind as n K d _))
  let c6b := (arith.ctrlConstXorMSBCircuit 2 3).mapWires
    (combineEmb (eSeqCtrl as n K d) (eRec2KR1 as n K d q1) (eSeqCtrl_disjoint_eRec2KR1 as n K d _))
  let c7 := (arith.ctrlConstXorMSBCircuit 1 1).mapWires
    (combineEmb (eSeqCtrl as n K d) (eSeqBSlot as n K d ⟨1, by decide⟩) (eSeqCtrl_disjoint_eSeqBSlot as n K d _))
  let c12 := (arith.eqConstMSBCircuit 2 2).mapWires
    (comb3 (eRec2Kind as n K d q1) (eSeqCtrl as n K d) (eArith345 as n K d 2 (by omega))
      (eRec2Kind_disjoint_eSeqCtrl as n K d _)
      (eRec2Kind_disjoint_eArith345 as n K d 2 (by omega) _)
      (eSeqCtrl_disjoint_eArith345 as n K d 2 (by omega)))
  LayeredCircuit.seqList [ancCmp, c4, c5, c6, c6b, c7, ancCmp, c12]

lemma hbNeighborStep_length (L : List HBRec) (p : ℕ) :
    (hbNeighborStep L p).length = L.length := by
  dsimp [hbNeighborStep]; split_ifs <;> simp

lemma hbNeighborStep_eq_pos (L : List HBRec) (p : ℕ) (hp : p + 1 < L.length)
    (hc : L[p].kind = 0 ∧ L[p + 1].kind = 1 ∧ L[p].m = L[p + 1].m ∧ L[p].occ = L[p + 1].occ) :
    hbNeighborStep L p =
      (L.set p { L[p] with dest := L[p + 1].dest }).set (p + 1) { L[p + 1] with kind := 2 } := by
  dsimp [hbNeighborStep]; rw [dif_pos hp, if_pos hc]

lemma hbNeighborStep_eq_neg (L : List HBRec) (p : ℕ) (hp : p + 1 < L.length)
    (hc : ¬ (L[p].kind = 0 ∧ L[p + 1].kind = 1 ∧ L[p].m = L[p + 1].m ∧ L[p].occ = L[p + 1].occ)) :
    hbNeighborStep L p = L := by
  dsimp [hbNeighborStep]; rw [dif_pos hp, if_neg hc]

lemma hbNeighborStep_getElem_p_pos (L : List HBRec) (p : ℕ) (hp : p + 1 < L.length)
    (hc : L[p].kind = 0 ∧ L[p + 1].kind = 1 ∧ L[p].m = L[p + 1].m ∧ L[p].occ = L[p + 1].occ)
    (hpL : p < (hbNeighborStep L p).length) :
    (hbNeighborStep L p)[p]'hpL = { L[p] with dest := L[p + 1].dest } := by
  have heq := hbNeighborStep_eq_pos L p hp hc
  simp only [heq, List.getElem_set_ne (by omega : p + 1 ≠ p), List.getElem_set_self]

lemma hbNeighborStep_getElem_succ_pos (L : List HBRec) (p : ℕ) (hp : p + 1 < L.length)
    (hc : L[p].kind = 0 ∧ L[p + 1].kind = 1 ∧ L[p].m = L[p + 1].m ∧ L[p].occ = L[p + 1].occ)
    (hpL : p + 1 < (hbNeighborStep L p).length) :
    (hbNeighborStep L p)[p + 1]'hpL = { L[p + 1] with kind := 2 } := by
  have heq := hbNeighborStep_eq_pos L p hp hc
  simp only [heq, List.getElem_set_self]

lemma hbNeighborStep_getElem_neg (L : List HBRec) (p : ℕ) (hp : p + 1 < L.length)
    (hc : ¬ (L[p].kind = 0 ∧ L[p + 1].kind = 1 ∧ L[p].m = L[p + 1].m ∧ L[p].occ = L[p + 1].occ))
    (q : ℕ) (hqL : q < (hbNeighborStep L p).length) (hq : q < L.length) :
    (hbNeighborStep L p)[q]'hqL = L[q]'hq := by
  have heq := hbNeighborStep_eq_neg L p hp hc
  simp only [heq]

def hbSeqState (s1 : List HBRec) (k : ℕ) : List HBRec :=
  (List.range k).foldl hbNeighborStep s1

lemma hbSeqState_zero (s1 : List HBRec) : hbSeqState s1 0 = s1 := rfl

lemma hbSeqState_succ (s1 : List HBRec) (k : ℕ) :
    hbSeqState s1 (k + 1) = hbNeighborStep (hbSeqState s1 k) k := by
  dsimp [hbSeqState]; rw [List.range_succ, List.foldl_append]; rfl

lemma hbNeighborStep_map_orig (L : List HBRec) (p : ℕ) :
    (hbNeighborStep L p).map (·.orig) = L.map (·.orig) := by
  dsimp [hbNeighborStep]
  split_ifs with hp hc
  · apply List.ext_getElem
    · simp
    · intro q h1 h2
      rw [List.length_map] at h2
      rw [List.getElem_map, List.getElem_map]
      by_cases hqp1 : q = p + 1
      · subst hqp1; rw [List.getElem_set_self]
      · rw [List.getElem_set_ne (Ne.symm hqp1)]
        by_cases hqp : q = p
        · subst hqp; rw [List.getElem_set_self]
        · rw [List.getElem_set_ne (Ne.symm hqp)]
  · rfl
  · rfl

lemma hbSeqState_length (s1 : List HBRec) (k : ℕ) :
    (hbSeqState s1 k).length = s1.length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [hbSeqState_succ, hbNeighborStep_length, ih]

lemma hbSeqPass_length (s1 : List HBRec) : (hbSeqPass s1).length = s1.length := by
  dsimp [hbSeqPass]
  have hfold : ∀ (ks : List ℕ) (L : List HBRec), (ks.foldl hbNeighborStep L).length = L.length := by
    intro ks; induction ks with
    | nil => intro L; rfl
    | cons k ks ih => intro L; simp only [List.foldl_cons, ih, hbNeighborStep_length]
  exact hfold _ _

lemma hbSeqState_map_orig (s1 : List HBRec) (k : ℕ) :
    (hbSeqState s1 k).map (·.orig) = s1.map (·.orig) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [hbSeqState_succ, hbNeighborStep_map_orig, ih]

lemma hbSeqPass_eq_hbSeqState (s1 : List HBRec) (h1 : 1 ≤ s1.length) :
    hbSeqPass s1 = hbSeqState s1 (s1.length - 1) := by
  dsimp [hbSeqPass]
  conv_lhs => rw [show s1.length = (s1.length - 1) + 1 by omega]
  rw [List.range_succ, List.foldl_append]
  change hbNeighborStep (hbSeqState s1 (s1.length - 1)) (s1.length - 1) = _
  dsimp [hbNeighborStep]
  rw [dif_neg (by rw [hbSeqState_length]; omega)]

lemma hbNeighborStep_inv (s1 L : List HBRec) (w k : ℕ) (hlen : L.length = s1.length)
    (ih_mem : ∀ r ∈ L, r.kind ≤ 3 ∧ r.m < 2 ^ w ∧ r.occ < 2 ^ w ∧ r.dest < 2 ^ w ∧ r.orig < 2 ^ w)
    (ih_d0 : ∀ q (hq : q < s1.length), k ≤ q → (L[q]'(by omega)).kind = 0 → (L[q]'(by omega)).dest = 0)
    (ih_eq : ∀ q (hq : q < s1.length), k < q → L[q]'(by omega) = s1[q]'hq)
    (ih_ne : ∀ q (hq : q < s1.length), k < q → (L[q]'(by omega)).kind ≠ 2) :
    (∀ r ∈ hbNeighborStep L k, r.kind ≤ 3 ∧ r.m < 2 ^ w ∧ r.occ < 2 ^ w ∧ r.dest < 2 ^ w ∧ r.orig < 2 ^ w) ∧
    (∀ q (hq : q < s1.length), k + 1 ≤ q →
      ((hbNeighborStep L k)[q]'(by rw [hbNeighborStep_length]; omega)).kind = 0 →
      ((hbNeighborStep L k)[q]'(by rw [hbNeighborStep_length]; omega)).dest = 0) ∧
    (∀ q (hq : q < s1.length), k + 1 < q →
      (hbNeighborStep L k)[q]'(by rw [hbNeighborStep_length]; omega) = s1[q]'hq) ∧
    (∀ q (hq : q < s1.length), k + 1 < q →
      ((hbNeighborStep L k)[q]'(by rw [hbNeighborStep_length]; omega)).kind ≠ 2) := by
  by_cases hk1 : k + 1 < L.length
  · have hstep : hbNeighborStep L k =
        if L[k].kind = 0 ∧ L[k + 1].kind = 1 ∧ L[k].m = L[k + 1].m ∧ L[k].occ = L[k + 1].occ then
          (L.set k { L[k] with dest := L[k + 1].dest }).set (k + 1) { L[k + 1] with kind := 2 }
        else L := by
      dsimp [hbNeighborStep]; rw [dif_pos hk1]
    by_cases hcond : L[k].kind = 0 ∧ L[k + 1].kind = 1 ∧ L[k].m = L[k + 1].m ∧ L[k].occ = L[k + 1].occ
    · have hL' : hbNeighborStep L k =
          (L.set k { L[k] with dest := L[k + 1].dest }).set (k + 1) { L[k + 1] with kind := 2 } := by
        rw [hstep, if_pos hcond]
      have hr0 := ih_mem L[k] (List.getElem_mem (by omega))
      have hr1 := ih_mem L[k + 1] (List.getElem_mem hk1)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro r hr; rw [hL'] at hr
        rcases List.mem_iff_getElem.mp hr with ⟨idx, hidx, rfl⟩
        have hlen_s1 : ((L.set k { L[k] with dest := L[k + 1].dest }).set (k + 1) { L[k + 1] with kind := 2 }).length = L.length := by simp
        by_cases hidx1 : idx = k + 1
        · subst hidx1; rw [List.getElem_set_self]; exact ⟨by simp, hr1.2.1, hr1.2.2.1, hr1.2.2.2.1, hr1.2.2.2.2⟩
        · rw [List.getElem_set_ne (Ne.symm hidx1)]
          by_cases hidx0 : idx = k
          · subst hidx0; rw [List.getElem_set_self]; exact ⟨hr0.1, hr0.2.1, hr0.2.2.1, hr1.2.2.2.1, hr0.2.2.2.2⟩
          · rw [List.getElem_set_ne (Ne.symm hidx0)]; exact ih_mem _ (List.getElem_mem (by omega))
      · intro q hq hkq h0
        have helem : (hbNeighborStep L k)[q]'(by rw [hbNeighborStep_length]; omega) =
            ((L.set k { L[k] with dest := L[k + 1].dest }).set (k + 1) { L[k + 1] with kind := 2 })[q]'(by simp; omega) := by
          simp only [hL']
        rw [helem] at h0 ⊢
        by_cases hqp1 : q = k + 1
        · subst hqp1; rw [List.getElem_set_self] at h0; cases h0
        · rw [List.getElem_set_ne (Ne.symm hqp1), List.getElem_set_ne (by omega)] at h0 ⊢
          exact ih_d0 q hq (by omega) h0
      · intro q hq hkq
        have helem : (hbNeighborStep L k)[q]'(by rw [hbNeighborStep_length]; omega) =
            ((L.set k { L[k] with dest := L[k + 1].dest }).set (k + 1) { L[k + 1] with kind := 2 })[q]'(by simp; omega) := by
          simp only [hL']
        rw [helem, List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
        exact ih_eq q hq (by omega)
      · intro q hq hkq
        have helem : (hbNeighborStep L k)[q]'(by rw [hbNeighborStep_length]; omega) =
            ((L.set k { L[k] with dest := L[k + 1].dest }).set (k + 1) { L[k + 1] with kind := 2 })[q]'(by simp; omega) := by
          simp only [hL']
        rw [helem, List.getElem_set_ne (by omega), List.getElem_set_ne (by omega)]
        exact ih_ne q hq (by omega)
    · have hL' : hbNeighborStep L k = L := by rw [hstep, if_neg hcond]
      refine ⟨fun r hr => ih_mem r (hL' ▸ hr), ?_, ?_, ?_⟩
      · intro q hq hkq; simp only [hL']; exact ih_d0 q hq (by omega)
      · intro q hq hkq; simp only [hL']; exact ih_eq q hq (by omega)
      · intro q hq hkq; simp only [hL']; exact ih_ne q hq (by omega)
  · have hL' : hbNeighborStep L k = L := by dsimp [hbNeighborStep]; rw [dif_neg hk1]
    refine ⟨fun r hr => ih_mem r (hL' ▸ hr), ?_, ?_, ?_⟩
    · intro q hq hkq; simp only [hL']; exact ih_d0 q hq (by omega)
    · intro q hq hkq; simp only [hL']; exact ih_eq q hq (by omega)
    · intro q hq hkq; simp only [hL']; exact ih_ne q hq (by omega)

lemma hbSeqState_inv (s1 : List HBRec) (w : ℕ)
    (hs1 : ∀ r ∈ s1, r.kind ≤ 3 ∧ r.kind ≠ 2 ∧ (r.kind = 0 → r.dest = 0) ∧
      r.m < 2 ^ w ∧ r.occ < 2 ^ w ∧ r.dest < 2 ^ w ∧ r.orig < 2 ^ w) :
    ∀ k : ℕ,
      (∀ r ∈ hbSeqState s1 k, r.kind ≤ 3 ∧ r.m < 2 ^ w ∧ r.occ < 2 ^ w ∧ r.dest < 2 ^ w ∧ r.orig < 2 ^ w) ∧
      (∀ q (hq : q < s1.length), k ≤ q →
        ((hbSeqState s1 k)[q]'(by rw [hbSeqState_length]; exact hq)).kind = 0 →
        ((hbSeqState s1 k)[q]'(by rw [hbSeqState_length]; exact hq)).dest = 0) ∧
      (∀ q (hq : q < s1.length), k < q →
        (hbSeqState s1 k)[q]'(by rw [hbSeqState_length]; exact hq) = s1[q]'hq) ∧
      (∀ q (hq : q < s1.length), k < q →
        ((hbSeqState s1 k)[q]'(by rw [hbSeqState_length]; exact hq)).kind ≠ 2) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun r hr => ?_, fun q hq _ h0 => ?_, fun q hq _ => rfl, fun q hq _ => ?_⟩
    · have h := hs1 r hr; exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
    · exact (hs1 _ (List.getElem_mem hq)).2.2.1 h0
    · exact (hs1 _ (List.getElem_mem hq)).2.1
  | succ k ih =>
    rcases ih with ⟨ih_mem, ih_d0, ih_eq, ih_ne⟩
    have hstep := hbNeighborStep_inv s1 (hbSeqState s1 k) w k (hbSeqState_length s1 k) ih_mem ih_d0 ih_eq ih_ne
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r hr; exact hstep.1 r (hbSeqState_succ s1 k ▸ hr)
    · intro q hq hkq h0
      have h0' : ((hbNeighborStep (hbSeqState s1 k) k)[q]'(by rw [hbNeighborStep_length, hbSeqState_length]; exact hq)).kind = 0 := by
        simpa only [hbSeqState_succ] using h0
      have hd := hstep.2.1 q hq hkq h0'
      simpa only [hbSeqState_succ] using hd
    · intro q hq hkq
      simpa only [hbSeqState_succ] using hstep.2.2.1 q hq hkq
    · intro q hq hkq
      simpa only [hbSeqState_succ] using hstep.2.2.2 q hq hkq

def hbSeqPassCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) :
    LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList ((List.range (arity (dHbOf K + 1) - 1)).map fun p =>
    if hp : p + 1 < arity (dHbOf K + 1) then hbSeqStepCirc as arith n K d h1K p hp else LayeredCircuit.id _)

lemma hb1ArrOfList_congr {K : ℕ} {L₁ L₂ : List HBRec} (h : L₁ = L₂)
    (h1 : L₁.length = arity (dHbOf K + 1)) (h2 : L₂.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K)) :
    hb1ArrOfList K L₁ h1 d_arr = hb1ArrOfList K L₂ h2 d_arr := by
  subst h; rfl

def hb3ArrOfList (K : ℕ) (L : List HBRec) (hL : L.length = arity (dHbOf K + 1))
    (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K)) :
    Fin (arity (dHbOf K + 1)) → Qubits (wR2Hb K) :=
  fun q => hbRecToRec3Bits (wOf K) (L[q.1]'(by omega)) (d_arr q)

def copyToRec3SlotCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (q : Fin (arity (dHbOf K + 1))) : LayeredCircuit (totWiresDef as n K d) :=
  let c0 := (arith.copyRegCircuit 1).mapWires
    (combineEmb (eRec2KindMsb as n K d q) (eRec3Group as n K d q) (eRec2KindMsb_disjoint_eRec3Group as n K d q))
  let c1 := (arith.copyRegCircuit (wOf K)).mapWires
    (combineEmb (eRec2Dest as n K d q) (eRec3Dest as n K d q) (eRec2Dest_disjoint_eRec3Dest as n K d q))
  let c2 := (arith.copyRegCircuit (wOf K)).mapWires
    (combineEmb (eRec2Orig as n K d q) (eRec3Orig as n K d q) (eRec2Orig_disjoint_eRec3Orig as n K d q))
  let c3 := (arith.copyRegCircuit 2).mapWires
    (combineEmb (eRec2Kind as n K d q) (eRec3Kind as n K d q) (eRec2Kind_disjoint_eRec3Kind as n K d q))
  LayeredCircuit.seqList [c0, c1, c2, c3]

def copyToRec3Circ (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) :
    LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList ((List.range (arity (dHbOf K + 1))).map fun q =>
    if hq : q < arity (dHbOf K + 1) then copyToRec3SlotCirc as arith n K d ⟨q, hq⟩ else LayeredCircuit.id _)

def sortHb2Circ (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ) :
    LayeredCircuit (totWiresDef as n K d) :=
  (br.bitonicSortKeyCircuit (dHbOf K + 1) (wK2Hb K) (wP2Hb K) true).mapWires
    (packDTA54Emb (eRec3 as n K d) (eTr2b as n K d) (eSort2bAnc as n K d)
      (eRec3_disjoint_eTr2b as n K d)
      (eRec3_disjoint_eSort2bAnc as n K d)
      (eTr2b_disjoint_eSort2bAnc as n K d))

noncomputable def rec3InitArr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    Fin (arity (dHbOf K + 1)) → Qubits (wR2Hb K) :=
  hb3ArrOfList K (hbSeqPass (hb1SortedList K l))
    (by rw [hbSeqPass_length, hb1SortedList_length]) (fun _ _ => false)

noncomputable def rec3SortedArr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    Fin (arity (dHbOf K + 1)) → Qubits (wR2Hb K) :=
  sort (fun r => bitsToNat (recKey54 r)) (dHbOf K + 1) true (rec3InitArr K l)

noncomputable def rec3SortTr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    Fin (sortTraceSize (dHbOf K + 1)) → Bool :=
  sortTrace (fun r => bitsToNat (recKey54 r)) (dHbOf K + 1) true (rec3InitArr K l)

def hb2SortedList (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) : List HBRec :=
  (hbSeqPass (hb1SortedList K l)).mergeSort (fun x y => decide (hbKey2 x ≤ hbKey2 y))

lemma hbSeqPass_hb1_bounds (comb : LcgSym54Comb) {n K : ℕ} (h1K : 1 ≤ K) (l : Fin (2 * K) → Fin (n + 1)) :
    ∀ r ∈ hbSeqPass (hb1SortedList K l),
      r.kind ≤ 3 ∧ r.m < 2 ^ wOf K ∧ r.occ < 2 ^ wOf K ∧ r.dest < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K := by
  have hs1_bnd : ∀ r ∈ hb1SortedList K l, r.kind ≤ 3 ∧ r.kind ≠ 2 ∧ (r.kind = 0 → r.dest = 0) ∧
      r.m < 2 ^ wOf K ∧ r.occ < 2 ^ wOf K ∧ r.dest < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K := fun r hr =>
    hbInit_bounds comb h1K l r ((hb1SortedList_mem_iff K l r).mp hr)
  have h1pos : 1 ≤ (hb1SortedList K l).length := by
    rw [hb1SortedList_length, arity_eq_two_pow]; exact Nat.two_pow_pos _
  rw [hbSeqPass_eq_hbSeqState _ h1pos]
  exact (hbSeqState_inv (hb1SortedList K l) (wOf K) hs1_bnd ((hb1SortedList K l).length - 1)).1

lemma hb2SortedList_length (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    (hb2SortedList K l).length = arity (dHbOf K + 1) := by
  dsimp [hb2SortedList]
  rw [List.length_mergeSort, hbSeqPass_length, hb1SortedList_length]

lemma hb2SortedList_orig_nodup (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    ((hb2SortedList K l).map (·.orig)).Nodup := by
  have hp : List.Perm ((hb2SortedList K l).map (·.orig))
      ((hbSeqPass (hb1SortedList K l)).map (·.orig)) :=
    (List.mergeSort_perm _ _).map _
  have h1pos : 1 ≤ (hb1SortedList K l).length := by
    rw [hb1SortedList_length, arity_eq_two_pow]; exact Nat.two_pow_pos _
  rw [hp.nodup_iff, hbSeqPass_eq_hbSeqState _ h1pos, hbSeqState_map_orig]
  exact hb1SortedList_orig_nodup K l

def step3Circ (as : AlonsoSchottSil54) (br : BitonicRouting54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (h1K : 1 ≤ K) : LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList [
    hbInitCirc as arith n K d,
    sortHb1Circ as br n K d,
    hbSeqPassCirc as arith n K d h1K,
    copyToRec3Circ as arith n K d,
    sortHb2Circ as br n K d
  ]



end HarmBucketWork54


