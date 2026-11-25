-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_7
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54_7
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:46:50.114743+00:00
-- url     : https://prove2.me/theorems/84ce3609-338a-54a7-9d24-d8685262e266
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (7/11)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 7 of 11 (`harmBucketWork54_7`).
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

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (7/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

def eRec3Dest (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q
    1 (wOf K) (by dsimp [wR2Hb, wK2Hb]; omega)

def eRec3Orig (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q
    (1 + wOf K) (wOf K) (by dsimp [wR2Hb, wK2Hb]; omega)

def eRec3Kind (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin 2 ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q
    (wK2Hb K) 2 (by dsimp [wR2Hb, wP2Hb, wK2Hb]; omega)

def eRec3DVal (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q
    (wK2Hb K + 2) (wOf K) (by dsimp [wR2Hb, wP2Hb, wK2Hb]; omega)

-- Block & field disjointness
lemma eRec2_disjoint_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (hk : k ≠ ⟨11, by decide⟩) :
    ∀ a b, eRec2 as n K d a ≠ ancEmb as n K d k b :=
  ancRegSlice_disjoint_anc as n K d hk.symm _ _ _

lemma eTr2a_disjoint_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (hk : k ≠ ⟨12, by decide⟩) :
    ∀ a b, eTr2a as n K d a ≠ ancEmb as n K d k b :=
  ancPrefix_disjoint_anc as n K d hk.symm _ _

lemma eRec3_disjoint_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (hk : k ≠ ⟨13, by decide⟩) :
    ∀ a b, eRec3 as n K d a ≠ ancEmb as n K d k b :=
  ancRegSlice_disjoint_anc as n K d hk.symm _ _ _

lemma eTr2b_disjoint_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (hk : k ≠ ⟨14, by decide⟩) :
    ∀ a b, eTr2b as n K d a ≠ ancEmb as n K d k b :=
  ancPrefix_disjoint_anc as n K d hk.symm _ _

lemma eRec2_disjoint_eTr2a (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec2 as n K d a ≠ eTr2a as n K d b :=
  trans_disjoint_right (eRec2_disjoint_anc_other as n K d ⟨12, by decide⟩ (by decide))

lemma eRec2_disjoint_eSort2aAnc (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec2 as n K d a ≠ eSort2aAnc as n K d b :=
  trans_disjoint_right (eRec2_disjoint_anc_other as n K d ⟨17, by decide⟩ (by decide))

lemma eTr2a_disjoint_eSort2aAnc (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eTr2a as n K d a ≠ eSort2aAnc as n K d b :=
  trans_disjoint_right (eTr2a_disjoint_anc_other as n K d ⟨17, by decide⟩ (by decide))

lemma eRec3_disjoint_eTr2b (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec3 as n K d a ≠ eTr2b as n K d b :=
  trans_disjoint_right (eRec3_disjoint_anc_other as n K d ⟨14, by decide⟩ (by decide))

lemma eRec3_disjoint_eSort2bAnc (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec3 as n K d a ≠ eSort2bAnc as n K d b :=
  trans_disjoint_right (eRec3_disjoint_anc_other as n K d ⟨18, by decide⟩ (by decide))

lemma eTr2b_disjoint_eSort2bAnc (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eTr2b as n K d a ≠ eSort2bAnc as n K d b :=
  trans_disjoint_right (eTr2b_disjoint_anc_other as n K d ⟨18, by decide⟩ (by decide))

lemma ancRegSlot_disjoint_ancRegField (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (N1 w1 : ℕ) (h1 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N1 * w1)
    (q1 : Fin N1) (N2 w2 : ℕ) (h2 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k2 = N2 * w2)
    (q2 : Fin N2) (o2 l2 : ℕ) (hf2 : o2 + l2 ≤ w2) :
    ∀ a b, ancRegSlot as n K d k1 N1 w1 h1 q1 a ≠
      ancRegField as n K d k2 N2 w2 h2 q2 o2 l2 hf2 b :=
  fun a b h => ancRegField_disjoint_ancRegSlot as n K d hk.symm N2 w2 h2 q2 o2 l2 hf2 N1 w1 h1 q1 b a h.symm

lemma ancRegField_disjoint_ancRegField (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (N1 w1 : ℕ) (h1 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N1 * w1)
    (q1 : Fin N1) (o1 l1 : ℕ) (hf1 : o1 + l1 ≤ w1)
    (N2 w2 : ℕ) (h2 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k2 = N2 * w2)
    (q2 : Fin N2) (o2 l2 : ℕ) (hf2 : o2 + l2 ≤ w2) :
    ∀ a b, ancRegField as n K d k1 N1 w1 h1 q1 o1 l1 hf1 a ≠
      ancRegField as n K d k2 N2 w2 h2 q2 o2 l2 hf2 b :=
  trans_disjoint_right (ancRegField_disjoint_ancRegSlot as n K d hk N1 w1 h1 q1 o1 l1 hf1 N2 w2 h2 q2)

lemma eRec2_disjoint_eRec3 (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec2 as n K d a ≠ eRec3 as n K d b :=
  trans_disjoint_right (eRec2_disjoint_anc_other as n K d ⟨13, by decide⟩ (by decide))

lemma eRec2_disjoint_eSeqB (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec2 as n K d a ≠ eSeqB as n K d b :=
  trans_disjoint_right (eRec2_disjoint_anc_other as n K d ⟨19, by decide⟩ (by decide))

lemma eSeqB_disjoint_eRec2 (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eSeqB as n K d a ≠ eRec2 as n K d b :=
  fun a b h => eRec2_disjoint_eSeqB as n K d b a h.symm

lemma eRec2_disjoint_eSeqCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec2 as n K d a ≠ eSeqCtrl as n K d b :=
  trans_disjoint_right (eRec2_disjoint_anc_other as n K d ⟨20, by decide⟩ (by decide))

lemma eSeqCtrl_disjoint_eRec2 (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eSeqCtrl as n K d a ≠ eRec2 as n K d b :=
  fun a b h => eRec2_disjoint_eSeqCtrl as n K d b a h.symm

lemma eRec3_disjoint_eRec2 (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec3 as n K d a ≠ eRec2 as n K d b :=
  fun a b h => eRec2_disjoint_eRec3 as n K d b a h.symm

lemma eTr2a_disjoint_eRec2 (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eTr2a as n K d a ≠ eRec2 as n K d b :=
  fun a b h => eRec2_disjoint_eTr2a as n K d b a h.symm

lemma eRec2_disjoint_eActReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec2 as n K d a ≠ eActReg as n K d b :=
  trans_disjoint_right (eRec2_disjoint_anc_other as n K d ⟨1, by decide⟩ (by decide))

lemma eRec2_disjoint_eMReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec2 as n K d a ≠ eMReg as n K d b :=
  trans_disjoint_right (eRec2_disjoint_anc_other as n K d ⟨0, by decide⟩ (by decide))

lemma eRec2_disjoint_eOccReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec2 as n K d a ≠ eOccReg as n K d b :=
  trans_disjoint_right (eRec2_disjoint_anc_other as n K d ⟨2, by decide⟩ (by decide))

lemma eSeqBSlot_disjoint (as : AlonsoSchottSil54) (n K d : ℕ) {j1 j2 : Fin 4} (hj : j1 ≠ j2) :
    ∀ a b, eSeqBSlot as n K d j1 a ≠ eSeqBSlot as n K d j2 b := by
  intro a b h
  have h1 := (eSeqB as n K d).injective h
  exact sliceEmb_disjoint (by omega) (by omega)
    (by rcases Nat.lt_trichotomy j1.1 j2.1 with hlt | heq | hgt
        · exact Or.inl (by omega)
        · exact absurd (Fin.ext heq) hj
        · exact Or.inr (by omega)) a b h1

lemma eSeqB_disjoint_eSeqCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eSeqB as n K d a ≠ eSeqCtrl as n K d b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨19, by decide⟩) (k2 := ⟨20, by decide⟩) (by decide) _ _)

lemma eSeqB_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1) :
    ∀ a b, eSeqB as n K d a ≠ eArith345 as n K d subLen hle b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨19, by decide⟩) (k2 := ⟨22, by decide⟩) (by decide) _ _)

lemma eSeqCtrl_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1) :
    ∀ a b, eSeqCtrl as n K d a ≠ eArith345 as n K d subLen hle b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨20, by decide⟩) (k2 := ⟨22, by decide⟩) (by decide) _ _)

lemma eSeqBSlot_disjoint_eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ wOf K + 1) (j : Fin 4) :
    ∀ a b, eSeqBSlot as n K d j a ≠ eArith345 as n K d subLen hle b :=
  trans_disjoint_left (eSeqB_disjoint_eArith345 as n K d subLen hle)

lemma eSeqCtrl_disjoint_eSeqB (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eSeqCtrl as n K d a ≠ eSeqB as n K d b :=
  fun a b h => eSeqB_disjoint_eSeqCtrl as n K d b a h.symm

lemma eSeqCtrl_disjoint_eSeqBSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin 4) :
    ∀ a b, eSeqCtrl as n K d a ≠ eSeqBSlot as n K d j b :=
  fun a b h => trans_disjoint_left (eSeqB_disjoint_eSeqCtrl as n K d) b a h.symm

lemma eActSlot_disjoint_eRec2Inact (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eActSlot as n K d i a ≠ eRec2Inact as n K d q b :=
  fun a b h => ancRegField_disjoint_anc as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨1, by decide⟩) (by decide) _ _ _ _ _ _ _ b _ h.symm

lemma eActSlot_disjoint_eRec2M (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eActSlot as n K d i a ≠ eRec2M as n K d q b :=
  fun a b h => ancRegField_disjoint_anc as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨1, by decide⟩) (by decide) _ _ _ _ _ _ _ b _ h.symm

lemma eActSlot_disjoint_eRec2Occ (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eActSlot as n K d i a ≠ eRec2Occ as n K d q b :=
  fun a b h => ancRegField_disjoint_anc as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨1, by decide⟩) (by decide) _ _ _ _ _ _ _ b _ h.symm

lemma eActSlot_disjoint_eRec2KR1 (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eActSlot as n K d i a ≠ eRec2KR1 as n K d q b :=
  fun a b h => ancRegField_disjoint_anc as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨1, by decide⟩) (by decide) _ _ _ _ _ _ _ b _ h.symm

lemma eActSlot_disjoint_eRec2Kind (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eActSlot as n K d i a ≠ eRec2Kind as n K d q b :=
  fun a b h => ancRegField_disjoint_anc as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨1, by decide⟩) (by decide) _ _ _ _ _ _ _ b _ h.symm

lemma eMSlot_disjoint_eRec2M (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eMSlot as n K d i a ≠ eRec2M as n K d q b :=
  fun a b h => ancRegField_disjoint_anc as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨0, by decide⟩) (by decide) _ _ _ _ _ _ _ b _ h.symm

lemma eOccSlot_disjoint_eRec2Occ (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) (q : Fin (arity (dHbOf K + 1))) :
    ∀ a b, eOccSlot as n K d i a ≠ eRec2Occ as n K d q b :=
  fun a b h => ancRegField_disjoint_anc as n K d (k1 := ⟨11, by decide⟩) (k2 := ⟨2, by decide⟩) (by decide) _ _ _ _ _ _ _ b _ h.symm

lemma eActSlot_disjoint_eMSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i j : Fin (2 * K)) :
    ∀ a b, eActSlot as n K d i a ≠ eMSlot as n K d j b :=
  fun a b h => ancEmb_disjoint as n K d (k1 := ⟨1, by decide⟩) (k2 := ⟨0, by decide⟩) (by decide) _ _ h

lemma eActSlot_disjoint_eOccSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i j : Fin (2 * K)) :
    ∀ a b, eActSlot as n K d i a ≠ eOccSlot as n K d j b :=
  fun a b h => ancEmb_disjoint as n K d (k1 := ⟨1, by decide⟩) (k2 := ⟨2, by decide⟩) (by decide) _ _ h

/-! #### 7.2 Pure `rec2` & `rec3` Encodings + Lex Isomorphisms -/

def rec2KeyFn (w : ℕ) (inact : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w) :
    Qubits (1 + w + w + 2 + w) :=
  Fin.append (Fin.append (Fin.append (Fin.append inact m) occ) kr1) orig

def rec2PayFn (w : ℕ) (kind : Qubits 2) (dest dval : Qubits w) : Qubits (2 + w + w) :=
  Fin.append (Fin.append kind dest) dval

def rec2SlotFn (w : ℕ) (inact : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) : Qubits ((1 + w + w + 2 + w) + (2 + w + w)) :=
  Fin.append (rec2KeyFn w inact m occ kr1 orig) (rec2PayFn w kind dest dval)

lemma recKey54_rec2SlotFn (w : ℕ) (inact : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    recKey54 (rec2SlotFn w inact m occ kr1 orig kind dest dval) = rec2KeyFn w inact m occ kr1 orig := by
  funext i; simp [recKey54, rec2SlotFn]

lemma recPay54_rec2SlotFn (w : ℕ) (inact : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    recPay54 (rec2SlotFn w inact m occ kr1 orig kind dest dval) = rec2PayFn w kind dest dval := by
  funext j; simp [recPay54, rec2SlotFn]

lemma rec2SlotFn_zero (w : ℕ) :
    rec2SlotFn w (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
      (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) = fun _ => false := by
  funext u
  dsimp [rec2SlotFn, rec2KeyFn, rec2PayFn]
  induction u using Fin.addCases with
  | left a =>
    rw [Fin.append_left]
    induction a using Fin.addCases with
    | left b =>
      rw [Fin.append_left]
      induction b using Fin.addCases with
      | left c =>
        rw [Fin.append_left]
        induction c using Fin.addCases with
        | left d => rw [Fin.append_left]; induction d using Fin.addCases <;> simp
        | right _ => simp
      | right _ => simp
    | right _ => simp
  | right e =>
    rw [Fin.append_right]
    induction e using Fin.addCases with
    | left f => rw [Fin.append_left]; induction f using Fin.addCases <;> simp
    | right _ => simp

lemma rec2SlotFn_comp_0 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    rec2SlotFn w na m occ kr1 orig kind dest dval ∘ sliceEmb 0 1 (by omega) = na := by
  funext i
  have heq : sliceEmb 0 1 (by omega) i =
      Fin.castAdd (2 + w + w) (Fin.castAdd w (Fin.castAdd 2 (Fin.castAdd w (Fin.castAdd w i)))) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec2SlotFn, rec2KeyFn, Fin.append_left, Fin.append_left,
    Fin.append_left, Fin.append_left, Fin.append_left]

lemma rec2SlotFn_comp_1 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    rec2SlotFn w na m occ kr1 orig kind dest dval ∘ sliceEmb 1 w (by omega) = m := by
  funext i
  have heq : sliceEmb 1 w (by omega) i =
      Fin.castAdd (2 + w + w) (Fin.castAdd w (Fin.castAdd 2 (Fin.castAdd w (Fin.natAdd 1 i)))) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec2SlotFn, rec2KeyFn, Fin.append_left, Fin.append_left,
    Fin.append_left, Fin.append_left, Fin.append_right]

lemma rec2SlotFn_comp_2 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    rec2SlotFn w na m occ kr1 orig kind dest dval ∘ sliceEmb (1 + w) w (by omega) = occ := by
  funext i
  have heq : sliceEmb (1 + w) w (by omega) i =
      Fin.castAdd (2 + w + w) (Fin.castAdd w (Fin.castAdd 2 (Fin.natAdd (1 + w) i))) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec2SlotFn, rec2KeyFn, Fin.append_left, Fin.append_left,
    Fin.append_left, Fin.append_right]

lemma rec2SlotFn_comp_3 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    rec2SlotFn w na m occ kr1 orig kind dest dval ∘ sliceEmb (1 + w + w) 2 (by omega) = kr1 := by
  funext i
  have heq : sliceEmb (1 + w + w) 2 (by omega) i =
      Fin.castAdd (2 + w + w) (Fin.castAdd w (Fin.natAdd (1 + w + w) i)) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec2SlotFn, rec2KeyFn, Fin.append_left, Fin.append_left, Fin.append_right]

lemma rec2SlotFn_comp_4 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    rec2SlotFn w na m occ kr1 orig kind dest dval ∘ sliceEmb (1 + w + w + 2) w (by omega) = orig := by
  funext i
  have heq : sliceEmb (1 + w + w + 2) w (by omega) i =
      Fin.castAdd (2 + w + w) (Fin.natAdd (1 + w + w + 2) i) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec2SlotFn, rec2KeyFn, Fin.append_left, Fin.append_right]

lemma rec2SlotFn_comp_5 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    rec2SlotFn w na m occ kr1 orig kind dest dval ∘ sliceEmb (1 + w + w + 2 + w) 2 (by omega) = kind := by
  funext i
  have heq : sliceEmb (1 + w + w + 2 + w) 2 (by omega) i =
      Fin.natAdd (1 + w + w + 2 + w) (Fin.castAdd w (Fin.castAdd w i)) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec2SlotFn, rec2PayFn, Fin.append_right, Fin.append_left, Fin.append_left]

lemma rec2SlotFn_comp_6 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    rec2SlotFn w na m occ kr1 orig kind dest dval ∘ sliceEmb (1 + w + w + 2 + w + 2) w (by omega) = dest := by
  funext i
  have heq : sliceEmb (1 + w + w + 2 + w + 2) w (by omega) i =
      Fin.natAdd (1 + w + w + 2 + w) (Fin.castAdd w (Fin.natAdd 2 i)) :=
    Fin.ext (by simp only [Fin.val_natAdd, Fin.val_castAdd, sliceEmb_apply]; omega)
  rw [Function.comp_apply, heq, rec2SlotFn, rec2PayFn, Fin.append_right, Fin.append_left, Fin.append_right]

lemma rec2SlotFn_comp_7 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    rec2SlotFn w na m occ kr1 orig kind dest dval ∘ sliceEmb (1 + w + w + 2 + w + 2 + w) w (by omega) = dval := by
  funext i
  have heq : sliceEmb (1 + w + w + 2 + w + 2 + w) w (by omega) i =
      Fin.natAdd (1 + w + w + 2 + w) (Fin.natAdd (2 + w) i) :=
    Fin.ext (by simp only [Fin.val_natAdd, sliceEmb_apply]; omega)
  rw [Function.comp_apply, heq, rec2SlotFn, rec2PayFn, Fin.append_right, Fin.append_right]

lemma eq_rec2SlotFn_iff (w : ℕ) (r : Qubits ((1 + w + w + 2 + w) + (2 + w + w)))
    (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2) (orig : Qubits w)
    (kind : Qubits 2) (dest dval : Qubits w) :
    r = rec2SlotFn w na m occ kr1 orig kind dest dval ↔
      r ∘ sliceEmb 0 1 (by omega) = na ∧
      r ∘ sliceEmb 1 w (by omega) = m ∧
      r ∘ sliceEmb (1 + w) w (by omega) = occ ∧
      r ∘ sliceEmb (1 + w + w) 2 (by omega) = kr1 ∧
      r ∘ sliceEmb (1 + w + w + 2) w (by omega) = orig ∧
      r ∘ sliceEmb (1 + w + w + 2 + w) 2 (by omega) = kind ∧
      r ∘ sliceEmb (1 + w + w + 2 + w + 2) w (by omega) = dest ∧
      r ∘ sliceEmb (1 + w + w + 2 + w + 2 + w) w (by omega) = dval := by
  constructor
  · rintro rfl
    exact ⟨rec2SlotFn_comp_0 _ _ _ _ _ _ _ _ _, rec2SlotFn_comp_1 _ _ _ _ _ _ _ _ _,
      rec2SlotFn_comp_2 _ _ _ _ _ _ _ _ _, rec2SlotFn_comp_3 _ _ _ _ _ _ _ _ _,
      rec2SlotFn_comp_4 _ _ _ _ _ _ _ _ _, rec2SlotFn_comp_5 _ _ _ _ _ _ _ _ _,
      rec2SlotFn_comp_6 _ _ _ _ _ _ _ _ _, rec2SlotFn_comp_7 _ _ _ _ _ _ _ _ _⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
    funext u; have hu := u.isLt
    by_cases hu0 : u.1 < 1
    · have heq : u = sliceEmb 0 1 (by omega) ⟨u.1, hu0⟩ := Fin.ext (by simp only [sliceEmb_apply]; omega)
      have hrhs := congrFun (rec2SlotFn_comp_0 w na m occ kr1 orig kind dest dval) ⟨u.1, hu0⟩
      rw [heq, ← Function.comp_apply (f := r), h0, ← hrhs]; rfl
    · by_cases hu1 : u.1 < 1 + w
      · have heq : u = sliceEmb 1 w (by omega) ⟨u.1 - 1, by omega⟩ := Fin.ext (by simp only [sliceEmb_apply]; omega)
        have hrhs := congrFun (rec2SlotFn_comp_1 w na m occ kr1 orig kind dest dval) ⟨u.1 - 1, by omega⟩
        rw [heq, ← Function.comp_apply (f := r), h1, ← hrhs]; rfl
      · by_cases hu2 : u.1 < 1 + w + w
        · have heq : u = sliceEmb (1 + w) w (by omega) ⟨u.1 - (1 + w), by omega⟩ :=
            Fin.ext (by simp only [sliceEmb_apply]; omega)
          have hrhs := congrFun (rec2SlotFn_comp_2 w na m occ kr1 orig kind dest dval) ⟨u.1 - (1 + w), by omega⟩
          rw [heq, ← Function.comp_apply (f := r), h2, ← hrhs]; rfl
        · by_cases hu3 : u.1 < 1 + w + w + 2
          · have heq : u = sliceEmb (1 + w + w) 2 (by omega) ⟨u.1 - (1 + w + w), by omega⟩ :=
              Fin.ext (by simp only [sliceEmb_apply]; omega)
            have hrhs := congrFun (rec2SlotFn_comp_3 w na m occ kr1 orig kind dest dval) ⟨u.1 - (1 + w + w), by omega⟩
            rw [heq, ← Function.comp_apply (f := r), h3, ← hrhs]; rfl
          · by_cases hu4 : u.1 < 1 + w + w + 2 + w
            · have heq : u = sliceEmb (1 + w + w + 2) w (by omega) ⟨u.1 - (1 + w + w + 2), by omega⟩ :=
                Fin.ext (by simp only [sliceEmb_apply]; omega)
              have hrhs := congrFun (rec2SlotFn_comp_4 w na m occ kr1 orig kind dest dval)
                ⟨u.1 - (1 + w + w + 2), by omega⟩
              rw [heq, ← Function.comp_apply (f := r), h4, ← hrhs]; rfl
            · by_cases hu5 : u.1 < 1 + w + w + 2 + w + 2
              · have heq : u = sliceEmb (1 + w + w + 2 + w) 2 (by omega) ⟨u.1 - (1 + w + w + 2 + w), by omega⟩ :=
                  Fin.ext (by simp only [sliceEmb_apply]; omega)
                have hrhs := congrFun (rec2SlotFn_comp_5 w na m occ kr1 orig kind dest dval)
                  ⟨u.1 - (1 + w + w + 2 + w), by omega⟩
                rw [heq, ← Function.comp_apply (f := r), h5, ← hrhs]; rfl
              · by_cases hu6 : u.1 < 1 + w + w + 2 + w + 2 + w
                · have heq : u = sliceEmb (1 + w + w + 2 + w + 2) w (by omega)
                      ⟨u.1 - (1 + w + w + 2 + w + 2), by omega⟩ :=
                    Fin.ext (by simp only [sliceEmb_apply]; omega)
                  have hrhs := congrFun (rec2SlotFn_comp_6 w na m occ kr1 orig kind dest dval)
                    ⟨u.1 - (1 + w + w + 2 + w + 2), by omega⟩
                  rw [heq, ← Function.comp_apply (f := r), h6, ← hrhs]; rfl
                · have heq : u = sliceEmb (1 + w + w + 2 + w + 2 + w) w (by omega)
                      ⟨u.1 - (1 + w + w + 2 + w + 2 + w), by omega⟩ :=
                    Fin.ext (by simp only [sliceEmb_apply]; omega)
                  have hrhs := congrFun (rec2SlotFn_comp_7 w na m occ kr1 orig kind dest dval)
                    ⟨u.1 - (1 + w + w + 2 + w + 2 + w), by omega⟩
                  rw [heq, ← Function.comp_apply (f := r), h7, ← hrhs]; rfl

lemma updateOn_rec2SlotFn_0 (w : ℕ) (na₀ na₁ : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2)
    (orig : Qubits w) (kind : Qubits 2) (dest dval : Qubits w) :
    updateOn (sliceEmb 0 1 (by omega)) (rec2SlotFn w na₀ m occ kr1 orig kind dest dval) na₁ =
      rec2SlotFn w na₁ m occ kr1 orig kind dest dval := by
  rw [eq_rec2SlotFn_iff]
  refine ⟨updateOn_comp_emb _ _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]
    first | exact rec2SlotFn_comp_1 .. | exact rec2SlotFn_comp_2 .. | exact rec2SlotFn_comp_3 ..
          | exact rec2SlotFn_comp_4 .. | exact rec2SlotFn_comp_5 .. | exact rec2SlotFn_comp_6 ..
          | exact rec2SlotFn_comp_7 ..


end HarmBucketWork54


