-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_5
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54_5
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:42:32.517254+00:00
-- url     : https://prove2.me/theorems/a027641c-d210-45da-82f2-78ce8aeb3efe
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (5/11)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 5 of 11 (`harmBucketWork54_5`).
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

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (5/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

lemma eOne12_disjoint_eMSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eOne12 as n K d a ≠ eMSlot as n K d i b :=
  trans_disjoint_right (trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨6, by decide⟩) (k2 := ⟨0, by decide⟩) (by decide) 1 _))

lemma eMSlot_disjoint_eOne12 (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eMSlot as n K d i a ≠ eOne12 as n K d b :=
  fun a b h => eOne12_disjoint_eMSlot as n K d i b a h.symm

lemma eOne12_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) :
    ∀ a b, eOne12 as n K d a ≠ eArith12Pref as n K d subLen hle b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨6, by decide⟩) (k2 := ⟨10, by decide⟩) (by decide) 1 _)

lemma eMSlot_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) (i : Fin (2 * K)) :
    ∀ a b, eMSlot as n K d i a ≠ eArith12Pref as n K d subLen hle b :=
  trans_disjoint_right (trans_disjoint_left (eMReg_disjoint_anc_other as n K d ⟨10, by decide⟩ (by decide)))

lemma eActSlot_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) (i : Fin (2 * K)) :
    ∀ a b, eActSlot as n K d i a ≠ eArith12Pref as n K d subLen hle b :=
  trans_disjoint_right (trans_disjoint_left (eActReg_disjoint_anc_other as n K d ⟨10, by decide⟩ (by decide)))

lemma eActSlot_disjoint_eEqFlag (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eActSlot as n K d i a ≠ eEqFlag as n K d b :=
  trans_disjoint_right (trans_disjoint_left (eActReg_disjoint_anc_other as n K d ⟨5, by decide⟩ (by decide)))

lemma eActSlot_disjoint_eOne12 (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eActSlot as n K d i a ≠ eOne12 as n K d b :=
  trans_disjoint_right (trans_disjoint_left (eActReg_disjoint_anc_other as n K d ⟨6, by decide⟩ (by decide)))

/-! #### 6.3 Step 1 Circuit (`step1StepCirc`, `step1Circ`) -/

def step1StepCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (k : ℕ) (hk : k + 1 < 2 * K) : LayeredCircuit (totWiresDef as n K d) :=
  let s := sOf n
  let w := wOf K
  let lk := eLSlot as n K d ⟨k, by omega⟩
  let lk1 := eLSlot as n K d ⟨k + 1, hk⟩
  let mk := eMSlot as n K d ⟨k, by omega⟩
  let mk1 := eMSlot as n K d ⟨k + 1, hk⟩
  let ak1 := eActSlot as n K d ⟨k + 1, hk⟩
  let eqF := eEqFlag as n K d
  let oneW := eOne12 as n K d
  let ancS := eArith12Pref as n K d s (le_max_left _ _)
  let ancW1 := eArith12Pref as n K d (w + 1) (le_max_right _ _)
  let ancW := eArith12Pref as n K d w (Nat.le_trans (Nat.le_succ w) (le_max_right _ _))
  let c1 := (arith.eqRegCircuit s).mapWires
    (comb4 lk lk1 eqF ancS
      (eLSlot_disjoint_slot as n K d (by simp [Fin.ext_iff]))
      (eLSlot_disjoint_eEqFlag as n K d _)
      (eLSlot_disjoint_eEqFlag as n K d _)
      (eLSlot_disjoint_eArith12 as n K d _ _ _)
      (eLSlot_disjoint_eArith12 as n K d _ _ _)
      (eEqFlag_disjoint_eArith12 as n K d _ _))
  let c2 := (arith.ctrlCopyRegCircuit w).mapWires
    (comb3 eqF mk mk1
      (eEqFlag_disjoint_eMSlot as n K d _)
      (eEqFlag_disjoint_eMSlot as n K d _)
      (eMSlot_disjoint_slot as n K d (by simp [Fin.ext_iff])))
  let c3 := (arith.setConstMSBCircuit 1 1).mapWires oneW
  let c4 := (arith.ctrlAddConstInPlaceMSBCircuit w 1).mapWires
    (comb3 oneW mk1 ancW1
      (eOne12_disjoint_eMSlot as n K d _)
      (eOne12_disjoint_eArith12 as n K d _ _)
      (eMSlot_disjoint_eArith12 as n K d _ _ _))
  let c5 := c3
  let c6 := c1
  let c7 := (arith.ltConstMSBCircuit w 2).mapWires
    (comb3 mk1 ak1 ancW
      (eMSlot_disjoint_eActSlot as n K d _ _)
      (eMSlot_disjoint_eArith12 as n K d _ _ _)
      (eActSlot_disjoint_eArith12 as n K d _ _ _))
  let c8 := (arith.setConstMSBCircuit 1 1).mapWires ak1
  LayeredCircuit.seqList [c1, c2, c3, c4, c5, c6, c7, c8]

def mBitsFn (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (i : Fin (2 * K)) :
    Qubits (wOf K) :=
  natToBits (wOf K) (runOffset l i)

def actBitsFn (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (i : Fin (2 * K)) :
    Qubits 1 :=
  fun _ => decide (2 ≤ runOffset l i)

def occBitsFn (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (i : Fin (2 * K)) :
    Qubits (wOf K) :=
  if 2 ≤ runOffset l i then natToBits (wOf K) (runOcc l i) else fun _ => false

def step1Circ (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) :
    LayeredCircuit (totWiresDef as n K d) :=
  let cInit := (arith.setConstMSBCircuit (wOf K) 1).mapWires (eMSlot as n K d ⟨0, by omega⟩)
  let cLoop := LayeredCircuit.seqList ((List.range (2 * K - 1)).map fun k =>
    if hk : k + 1 < 2 * K then step1StepCirc as arith n K d k hk else LayeredCircuit.id _)
  cInit.seq cLoop


lemma nat_mul_add_le_iff {B : ℕ} (a₁ a₂ : ℕ) {b₁ b₂ : ℕ} (hb₁ : b₁ < B) (hb₂ : b₂ < B) :
    a₁ * B + b₁ ≤ a₂ * B + b₂ ↔ a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ ≤ b₂) := by
  constructor
  · intro h
    rcases lt_trichotomy a₁ a₂ with hlt | rfl | hgt
    · exact Or.inl hlt
    · exact Or.inr ⟨rfl, by omega⟩
    · have : a₂ + 1 ≤ a₁ := hgt
      nlinarith
  · rintro (hlt | ⟨rfl, hle⟩)
    · have : a₁ + 1 ≤ a₂ := hlt
      nlinarith
    · omega

lemma nat_mul_add_eq_iff {B : ℕ} (a₁ a₂ : ℕ) {b₁ b₂ : ℕ} (hb₁ : b₁ < B) (hb₂ : b₂ < B) :
    a₁ * B + b₁ = a₂ * B + b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · intro h
    have h1 := (nat_mul_add_le_iff a₁ a₂ hb₁ hb₂).mp h.le
    have h2 := (nat_mul_add_le_iff a₂ a₁ hb₂ hb₁).mp h.symm.le
    rcases h1 with hlt1 | ⟨rfl, hle1⟩ <;> rcases h2 with hlt2 | ⟨_, hle2⟩
    · omega
    · omega
    · omega
    · exact ⟨rfl, le_antisymm hle1 hle2⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma nat_mul_add_lt_iff {B : ℕ} (a₁ a₂ : ℕ) {b₁ b₂ : ℕ} (hb₁ : b₁ < B) (hb₂ : b₂ < B) :
    a₁ * B + b₁ < a₂ * B + b₂ ↔ a₁ < a₂ ∨ (a₁ = a₂ ∧ b₁ < b₂) := by
  rw [← not_le, nat_mul_add_le_iff a₂ a₁ hb₂ hb₁]
  omega

lemma natToBits_zero (comb : LcgSym54Comb) (w : ℕ) :
    natToBits w 0 = fun _ : Fin w => false := by
  apply comb.bitsToNat_inj
  rw [comb.bitsToNat_natToBits (Nat.two_pow_pos w)]
  simp [bitsToNat]

lemma natToBits_one_zero (comb : LcgSym54Comb) :
    natToBits 1 0 = fun _ : Fin 1 => false :=
  natToBits_zero comb 1

lemma updateOn_ancRegField_eq_slot (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (N_rec w_r : ℕ) (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    (z : Qubits (totWiresDef as n K d)) (q : Fin N_rec)
    (fOff fLen : ℕ) (hf : fOff + fLen ≤ w_r) (val : Qubits fLen) :
    updateOn (ancRegField as n K d k N_rec w_r hlen q fOff fLen hf) z val =
      updateOn (ancRegSlot as n K d k N_rec w_r hlen q) z
        (updateOn (sliceEmb fOff fLen hf) (z ∘ ancRegSlot as n K d k N_rec w_r hlen q) val) :=
  updateOn_trans_emb (sliceEmb fOff fLen hf) (ancRegSlot as n K d k N_rec w_r hlen q) z val

lemma updateOn_ancRegSlot_eq (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (N_rec w_r : ℕ) (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    (z : Qubits (totWiresDef as n K d)) (arr : Fin N_rec → Qubits w_r)
    (hz : z ∘ ancRegSlice as n K d k N_rec w_r hlen = flatReg N_rec w_r arr)
    (q : Fin N_rec) (val : Qubits w_r) :
    updateOn (ancRegSlot as n K d k N_rec w_r hlen q) z val =
      updateOn (ancRegSlice as n K d k N_rec w_r hlen) z
        (flatReg N_rec w_r (Function.update arr q val)) := by
  conv_lhs => rw [← updateOn_noop (ancRegSlice as n K d k N_rec w_r hlen) z (flatReg N_rec w_r arr) hz]
  exact updateOn_slot_absorb _ z arr q val

lemma updateOn_packDTA54_eq_two {W N_d w_d N_t w_a : ℕ}
    (eArr : Fin (N_d * w_d) ↪ Fin W) (eTr : Fin N_t ↪ Fin W) (eAnc : Fin w_a ↪ Fin W)
    (h1 : ∀ a b, eArr a ≠ eTr b) (h2 : ∀ a b, eArr a ≠ eAnc b) (h3 : ∀ a b, eTr a ≠ eAnc b)
    (z : Qubits W) (hanc : z ∘ eAnc = fun _ => false)
    (arr : Fin N_d → Qubits w_d) (tr : Fin N_t → Bool) :
    updateOn (packDTA54Emb eArr eTr eAnc h1 h2 h3) z (packDTA54 N_d w_d N_t w_a arr tr) =
      updateOn eTr (updateOn eArr z (flatReg N_d w_d arr)) tr := by
  funext u
  by_cases huR : u ∈ Set.range eArr
  · rcases huR with ⟨i, rfl⟩
    have hnotT : eArr i ∉ Set.range eTr := by rintro ⟨j, hj⟩; exact h1 i j hj.symm
    rw [updateOn_apply_not_mem _ _ _ hnotT, updateOn_apply_emb]
    exact congrFun (updateOn_packDTA54_arr eArr eTr eAnc h1 h2 h3 z arr tr) i
  · by_cases huT : u ∈ Set.range eTr
    · rcases huT with ⟨j, rfl⟩
      rw [updateOn_apply_emb]
      exact congrFun (updateOn_packDTA54_tr eArr eTr eAnc h1 h2 h3 z arr tr) j
    · by_cases huA : u ∈ Set.range eAnc
      · rcases huA with ⟨k, rfl⟩
        have ha := congrFun (updateOn_packDTA54_anc eArr eTr eAnc h1 h2 h3 z arr tr) k
        have hb := congrFun hanc k
        rw [updateOn_apply_not_mem _ _ _ huT, updateOn_apply_not_mem _ _ _ huR]
        exact ha.trans hb.symm
      · have hnotP : u ∉ Set.range (packDTA54Emb eArr eTr eAnc h1 h2 h3) := by
          rintro ⟨x, rfl⟩
          induction x using Fin.addCases with
          | left xy =>
            induction xy using Fin.addCases with
            | left i => exact huR ⟨i, by simp⟩
            | right j => exact huT ⟨j, by simp⟩
          | right k => exact huA ⟨k, by simp⟩
        rw [updateOn_apply_not_mem _ _ _ hnotP, updateOn_apply_not_mem _ _ _ huT,
          updateOn_apply_not_mem _ _ _ huR]

/-! #### 6.5 Step 2 Embeddings & Disjointness -/

def eTr1 (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (sortTraceSize (dOccOf K)) ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨4, by decide⟩ (sortTraceSize (dOccOf K)) (by rw [ancLen_4])

def eSort1Anc (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (wK1Occ K) ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨7, by decide⟩ (wK1Occ K) (by rw [ancLen_7])

def eScanB (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin 3 ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨8, by decide⟩ 3 (by rw [ancLen_8])

def eScanBSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin 3) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  (sliceEmb j.1 1 (by omega)).trans (eScanB as n K d)

def eScanCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨9, by decide⟩ 1 (by rw [ancLen_9])

def eRec1NotAct (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dOccOf K))) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) q
    0 1 (by dsimp [wR1Occ, wK1Occ]; omega)

def eRec1M (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dOccOf K))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) q
    1 (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega)

def eRec1Idx (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dOccOf K))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) q
    (1 + wOf K) (wOf K) (by dsimp [wR1Occ, wK1Occ]; omega)

def eRec1Occ (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dOccOf K))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _) q
    (wK1Occ K) (wOf K) (by dsimp [wR1Occ, wP1Occ, wK1Occ]; omega)

lemma eOccReg_disjoint_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (hk : k ≠ ⟨2, by decide⟩) :
    ∀ a b, eOccReg as n K d a ≠ ancEmb as n K d k b :=
  ancRegSlice_disjoint_anc as n K d hk.symm _ _ _

lemma eRec1Reg_disjoint_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (hk : k ≠ ⟨3, by decide⟩) :
    ∀ a b, eRec1Reg as n K d a ≠ ancEmb as n K d k b :=
  ancRegSlice_disjoint_anc as n K d hk.symm _ _ _

lemma eTr1_disjoint_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (hk : k ≠ ⟨4, by decide⟩) :
    ∀ a b, eTr1 as n K d a ≠ ancEmb as n K d k b :=
  ancPrefix_disjoint_anc as n K d hk.symm _ _

lemma eRec1M_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ)
    {q1 q2 : Fin (arity (dOccOf K))} (hq : q1 ≠ q2) :
    ∀ a b, eRec1M as n K d q1 a ≠ eRec1M as n K d q2 b :=
  ancRegField_disjoint_slot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K)
    (ancLen_3 n K d _) hq _ _

lemma eRec1Occ_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ)
    {q1 q2 : Fin (arity (dOccOf K))} (hq : q1 ≠ q2) :
    ∀ a b, eRec1Occ as n K d q1 a ≠ eRec1Occ as n K d q2 b :=
  ancRegField_disjoint_slot as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K)
    (ancLen_3 n K d _) hq _ _

lemma eRec1Reg_disjoint_eMReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec1Reg as n K d a ≠ eMReg as n K d b :=
  trans_disjoint_right (eRec1Reg_disjoint_anc_other as n K d ⟨0, by decide⟩ (by decide))

lemma eRec1Reg_disjoint_eActReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec1Reg as n K d a ≠ eActReg as n K d b :=
  trans_disjoint_right (eRec1Reg_disjoint_anc_other as n K d ⟨1, by decide⟩ (by decide))

lemma eRec1Reg_disjoint_eOccReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec1Reg as n K d a ≠ eOccReg as n K d b :=
  trans_disjoint_right (eRec1Reg_disjoint_anc_other as n K d ⟨2, by decide⟩ (by decide))

lemma eRec1Reg_disjoint_eTr1 (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec1Reg as n K d a ≠ eTr1 as n K d b :=
  trans_disjoint_right (eRec1Reg_disjoint_anc_other as n K d ⟨4, by decide⟩ (by decide))

lemma eRec1Reg_disjoint_eSort1Anc (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec1Reg as n K d a ≠ eSort1Anc as n K d b :=
  trans_disjoint_right (eRec1Reg_disjoint_anc_other as n K d ⟨7, by decide⟩ (by decide))

lemma eTr1_disjoint_eSort1Anc (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eTr1 as n K d a ≠ eSort1Anc as n K d b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨4, by decide⟩) (k2 := ⟨7, by decide⟩) (by decide) _ _)

lemma eRec1Reg_disjoint_eL (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec1Reg as n K d a ≠ eL as n K d b :=
  trans_disjoint_left (anc_disjoint_eL as n K d ⟨3, by decide⟩)

lemma eOccReg_disjoint_eL (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eOccReg as n K d a ≠ eL as n K d b :=
  trans_disjoint_left (anc_disjoint_eL as n K d ⟨2, by decide⟩)

lemma eOccReg_disjoint_eMReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eOccReg as n K d a ≠ eMReg as n K d b :=
  trans_disjoint_right (eOccReg_disjoint_anc_other as n K d ⟨0, by decide⟩ (by decide))

lemma eOccReg_disjoint_eActReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eOccReg as n K d a ≠ eActReg as n K d b :=
  trans_disjoint_right (eOccReg_disjoint_anc_other as n K d ⟨1, by decide⟩ (by decide))

lemma eScanBSlot_disjoint (as : AlonsoSchottSil54) (n K d : ℕ) {j1 j2 : Fin 3} (hj : j1 ≠ j2) :
    ∀ a b, eScanBSlot as n K d j1 a ≠ eScanBSlot as n K d j2 b := by
  intro a b h
  have h1 := (eScanB as n K d).injective h
  exact sliceEmb_disjoint (by omega) (by omega)
    (by rcases Nat.lt_trichotomy j1.1 j2.1 with hlt | heq | hgt
        · exact Or.inl (by omega)
        · exact absurd (Fin.ext heq) hj
        · exact Or.inr (by omega)) a b h1

lemma eRec1NotAct_disjoint_eScanBSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dOccOf K))) (j : Fin 3) :
    ∀ a b, eRec1NotAct as n K d q a ≠ eScanBSlot as n K d j b :=
  trans_disjoint_right (ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨8, by decide⟩)
    (by decide) _ _ _ _ _ _ _ _ _)

lemma eRec1M_disjoint_eScanBSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dOccOf K))) (j : Fin 3) :
    ∀ a b, eRec1M as n K d q a ≠ eScanBSlot as n K d j b :=
  trans_disjoint_right (ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨8, by decide⟩)
    (by decide) _ _ _ _ _ _ _ _ _)

lemma eRec1NotAct_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) (q : Fin (arity (dOccOf K))) :
    ∀ a b, eRec1NotAct as n K d q a ≠ eArith12Pref as n K d subLen hle b :=
  ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨10, by decide⟩) (by decide) _ _ _ _ _ _ _ _ _

lemma eRec1M_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) (q : Fin (arity (dOccOf K))) :
    ∀ a b, eRec1M as n K d q a ≠ eArith12Pref as n K d subLen hle b :=
  ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨10, by decide⟩) (by decide) _ _ _ _ _ _ _ _ _

lemma eRec1Occ_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) (q : Fin (arity (dOccOf K))) :
    ∀ a b, eRec1Occ as n K d q a ≠ eArith12Pref as n K d subLen hle b :=
  ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨10, by decide⟩) (by decide) _ _ _ _ _ _ _ _ _

lemma eScanBSlot_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) (j : Fin 3) :
    ∀ a b, eScanBSlot as n K d j a ≠ eArith12Pref as n K d subLen hle b :=
  trans_disjoint_left (trans_disjoint_right
    (ancPrefix_disjoint_anc as n K d (k1 := ⟨8, by decide⟩) (k2 := ⟨10, by decide⟩) (by decide) _ _))

lemma eScanB_disjoint_eScanCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eScanB as n K d a ≠ eScanCtrl as n K d b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨8, by decide⟩) (k2 := ⟨9, by decide⟩) (by decide) _ _)

lemma eScanB_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) :
    ∀ a b, eScanB as n K d a ≠ eArith12Pref as n K d subLen hle b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨8, by decide⟩) (k2 := ⟨10, by decide⟩) (by decide) _ _)

lemma eScanCtrl_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) :
    ∀ a b, eScanCtrl as n K d a ≠ eArith12Pref as n K d subLen hle b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨9, by decide⟩) (k2 := ⟨10, by decide⟩) (by decide) _ _)

lemma eScanCtrl_disjoint_eRec1Occ (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dOccOf K))) :
    ∀ a b, eScanCtrl as n K d a ≠ eRec1Occ as n K d q b :=
  fun a b h => ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨9, by decide⟩)
    (by decide) _ _ _ _ _ _ _ _ _ b a h.symm

lemma eScanCtrl_disjoint_eScanB (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eScanCtrl as n K d a ≠ eScanB as n K d b :=
  fun a b h => eScanB_disjoint_eScanCtrl as n K d b a h.symm

lemma eScanCtrl_disjoint_eScanBSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin 3) :
    ∀ a b, eScanCtrl as n K d a ≠ eScanBSlot as n K d j b :=
  fun a b h => trans_disjoint_left (eScanB_disjoint_eScanCtrl as n K d) b a h.symm

lemma eScanB_disjoint_eRec1Occ (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dOccOf K))) :
    ∀ a b, eScanB as n K d a ≠ eRec1Occ as n K d q b :=
  fun a b h => ancRegField_disjoint_ancPrefix as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨8, by decide⟩)
    (by decide) _ _ _ _ _ _ _ _ _ b a h.symm

lemma eRec1Occ_disjoint_eOccSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dOccOf K))) (i : Fin (2 * K)) :
    ∀ a b, eRec1Occ as n K d q a ≠ eOccSlot as n K d i b :=
  trans_disjoint_right (trans_disjoint_right
    (ancRegField_disjoint_anc as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨2, by decide⟩) (by decide) _ _ _ _ _ _ _))

lemma eRec1NotAct_disjoint_eMSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dOccOf K))) (i : Fin (2 * K)) :
    ∀ a b, eRec1NotAct as n K d q a ≠ eMSlot as n K d i b :=
  trans_disjoint_right (trans_disjoint_right
    (ancRegField_disjoint_anc as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨0, by decide⟩) (by decide) _ _ _ _ _ _ _))

lemma eRec1NotAct_disjoint_eActSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dOccOf K))) (i : Fin (2 * K)) :
    ∀ a b, eRec1NotAct as n K d q a ≠ eActSlot as n K d i b :=
  trans_disjoint_right (trans_disjoint_right
    (ancRegField_disjoint_anc as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨1, by decide⟩) (by decide) _ _ _ _ _ _ _))

lemma eRec1M_disjoint_eMSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (q : Fin (arity (dOccOf K))) (i : Fin (2 * K)) :
    ∀ a b, eRec1M as n K d q a ≠ eMSlot as n K d i b :=
  trans_disjoint_right (trans_disjoint_right
    (ancRegField_disjoint_anc as n K d (k1 := ⟨3, by decide⟩) (k2 := ⟨0, by decide⟩) (by decide) _ _ _ _ _ _ _))

lemma eActSlot_disjoint_eRec1NotAct (as : AlonsoSchottSil54) (n K d : ℕ)
    (i : Fin (2 * K)) (q : Fin (arity (dOccOf K))) :
    ∀ a b, eActSlot as n K d i a ≠ eRec1NotAct as n K d q b :=
  fun a b h => eRec1NotAct_disjoint_eActSlot as n K d q i b a h.symm

lemma eMSlot_disjoint_eRec1M (as : AlonsoSchottSil54) (n K d : ℕ)
    (i : Fin (2 * K)) (q : Fin (arity (dOccOf K))) :
    ∀ a b, eMSlot as n K d i a ≠ eRec1M as n K d q b :=
  fun a b h => eRec1M_disjoint_eMSlot as n K d q i b a h.symm

lemma eRec1Reg_disjoint_eScanB (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec1Reg as n K d a ≠ eScanB as n K d b :=
  trans_disjoint_right (eRec1Reg_disjoint_anc_other as n K d ⟨8, by decide⟩ (by decide))

lemma eRec1Reg_disjoint_eScanCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eRec1Reg as n K d a ≠ eScanCtrl as n K d b :=
  trans_disjoint_right (eRec1Reg_disjoint_anc_other as n K d ⟨9, by decide⟩ (by decide))

/-! #### 6.6 Pure `rec1` Record Encoding & Lex Order-Isomorphism -/

def rec1KeyFn (w : ℕ) (na : Qubits 1) (m idx : Qubits w) : Qubits (1 + w + w) :=
  Fin.append (Fin.append na m) idx

def rec1SlotFn (w : ℕ) (na : Qubits 1) (m idx occ : Qubits w) : Qubits ((1 + w + w) + w) :=
  Fin.append (rec1KeyFn w na m idx) occ

lemma recKey54_rec1SlotFn (w : ℕ) (na : Qubits 1) (m idx occ : Qubits w) :
    recKey54 (rec1SlotFn w na m idx occ) = rec1KeyFn w na m idx := by
  funext i; simp [recKey54, rec1SlotFn]

lemma recPay54_rec1SlotFn (w : ℕ) (na : Qubits 1) (m idx occ : Qubits w) :
    recPay54 (rec1SlotFn w na m idx occ) = occ := by
  funext j; simp [recPay54, rec1SlotFn]

lemma rec1SlotFn_zero (w : ℕ) :
    rec1SlotFn w (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) = fun _ => false := by
  funext u
  dsimp [rec1SlotFn, rec1KeyFn]
  induction u using Fin.addCases with
  | left u1 =>
    rw [Fin.append_left]
    induction u1 using Fin.addCases with
    | left u2 =>
      rw [Fin.append_left]
      induction u2 using Fin.addCases <;> simp
    | right _ => simp
  | right _ => simp

lemma rec1SlotFn_comp_0 (w : ℕ) (na : Qubits 1) (m idx occ : Qubits w) :
    rec1SlotFn w na m idx occ ∘ sliceEmb 0 1 (by omega) = na := by
  funext i
  have heq : sliceEmb 0 1 (by omega) i = Fin.castAdd w (Fin.castAdd w (Fin.castAdd w i)) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec1SlotFn, rec1KeyFn, Fin.append_left, Fin.append_left, Fin.append_left]


end HarmBucketWork54


