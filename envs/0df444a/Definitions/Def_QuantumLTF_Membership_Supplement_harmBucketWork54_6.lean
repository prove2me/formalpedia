-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_6
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54_6
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:45:53.140495+00:00
-- url     : https://prove2.me/theorems/def19808-04d0-4a59-81cf-71c7a474af37
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (6/11)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 6 of 11 (`harmBucketWork54_6`).
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

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (6/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

lemma rec1SlotFn_comp_1 (w : ℕ) (na : Qubits 1) (m idx occ : Qubits w) :
    rec1SlotFn w na m idx occ ∘ sliceEmb 1 w (by omega) = m := by
  funext j
  have heq : sliceEmb 1 w (by omega) j = Fin.castAdd w (Fin.castAdd w (Fin.natAdd 1 j)) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec1SlotFn, rec1KeyFn, Fin.append_left, Fin.append_left, Fin.append_right]

lemma rec1SlotFn_comp_2 (w : ℕ) (na : Qubits 1) (m idx occ : Qubits w) :
    rec1SlotFn w na m idx occ ∘ sliceEmb (1 + w) w (by omega) = idx := by
  funext j
  have heq : sliceEmb (1 + w) w (by omega) j = Fin.castAdd w (Fin.natAdd (1 + w) j) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec1SlotFn, rec1KeyFn, Fin.append_left, Fin.append_right]

lemma rec1SlotFn_comp_3 (w : ℕ) (na : Qubits 1) (m idx occ : Qubits w) :
    rec1SlotFn w na m idx occ ∘ sliceEmb (1 + w + w) w (by omega) = occ := by
  funext j
  have heq : sliceEmb (1 + w + w) w (by omega) j = Fin.natAdd (1 + w + w) j :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec1SlotFn, Fin.append_right]

lemma eq_rec1SlotFn_iff (w : ℕ) (r : Qubits ((1 + w + w) + w))
    (na : Qubits 1) (m idx occ : Qubits w) :
    r = rec1SlotFn w na m idx occ ↔
      r ∘ sliceEmb 0 1 (by omega) = na ∧
      r ∘ sliceEmb 1 w (by omega) = m ∧
      r ∘ sliceEmb (1 + w) w (by omega) = idx ∧
      r ∘ sliceEmb (1 + w + w) w (by omega) = occ := by
  constructor
  · rintro rfl
    exact ⟨rec1SlotFn_comp_0 _ _ _ _ _, rec1SlotFn_comp_1 _ _ _ _ _,
      rec1SlotFn_comp_2 _ _ _ _ _, rec1SlotFn_comp_3 _ _ _ _ _⟩
  · rintro ⟨h0, h1, h2, h3⟩
    funext u
    have hu := u.isLt
    by_cases hu0 : u.1 < 1
    · have heq : u = sliceEmb 0 1 (by omega) ⟨u.1, hu0⟩ := Fin.ext (by simp)
      have hrhs := congrFun (rec1SlotFn_comp_0 w na m idx occ) ⟨u.1, hu0⟩
      rw [heq, ← Function.comp_apply (f := r), h0, ← hrhs]; rfl
    · by_cases hu1 : u.1 < 1 + w
      · have heq : u = sliceEmb 1 w (by omega) ⟨u.1 - 1, by omega⟩ := Fin.ext (by simp; omega)
        have hrhs := congrFun (rec1SlotFn_comp_1 w na m idx occ) ⟨u.1 - 1, by omega⟩
        rw [heq, ← Function.comp_apply (f := r), h1, ← hrhs]; rfl
      · by_cases hu2 : u.1 < 1 + w + w
        · have heq : u = sliceEmb (1 + w) w (by omega) ⟨u.1 - (1 + w), by omega⟩ :=
            Fin.ext (by simp; omega)
          have hrhs := congrFun (rec1SlotFn_comp_2 w na m idx occ) ⟨u.1 - (1 + w), by omega⟩
          rw [heq, ← Function.comp_apply (f := r), h2, ← hrhs]; rfl
        · have heq : u = sliceEmb (1 + w + w) w (by omega) ⟨u.1 - (1 + w + w), by omega⟩ :=
            Fin.ext (by simp; omega)
          have hrhs := congrFun (rec1SlotFn_comp_3 w na m idx occ) ⟨u.1 - (1 + w + w), by omega⟩
          rw [heq, ← Function.comp_apply (f := r), h3, ← hrhs]; rfl

lemma updateOn_rec1SlotFn_0 (w : ℕ) (na₀ na₁ : Qubits 1) (m idx occ : Qubits w) :
    updateOn (sliceEmb 0 1 (by omega)) (rec1SlotFn w na₀ m idx occ) na₁ =
      rec1SlotFn w na₁ m idx occ := by
  rw [eq_rec1SlotFn_iff]
  refine ⟨updateOn_comp_emb _ _ _, ?_, ?_, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]; exact rec1SlotFn_comp_1 _ _ _ _ _
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]; exact rec1SlotFn_comp_2 _ _ _ _ _
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]; exact rec1SlotFn_comp_3 _ _ _ _ _

lemma updateOn_rec1SlotFn_1 (w : ℕ) (na : Qubits 1) (m₀ m₁ idx occ : Qubits w) :
    updateOn (sliceEmb 1 w (by omega)) (rec1SlotFn w na m₀ idx occ) m₁ =
      rec1SlotFn w na m₁ idx occ := by
  rw [eq_rec1SlotFn_iff]
  refine ⟨?_, updateOn_comp_emb _ _ _, ?_, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec1SlotFn_comp_0 _ _ _ _ _
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]; exact rec1SlotFn_comp_2 _ _ _ _ _
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]; exact rec1SlotFn_comp_3 _ _ _ _ _

lemma updateOn_rec1SlotFn_2 (w : ℕ) (na : Qubits 1) (m idx₀ idx₁ occ : Qubits w) :
    updateOn (sliceEmb (1 + w) w (by omega)) (rec1SlotFn w na m idx₀ occ) idx₁ =
      rec1SlotFn w na m idx₁ occ := by
  rw [eq_rec1SlotFn_iff]
  refine ⟨?_, ?_, updateOn_comp_emb _ _ _, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec1SlotFn_comp_0 _ _ _ _ _
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec1SlotFn_comp_1 _ _ _ _ _
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]; exact rec1SlotFn_comp_3 _ _ _ _ _

lemma updateOn_rec1SlotFn_3 (w : ℕ) (na : Qubits 1) (m idx occ₀ occ₁ : Qubits w) :
    updateOn (sliceEmb (1 + w + w) w (by omega)) (rec1SlotFn w na m idx occ₀) occ₁ =
      rec1SlotFn w na m idx occ₁ := by
  rw [eq_rec1SlotFn_iff]
  refine ⟨?_, ?_, ?_, updateOn_comp_emb _ _ _⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec1SlotFn_comp_0 _ _ _ _ _
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec1SlotFn_comp_1 _ _ _ _ _
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec1SlotFn_comp_2 _ _ _ _ _

def rec1KeyBits (w : ℕ) (na : Bool) (m idx : ℕ) : Qubits (1 + w + w) :=
  rec1KeyFn w (fun _ => na) (natToBits w m) (natToBits w idx)

lemma rec1KeyBits_bitsToNat (comb : LcgSym54Comb) (w : ℕ) (na : Bool) {m idx : ℕ}
    (hm : m < 2 ^ w) (hi : idx < 2 ^ w) :
    bitsToNat (rec1KeyBits w na m idx) =
      ((if na then 1 else 0) * 2 ^ w + m) * 2 ^ w + idx := by
  dsimp [rec1KeyBits, rec1KeyFn]
  rw [comb.bitsToNat_append, comb.bitsToNat_append, bitsToNat_one_bit,
    comb.bitsToNat_natToBits hm, comb.bitsToNat_natToBits hi]
  ring

lemma rec1KeyBits_le_iff (comb : LcgSym54Comb) (w : ℕ)
    (na₁ na₂ : Bool) {m₁ m₂ idx₁ idx₂ : ℕ}
    (hm₁ : m₁ < 2 ^ w) (hm₂ : m₂ < 2 ^ w) (hi₁ : idx₁ < 2 ^ w) (hi₂ : idx₂ < 2 ^ w) :
    bitsToNat (rec1KeyBits w na₁ m₁ idx₁) ≤ bitsToNat (rec1KeyBits w na₂ m₂ idx₂) ↔
      (toLex (if na₁ then (1 : ℕ) else 0, toLex (m₁, idx₁)) : ℕ ×ₗ ℕ ×ₗ ℕ) ≤
        toLex (if na₂ then (1 : ℕ) else 0, toLex (m₂, idx₂)) := by
  rw [rec1KeyBits_bitsToNat comb w na₁ hm₁ hi₁, rec1KeyBits_bitsToNat comb w na₂ hm₂ hi₂]
  rw [nat_mul_add_le_iff _ _ hi₁ hi₂, nat_mul_add_lt_iff _ _ hm₁ hm₂, nat_mul_add_eq_iff _ _ hm₁ hm₂]
  simp only [Prod.Lex.le_iff]
  tauto

lemma rec1KeyBits_eq_iff (comb : LcgSym54Comb) (w : ℕ)
    (na₁ na₂ : Bool) {m₁ m₂ idx₁ idx₂ : ℕ}
    (hm₁ : m₁ < 2 ^ w) (hm₂ : m₂ < 2 ^ w) (hi₁ : idx₁ < 2 ^ w) (hi₂ : idx₂ < 2 ^ w) :
    bitsToNat (rec1KeyBits w na₁ m₁ idx₁) = bitsToNat (rec1KeyBits w na₂ m₂ idx₂) ↔
      na₁ = na₂ ∧ m₁ = m₂ ∧ idx₁ = idx₂ := by
  rw [rec1KeyBits_bitsToNat comb w na₁ hm₁ hi₁, rec1KeyBits_bitsToNat comb w na₂ hm₂ hi₂]
  rw [nat_mul_add_eq_iff _ _ hi₁ hi₂, nat_mul_add_eq_iff _ _ hm₁ hm₂]
  cases na₁ <;> cases na₂ <;> simp

/-! #### 6.7 Packing `eRec1Reg` (`packRec1Circ`) -/

def rec1InitArr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (q : Fin (arity (dOccOf K))) :
    Qubits (wR1Occ K) :=
  if hq : q.1 < 2 * K then
    rec1SlotFn (wOf K) (fun _ => !(actBitsFn K l ⟨q.1, hq⟩ 0)) (mBitsFn K l ⟨q.1, hq⟩)
      (natToBits (wOf K) q.1) (fun _ => false)
  else
    rec1SlotFn (wOf K) (fun _ => true) (natToBits (wOf K) 1)
      (natToBits (wOf K) q.1) (fun _ => false)

lemma rec1InitArr_lt_key (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (q : Fin (arity (dOccOf K))) (hq : q.1 < 2 * K) :
    recKey54 (rec1InitArr K l q) =
      rec1KeyBits (wOf K) (!(decide (2 ≤ runOffset l ⟨q.1, hq⟩))) (runOffset l ⟨q.1, hq⟩) q.1 := by
  dsimp only [rec1InitArr, actBitsFn, mBitsFn]
  rw [dif_pos hq, recKey54_rec1SlotFn]; rfl

lemma rec1InitArr_ge_key (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1))
    (q : Fin (arity (dOccOf K))) (hq : ¬ q.1 < 2 * K) :
    recKey54 (rec1InitArr K l q) = rec1KeyBits (wOf K) true 1 q.1 := by
  dsimp only [rec1InitArr]
  rw [dif_neg hq, recKey54_rec1SlotFn]; rfl

lemma recPay54_rec1InitArr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) (q : Fin (arity (dOccOf K))) :
    recPay54 (rec1InitArr K l q) = fun _ => false := by
  dsimp [rec1InitArr]
  split_ifs <;> exact recPay54_rec1SlotFn _ _ _ _ _

def packRec1SlotCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ)
    (q : ℕ) (hq : q < arity (dOccOf K)) : LayeredCircuit (totWiresDef as n K d) :=
  let qF : Fin (arity (dOccOf K)) := ⟨q, hq⟩
  let w := wOf K
  if hq2 : q < 2 * K then
    let c1 := (arith.copyRegCircuit 1).mapWires
      (combineEmb (eActSlot as n K d ⟨q, hq2⟩) (eRec1NotAct as n K d qF)
        (eActSlot_disjoint_eRec1NotAct as n K d _ _))
    let c2 := (arith.setConstMSBCircuit 1 1).mapWires (eRec1NotAct as n K d qF)
    let c3 := (arith.copyRegCircuit w).mapWires
      (combineEmb (eMSlot as n K d ⟨q, hq2⟩) (eRec1M as n K d qF)
        (eMSlot_disjoint_eRec1M as n K d _ _))
    let c4 := (arith.setConstMSBCircuit w q).mapWires (eRec1Idx as n K d qF)
    LayeredCircuit.seqList [c1, c2, c3, c4]
  else
    let c1 := (arith.setConstMSBCircuit 1 1).mapWires (eRec1NotAct as n K d qF)
    let c2 := (arith.setConstMSBCircuit w 1).mapWires (eRec1M as n K d qF)
    let c3 := (arith.setConstMSBCircuit w q).mapWires (eRec1Idx as n K d qF)
    LayeredCircuit.seqList [c1, c2, c3]

def packRec1Circ (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) :
    LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList ((List.range (arity (dOccOf K))).map fun q =>
    if hq : q < arity (dOccOf K) then packRec1SlotCirc as arith n K d q hq else LayeredCircuit.id _)

def sortRec1Circ (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ) :
    LayeredCircuit (totWiresDef as n K d) :=
  (br.bitonicSortKeyCircuit (dOccOf K) (wK1Occ K) (wP1Occ K) true).mapWires
    (packDTA54Emb (eRec1Reg as n K d) (eTr1 as n K d) (eSort1Anc as n K d)
      (eRec1Reg_disjoint_eTr1 as n K d)
      (eRec1Reg_disjoint_eSort1Anc as n K d)
      (eTr1_disjoint_eSort1Anc as n K d))

noncomputable def rec1SortedArr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    Fin (arity (dOccOf K)) → Qubits (wR1Occ K) :=
  sort (fun r => bitsToNat (recKey54 r)) (dOccOf K) true (rec1InitArr K l)

noncomputable def rec1SortTr (K : ℕ) {n : ℕ} (l : Fin (2 * K) → Fin (n + 1)) :
    Fin (sortTraceSize (dOccOf K)) → Bool :=
  sortTrace (fun r => bitsToNat (recKey54 r)) (dOccOf K) true (rec1InitArr K l)

def cmpScanStep (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (p : ℕ) (hp : p + 1 < 2 * K) : LayeredCircuit (totWiresDef as n K d) :=
  have h2K : 2 * K ≤ arity (dOccOf K) := two_K_le_arity_dOcc
  have h5w := five_le_wOf h1K
  let q0 : Fin (arity (dOccOf K)) := ⟨p, by omega⟩
  let q1 : Fin (arity (dOccOf K)) := ⟨p + 1, by omega⟩
  let w := wOf K
  let anc1 := eArith12Pref as n K d 1 (by omega)
  let anc3 := eArith12Pref as n K d 3 (by omega)
  let ancW := eArith12Pref as n K d w (Nat.le_trans (Nat.le_succ w) (le_max_right _ _))
  let c1 := (arith.eqConstMSBCircuit 1 0).mapWires
    (comb3 (eRec1NotAct as n K d q1) (eScanBSlot as n K d ⟨0, by decide⟩) anc1
      (eRec1NotAct_disjoint_eScanBSlot as n K d _ _)
      (eRec1NotAct_disjoint_eArith12 as n K d _ _ _)
      (eScanBSlot_disjoint_eArith12 as n K d _ _ _))
  let c2 := (arith.eqConstMSBCircuit 1 0).mapWires
    (comb3 (eRec1NotAct as n K d q0) (eScanBSlot as n K d ⟨1, by decide⟩) anc1
      (eRec1NotAct_disjoint_eScanBSlot as n K d _ _)
      (eRec1NotAct_disjoint_eArith12 as n K d _ _ _)
      (eScanBSlot_disjoint_eArith12 as n K d _ _ _))
  let c3 := (arith.eqRegCircuit w).mapWires
    (comb4 (eRec1M as n K d q1) (eRec1M as n K d q0) (eScanBSlot as n K d ⟨2, by decide⟩) ancW
      (eRec1M_disjoint_slot as n K d (by simp [q0, q1, Fin.ext_iff]))
      (eRec1M_disjoint_eScanBSlot as n K d _ _)
      (eRec1M_disjoint_eScanBSlot as n K d _ _)
      (eRec1M_disjoint_eArith12 as n K d _ _ _)
      (eRec1M_disjoint_eArith12 as n K d _ _ _)
      (eScanBSlot_disjoint_eArith12 as n K d _ _ _))
  let c4 := (arith.eqConstMSBCircuit 3 (2 ^ 3 - 1)).mapWires
    (comb3 (eScanB as n K d) (eScanCtrl as n K d) anc3
      (eScanB_disjoint_eScanCtrl as n K d)
      (eScanB_disjoint_eArith12 as n K d _ _)
      (eScanCtrl_disjoint_eArith12 as n K d _ _))
  LayeredCircuit.seqList [c1, c2, c3, c4]

def scanOccStep (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K)
    (p : ℕ) (hp : p + 1 < 2 * K) : LayeredCircuit (totWiresDef as n K d) :=
  have h2K : 2 * K ≤ arity (dOccOf K) := two_K_le_arity_dOcc
  let q0 : Fin (arity (dOccOf K)) := ⟨p, by omega⟩
  let q1 : Fin (arity (dOccOf K)) := ⟨p + 1, by omega⟩
  let w := wOf K
  let cmp := cmpScanStep as arith n K d h1K p hp
  let cCtrlCopy := (arith.ctrlCopyRegCircuit w).mapWires
    (comb3 (eScanCtrl as n K d) (eRec1Occ as n K d q0) (eRec1Occ as n K d q1)
      (eScanCtrl_disjoint_eRec1Occ as n K d q0)
      (eScanCtrl_disjoint_eRec1Occ as n K d q1)
      (eRec1Occ_disjoint_slot as n K d (by simp [q0, q1, Fin.ext_iff])))
  let cCtrlAdd := (arith.ctrlAddConstInPlaceMSBCircuit w 1).mapWires
    (comb3 (eScanCtrl as n K d) (eRec1Occ as n K d q1)
      (eArith12Pref as n K d (w + 1) (le_max_right _ _))
      (eScanCtrl_disjoint_eRec1Occ as n K d q1)
      (eScanCtrl_disjoint_eArith12 as n K d _ _)
      (eRec1Occ_disjoint_eArith12 as n K d _ _ q1))
  LayeredCircuit.seqList [cmp, cCtrlCopy, cCtrlAdd, cmp.adj]

def scanOccCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) :
    LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList ((List.range (2 * K - 1)).map fun p =>
    if hp : p + 1 < 2 * K then scanOccStep as arith n K d h1K p hp else LayeredCircuit.id _)

def unrouteRec1Circ (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ) :
    LayeredCircuit (totWiresDef as n K d) :=
  (br.bitonicSortKeyCircuit (dOccOf K) (wK1Occ K) (wP1Occ K) true).adj.mapWires
    (packDTA54Emb (eRec1Reg as n K d) (eTr1 as n K d) (eSort1Anc as n K d)
      (eRec1Reg_disjoint_eTr1 as n K d)
      (eRec1Reg_disjoint_eSort1Anc as n K d)
      (eTr1_disjoint_eSort1Anc as n K d))

def swapOccOutCirc (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (_h1K : 1 ≤ K) :
    LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList ((List.range (2 * K)).map fun i =>
    if hi : i < 2 * K then
      let q : Fin (arity (dOccOf K)) := ⟨i, by have := two_K_le_arity_dOcc (K := K); omega⟩
      (arith.swapRegCircuit (wOf K)).mapWires
        (combineEmb (eRec1Occ as n K d q) (eOccSlot as n K d ⟨i, hi⟩)
          (eRec1Occ_disjoint_eOccSlot as n K d q ⟨i, hi⟩))
    else LayeredCircuit.id _)

def step2Circ (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (br : BitonicRouting54)
    (n K d : ℕ) (h1K : 1 ≤ K) : LayeredCircuit (totWiresDef as n K d) :=
  LayeredCircuit.seqList
    [ packRec1Circ as arith n K d
    , sortRec1Circ as br n K d
    , scanOccCirc as arith n K d h1K
    , unrouteRec1Circ as br n K d
    , swapOccOutCirc as arith n K d h1K
    , (packRec1Circ as arith n K d).adj ]

def step12Circ (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (br : BitonicRouting54)
    (n K d : ℕ) (h1K : 1 ≤ K) : LayeredCircuit (totWiresDef as n K d) :=
  (step1Circ as arith n K d h1K).seq (step2Circ as arith br n K d h1K)


/-! ### Part 7: Step 3 Definitions, Disjointness & Combinatorial Invariants -/

lemma arity_succ_eq (m : ℕ) : arity (m + 1) = 2 * arity m := by
  rw [arity_eq_two_pow, arity_eq_two_pow, pow_succ']

lemma eq_of_mem_of_nodup_map {α β : Type*} (f : α → β) {L : List α} (hn : (L.map f).Nodup)
    {x y : α} (hx : x ∈ L) (hy : y ∈ L) (hxy : f x = f y) : x = y := by
  induction L with
  | nil => simp at hx
  | cons a t ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd ⟨y, hy', hxy.symm⟩ hn.1
    · exact absurd ⟨x, hx', hxy⟩ hn.1
    · exact ih hn.2 hx' hy'

lemma comp_ancRegField_of_eq_slot (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (N_rec w_r : ℕ) (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    (z : Qubits (totWiresDef as n K d)) (q : Fin N_rec) (val : Qubits w_r)
    (fOff fLen : ℕ) (hf : fOff + fLen ≤ w_r) :
    updateOn (ancRegSlot as n K d k N_rec w_r hlen q) z val ∘
        ancRegField as n K d k N_rec w_r hlen q fOff fLen hf =
      val ∘ sliceEmb fOff fLen hf := by
  funext i
  exact congrFun (updateOn_comp_emb (ancRegSlot as n K d k N_rec w_r hlen q) z val) _

lemma updateOn_ancRegField_on_slot (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (N_rec w_r : ℕ) (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    (z : Qubits (totWiresDef as n K d)) (q : Fin N_rec) (slotVal : Qubits w_r)
    (fOff fLen : ℕ) (hf : fOff + fLen ≤ w_r) (fVal : Qubits fLen) :
    updateOn (ancRegField as n K d k N_rec w_r hlen q fOff fLen hf)
        (updateOn (ancRegSlot as n K d k N_rec w_r hlen q) z slotVal) fVal =
      updateOn (ancRegSlot as n K d k N_rec w_r hlen q) z
        (updateOn (sliceEmb fOff fLen hf) slotVal fVal) := by
  rw [updateOn_ancRegField_eq_slot, updateOn_comp_emb, updateOn_idem]

lemma act_setConst_ancRegField_zero (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
    (n K d : ℕ) (k : Fin 24) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    (z : Qubits (totWiresDef as n K d)) (q : Fin N_rec) (slotVal : Qubits w_r)
    (fOff fLen : ℕ) (hf : fOff + fLen ≤ w_r) (c : ℕ)
    (hz0 : slotVal ∘ sliceEmb fOff fLen hf = fun _ => false) :
    act ((arith.setConstMSBCircuit fLen c).mapWires
        (ancRegField as n K d k N_rec w_r hlen q fOff fLen hf)).unitary
      (ket (updateOn (ancRegSlot as n K d k N_rec w_r hlen q) z slotVal)) =
      ket (updateOn (ancRegSlot as n K d k N_rec w_r hlen q) z
        (updateOn (sliceEmb fOff fLen hf) slotVal (natToBits fLen c))) := by
  rw [act_setConstOn arith]
  have hcomp := comp_ancRegField_of_eq_slot as n K d k N_rec w_r hlen z q slotVal fOff fLen hf
  have hx : (fun i => updateOn (ancRegSlot as n K d k N_rec w_r hlen q) z slotVal
        (ancRegField as n K d k N_rec w_r hlen q fOff fLen hf i) ^^ natToBits fLen c i) =
      natToBits fLen c := by
    funext i
    rw [← Function.comp_apply (f := updateOn (ancRegSlot as n K d k N_rec w_r hlen q) z slotVal),
      hcomp, hz0, xor_false_left]
  rw [hx, updateOn_ancRegField_on_slot]

def eRec2 (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (arity (dHbOf K + 1) * wR1Hb K) ↪ Fin (totWiresDef as n K d) :=
  ancRegSlice as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _)

def eTr2a (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (sortTraceSize (dHbOf K + 1)) ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨12, by decide⟩ (sortTraceSize (dHbOf K + 1)) (by rw [ancLen_12])

def eRec3 (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (arity (dHbOf K + 1) * wR2Hb K) ↪ Fin (totWiresDef as n K d) :=
  ancRegSlice as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _)

def eTr2b (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (sortTraceSize (dHbOf K + 1)) ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨14, by decide⟩ (sortTraceSize (dHbOf K + 1)) (by rw [ancLen_14])

def eSort2aAnc (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (wK1Hb K) ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨17, by decide⟩ (wK1Hb K) (by rw [ancLen_17])

def eSort2bAnc (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (wK2Hb K) ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨18, by decide⟩ (wK2Hb K) (by rw [ancLen_18])

def eSeqB (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin 4 ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨19, by decide⟩ 4 (by rw [ancLen_19])

def eSeqBSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin 4) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  (sliceEmb j.1 1 (by omega)).trans (eSeqB as n K d)

def eSeqCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨20, by decide⟩ 1 (by rw [ancLen_20])

def eUnifCtrl (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨21, by decide⟩ 1 (by rw [ancLen_21])

def eArith345 (as : AlonsoSchottSil54) (n K d subLen : ℕ) (hle : subLen ≤ wOf K + 1) :
    Fin subLen ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨22, by decide⟩ subLen (by rw [ancLen_22]; exact hle)

def eRec2Inact (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q
    0 1 (by dsimp [wR1Hb, wK1Hb]; omega)

def eRec2M (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q
    1 (wOf K) (by dsimp [wR1Hb, wK1Hb]; omega)

def eRec2Occ (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q
    (1 + wOf K) (wOf K) (by dsimp [wR1Hb, wK1Hb]; omega)

def eRec2KR1 (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin 2 ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q
    (1 + wOf K + wOf K) 2 (by dsimp [wR1Hb, wK1Hb]; omega)

def eRec2Orig (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q
    (1 + wOf K + wOf K + 2) (wOf K) (by dsimp [wR1Hb, wK1Hb]; omega)

def eRec2Kind (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin 2 ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q
    (wK1Hb K) 2 (by dsimp [wR1Hb, wP1Hb, wK1Hb]; omega)

def eRec2KindMsb (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  (sliceEmb 0 1 (by omega)).trans (eRec2Kind as n K d q)

def eRec2Dest (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q
    (wK1Hb K + 2) (wOf K) (by dsimp [wR1Hb, wP1Hb, wK1Hb]; omega)

def eRec2DVal (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨11, by decide⟩ (arity (dHbOf K + 1)) (wR1Hb K) (ancLen_11 n K d _) q
    (wK1Hb K + 2 + wOf K) (wOf K) (by dsimp [wR1Hb, wP1Hb, wK1Hb]; omega)

def eRec3Group (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dHbOf K + 1))) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  ancRegField as n K d ⟨13, by decide⟩ (arity (dHbOf K + 1)) (wR2Hb K) (ancLen_13 n K d _) q
    0 1 (by dsimp [wR2Hb, wK2Hb]; omega)


end HarmBucketWork54


