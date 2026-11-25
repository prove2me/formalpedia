-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_8
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54_8
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:47:44.396997+00:00
-- url     : https://prove2.me/theorems/b4486d7a-623f-58d6-a2c4-cf581de78851
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (8/11)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 8 of 11 (`harmBucketWork54_8`).
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

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (8/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

lemma updateOn_rec2SlotFn_1 (w : ℕ) (na : Qubits 1) (m₀ m₁ occ : Qubits w) (kr1 : Qubits 2)
    (orig : Qubits w) (kind : Qubits 2) (dest dval : Qubits w) :
    updateOn (sliceEmb 1 w (by omega)) (rec2SlotFn w na m₀ occ kr1 orig kind dest dval) m₁ =
      rec2SlotFn w na m₁ occ kr1 orig kind dest dval := by
  rw [eq_rec2SlotFn_iff]
  refine ⟨?_, updateOn_comp_emb _ _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_0 ..
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]
    first | exact rec2SlotFn_comp_2 .. | exact rec2SlotFn_comp_3 .. | exact rec2SlotFn_comp_4 ..
          | exact rec2SlotFn_comp_5 .. | exact rec2SlotFn_comp_6 .. | exact rec2SlotFn_comp_7 ..

lemma updateOn_rec2SlotFn_2 (w : ℕ) (na : Qubits 1) (m occ₀ occ₁ : Qubits w) (kr1 : Qubits 2)
    (orig : Qubits w) (kind : Qubits 2) (dest dval : Qubits w) :
    updateOn (sliceEmb (1 + w) w (by omega)) (rec2SlotFn w na m occ₀ kr1 orig kind dest dval) occ₁ =
      rec2SlotFn w na m occ₁ kr1 orig kind dest dval := by
  rw [eq_rec2SlotFn_iff]
  refine ⟨?_, ?_, updateOn_comp_emb _ _ _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_0 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_1 ..
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]
    first | exact rec2SlotFn_comp_3 .. | exact rec2SlotFn_comp_4 .. | exact rec2SlotFn_comp_5 ..
          | exact rec2SlotFn_comp_6 .. | exact rec2SlotFn_comp_7 ..

lemma updateOn_rec2SlotFn_3 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1₀ kr1₁ : Qubits 2)
    (orig : Qubits w) (kind : Qubits 2) (dest dval : Qubits w) :
    updateOn (sliceEmb (1 + w + w) 2 (by omega)) (rec2SlotFn w na m occ kr1₀ orig kind dest dval) kr1₁ =
      rec2SlotFn w na m occ kr1₁ orig kind dest dval := by
  rw [eq_rec2SlotFn_iff]
  refine ⟨?_, ?_, ?_, updateOn_comp_emb _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_0 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_1 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_2 ..
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]
    first | exact rec2SlotFn_comp_4 .. | exact rec2SlotFn_comp_5 .. | exact rec2SlotFn_comp_6 ..
          | exact rec2SlotFn_comp_7 ..

lemma updateOn_rec2SlotFn_4 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2)
    (orig₀ orig₁ : Qubits w) (kind : Qubits 2) (dest dval : Qubits w) :
    updateOn (sliceEmb (1 + w + w + 2) w (by omega)) (rec2SlotFn w na m occ kr1 orig₀ kind dest dval) orig₁ =
      rec2SlotFn w na m occ kr1 orig₁ kind dest dval := by
  rw [eq_rec2SlotFn_iff]
  refine ⟨?_, ?_, ?_, ?_, updateOn_comp_emb _ _ _, ?_, ?_, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_0 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_1 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_2 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_3 ..
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]
    first | exact rec2SlotFn_comp_5 .. | exact rec2SlotFn_comp_6 .. | exact rec2SlotFn_comp_7 ..

lemma updateOn_rec2SlotFn_5 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2)
    (orig : Qubits w) (kind₀ kind₁ : Qubits 2) (dest dval : Qubits w) :
    updateOn (sliceEmb (1 + w + w + 2 + w) 2 (by omega)) (rec2SlotFn w na m occ kr1 orig kind₀ dest dval) kind₁ =
      rec2SlotFn w na m occ kr1 orig kind₁ dest dval := by
  rw [eq_rec2SlotFn_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, updateOn_comp_emb _ _ _, ?_, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_0 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_1 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_2 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_3 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_4 ..
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]
    first | exact rec2SlotFn_comp_6 .. | exact rec2SlotFn_comp_7 ..

lemma updateOn_rec2SlotFn_6 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2)
    (orig : Qubits w) (kind : Qubits 2) (dest₀ dest₁ dval : Qubits w) :
    updateOn (sliceEmb (1 + w + w + 2 + w + 2) w (by omega)) (rec2SlotFn w na m occ kr1 orig kind dest₀ dval) dest₁ =
      rec2SlotFn w na m occ kr1 orig kind dest₁ dval := by
  rw [eq_rec2SlotFn_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, updateOn_comp_emb _ _ _, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_0 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_1 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_2 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_3 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_4 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec2SlotFn_comp_5 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]; exact rec2SlotFn_comp_7 ..

lemma updateOn_rec2SlotFn_7 (w : ℕ) (na : Qubits 1) (m occ : Qubits w) (kr1 : Qubits 2)
    (orig : Qubits w) (kind : Qubits 2) (dest dval₀ dval₁ : Qubits w) :
    updateOn (sliceEmb (1 + w + w + 2 + w + 2 + w) w (by omega)) (rec2SlotFn w na m occ kr1 orig kind dest dval₀) dval₁ =
      rec2SlotFn w na m occ kr1 orig kind dest dval₁ := by
  rw [eq_rec2SlotFn_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, updateOn_comp_emb _ _ _⟩
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]
    first | exact rec2SlotFn_comp_0 .. | exact rec2SlotFn_comp_1 .. | exact rec2SlotFn_comp_2 ..
          | exact rec2SlotFn_comp_3 .. | exact rec2SlotFn_comp_4 .. | exact rec2SlotFn_comp_5 ..
          | exact rec2SlotFn_comp_6 ..

def hbRecToBits (w : ℕ) (r : HBRec) (dval : Qubits w) : Qubits ((1 + w + w + 2 + w) + (2 + w + w)) :=
  rec2SlotFn w (natToBits 1 (hbInactive r)) (natToBits w r.m) (natToBits w r.occ)
    (natToBits 2 (hbKindRank1 r)) (natToBits w r.orig) (natToBits 2 r.kind) (natToBits w r.dest) dval

lemma hbKey1_bitsToNat (comb : LcgSym54Comb) (w : ℕ) (r : HBRec) (dval : Qubits w)
    (hm : r.m < 2 ^ w) (hocc : r.occ < 2 ^ w) (horig : r.orig < 2 ^ w) :
    bitsToNat (recKey54 (hbRecToBits w r dval)) =
      ((((hbInactive r * 2 ^ w + r.m) * 2 ^ w + r.occ) * 4 + hbKindRank1 r) * 2 ^ w + r.orig) := by
  dsimp [hbRecToBits]; rw [recKey54_rec2SlotFn]; dsimp [rec2KeyFn]
  have hin : hbInactive r < 2 ^ 1 := by dsimp [hbInactive]; split_ifs <;> omega
  have hkr : hbKindRank1 r < 2 ^ 2 := by dsimp [hbKindRank1]; split_ifs <;> omega
  rw [comb.bitsToNat_append, comb.bitsToNat_append, comb.bitsToNat_append, comb.bitsToNat_append,
    comb.bitsToNat_natToBits hin, comb.bitsToNat_natToBits hm, comb.bitsToNat_natToBits hocc,
    comb.bitsToNat_natToBits hkr, comb.bitsToNat_natToBits horig]
  norm_num; ring

lemma hbKey1_bitsToNat_le_iff (comb : LcgSym54Comb) (w : ℕ) (r₁ r₂ : HBRec) (d₁ d₂ : Qubits w)
    (hm₁ : r₁.m < 2 ^ w) (hm₂ : r₂.m < 2 ^ w)
    (ho₁ : r₁.occ < 2 ^ w) (ho₂ : r₂.occ < 2 ^ w)
    (hi₁ : r₁.orig < 2 ^ w) (hi₂ : r₂.orig < 2 ^ w) :
    bitsToNat (recKey54 (hbRecToBits w r₁ d₁)) ≤ bitsToNat (recKey54 (hbRecToBits w r₂ d₂)) ↔
      hbKey1 r₁ ≤ hbKey1 r₂ := by
  rw [hbKey1_bitsToNat comb w r₁ d₁ hm₁ ho₁ hi₁, hbKey1_bitsToNat comb w r₂ d₂ hm₂ ho₂ hi₂]
  have hkr₁ : hbKindRank1 r₁ < 4 := by dsimp [hbKindRank1]; split_ifs <;> omega
  have hkr₂ : hbKindRank1 r₂ < 4 := by dsimp [hbKindRank1]; split_ifs <;> omega
  rw [nat_mul_add_le_iff _ _ hi₁ hi₂,
    nat_mul_add_lt_iff _ _ hkr₁ hkr₂, nat_mul_add_eq_iff _ _ hkr₁ hkr₂,
    nat_mul_add_lt_iff _ _ ho₁ ho₂, nat_mul_add_eq_iff _ _ ho₁ ho₂,
    nat_mul_add_lt_iff _ _ hm₁ hm₂, nat_mul_add_eq_iff _ _ hm₁ hm₂]
  dsimp [hbKey1]; simp only [Prod.Lex.le_iff]; tauto

lemma hbKey1_bitsToNat_eq_iff (comb : LcgSym54Comb) (w : ℕ) (r₁ r₂ : HBRec) (d₁ d₂ : Qubits w)
    (hm₁ : r₁.m < 2 ^ w) (hm₂ : r₂.m < 2 ^ w)
    (ho₁ : r₁.occ < 2 ^ w) (ho₂ : r₂.occ < 2 ^ w)
    (hi₁ : r₁.orig < 2 ^ w) (hi₂ : r₂.orig < 2 ^ w) :
    bitsToNat (recKey54 (hbRecToBits w r₁ d₁)) = bitsToNat (recKey54 (hbRecToBits w r₂ d₂)) ↔
      hbKey1 r₁ = hbKey1 r₂ := by
  have h1 := hbKey1_bitsToNat_le_iff comb w r₁ r₂ d₁ d₂ hm₁ hm₂ ho₁ ho₂ hi₁ hi₂
  have h2 := hbKey1_bitsToNat_le_iff comb w r₂ r₁ d₂ d₁ hm₂ hm₁ ho₂ ho₁ hi₂ hi₁
  exact ⟨fun he => le_antisymm (h1.mp he.le) (h2.mp he.symm.le),
    fun he => le_antisymm (h1.mpr he.le) (h2.mpr he.symm.le)⟩

-- `rec3` encoding
def rec3KeyFn (w : ℕ) (grp : Qubits 1) (dest orig : Qubits w) : Qubits (1 + w + w) :=
  Fin.append (Fin.append grp dest) orig

def rec3PayFn (w : ℕ) (kind : Qubits 2) (dval : Qubits w) : Qubits (2 + w) :=
  Fin.append kind dval

def rec3SlotFn (w : ℕ) (grp : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    Qubits ((1 + w + w) + (2 + w)) :=
  Fin.append (rec3KeyFn w grp dest orig) (rec3PayFn w kind dval)

lemma recKey54_rec3SlotFn (w : ℕ) (grp : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    recKey54 (rec3SlotFn w grp dest orig kind dval) = rec3KeyFn w grp dest orig := by
  funext i; simp [recKey54, rec3SlotFn]

lemma recPay54_rec3SlotFn (w : ℕ) (grp : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    recPay54 (rec3SlotFn w grp dest orig kind dval) = rec3PayFn w kind dval := by
  funext j; simp [recPay54, rec3SlotFn]

lemma rec3SlotFn_zero (w : ℕ) :
    rec3SlotFn w (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) =
      fun _ => false := by
  funext u; dsimp [rec3SlotFn, rec3KeyFn, rec3PayFn]
  induction u using Fin.addCases with
  | left a =>
    rw [Fin.append_left]
    induction a using Fin.addCases with
    | left b => rw [Fin.append_left]; induction b using Fin.addCases <;> simp
    | right _ => simp
  | right c => rw [Fin.append_right]; induction c using Fin.addCases <;> simp

lemma rec3SlotFn_comp_0 (w : ℕ) (grp : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    rec3SlotFn w grp dest orig kind dval ∘ sliceEmb 0 1 (by omega) = grp := by
  funext i
  have heq : sliceEmb 0 1 (by omega) i = Fin.castAdd (2 + w) (Fin.castAdd w (Fin.castAdd w i)) := Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec3SlotFn, rec3KeyFn, Fin.append_left, Fin.append_left, Fin.append_left]

lemma rec3SlotFn_comp_1 (w : ℕ) (grp : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    rec3SlotFn w grp dest orig kind dval ∘ sliceEmb 1 w (by omega) = dest := by
  funext i
  have heq : sliceEmb 1 w (by omega) i = Fin.castAdd (2 + w) (Fin.castAdd w (Fin.natAdd 1 i)) := Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec3SlotFn, rec3KeyFn, Fin.append_left, Fin.append_left, Fin.append_right]

lemma rec3SlotFn_comp_2 (w : ℕ) (grp : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    rec3SlotFn w grp dest orig kind dval ∘ sliceEmb (1 + w) w (by omega) = orig := by
  funext i
  have heq : sliceEmb (1 + w) w (by omega) i = Fin.castAdd (2 + w) (Fin.natAdd (1 + w) i) := Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec3SlotFn, rec3KeyFn, Fin.append_left, Fin.append_right]

lemma rec3SlotFn_comp_3 (w : ℕ) (grp : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    rec3SlotFn w grp dest orig kind dval ∘ sliceEmb (1 + w + w) 2 (by omega) = kind := by
  funext i
  have heq : sliceEmb (1 + w + w) 2 (by omega) i = Fin.natAdd (1 + w + w) (Fin.castAdd w i) :=
    Fin.ext (by simp)
  rw [Function.comp_apply, heq, rec3SlotFn, rec3PayFn, Fin.append_right, Fin.append_left]

lemma rec3SlotFn_comp_4 (w : ℕ) (grp : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    rec3SlotFn w grp dest orig kind dval ∘ sliceEmb (1 + w + w + 2) w (by omega) = dval := by
  funext i
  have heq : sliceEmb (1 + w + w + 2) w (by omega) i = Fin.natAdd (1 + w + w) (Fin.natAdd 2 i) :=
    Fin.ext (by simp only [Fin.val_natAdd, sliceEmb_apply]; omega)
  rw [Function.comp_apply, heq, rec3SlotFn, rec3PayFn, Fin.append_right, Fin.append_right]

lemma eq_rec3SlotFn_iff (w : ℕ) (r : Qubits ((1 + w + w) + (2 + w)))
    (grp : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    r = rec3SlotFn w grp dest orig kind dval ↔
      r ∘ sliceEmb 0 1 (by omega) = grp ∧
      r ∘ sliceEmb 1 w (by omega) = dest ∧
      r ∘ sliceEmb (1 + w) w (by omega) = orig ∧
      r ∘ sliceEmb (1 + w + w) 2 (by omega) = kind ∧
      r ∘ sliceEmb (1 + w + w + 2) w (by omega) = dval := by
  constructor
  · rintro rfl
    exact ⟨rec3SlotFn_comp_0 _ _ _ _ _ _, rec3SlotFn_comp_1 _ _ _ _ _ _,
      rec3SlotFn_comp_2 _ _ _ _ _ _, rec3SlotFn_comp_3 _ _ _ _ _ _, rec3SlotFn_comp_4 _ _ _ _ _ _⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    funext u; have hu := u.isLt
    by_cases hu0 : u.1 < 1
    · have heq : u = sliceEmb 0 1 (by omega) ⟨u.1, hu0⟩ := Fin.ext (by simp only [sliceEmb_apply]; omega)
      have hrhs := congrFun (rec3SlotFn_comp_0 w grp dest orig kind dval) ⟨u.1, hu0⟩
      rw [heq, ← Function.comp_apply (f := r), h0, ← hrhs]; rfl
    · by_cases hu1 : u.1 < 1 + w
      · have heq : u = sliceEmb 1 w (by omega) ⟨u.1 - 1, by omega⟩ := Fin.ext (by simp only [sliceEmb_apply]; omega)
        have hrhs := congrFun (rec3SlotFn_comp_1 w grp dest orig kind dval) ⟨u.1 - 1, by omega⟩
        rw [heq, ← Function.comp_apply (f := r), h1, ← hrhs]; rfl
      · by_cases hu2 : u.1 < 1 + w + w
        · have heq : u = sliceEmb (1 + w) w (by omega) ⟨u.1 - (1 + w), by omega⟩ :=
            Fin.ext (by simp only [sliceEmb_apply]; omega)
          have hrhs := congrFun (rec3SlotFn_comp_2 w grp dest orig kind dval) ⟨u.1 - (1 + w), by omega⟩
          rw [heq, ← Function.comp_apply (f := r), h2, ← hrhs]; rfl
        · by_cases hu3 : u.1 < 1 + w + w + 2
          · have heq : u = sliceEmb (1 + w + w) 2 (by omega) ⟨u.1 - (1 + w + w), by omega⟩ :=
              Fin.ext (by simp only [sliceEmb_apply]; omega)
            have hrhs := congrFun (rec3SlotFn_comp_3 w grp dest orig kind dval) ⟨u.1 - (1 + w + w), by omega⟩
            rw [heq, ← Function.comp_apply (f := r), h3, ← hrhs]; rfl
          · have heq : u = sliceEmb (1 + w + w + 2) w (by omega) ⟨u.1 - (1 + w + w + 2), by omega⟩ :=
              Fin.ext (by simp only [sliceEmb_apply]; omega)
            have hrhs := congrFun (rec3SlotFn_comp_4 w grp dest orig kind dval) ⟨u.1 - (1 + w + w + 2), by omega⟩
            rw [heq, ← Function.comp_apply (f := r), h4, ← hrhs]; rfl

lemma updateOn_rec3SlotFn_0 (w : ℕ) (g₀ g₁ : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    updateOn (sliceEmb 0 1 (by omega)) (rec3SlotFn w g₀ dest orig kind dval) g₁ =
      rec3SlotFn w g₁ dest orig kind dval := by
  rw [eq_rec3SlotFn_iff]
  refine ⟨updateOn_comp_emb _ _ _, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]
    first | exact rec3SlotFn_comp_1 .. | exact rec3SlotFn_comp_2 ..
          | exact rec3SlotFn_comp_3 .. | exact rec3SlotFn_comp_4 ..

lemma updateOn_rec3SlotFn_1 (w : ℕ) (g : Qubits 1) (d₀ d₁ orig : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    updateOn (sliceEmb 1 w (by omega)) (rec3SlotFn w g d₀ orig kind dval) d₁ =
      rec3SlotFn w g d₁ orig kind dval := by
  rw [eq_rec3SlotFn_iff]
  refine ⟨?_, updateOn_comp_emb _ _ _, ?_, ?_, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec3SlotFn_comp_0 ..
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]
    first | exact rec3SlotFn_comp_2 .. | exact rec3SlotFn_comp_3 .. | exact rec3SlotFn_comp_4 ..

lemma updateOn_rec3SlotFn_2 (w : ℕ) (g : Qubits 1) (dest o₀ o₁ : Qubits w) (kind : Qubits 2) (dval : Qubits w) :
    updateOn (sliceEmb (1 + w) w (by omega)) (rec3SlotFn w g dest o₀ kind dval) o₁ =
      rec3SlotFn w g dest o₁ kind dval := by
  rw [eq_rec3SlotFn_iff]
  refine ⟨?_, ?_, updateOn_comp_emb _ _ _, ?_, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec3SlotFn_comp_0 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec3SlotFn_comp_1 ..
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]
    first | exact rec3SlotFn_comp_3 .. | exact rec3SlotFn_comp_4 ..

lemma updateOn_rec3SlotFn_3 (w : ℕ) (g : Qubits 1) (dest orig : Qubits w) (k₀ k₁ : Qubits 2) (dval : Qubits w) :
    updateOn (sliceEmb (1 + w + w) 2 (by omega)) (rec3SlotFn w g dest orig k₀ dval) k₁ =
      rec3SlotFn w g dest orig k₁ dval := by
  rw [eq_rec3SlotFn_iff]
  refine ⟨?_, ?_, ?_, updateOn_comp_emb _ _ _, ?_⟩
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec3SlotFn_comp_0 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec3SlotFn_comp_1 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]; exact rec3SlotFn_comp_2 ..
  · rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inl (by omega)))]; exact rec3SlotFn_comp_4 ..

lemma updateOn_rec3SlotFn_4 (w : ℕ) (g : Qubits 1) (dest orig : Qubits w) (kind : Qubits 2) (dv₀ dv₁ : Qubits w) :
    updateOn (sliceEmb (1 + w + w + 2) w (by omega)) (rec3SlotFn w g dest orig kind dv₀) dv₁ =
      rec3SlotFn w g dest orig kind dv₁ := by
  rw [eq_rec3SlotFn_iff]
  refine ⟨?_, ?_, ?_, ?_, updateOn_comp_emb _ _ _⟩
  all_goals
    rw [updateOn_comp_disjoint _ _ (sliceEmb_disjoint _ _ (Or.inr (by omega)))]
    first | exact rec3SlotFn_comp_0 .. | exact rec3SlotFn_comp_1 ..
          | exact rec3SlotFn_comp_2 .. | exact rec3SlotFn_comp_3 ..

def hbRecToRec3Bits (w : ℕ) (r : HBRec) (dval : Qubits w) : Qubits ((1 + w + w) + (2 + w)) :=
  rec3SlotFn w (natToBits 1 (hbGroup r)) (natToBits w r.dest) (natToBits w r.orig) (natToBits 2 r.kind) dval

lemma hbKey2_bitsToNat (comb : LcgSym54Comb) (w : ℕ) (r : HBRec) (dval : Qubits w)
    (hd : r.dest < 2 ^ w) (horig : r.orig < 2 ^ w) :
    bitsToNat (recKey54 (hbRecToRec3Bits w r dval)) =
      (hbGroup r * 2 ^ w + r.dest) * 2 ^ w + r.orig := by
  dsimp [hbRecToRec3Bits]; rw [recKey54_rec3SlotFn]; dsimp [rec3KeyFn]
  have hg : hbGroup r < 2 ^ 1 := by dsimp [hbGroup]; split_ifs <;> omega
  rw [comb.bitsToNat_append, comb.bitsToNat_append,
    comb.bitsToNat_natToBits hg, comb.bitsToNat_natToBits hd, comb.bitsToNat_natToBits horig]
  ring

lemma hbKey2_bitsToNat_le_iff (comb : LcgSym54Comb) (w : ℕ) (r₁ r₂ : HBRec) (d₁ d₂ : Qubits w)
    (hd₁ : r₁.dest < 2 ^ w) (hd₂ : r₂.dest < 2 ^ w)
    (hi₁ : r₁.orig < 2 ^ w) (hi₂ : r₂.orig < 2 ^ w) :
    bitsToNat (recKey54 (hbRecToRec3Bits w r₁ d₁)) ≤ bitsToNat (recKey54 (hbRecToRec3Bits w r₂ d₂)) ↔
      hbKey2 r₁ ≤ hbKey2 r₂ := by
  rw [hbKey2_bitsToNat comb w r₁ d₁ hd₁ hi₁, hbKey2_bitsToNat comb w r₂ d₂ hd₂ hi₂]
  rw [nat_mul_add_le_iff _ _ hi₁ hi₂, nat_mul_add_lt_iff _ _ hd₁ hd₂, nat_mul_add_eq_iff _ _ hd₁ hd₂]
  dsimp [hbKey2]; simp only [Prod.Lex.le_iff]; tauto

lemma hbKey2_bitsToNat_eq_iff (comb : LcgSym54Comb) (w : ℕ) (r₁ r₂ : HBRec) (d₁ d₂ : Qubits w)
    (hd₁ : r₁.dest < 2 ^ w) (hd₂ : r₂.dest < 2 ^ w)
    (hi₁ : r₁.orig < 2 ^ w) (hi₂ : r₂.orig < 2 ^ w) :
    bitsToNat (recKey54 (hbRecToRec3Bits w r₁ d₁)) = bitsToNat (recKey54 (hbRecToRec3Bits w r₂ d₂)) ↔
      hbKey2 r₁ = hbKey2 r₂ := by
  have h1 := hbKey2_bitsToNat_le_iff comb w r₁ r₂ d₁ d₂ hd₁ hd₂ hi₁ hi₂
  have h2 := hbKey2_bitsToNat_le_iff comb w r₂ r₁ d₂ d₁ hd₂ hd₁ hi₂ hi₁
  exact ⟨fun he => le_antisymm (h1.mp he.le) (h2.mp he.symm.le),
    fun he => le_antisymm (h1.mpr he.le) (h2.mpr he.symm.le)⟩

lemma natToBits_two_zero_eq_hbGroup (comb : LcgSym54Comb) (r : HBRec) (hr : r.kind ≤ 3) :
    (fun _ : Fin 1 => natToBits 2 r.kind 0) = natToBits 1 (hbGroup r) := by
  funext i; have hi0 : i = 0 := Fin.ext (by omega); subst hi0
  have hL : natToBits 2 r.kind 0 = Nat.testBit r.kind 1 :=
    comb.natToBits_comp_revPerm 2 r.kind ⟨1, by decide⟩
  have hR : natToBits 1 (hbGroup r) 0 = Nat.testBit (hbGroup r) 0 :=
    comb.natToBits_comp_revPerm 1 (hbGroup r) ⟨0, by decide⟩
  rw [hL, hR]
  rcases (by omega : r.kind = 0 ∨ r.kind = 1 ∨ r.kind = 2 ∨ r.kind = 3) with h | h | h | h <;>
    simp [hbGroup, h] <;> decide

lemma natToBits_two_one_xor_three (comb : LcgSym54Comb) :
    (fun j : Fin 2 => xor (natToBits 2 1 j) (natToBits 2 3 j)) = natToBits 2 2 := by
  funext j; fin_cases j
  · change xor (natToBits 2 1 (⟨1, by decide⟩ : Fin 2).rev) (natToBits 2 3 (⟨1, by decide⟩ : Fin 2).rev) =
        natToBits 2 2 (⟨1, by decide⟩ : Fin 2).rev
    rw [comb.natToBits_comp_revPerm, comb.natToBits_comp_revPerm, comb.natToBits_comp_revPerm]; decide
  · change xor (natToBits 2 1 (⟨0, by decide⟩ : Fin 2).rev) (natToBits 2 3 (⟨0, by decide⟩ : Fin 2).rev) =
        natToBits 2 2 (⟨0, by decide⟩ : Fin 2).rev
    rw [comb.natToBits_comp_revPerm, comb.natToBits_comp_revPerm, comb.natToBits_comp_revPerm]; decide

/-! #### 7.3 Packing `eRec2` (`hbInitCirc`) -/


end HarmBucketWork54


