-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_2
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54_2
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:33:40.32153+00:00
-- url     : https://prove2.me/theorems/90366e30-daf5-595b-919b-ecbb783d13e1
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (2/11)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 2 of 11 (`harmBucketWork54_2`).
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

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (2/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

section ArithWrappers

open QuantumLTF.Membership.Supplement.LcgSym54

lemma act_ctrlCopyRegOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eC : Fin 1 ↪ Fin m) (eSrc eDst : Fin w ↪ Fin m)
    (hCS : ∀ i j, eC i ≠ eSrc j) (hCD : ∀ i j, eC i ≠ eDst j) (hSD : ∀ i j, eSrc i ≠ eDst j)
    (z : Qubits m) :
    act ((arith.ctrlCopyRegCircuit w).mapWires
        (combineEmb (combineEmb eC eSrc hCS) eDst (emb_disjoint_combineEmb hCS hCD hSD))).unitary (ket z) =
      ket (updateOn eDst z (if z (eC 0) then fun j => xor (z (eDst j)) (z (eSrc j)) else z ∘ eDst)) := by
  let embMain := combineEmb (combineEmb eC eSrc hCS) eDst (emb_disjoint_combineEmb hCS hCD hSD)
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hdisj : ∀ i j, embMain i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (arith.ctrlCopyRegCircuit w) (ctrlCopyRegFn w)
    (arith.ctrlCopyRegCircuit_implements w) embMain embAnc hdisj z (fun j => Fin.elim0 j)
  rw [combineEmb_zero_right] at hsub
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right (combineEmb eC eSrc hCS) eDst (emb_disjoint_combineEmb hCS hCD hSD) z
    (ctrlCopyRegFn w) ?_ _ ?_
  · intro x i
    dsimp only [ctrlCopyRegFn]
    have hlt : ¬ (1 + w ≤ (Fin.castAdd w i : Fin (1 + w + w)).1) := by dsimp [Fin.castAdd]; exact Nat.not_le_of_lt i.isLt
    split_ifs <;> simp
  · intro j
    dsimp only [ctrlCopyRegFn, Function.comp_apply]
    have hc0 : embMain (⟨0, by omega⟩ : Fin (1 + w + w)) = eC 0 := by
      change combineEmb (combineEmb eC eSrc hCS) eDst _ (Fin.castAdd w (Fin.castAdd w 0)) = eC 0
      simp
    have hzc : z ((combineEmb (combineEmb eC eSrc hCS) eDst (emb_disjoint_combineEmb hCS hCD hSD)) ⟨0, by omega⟩) =
        z (eC 0) := congrArg z hc0
    have hge : 1 + w ≤ (Fin.natAdd (1 + w) j : Fin (1 + w + w)).1 := by simp [Fin.natAdd]
    simp only [hzc]
    cases hx : z (eC 0)
    · simp only [Bool.false_eq_true, ↓reduceIte, combineEmb_natAdd, Function.comp_apply]
    · simp only [↓reduceIte, dif_pos hge, combineEmb_natAdd]
      have hidx : (⟨(Fin.natAdd (1 + w) j : Fin (1 + w + w)).1 - w, by simp [Fin.natAdd]; omega⟩ : Fin (1 + w + w)) =
          Fin.castAdd w (Fin.natAdd 1 j) := by
        apply Fin.ext; simp [Fin.natAdd, Fin.castAdd]; omega
      rw [hidx, combineEmb_castAdd, combineEmb_natAdd]

lemma act_ctrlConstXorOn {w c m : ℕ} (arith : LcgSym54ArithV2)
    (eC : Fin 1 ↪ Fin m) (eB : Fin w ↪ Fin m) (hCB : ∀ i j, eC i ≠ eB j) (z : Qubits m) :
    act ((arith.ctrlConstXorMSBCircuit w c).mapWires (combineEmb eC eB hCB)).unitary (ket z) =
      ket (updateOn eB z (if z (eC 0) then fun j => xor (z (eB j)) (natToBits w c j) else z ∘ eB)) := by
  let embAnc : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  have hdisj : ∀ i j, combineEmb eC eB hCB i ≠ embAnc j := fun _ j => Fin.elim0 j
  have hsub := arith.act_subReg_perm (arith.ctrlConstXorMSBCircuit w c) (ctrlConstXorMSBFn w c)
    (arith.ctrlConstXorMSBCircuit_implements w c) (combineEmb eC eB hCB) embAnc hdisj z (fun j => Fin.elim0 j)
  rw [combineEmb_zero_right] at hsub
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eC eB hCB z (ctrlConstXorMSBFn w c) ?_ _ ?_
  · intro x i
    have hi0 : i = 0 := Fin.ext (by omega); subst hi0
    dsimp only [ctrlConstXorMSBFn]
    have hlt : ¬ (1 ≤ (Fin.castAdd w (0 : Fin 1) : Fin (1 + w)).1) := by simp
    split_ifs <;> simp
  · intro j
    dsimp only [ctrlConstXorMSBFn, Function.comp_apply]
    have hc0 : combineEmb eC eB hCB ⟨0, by omega⟩ = eC 0 := by
      change combineEmb eC eB hCB (Fin.castAdd w 0) = eC 0; simp
    have hzc : z ((combineEmb eC eB hCB) ⟨0, by omega⟩) = z (eC 0) := congrArg z hc0
    have hge : 1 ≤ (Fin.natAdd 1 j : Fin (1 + w)).1 := by simp [Fin.natAdd]
    simp only [hzc]
    cases hx : z (eC 0)
    · simp
    · simp only [↓reduceIte, dif_pos hge, combineEmb_natAdd]
      have hidx : (⟨(Fin.natAdd 1 j : Fin (1 + w)).1 - 1, by simp [Fin.natAdd]⟩ : Fin w) = j :=
        Fin.ext (by simp [Fin.natAdd])
      rw [hidx]

lemma act_eqRegOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eA eB : Fin w ↪ Fin m) (eOut : Fin 1 ↪ Fin m) (eAnc : Fin w ↪ Fin m)
    (hAB : ∀ i j, eA i ≠ eB j) (hAO : ∀ i j, eA i ≠ eOut j) (hBO : ∀ i j, eB i ≠ eOut j)
    (hAA : ∀ i k, eA i ≠ eAnc k) (hBA : ∀ i k, eB i ≠ eAnc k) (hOA : ∀ j k, eOut j ≠ eAnc k)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.eqRegCircuit w).mapWires
        (combineEmb (combineEmb (combineEmb eA eB hAB) eOut (emb_disjoint_combineEmb hAB hAO hBO))
          eAnc (emb_disjoint_combineEmb (emb_disjoint_combineEmb hAB hAO hBO)
            (emb_disjoint_combineEmb hAB hAA hBA) hOA))).unitary (ket z) =
      ket (updateOn eOut z (fun _ => xor (z (eOut 0)) (decide (z ∘ eA = z ∘ eB)))) := by
  let embAB := combineEmb eA eB hAB
  let embM := combineEmb embAB eOut (emb_disjoint_combineEmb hAB hAO hBO)
  have hsub := arith.act_subReg_perm (arith.eqRegCircuit w) (eqRegFn w)
    (arith.eqRegCircuit_implements w) embM eAnc
    (emb_disjoint_combineEmb (emb_disjoint_combineEmb hAB hAO hBO) (emb_disjoint_combineEmb hAB hAA hBA) hOA)
    z (fun k => congrFun hzAnc k)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right embAB eOut (emb_disjoint_combineEmb hAB hAO hBO) z (eqRegFn w) ?_ _ ?_
  · intro x i
    dsimp only [eqRegFn]
    have hne : Fin.castAdd 1 i ≠ ⟨w + w, by omega⟩ := Fin.ne_of_val_ne (by simp; omega)
    rw [Function.update_of_ne hne]
  · intro j
    have hj0 : j = 0 := Fin.ext (by omega); subst hj0
    dsimp only [eqRegFn, Function.comp_apply]
    have hnw : Fin.natAdd (w + w) (0 : Fin 1) = ⟨w + w, by omega⟩ := rfl
    rw [hnw, Function.update_self]
    have hc : embM ⟨w + w, by omega⟩ = eOut 0 := by
      rw [← hnw]; dsimp [embM]; rw [combineEmb_natAdd]
    rw [hc]
    congr 1
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, funext_iff, Function.comp_apply]
    refine forall_congr' fun i => ?_
    have ha : embM ⟨i.1, by omega⟩ = eA i := by
      change embM (Fin.castAdd 1 (Fin.castAdd w i)) = eA i
      dsimp [embM, embAB]; rw [combineEmb_castAdd, combineEmb_castAdd]
    have hb : embM ⟨w + i.1, by omega⟩ = eB i := by
      change embM (Fin.castAdd 1 (Fin.natAdd w i)) = eB i
      dsimp [embM, embAB]; rw [combineEmb_castAdd, combineEmb_natAdd]
    rw [ha, hb]

lemma act_eqConstOn {w c m : ℕ} (arith : LcgSym54ArithV2)
    (eIn : Fin w ↪ Fin m) (eOut : Fin 1 ↪ Fin m) (eAnc : Fin w ↪ Fin m)
    (hIO : ∀ i j, eIn i ≠ eOut j) (hIA : ∀ i k, eIn i ≠ eAnc k) (hOA : ∀ j k, eOut j ≠ eAnc k)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.eqConstMSBCircuit w c).mapWires
        (combineEmb (combineEmb eIn eOut hIO) eAnc (emb_disjoint_combineEmb hIO hIA hOA))).unitary (ket z) =
      ket (updateOn eOut z (fun _ => xor (z (eOut 0)) (decide (z ∘ eIn = natToBits w c)))) := by
  have hsub := arith.act_subReg_perm (arith.eqConstMSBCircuit w c) (eqConstMSBFn w c)
    (arith.eqConstMSBCircuit_implements w c) (combineEmb eIn eOut hIO) eAnc
    (emb_disjoint_combineEmb hIO hIA hOA) z (fun j => congrFun hzAnc j)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eIn eOut hIO z (eqConstMSBFn w c) ?_ _ ?_
  · intro x i
    dsimp only [eqConstMSBFn]
    have hne : Fin.castAdd 1 i ≠ ⟨w, by omega⟩ := Fin.ne_of_val_ne (by simp; omega)
    rw [Function.update_of_ne hne]
  · intro j
    have hj0 : j = 0 := Fin.ext (by omega); subst hj0
    dsimp only [eqConstMSBFn, Function.comp_apply]
    have hnw : Fin.natAdd w (0 : Fin 1) = ⟨w, by omega⟩ := rfl
    rw [hnw, Function.update_self]
    have hc : combineEmb eIn eOut hIO ⟨w, by omega⟩ = eOut 0 := by
      rw [← hnw, combineEmb_natAdd]
    rw [hc]
    congr 1
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, funext_iff, Function.comp_apply]
    refine forall_congr' fun i => ?_
    have hi : combineEmb eIn eOut hIO ⟨i.1, by omega⟩ = eIn i := by
      change combineEmb eIn eOut hIO (Fin.castAdd 1 i) = eIn i; simp
    rw [hi]

lemma act_ltConstOn {w H m : ℕ} (arith : LcgSym54ArithV2)
    (eIn : Fin w ↪ Fin m) (eOut : Fin 1 ↪ Fin m) (eAnc : Fin w ↪ Fin m)
    (hIO : ∀ i j, eIn i ≠ eOut j) (hIA : ∀ i k, eIn i ≠ eAnc k) (hOA : ∀ j k, eOut j ≠ eAnc k)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.ltConstMSBCircuit w H).mapWires
        (combineEmb (combineEmb eIn eOut hIO) eAnc (emb_disjoint_combineEmb hIO hIA hOA))).unitary (ket z) =
      ket (updateOn eOut z (fun _ => xor (z (eOut 0)) (decide (bitsToNat (z ∘ eIn) < H)))) := by
  have hsub := arith.act_subReg_perm (arith.ltConstMSBCircuit w H) (ltConstMSBFn w H)
    (arith.ltConstMSBCircuit_implements w H) (combineEmb eIn eOut hIO) eAnc
    (emb_disjoint_combineEmb hIO hIA hOA) z (fun j => congrFun hzAnc j)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eIn eOut hIO z (ltConstMSBFn w H) ?_ _ ?_
  · intro x i
    dsimp only [ltConstMSBFn]
    have hne : Fin.castAdd 1 i ≠ ⟨w, Nat.lt_succ_self w⟩ := Fin.ne_of_val_ne (by simp; omega)
    rw [Function.update_of_ne hne]
  · intro j
    have hj0 : j = 0 := Fin.ext (by omega); subst hj0
    dsimp only [ltConstMSBFn, Function.comp_apply]
    have hnw : Fin.natAdd w (0 : Fin 1) = ⟨w, Nat.lt_succ_self w⟩ := rfl
    rw [hnw, Function.update_self]
    have hc : combineEmb eIn eOut hIO ⟨w, Nat.lt_succ_self w⟩ = eOut 0 := by
      rw [← hnw, combineEmb_natAdd]
    have hin : (fun i : Fin w => z (combineEmb eIn eOut hIO ⟨i.1, by omega⟩)) = z ∘ eIn :=
      funext fun i => by change z (combineEmb eIn eOut hIO (Fin.castAdd 1 i)) = z (eIn i); rw [combineEmb_castAdd]
    rw [hc, hin]

lemma act_ctrlAddConstOn {w c m : ℕ} (arith : LcgSym54ArithV2)
    (eC : Fin 1 ↪ Fin m) (eB : Fin w ↪ Fin m) (eAnc : Fin (w + 1) ↪ Fin m)
    (hCB : ∀ i j, eC i ≠ eB j) (hCA : ∀ i k, eC i ≠ eAnc k) (hBA : ∀ j k, eB j ≠ eAnc k)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.ctrlAddConstInPlaceMSBCircuit w c).mapWires
        (combineEmb (combineEmb eC eB hCB) eAnc (emb_disjoint_combineEmb hCB hCA hBA))).unitary (ket z) =
      ket (updateOn eB z (if z (eC 0) then natToBits w (c % 2 ^ w + bitsToNat (z ∘ eB)) else z ∘ eB)) := by
  let embM := combineEmb eC eB hCB
  have hsub := arith.act_subReg_perm (arith.ctrlAddConstInPlaceMSBCircuit w c) (ctrlAddConstInPlaceMSBFn w c)
    (arith.ctrlAddConstInPlaceMSBCircuit_implements w c) embM eAnc
    (emb_disjoint_combineEmb hCB hCA hBA) z (fun k => congrFun hzAnc k)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eC eB hCB z (ctrlAddConstInPlaceMSBFn w c) ?_ _ ?_
  · intro x i
    have hi0 : i = 0 := Fin.ext (by omega); subst hi0
    dsimp only [ctrlAddConstInPlaceMSBFn]
    have hlt : ¬ (1 ≤ (Fin.castAdd w (0 : Fin 1) : Fin (1 + w)).1) := by simp
    split_ifs <;> simp
  · intro j
    dsimp only [ctrlAddConstInPlaceMSBFn, Function.comp_apply]
    have hc0 : (combineEmb eC eB hCB) ⟨0, by omega⟩ = eC 0 := by
      change (combineEmb eC eB hCB) (Fin.castAdd w 0) = eC 0; simp
    have hzc : z ((combineEmb eC eB hCB) ⟨0, by omega⟩) = z (eC 0) := congrArg z hc0
    have hb : (fun i : Fin w => z ((combineEmb eC eB hCB) ⟨1 + i.1, by omega⟩)) = z ∘ eB := funext fun i => by
      change z ((combineEmb eC eB hCB) (Fin.natAdd 1 i)) = z (eB i); simp
    have hge : 1 ≤ (Fin.natAdd 1 j : Fin (1 + w)).1 := by simp [Fin.natAdd]
    simp only [hzc, hb]
    cases hx : z (eC 0)
    · simp only [Bool.false_eq_true, ↓reduceIte, Function.comp_apply, combineEmb_natAdd]
    · simp only [↓reduceIte, dif_pos hge]
      have hidx : (⟨(Fin.natAdd 1 j : Fin (1 + w)).1 - 1, by simp [Fin.natAdd]⟩ : Fin w) = j :=
        Fin.ext (by simp [Fin.natAdd])
      rw [hidx]

lemma act_addInPlaceOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eA eB : Fin w ↪ Fin m) (eAnc : Fin 1 ↪ Fin m)
    (hAB : ∀ i j, eA i ≠ eB j) (hAA : ∀ i j, eA i ≠ eAnc j) (hBA : ∀ i j, eB i ≠ eAnc j)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.addInPlaceMSBCircuit w).mapWires
        (combineEmb (combineEmb eA eB hAB) eAnc (emb_disjoint_combineEmb hAB hAA hBA))).unitary (ket z) =
      ket (updateOn eB z (natToBits w (bitsToNat (z ∘ eA) + bitsToNat (z ∘ eB)))) := by
  have hsub := arith.act_subReg_perm (arith.addInPlaceMSBCircuit w) (addInPlaceMSBFn w)
    (arith.addInPlaceMSBCircuit_implements w) (combineEmb eA eB hAB) eAnc
    (emb_disjoint_combineEmb hAB hAA hBA) z (fun j => congrFun hzAnc j)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eA eB hAB z (addInPlaceMSBFn w) ?_ _ ?_
  · intro x i
    dsimp only [addInPlaceMSBFn]
    have hlt : (Fin.castAdd w i : Fin (w + w)).1 < w := by dsimp [Fin.castAdd]; exact i.isLt
    rw [dif_pos hlt]
  · intro j
    dsimp only [addInPlaceMSBFn, Function.comp_apply]
    have hge : ¬ ((Fin.natAdd w j : Fin (w + w)).1 < w) := by simp [Fin.natAdd]
    rw [dif_neg hge]
    have hidx : (⟨(Fin.natAdd w j : Fin (w + w)).1 - w, by simp [Fin.natAdd]⟩ : Fin w) = j :=
      Fin.ext (by simp [Fin.natAdd])
    rw [hidx]
    have ha : (fun i : Fin w => z (combineEmb eA eB hAB ⟨i.1, by omega⟩)) = z ∘ eA :=
      funext fun i => by change z (combineEmb eA eB hAB (Fin.castAdd w i)) = z (eA i); rw [combineEmb_castAdd]
    have hb : (fun i : Fin w => z (combineEmb eA eB hAB ⟨w + i.1, by omega⟩)) = z ∘ eB :=
      funext fun i => by change z (combineEmb eA eB hAB (Fin.natAdd w i)) = z (eB i); rw [combineEmb_natAdd]
    rw [ha, hb]

lemma act_subInPlaceOn {w m : ℕ} (arith : LcgSym54ArithV2)
    (eA eB : Fin w ↪ Fin m) (eAnc : Fin 1 ↪ Fin m)
    (hAB : ∀ i j, eA i ≠ eB j) (hAA : ∀ i j, eA i ≠ eAnc j) (hBA : ∀ i j, eB i ≠ eAnc j)
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.subInPlaceMSBCircuit w).mapWires
        (combineEmb (combineEmb eA eB hAB) eAnc (emb_disjoint_combineEmb hAB hAA hBA))).unitary (ket z) =
      ket (updateOn eB z (natToBits w (2 ^ w + bitsToNat (z ∘ eB) - bitsToNat (z ∘ eA)))) := by
  have hsub := arith.act_subReg_perm (arith.subInPlaceMSBCircuit w) (subInPlaceMSBFn w)
    (arith.subInPlaceMSBCircuit_implements w) (combineEmb eA eB hAB) eAnc
    (emb_disjoint_combineEmb hAB hAA hBA) z (fun j => congrFun hzAnc j)
  rw [hsub]
  congr 1
  refine updateOn_combineEmb_right eA eB hAB z (subInPlaceMSBFn w) ?_ _ ?_
  · intro x i
    dsimp only [subInPlaceMSBFn]
    have hlt : (Fin.castAdd w i : Fin (w + w)).1 < w := by dsimp [Fin.castAdd]; exact i.isLt
    rw [dif_pos hlt]
  · intro j
    dsimp only [subInPlaceMSBFn, Function.comp_apply]
    have hge : ¬ ((Fin.natAdd w j : Fin (w + w)).1 < w) := by simp [Fin.natAdd]
    rw [dif_neg hge]
    have hidx : (⟨(Fin.natAdd w j : Fin (w + w)).1 - w, by simp [Fin.natAdd]⟩ : Fin w) = j :=
      Fin.ext (by simp [Fin.natAdd])
    rw [hidx]
    have ha : (fun i : Fin w => z (combineEmb eA eB hAB ⟨i.1, by omega⟩)) = z ∘ eA :=
      funext fun i => by change z (combineEmb eA eB hAB (Fin.castAdd w i)) = z (eA i); rw [combineEmb_castAdd]
    have hb : (fun i : Fin w => z (combineEmb eA eB hAB ⟨w + i.1, by omega⟩)) = z ∘ eB :=
      funext fun i => by change z (combineEmb eA eB hAB (Fin.natAdd w i)) = z (eB i); rw [combineEmb_natAdd]
    rw [ha, hb]

lemma natToBits_all_true (comb : LcgSym54Comb) (k : ℕ) :
    natToBits k (2 ^ k - 1) = fun _ : Fin k => true := by
  apply comb.bitsToNat_inj
  rw [comb.bitsToNat_natToBits (Nat.sub_lt (Nat.two_pow_pos k) Nat.zero_lt_one)]
  dsimp only [bitsToNat]
  simp only [↓reduceIte]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    have h0 : k + 1 - 1 - (0 : Fin (k + 1)).1 = k := by simp
    have hs : (∑ x : Fin k, 2 ^ (k + 1 - 1 - (Fin.succ x).1)) = ∑ x : Fin k, 2 ^ (k - 1 - x.1) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      have h1 : k + 1 - 1 - (Fin.succ x).1 = k - 1 - x.1 := by
        have hx := x.isLt; simp [Fin.val_succ]; omega
      rw [h1]
    rw [h0, hs, ← ih]
    have hpos : 1 ≤ 2 ^ k := Nat.two_pow_pos k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
    omega

lemma act_allTrueAndOn {k m : ℕ} (comb : LcgSym54Comb) (arith : LcgSym54ArithV2)
    (eIn : Fin k ↪ Fin m) (eOut : Fin 1 ↪ Fin m) (eAnc : Fin k ↪ Fin m)
    (hIO : ∀ i j, eIn i ≠ eOut j) (hIA : ∀ i j, eIn i ≠ eAnc j) (hOA : ∀ j j', eOut j ≠ eAnc j')
    (z : Qubits m) (hzAnc : z ∘ eAnc = fun _ => false) :
    act ((arith.eqConstMSBCircuit k (2 ^ k - 1)).mapWires
        (combineEmb (combineEmb eIn eOut hIO) eAnc (emb_disjoint_combineEmb hIO hIA hOA))).unitary (ket z) =
      ket (updateOn eOut z (fun _ => xor (z (eOut 0)) (decide (∀ i : Fin k, z (eIn i) = true)))) := by
  have h := @act_eqConstOn k (2 ^ k - 1) m arith eIn eOut eAnc hIO hIA hOA z hzAnc
  rw [h, natToBits_all_true comb k]
  congr 1; congr 1; funext _
  congr 1
  rw [Bool.eq_iff_iff]
  simp [funext_iff]


end ArithWrappers


/-! ### Part 4: Bitonic Pack Helpers & Global Parameter Bundle (`HarmBucketParams`) -/

lemma act_mapWires_ket_singleton {m₀ m : ℕ} (lc : LayeredCircuit m₀) (emb : Fin m₀ ↪ Fin m)
    (z : Qubits m) (y₀ : Qubits m₀) (h : act lc.unitary (ket (z ∘ emb)) = ket y₀) :
    act (lc.mapWires emb).unitary (ket z) = ket (updateOn emb z y₀) := by
  have hsum := LcgSym54.act_mapWires_ket_sum lc emb z ({()} : Finset Unit) (fun _ => 1) (fun _ => y₀)
    (by simpa using h)
  simpa using hsum

def packDTA54Emb {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k) :
    Fin ((N * w + T) + anc) ↪ Fin m :=
  combineEmb (combineEmb eArr eTr hAT) eAnc (emb_disjoint_combineEmb hAT hAA hTA)

@[simp] lemma packDTA54Emb_arr {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (i : Fin (N * w)) :
    packDTA54Emb eArr eTr eAnc hAT hAA hTA (Fin.castAdd anc (Fin.castAdd T i)) = eArr i := by
  simp [packDTA54Emb]

@[simp] lemma packDTA54Emb_tr {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (j : Fin T) :
    packDTA54Emb eArr eTr eAnc hAT hAA hTA (Fin.castAdd anc (Fin.natAdd (N * w) j)) = eTr j := by
  simp [packDTA54Emb]

@[simp] lemma packDTA54Emb_anc {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (k : Fin anc) :
    packDTA54Emb eArr eTr eAnc hAT hAA hTA (Fin.natAdd (N * w + T) k) = eAnc k := by
  simp [packDTA54Emb]

lemma comp_packDTA54Emb {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (z : Qubits m) (arr : Fin N → Qubits w) (tr : Qubits T)
    (hzA : z ∘ eArr = flatReg N w arr) (hzT : z ∘ eTr = tr) (hzAnc : z ∘ eAnc = fun _ => false) :
    z ∘ packDTA54Emb eArr eTr eAnc hAT hAA hTA = packDTA54 N w T anc arr tr := by
  funext u
  refine Fin.addCases (fun ij => ?_) (fun k => ?_) u
  · refine Fin.addCases (fun i => ?_) (fun j => ?_) ij
    · simp only [Function.comp_apply, packDTA54Emb_arr, packDTA54, padZero_castAdd, Fin.append_left]
      exact congrFun hzA i
    · simp only [Function.comp_apply, packDTA54Emb_tr, packDTA54, padZero_castAdd, Fin.append_right]
      exact congrFun hzT j
  · simp only [Function.comp_apply, packDTA54Emb_anc, packDTA54, padZero_natAdd]
    exact congrFun hzAnc k

lemma updateOn_packDTA54_arr {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (z : Qubits m) (arr : Fin N → Qubits w) (tr : Qubits T) :
    updateOn (packDTA54Emb eArr eTr eAnc hAT hAA hTA) z (packDTA54 N w T anc arr tr) ∘ eArr =
      flatReg N w arr := by
  funext i
  rw [Function.comp_apply, ← packDTA54Emb_arr eArr eTr eAnc hAT hAA hTA i, updateOn_apply_emb,
    packDTA54, padZero_castAdd, Fin.append_left]

lemma updateOn_packDTA54_tr {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (z : Qubits m) (arr : Fin N → Qubits w) (tr : Qubits T) :
    updateOn (packDTA54Emb eArr eTr eAnc hAT hAA hTA) z (packDTA54 N w T anc arr tr) ∘ eTr = tr := by
  funext j
  rw [Function.comp_apply, ← packDTA54Emb_tr eArr eTr eAnc hAT hAA hTA j, updateOn_apply_emb,
    packDTA54, padZero_castAdd, Fin.append_right]

lemma updateOn_packDTA54_anc {N w T anc m : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (z : Qubits m) (arr : Fin N → Qubits w) (tr : Qubits T) :
    updateOn (packDTA54Emb eArr eTr eAnc hAT hAA hTA) z (packDTA54 N w T anc arr tr) ∘ eAnc =
      fun _ => false := by
  funext k
  rw [Function.comp_apply, ← packDTA54Emb_anc eArr eTr eAnc hAT hAA hTA k, updateOn_apply_emb,
    packDTA54, padZero_natAdd]

lemma updateOn_packDTA54_disjoint {N w T anc m k2 : ℕ}
    (eArr : Fin (N * w) ↪ Fin m) (eTr : Fin T ↪ Fin m) (eAnc : Fin anc ↪ Fin m)
    (hAT : ∀ i j, eArr i ≠ eTr j) (hAA : ∀ i k, eArr i ≠ eAnc k) (hTA : ∀ j k, eTr j ≠ eAnc k)
    (eOther : Fin k2 ↪ Fin m)
    (hoA : ∀ i x, eArr i ≠ eOther x) (hoT : ∀ j x, eTr j ≠ eOther x) (hoAnc : ∀ k x, eAnc k ≠ eOther x)
    (z : Qubits m) (arr : Fin N → Qubits w) (tr : Qubits T) :
    updateOn (packDTA54Emb eArr eTr eAnc hAT hAA hTA) z (packDTA54 N w T anc arr tr) ∘ eOther =
      z ∘ eOther :=
  updateOn_comp_disjoint _ _
    (emb_disjoint_combineEmb (emb_disjoint_combineEmb hAT hAA hTA)
      (emb_disjoint_combineEmb hAT hoA hoT) hoAnc) z _

lemma sortTraceSize_mono (br : BitonicRouting54) {d1 d2 : ℕ} (h : d1 ≤ d2) :
    sortTraceSize d1 ≤ sortTraceSize d2 := by
  have h1 := br.four_mul_sortTraceSize d1
  have h2 := br.four_mul_sortTraceSize d2
  have hpow : 2 ^ d1 ≤ 2 ^ d2 := Nat.pow_le_pow_right (by norm_num) h
  have hmul : d1 * (d1 + 1) ≤ d2 * (d2 + 1) := Nat.mul_le_mul h (Nat.add_le_add_right h 1)
  have hprod : d1 * (d1 + 1) * 2 ^ d1 ≤ d2 * (d2 + 1) * 2 ^ d2 := Nat.mul_le_mul hmul hpow
  omega

lemma natToBits_two_pow_add (w x : ℕ) :
    natToBits w (2 ^ w + x) = natToBits w x := by
  simp [natToBits]

lemma natToBits_mod_two_pow (w x : ℕ) :
    natToBits w (x % 2 ^ w) = natToBits w x := by
  simp [natToBits]


/-! #### 5.1 Pure Parameter Functions & Numeric Bounds -/

def sOf (n : ℕ) : ℕ := Nat.clog 2 n + 1

def lOf (n K : ℕ) : ℕ := Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1

def dOccOf (K : ℕ) : ℕ := Nat.clog 2 (2 * K)

def dHbOf (K : ℕ) : ℕ := Nat.clog 2 (2 * K * Nat.clog 2 (2 * K + 2) + 2)

def wOf (K : ℕ) : ℕ := dHbOf K + 2

lemma four_le_lOf {n K : ℕ} (h1n : 1 ≤ n) (h1K : 1 ≤ K) : 4 ≤ lOf n K := by
  dsimp [lOf]
  have hge : 6 ≤ (K + 1) * (n + 1) + 2 := by nlinarith
  have hnot : ¬ Nat.clog 2 ((K + 1) * (n + 1) + 2) ≤ 2 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    omega
  omega


end HarmBucketWork54


