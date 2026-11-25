-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_4
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54_4
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:40:55.218736+00:00
-- url     : https://prove2.me/theorems/40dae0ca-ae54-4e30-aa2a-7dfed6b4c644
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (4/11)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 4 of 11 (`harmBucketWork54_4`).
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

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (4/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort

lemma updateOn_ancRegSlot (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    (z : Qubits (totWiresDef as n K d)) (arr : Fin N_rec → Qubits w_r)
    (hz : z ∘ ancRegSlice as n K d k N_rec w_r hlen = flatReg N_rec w_r arr)
    (q : Fin N_rec) (val : Qubits w_r) :
    updateOn (ancRegSlot as n K d k N_rec w_r hlen q) z val ∘
        ancRegSlice as n K d k N_rec w_r hlen =
      flatReg N_rec w_r (Function.update arr q val) := by
  let eBig := ancRegSlice as n K d k N_rec w_r hlen
  funext idx
  rcases finProdFinEquiv.surjective idx with ⟨⟨q', b⟩, rfl⟩
  simp only [Function.comp_apply, flatReg, Equiv.symm_apply_apply]
  by_cases hqq : q' = q
  · subst hqq
    change updateOn (ancRegSlot as n K d k N_rec w_r hlen q') z val
        (ancRegSlot as n K d k N_rec w_r hlen q' b) =
      Function.update arr q' val q' b
    rw [updateOn_apply_emb, Function.update_self]
  · rw [Function.update_of_ne hqq]
    have hnot : eBig (finProdFinEquiv (q', b)) ∉ Set.range (ancRegSlot as n K d k N_rec w_r hlen q) := by
      rintro ⟨b', hb'⟩
      have heq := eBig.injective hb'
      exact hqq (Prod.ext_iff.mp (finProdFinEquiv.injective heq)).1.symm
    rw [updateOn_apply_not_mem _ _ _ hnot]
    have := congrFun hz (finProdFinEquiv (q', b))
    simpa [flatReg] using this

lemma updateOn_ancRegField (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (N_rec w_r : ℕ)
    (hlen : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N_rec * w_r)
    (z : Qubits (totWiresDef as n K d)) (arr : Fin N_rec → Qubits w_r)
    (hz : z ∘ ancRegSlice as n K d k N_rec w_r hlen = flatReg N_rec w_r arr)
    (q : Fin N_rec) (fOff fLen : ℕ) (hf : fOff + fLen ≤ w_r) (val : Qubits fLen) :
    updateOn (ancRegField as n K d k N_rec w_r hlen q fOff fLen hf) z val ∘
        ancRegSlice as n K d k N_rec w_r hlen =
      flatReg N_rec w_r
        (Function.update arr q (updateOn (sliceEmb fOff fLen hf) (arr q) val)) := by
  let eBig := ancRegSlice as n K d k N_rec w_r hlen
  funext idx
  rcases finProdFinEquiv.surjective idx with ⟨⟨q', b⟩, rfl⟩
  simp only [Function.comp_apply, flatReg, Equiv.symm_apply_apply]
  by_cases hqq : q' = q
  · subst hqq
    rw [Function.update_self]
    by_cases hb : b ∈ Set.range (sliceEmb fOff fLen hf)
    · rcases hb with ⟨i, rfl⟩
      change updateOn (ancRegField as n K d k N_rec w_r hlen q' fOff fLen hf) z val
          (ancRegField as n K d k N_rec w_r hlen q' fOff fLen hf i) =
        updateOn (sliceEmb fOff fLen hf) (arr q') val (sliceEmb fOff fLen hf i)
      rw [updateOn_apply_emb, updateOn_apply_emb]
    · have hnot : eBig (finProdFinEquiv (q', b)) ∉
          Set.range (ancRegField as n K d k N_rec w_r hlen q' fOff fLen hf) := by
        rintro ⟨i, hi⟩
        have heq := eBig.injective hi
        have hb' := (Prod.ext_iff.mp (finProdFinEquiv.injective heq)).2
        exact hb ⟨i, hb'⟩
      rw [updateOn_apply_not_mem _ _ _ hnot, updateOn_apply_not_mem _ _ _ hb]
      have := congrFun hz (finProdFinEquiv (q', b))
      simpa [flatReg] using this
  · rw [Function.update_of_ne hqq]
    have hnot : eBig (finProdFinEquiv (q', b)) ∉
        Set.range (ancRegField as n K d k N_rec w_r hlen q fOff fLen hf) := by
      rintro ⟨i, hi⟩
      have heq := eBig.injective hi
      exact hqq (Prod.ext_iff.mp (finProdFinEquiv.injective heq)).1.symm
    rw [updateOn_apply_not_mem _ _ _ hnot]
    have := congrFun hz (finProdFinEquiv (q', b))
    simpa [flatReg] using this

def ancPrefixEmb (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24) (subLen : ℕ)
    (hle : subLen ≤ ancLen n K d (as.alonsoSchottAnc (2 * K) d) k) :
    Fin subLen ↪ Fin (totWiresDef as n K d) :=
  (sliceEmb 0 subLen (by omega)).trans (ancEmb as n K d k)

lemma ancPrefix_disjoint_anc (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (subLen : ℕ)
    (hle : subLen ≤ ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1) :
    ∀ i j, ancPrefixEmb as n K d k1 subLen hle i ≠ ancEmb as n K d k2 j :=
  trans_disjoint_left (ancEmb_disjoint as n K d hk)

lemma anc_disjoint_ancPrefix (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k2 ≠ k1) (subLen : ℕ)
    (hle : subLen ≤ ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1) :
    ∀ i j, ancEmb as n K d k2 i ≠ ancPrefixEmb as n K d k1 subLen hle j :=
  fun i j h => ancPrefix_disjoint_anc as n K d hk.symm subLen hle j i h.symm

def eLSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    Fin (sOf n) ↪ Fin (totWiresDef as n K d) :=
  (slotInReg (2 * K) (sOf n) i).trans (eL as n K d)

lemma eLSlot_disjoint_anc (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) (k : Fin 24) :
    ∀ a b, eLSlot as n K d i a ≠ ancEmb as n K d k b :=
  trans_disjoint_left (eL_disjoint_anc as n K d k)

lemma comp_eLSlot (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (arr : Fin (2 * K) → Qubits (sOf n))
    (hz : z ∘ eL as n K d = flatReg (2 * K) (sOf n) arr) (i : Fin (2 * K)) :
    z ∘ eLSlot as n K d i = arr i := by
  funext b
  have := congrFun hz (finProdFinEquiv (i, b))
  simpa [flatReg, eLSlot, Function.comp_apply] using this

def eOutSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin (arity d)) :
    Fin d ↪ Fin (totWiresDef as n K d) :=
  (slotInReg (arity d) d j).trans (eOut as n K d)

lemma eOutSlot_disjoint_anc (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin (arity d)) (k : Fin 24) :
    ∀ a b, eOutSlot as n K d j a ≠ ancEmb as n K d k b :=
  trans_disjoint_left (eOut_disjoint_anc as n K d k)

lemma anc_disjoint_eOutSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin (arity d)) (k : Fin 24) :
    ∀ a b, ancEmb as n K d k a ≠ eOutSlot as n K d j b :=
  fun a b h => eOutSlot_disjoint_anc as n K d j k b a h.symm

lemma updateOn_eOutSlot_comp_eOut (as : AlonsoSchottSil54) (n K d : ℕ)
    (z : Qubits (totWiresDef as n K d)) (arr : Fin (arity d) → Qubits d)
    (hz : z ∘ eOut as n K d = flatReg (arity d) d arr)
    (j : Fin (arity d)) (val : Qubits d) :
    updateOn (eOutSlot as n K d j) z val ∘ eOut as n K d =
      flatReg (arity d) d (Function.update arr j val) := by
  funext idx
  rcases finProdFinEquiv.surjective idx with ⟨⟨q', b⟩, rfl⟩
  simp only [Function.comp_apply, flatReg, Equiv.symm_apply_apply]
  by_cases hqq : q' = j
  · subst hqq
    change updateOn (eOutSlot as n K d q') z val (eOutSlot as n K d q' b) =
      Function.update arr q' val q' b
    rw [updateOn_apply_emb, Function.update_self]
  · rw [Function.update_of_ne hqq]
    have hnot : eOut as n K d (finProdFinEquiv (q', b)) ∉ Set.range (eOutSlot as n K d j) := by
      rintro ⟨b', hb'⟩
      have heq := (eOut as n K d).injective hb'
      exact hqq (Prod.ext_iff.mp (finProdFinEquiv.injective heq)).1.symm
    rw [updateOn_apply_not_mem _ _ _ hnot]
    have := congrFun hz (finProdFinEquiv (q', b))
    simpa [flatReg] using this

lemma ancRegSlot_disjoint_ancRegSlot (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (N1 w1 N2 w2 : ℕ)
    (h1 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N1 * w1)
    (h2 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k2 = N2 * w2)
    (q1 : Fin N1) (q2 : Fin N2) :
    ∀ a b, ancRegSlot as n K d k1 N1 w1 h1 q1 a ≠ ancRegSlot as n K d k2 N2 w2 h2 q2 b :=
  trans_disjoint_right (trans_disjoint_right (ancRegSlot_disjoint_anc as n K d hk N1 w1 h1 q1))

lemma ancRegSlot_disjoint_ancPrefix (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (N1 w1 : ℕ)
    (h1 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N1 * w1) (q1 : Fin N1)
    (subLen : ℕ) (hle : subLen ≤ ancLen n K d (as.alonsoSchottAnc (2 * K) d) k2) :
    ∀ a b, ancRegSlot as n K d k1 N1 w1 h1 q1 a ≠ ancPrefixEmb as n K d k2 subLen hle b :=
  trans_disjoint_right (ancRegSlot_disjoint_anc as n K d hk N1 w1 h1 q1)

lemma ancPrefix_disjoint_ancRegSlot (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (subLen : ℕ) (hle : subLen ≤ ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1)
    (N2 w2 : ℕ) (h2 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k2 = N2 * w2) (q2 : Fin N2) :
    ∀ a b, ancPrefixEmb as n K d k1 subLen hle a ≠ ancRegSlot as n K d k2 N2 w2 h2 q2 b :=
  trans_disjoint_left (anc_disjoint_ancRegSlot as n K d hk N2 w2 h2 q2)

lemma eLSlot_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ) {i1 i2 : Fin (2 * K)}
    (hi : i1 ≠ i2) :
    ∀ a b, eLSlot as n K d i1 a ≠ eLSlot as n K d i2 b := by
  intro a b h
  exact slotInReg_disjoint hi a b ((eL as n K d).injective h)

lemma eLSlot_disjoint_ancPrefix (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K))
    (k : Fin 24) (subLen : ℕ) (hle : subLen ≤ ancLen n K d (as.alonsoSchottAnc (2 * K) d) k) :
    ∀ a b, eLSlot as n K d i a ≠ ancPrefixEmb as n K d k subLen hle b :=
  trans_disjoint_right (eLSlot_disjoint_anc as n K d i k)

lemma ancRegField_disjoint_ancPrefix (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (N1 w1 : ℕ) (h1 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N1 * w1)
    (q1 : Fin N1) (fOff fLen : ℕ) (hf : fOff + fLen ≤ w1)
    (subLen : ℕ) (hle : subLen ≤ ancLen n K d (as.alonsoSchottAnc (2 * K) d) k2) :
    ∀ a b, ancRegField as n K d k1 N1 w1 h1 q1 fOff fLen hf a ≠
      ancPrefixEmb as n K d k2 subLen hle b :=
  trans_disjoint_right (ancRegField_disjoint_anc as n K d hk N1 w1 h1 q1 fOff fLen hf)

lemma ancRegField_disjoint_ancRegSlot (as : AlonsoSchottSil54) (n K d : ℕ) {k1 k2 : Fin 24}
    (hk : k1 ≠ k2) (N1 w1 : ℕ) (h1 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k1 = N1 * w1)
    (q1 : Fin N1) (fOff fLen : ℕ) (hf : fOff + fLen ≤ w1)
    (N2 w2 : ℕ) (h2 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k2 = N2 * w2) (q2 : Fin N2) :
    ∀ a b, ancRegField as n K d k1 N1 w1 h1 q1 fOff fLen hf a ≠
      ancRegSlot as n K d k2 N2 w2 h2 q2 b :=
  trans_disjoint_right (trans_disjoint_right (ancRegField_disjoint_anc as n K d hk N1 w1 h1 q1 fOff fLen hf))

lemma eOutSlot_disjoint_ancRegSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin (arity d))
    (k : Fin 24) (N1 w1 : ℕ) (h1 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N1 * w1) (q : Fin N1) :
    ∀ a b, eOutSlot as n K d j a ≠ ancRegSlot as n K d k N1 w1 h1 q b :=
  trans_disjoint_right (trans_disjoint_right (eOutSlot_disjoint_anc as n K d j k))

lemma ancRegSlot_disjoint_eOutSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin (arity d))
    (k : Fin 24) (N1 w1 : ℕ) (h1 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N1 * w1) (q : Fin N1) :
    ∀ a b, ancRegSlot as n K d k N1 w1 h1 q a ≠ eOutSlot as n K d j b :=
  fun a b h => eOutSlot_disjoint_ancRegSlot as n K d j k N1 w1 h1 q b a h.symm

lemma eOutSlot_disjoint_ancPrefix (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin (arity d))
    (k : Fin 24) (subLen : ℕ) (hle : subLen ≤ ancLen n K d (as.alonsoSchottAnc (2 * K) d) k) :
    ∀ a b, eOutSlot as n K d j a ≠ ancPrefixEmb as n K d k subLen hle b :=
  trans_disjoint_right (eOutSlot_disjoint_anc as n K d j k)

lemma ancRegField_disjoint_eOutSlot (as : AlonsoSchottSil54) (n K d : ℕ) (j : Fin (arity d))
    (k : Fin 24) (N1 w1 : ℕ) (h1 : ancLen n K d (as.alonsoSchottAnc (2 * K) d) k = N1 * w1)
    (q : Fin N1) (fOff fLen : ℕ) (hf : fOff + fLen ≤ w1) :
    ∀ a b, ancRegField as n K d k N1 w1 h1 q fOff fLen hf a ≠ eOutSlot as n K d j b :=
  trans_disjoint_left (ancRegSlot_disjoint_eOutSlot as n K d j k N1 w1 h1 q)

/-! #### 5.4 `updateOn` Algebra Helpers -/

lemma updateOn_comm {a b m : ℕ} (e1 : Fin a ↪ Fin m) (e2 : Fin b ↪ Fin m)
    (h12 : ∀ i j, e1 i ≠ e2 j) (z : Qubits m) (v1 : Qubits a) (v2 : Qubits b) :
    updateOn e1 (updateOn e2 z v2) v1 = updateOn e2 (updateOn e1 z v1) v2 := by
  funext u
  by_cases h1 : u ∈ Set.range e1
  · rcases h1 with ⟨i, rfl⟩
    have hnot2 : e1 i ∉ Set.range e2 := by rintro ⟨j, hj⟩; exact h12 i j hj.symm
    rw [updateOn_apply_emb, updateOn_apply_not_mem _ _ _ hnot2, updateOn_apply_emb]
  · rw [updateOn_apply_not_mem _ _ _ h1]
    by_cases h2 : u ∈ Set.range e2
    · rcases h2 with ⟨j, rfl⟩
      rw [updateOn_apply_emb, updateOn_apply_emb]
    · rw [updateOn_apply_not_mem _ _ _ h2, updateOn_apply_not_mem _ _ _ h2,
        updateOn_apply_not_mem _ _ _ h1]

lemma updateOn_idem {a m : ℕ} (e : Fin a ↪ Fin m) (z : Qubits m) (v1 v2 : Qubits a) :
    updateOn e (updateOn e z v1) v2 = updateOn e z v2 := by
  funext u
  by_cases h : u ∈ Set.range e
  · rcases h with ⟨i, rfl⟩; simp [updateOn_apply_emb]
  · simp [updateOn_apply_not_mem _ _ _ h]

lemma updateOn_noop {a m : ℕ} (e : Fin a ↪ Fin m) (z : Qubits m) (v : Qubits a)
    (h : z ∘ e = v) : updateOn e z v = z := by
  subst h
  funext u
  by_cases hmem : u ∈ Set.range e
  · rcases hmem with ⟨i, rfl⟩; rw [updateOn_apply_emb]; rfl
  · rw [updateOn_apply_not_mem _ _ _ hmem]

lemma updateOn_slot_absorb {N w m : ℕ} (e : Fin (N * w) ↪ Fin m) (z : Qubits m)
    (arr : Fin N → Qubits w) (q : Fin N) (val : Qubits w) :
    updateOn ((slotInReg N w q).trans e) (updateOn e z (flatReg N w arr)) val =
      updateOn e z (flatReg N w (Function.update arr q val)) := by
  funext u
  by_cases hu : u ∈ Set.range e
  · rcases hu with ⟨idx, rfl⟩
    rcases finProdFinEquiv.surjective idx with ⟨⟨q', b⟩, rfl⟩
    by_cases hq : q' = q
    · subst hq
      change updateOn ((slotInReg N w q').trans e) _ val (((slotInReg N w q').trans e) b) =
        updateOn e z (flatReg N w (Function.update arr q' val)) (e (finProdFinEquiv (q', b)))
      rw [updateOn_apply_emb, updateOn_apply_emb, flatReg, Equiv.symm_apply_apply, Function.update_self]
    · have hnot : e (finProdFinEquiv (q', b)) ∉ Set.range ((slotInReg N w q).trans e) := by
        rintro ⟨b', hb'⟩
        have heq := e.injective hb'
        exact hq (Prod.ext_iff.mp (finProdFinEquiv.injective heq)).1.symm
      rw [updateOn_apply_not_mem _ _ _ hnot, updateOn_apply_emb, updateOn_apply_emb]
      simp only [flatReg, Equiv.symm_apply_apply, Function.update_of_ne hq]
  · have hnot : u ∉ Set.range ((slotInReg N w q).trans e) := by
      rintro ⟨b, hb⟩; exact hu ⟨slotInReg N w q b, hb⟩
    rw [updateOn_apply_not_mem _ _ _ hnot, updateOn_apply_not_mem _ _ _ hu,
      updateOn_apply_not_mem _ _ _ hu]

lemma updateOn_comp_emb {a m : ℕ} (e : Fin a ↪ Fin m) (z : Qubits m) (val : Qubits a) :
    updateOn e z val ∘ e = val := by
  funext i; exact updateOn_apply_emb e z val i

lemma updateOn_trans_emb {a b m : ℕ} (s : Fin a ↪ Fin b) (e : Fin b ↪ Fin m)
    (z : Qubits m) (val : Qubits a) :
    updateOn (s.trans e) z val = updateOn e z (updateOn s (z ∘ e) val) := by
  funext u
  by_cases hu : u ∈ Set.range e
  · rcases hu with ⟨j, rfl⟩
    by_cases hj : j ∈ Set.range s
    · rcases hj with ⟨i, rfl⟩
      change updateOn (s.trans e) z val ((s.trans e) i) =
        updateOn e z (updateOn s (z ∘ e) val) (e (s i))
      rw [updateOn_apply_emb, updateOn_apply_emb, updateOn_apply_emb]
    · have hnot : e j ∉ Set.range (s.trans e) := by
        rintro ⟨i, hi⟩; exact hj ⟨i, e.injective hi⟩
      rw [updateOn_apply_not_mem _ _ _ hnot, updateOn_apply_emb, updateOn_apply_not_mem _ _ _ hj]
      rfl
  · have hnot : u ∉ Set.range (s.trans e) := by
      rintro ⟨i, hi⟩; exact hu ⟨s i, hi⟩
    rw [updateOn_apply_not_mem _ _ _ hnot, updateOn_apply_not_mem _ _ _ hu]

def comb3 {a b c m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m) (ec : Fin c ↪ Fin m)
    (hab : ∀ i j, ea i ≠ eb j) (hac : ∀ i k, ea i ≠ ec k) (hbc : ∀ j k, eb j ≠ ec k) :
    Fin (a + b + c) ↪ Fin m :=
  combineEmb (combineEmb ea eb hab) ec (emb_disjoint_combineEmb hab hac hbc)

def comb4 {a b c d m : ℕ} (ea : Fin a ↪ Fin m) (eb : Fin b ↪ Fin m) (ec : Fin c ↪ Fin m)
    (ed : Fin d ↪ Fin m)
    (hab : ∀ i j, ea i ≠ eb j) (hac : ∀ i k, ea i ≠ ec k) (hbc : ∀ j k, eb j ≠ ec k)
    (had : ∀ i l, ea i ≠ ed l) (hbd : ∀ j l, eb j ≠ ed l) (hcd : ∀ k l, ec k ≠ ed l) :
    Fin (a + b + c + d) ↪ Fin m :=
  combineEmb (comb3 ea eb ec hab hac hbc) ed
    (emb_disjoint_combineEmb _ (emb_disjoint_combineEmb hab had hbd) hcd)


lemma sOf_le_lOf {n K : ℕ} : sOf n ≤ lOf n K := by
  dsimp [sOf, lOf]
  exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by nlinarith)) 1


/-! ### Part 6: Step 1 & Step 2 Definitions & Disjointness -/

lemma runOffset_zero_two_K {α : Type*} [LinearOrder α] {K : ℕ} (h1K : 1 ≤ K)
    {l : Fin (2 * K) → α} (hl : Monotone l) :
    runOffset l ⟨0, by omega⟩ = 1 := by
  have hstart : runStart l ⟨0, by omega⟩ = 0 := by
    rw [runStart, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _
    exact not_lt.mpr (hl (Nat.zero_le j.1))
  simp [runOffset, hstart]

lemma particleSym54_eq_iff (comb : LcgSym54Comb) (n : ℕ) (a b : Fin (n + 1)) :
    particleSym54 n (sOf n) a = particleSym54 n (sOf n) b ↔ a = b :=
  ⟨fun h => (comb.bitsToNat_particleSym54_strictMono n).injective (congrArg bitsToNat h),
   fun h => congrArg _ h⟩

lemma natToBits_one_one (comb : LcgSym54Comb) :
    natToBits 1 1 = fun _ : Fin 1 => true := by
  simpa using natToBits_all_true comb 1

lemma bitsToNat_one_bit (b : Qubits 1) :
    bitsToNat b = if b 0 then 1 else 0 := by
  rw [bitsToNat, Fin.sum_univ_one]
  cases b 0 <;> simp

lemma xor_false_left (b : Bool) : xor false b = b := by cases b <;> rfl
lemma xor_self_cancel (a : Bool) : xor a a = false := by cases a <;> rfl

/-! #### 6.2 Register Shorthands (with `@[irreducible]` `ancLen`) -/

def eMReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (2 * K * wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegSlice as n K d ⟨0, by decide⟩ (2 * K) (wOf K) (ancLen_0 n K d _)

def eMSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  (slotInReg (2 * K) (wOf K) i).trans (eMReg as n K d)

def eActReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (2 * K * 1) ↪ Fin (totWiresDef as n K d) :=
  ancRegSlice as n K d ⟨1, by decide⟩ (2 * K) 1 (ancLen_1 n K d _)

def eActSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  (slotInReg (2 * K) 1 i).trans (eActReg as n K d)

def eOccReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (2 * K * wOf K) ↪ Fin (totWiresDef as n K d) :=
  ancRegSlice as n K d ⟨2, by decide⟩ (2 * K) (wOf K) (ancLen_2 n K d _)

def eOccSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    Fin (wOf K) ↪ Fin (totWiresDef as n K d) :=
  (slotInReg (2 * K) (wOf K) i).trans (eOccReg as n K d)

def eRec1Reg (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin (arity (dOccOf K) * wR1Occ K) ↪ Fin (totWiresDef as n K d) :=
  ancRegSlice as n K d ⟨3, by decide⟩ (arity (dOccOf K)) (wR1Occ K) (ancLen_3 n K d _)

def eRec1Slot (as : AlonsoSchottSil54) (n K d : ℕ) (q : Fin (arity (dOccOf K))) :
    Fin (wR1Occ K) ↪ Fin (totWiresDef as n K d) :=
  (slotInReg (arity (dOccOf K)) (wR1Occ K) q).trans (eRec1Reg as n K d)

def eEqFlag (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨5, by decide⟩ 1 (by rw [ancLen_5])

def eOne12 (as : AlonsoSchottSil54) (n K d : ℕ) :
    Fin 1 ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨6, by decide⟩ 1 (by rw [ancLen_6])

def eArith12Pref (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) :
    Fin subLen ↪ Fin (totWiresDef as n K d) :=
  ancPrefixEmb as n K d ⟨10, by decide⟩ subLen (by rw [ancLen_10]; exact hle)

-- Clean disjointness wrappers (explicit `k1`/`k2`, zero metavariables!)
lemma eMReg_disjoint_eL (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eMReg as n K d a ≠ eL as n K d b :=
  trans_disjoint_left (anc_disjoint_eL as n K d ⟨0, by decide⟩)

lemma eActReg_disjoint_eL (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eActReg as n K d a ≠ eL as n K d b :=
  trans_disjoint_left (anc_disjoint_eL as n K d ⟨1, by decide⟩)

lemma eMReg_disjoint_eActReg (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eMReg as n K d a ≠ eActReg as n K d b :=
  trans_disjoint_right (ancRegSlice_disjoint_anc as n K d (k1 := ⟨0, by decide⟩) (k2 := ⟨1, by decide⟩) (by decide) _ _ _)

lemma eMReg_disjoint_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (hk : k ≠ ⟨0, by decide⟩) :
    ∀ a b, eMReg as n K d a ≠ ancEmb as n K d k b :=
  ancRegSlice_disjoint_anc as n K d hk.symm _ _ _

lemma eActReg_disjoint_anc_other (as : AlonsoSchottSil54) (n K d : ℕ) (k : Fin 24)
    (hk : k ≠ ⟨1, by decide⟩) :
    ∀ a b, eActReg as n K d a ≠ ancEmb as n K d k b :=
  ancRegSlice_disjoint_anc as n K d hk.symm _ _ _

lemma eMSlot_disjoint_slot (as : AlonsoSchottSil54) (n K d : ℕ) {i1 i2 : Fin (2 * K)}
    (hi : i1 ≠ i2) : ∀ a b, eMSlot as n K d i1 a ≠ eMSlot as n K d i2 b := by
  intro a b h; exact slotInReg_disjoint hi a b ((eMReg as n K d).injective h)

lemma eMSlot_disjoint_eActReg (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eMSlot as n K d i a ≠ eActReg as n K d b :=
  trans_disjoint_left (eMReg_disjoint_eActReg as n K d)

lemma eMSlot_disjoint_eActSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i1 i2 : Fin (2 * K)) :
    ∀ a b, eMSlot as n K d i1 a ≠ eActSlot as n K d i2 b :=
  trans_disjoint_right (eMSlot_disjoint_eActReg as n K d i1)

lemma eMSlot_disjoint_eL (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eMSlot as n K d i a ≠ eL as n K d b :=
  trans_disjoint_left (eMReg_disjoint_eL as n K d)

lemma eLSlot_disjoint_eMSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i1 i2 : Fin (2 * K)) :
    ∀ a b, eLSlot as n K d i1 a ≠ eMSlot as n K d i2 b :=
  fun a b h => eMSlot_disjoint_eL as n K d i2 b (slotInReg _ _ i1 a) h.symm

lemma eActSlot_disjoint_eL (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eActSlot as n K d i a ≠ eL as n K d b :=
  trans_disjoint_left (eActReg_disjoint_eL as n K d)

lemma eLSlot_disjoint_eEqFlag (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eLSlot as n K d i a ≠ eEqFlag as n K d b :=
  eLSlot_disjoint_ancPrefix as n K d i ⟨5, by decide⟩ 1 _

lemma eLSlot_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) (i : Fin (2 * K)) :
    ∀ a b, eLSlot as n K d i a ≠ eArith12Pref as n K d subLen hle b :=
  eLSlot_disjoint_ancPrefix as n K d i ⟨10, by decide⟩ subLen _

lemma eEqFlag_disjoint_eArith12 (as : AlonsoSchottSil54) (n K d subLen : ℕ)
    (hle : subLen ≤ max (sOf n) (wOf K + 1)) :
    ∀ a b, eEqFlag as n K d a ≠ eArith12Pref as n K d subLen hle b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨5, by decide⟩) (k2 := ⟨10, by decide⟩) (by decide) 1 _)

lemma eEqFlag_disjoint_eMSlot (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eEqFlag as n K d a ≠ eMSlot as n K d i b :=
  trans_disjoint_right (trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨5, by decide⟩) (k2 := ⟨0, by decide⟩) (by decide) 1 _))

lemma eMSlot_disjoint_eEqFlag (as : AlonsoSchottSil54) (n K d : ℕ) (i : Fin (2 * K)) :
    ∀ a b, eMSlot as n K d i a ≠ eEqFlag as n K d b :=
  fun a b h => eEqFlag_disjoint_eMSlot as n K d i b a h.symm

lemma eEqFlag_disjoint_eOne12 (as : AlonsoSchottSil54) (n K d : ℕ) :
    ∀ a b, eEqFlag as n K d a ≠ eOne12 as n K d b :=
  trans_disjoint_right (ancPrefix_disjoint_anc as n K d (k1 := ⟨5, by decide⟩) (k2 := ⟨6, by decide⟩) (by decide) 1 _)


end HarmBucketWork54


