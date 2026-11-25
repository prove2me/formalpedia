-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54
-- name    : QuantumLTF_Membership_Supplement_harmBucketWork54
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-25T06:59:50.729995+00:00
-- url     : https://prove2.me/theorems/73cfee13-1df0-4488-842d-e5b88ebdffe3
-- title:
--   Harmonic-Bucket $2$-Sort working layout and layer module (11/11, interfaces)
-- statement:
--   Working Lean definitions, register embeddings, disjointness lemmas, circuit combinators, and layer interface structures (`HarmBucketOcc54`, `HarmBucketRouteA54`, `HarmBucketRouteB54`) for `HarmBucketHL54V2` — module slice 11 of 11 (`harmBucketWork54`).
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
import Definitions.Def_QuantumLTF_Membership_Supplement_harmBucketWork54_10

set_option autoImplicit false

/-!
# Harmonic-Bucket 2-Sort Working Module (11/11)
-/

namespace HarmBucketWork54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router Cslib.BitonicSort


end HarmBucketWork54

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router Cslib.BitonicSort HarmBucketWork54
open QuantumLTF.Membership.Supplement.LcgSym54

/-- Bundled Steps 1–2 (`runOffset`, active indicator, and `runOcc` computation) circuit spec. -/
structure HarmBucketOcc54 where
  step12Circ_size :
    ∀ (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (br : BitonicRouting54)
      (n K d : ℕ) (h1K : 1 ≤ K),
      ((step12Circ as arith br n K d h1K).size : ℝ) ≤
        (wOf K + (2 * K - 1) * (28 * sOf n + 42 * wOf K + 28) : ℕ) +
        2 * (arity (dOccOf K) * (2 * wOf K + 2) : ℕ) +
        2 * (br.C_sort * (2 ^ (dOccOf K) : ℝ) * (((dOccOf K : ℝ) + 1) ^ 2) * ((wR1Occ K : ℝ) + 1)) +
        ((2 * K - 1) * (49 * wOf K + 236) : ℕ) +
        ((2 * K) * (3 * wOf K) : ℕ)
  act_step12Circ :
    ∀ (_comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
      (br : BitonicRouting54) (n K d : ℕ) (h1K : 1 ≤ K)
      (l : Fin (2 * K) → Fin (n + 1)) (_hl : Monotone l)
      (z : Qubits (totWiresDef as n K d))
      (_hzL : z ∘ eL as n K d = flatReg (2 * K) (sOf n) fun p => particleSym54 n (sOf n) (l p))
      (_hzAnc : ∀ k : Fin 24, k.1 ≤ 10 → z ∘ ancEmb as n K d k = fun _ => false),
      act (step12Circ as arith br n K d h1K).unitary (ket z) =
        ket (updateOn (eOccReg as n K d)
          (updateOn (eActReg as n K d)
            (updateOn (eMReg as n K d) z (flatReg (2 * K) (wOf K) (mBitsFn K l)))
            (flatReg (2 * K) 1 (actBitsFn K l)))
          (flatReg (2 * K) (wOf K) (occBitsFn K l)))

/-- Bundled Step 3A (`hbInitCirc`, `sortHb1Circ`, `hbSeqPassCirc`) circuit and semantic spec. -/
structure HarmBucketRouteA54 where
  hbInitCirc_size :
    ∀ (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ),
      (hbInitCirc as arith n K d).size ≤ arity (dHbOf K + 1) * (11 * wOf K + 12)
  sortHb1Circ_size :
    ∀ (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ),
      ((sortHb1Circ as br n K d).size : ℝ) ≤
        br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + 1)
  hbSeqPassCirc_size :
    ∀ (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K),
      (hbSeqPassCirc as arith n K d h1K).size ≤ (arity (dHbOf K + 1) - 1) * (61 * wOf K + 321)
  rec2SortedArr_eq_hb1Spec :
    ∀ (_comb : LcgSym54Comb) (_br : BitonicRouting54) {n K : ℕ} (_h1K : 1 ≤ K)
      (l : Fin (2 * K) → Fin (n + 1)),
      rec2SortedArr K l =
        hb1ArrOfList K (hb1SortedList K l) (hb1SortedList_length K l) (fun _ _ => false)
  act_hbInitCirc :
    ∀ (_comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
      (n K d : ℕ) {l : Fin (2 * K) → Fin (n + 1)} (z : Qubits (totWiresDef as n K d)),
      z ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l) →
      z ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l) →
      z ∘ eOccReg as n K d = flatReg (2 * K) (wOf K) (occBitsFn K l) →
      z ∘ ancEmb as n K d ⟨11, by decide⟩ = (fun _ => false) →
      act (hbInitCirc as arith n K d).unitary (ket z) =
        ket (updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hbInitArr K l)))
  act_sortHb1Circ :
    ∀ (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ)
      {l : Fin (2 * K) → Fin (n + 1)} (z : Qubits (totWiresDef as n K d)),
      z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hbInitArr K l) →
      z ∘ ancEmb as n K d ⟨12, by decide⟩ = (fun _ => false) →
      z ∘ ancEmb as n K d ⟨17, by decide⟩ = (fun _ => false) →
      act (sortHb1Circ as br n K d).unitary (ket z) =
        ket (updateOn (eTr2a as n K d)
          (updateOn (eRec2 as n K d) z (flatReg (arity (dHbOf K + 1)) (wR1Hb K) (rec2SortedArr K l)))
          (rec2SortTr K l))
  act_hbSeqPassCirc :
    ∀ (_comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
      (n K d : ℕ) (h1K : 1 ≤ K) (z : Qubits (totWiresDef as n K d))
      (s1 : List HBRec) (hs1_len : s1.length = arity (dHbOf K + 1))
      (_hs1_bnd : ∀ r ∈ s1, r.kind ≤ 3 ∧ r.kind ≠ 2 ∧ (r.kind = 0 → r.dest = 0) ∧
        r.m < 2 ^ wOf K ∧ r.occ < 2 ^ wOf K ∧ r.dest < 2 ^ wOf K ∧ r.orig < 2 ^ wOf K)
      (d_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K)),
      z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K s1 hs1_len d_arr) →
      z ∘ eSeqB as n K d = (fun _ => false) →
      z ∘ eSeqCtrl as n K d = (fun _ => false) →
      z ∘ ancEmb as n K d ⟨22, by decide⟩ = (fun _ => false) →
      act (hbSeqPassCirc as arith n K d h1K).unitary (ket z) =
        ket (updateOn (eRec2 as n K d) z
          (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
            (hb1ArrOfList K (hbSeqPass s1) (by rw [hbSeqPass_length]; exact hs1_len) d_arr)))

/-- Bundled Step 3B (`copyToRec3Circ`, `sortHb2Circ`, `step3Circ`) circuit and semantic spec. -/
structure HarmBucketRouteB54 where
  copyToRec3Circ_size :
    ∀ (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2) (n K d : ℕ),
      (copyToRec3Circ as arith n K d).size ≤ arity (dHbOf K + 1) * (2 * wOf K + 3)
  sortHb2Circ_size :
    ∀ (as : AlonsoSchottSil54) (br : BitonicRouting54) (n K d : ℕ),
      ((sortHb2Circ as br n K d).size : ℝ) ≤
        br.C_sort * (2 ^ (dHbOf K + 1) : ℝ) * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR2Hb K : ℝ) + 1)
  step3Circ_size :
    ∀ (as : AlonsoSchottSil54) (br : BitonicRouting54) (arith : LcgSym54ArithV2)
      (n K d : ℕ) (h1K : 1 ≤ K),
      ((step3Circ as br arith n K d h1K).size : ℝ) ≤
        ((arity (dHbOf K + 1) : ℕ) : ℝ) * (74 * (wOf K : ℝ) + 336 +
          br.C_sort * (((dHbOf K + 1 : ℕ) : ℝ) + 1) ^ 2 * ((wR1Hb K : ℝ) + (wR2Hb K : ℝ) + 2))
  rec3SortedArr_eq_hb2Spec :
    ∀ (_comb : LcgSym54Comb) (_br : BitonicRouting54) {n K : ℕ} (_h1K : 1 ≤ K)
      (l : Fin (2 * K) → Fin (n + 1)),
      rec3SortedArr K l =
        hb3ArrOfList K (hb2SortedList K l) (hb2SortedList_length K l) (fun _ _ => false)
  act_copyToRec3Circ :
    ∀ (_comb : LcgSym54Comb) (as : AlonsoSchottSil54) (arith : LcgSym54ArithV2)
      (n K d : ℕ) (z : Qubits (totWiresDef as n K d))
      (s2 : List HBRec) (hs2_len : s2.length = arity (dHbOf K + 1))
      (_hs2_kind : ∀ r ∈ s2, r.kind ≤ 3)
      (d2_arr : Fin (arity (dHbOf K + 1)) → Qubits (wOf K)),
      z ∘ eRec2 as n K d = flatReg (arity (dHbOf K + 1)) (wR1Hb K) (hb1ArrOfList K s2 hs2_len d2_arr) →
      z ∘ ancEmb as n K d ⟨13, by decide⟩ = (fun _ => false) →
      act (copyToRec3Circ as arith n K d).unitary (ket z) =
        ket (updateOn (eRec3 as n K d) z
          (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (hb3ArrOfList K s2 hs2_len (fun _ _ => false))))
  act_step3Circ :
    ∀ (_comb : LcgSym54Comb) (br : BitonicRouting54) (as : AlonsoSchottSil54)
      (arith : LcgSym54ArithV2) (n K d : ℕ) (h1K : 1 ≤ K) {l : Fin (2 * K) → Fin (n + 1)}
      (z : Qubits (totWiresDef as n K d)),
      z ∘ eActReg as n K d = flatReg (2 * K) 1 (actBitsFn K l) →
      z ∘ eMReg as n K d = flatReg (2 * K) (wOf K) (mBitsFn K l) →
      z ∘ eOccReg as n K d = flatReg (2 * K) (wOf K) (occBitsFn K l) →
      z ∘ ancEmb as n K d ⟨11, by decide⟩ = (fun _ => false) →
      z ∘ ancEmb as n K d ⟨12, by decide⟩ = (fun _ => false) →
      z ∘ ancEmb as n K d ⟨13, by decide⟩ = (fun _ => false) →
      z ∘ ancEmb as n K d ⟨14, by decide⟩ = (fun _ => false) →
      z ∘ ancEmb as n K d ⟨17, by decide⟩ = (fun _ => false) →
      z ∘ ancEmb as n K d ⟨18, by decide⟩ = (fun _ => false) →
      z ∘ ancEmb as n K d ⟨19, by decide⟩ = (fun _ => false) →
      z ∘ ancEmb as n K d ⟨20, by decide⟩ = (fun _ => false) →
      z ∘ ancEmb as n K d ⟨22, by decide⟩ = (fun _ => false) →
      act (step3Circ as br arith n K d h1K).unitary (ket z) =
        ket (updateOn (eTr2b as n K d)
          (updateOn (eRec3 as n K d)
            (updateOn (eTr2a as n K d)
              (updateOn (eRec2 as n K d) z
                (flatReg (arity (dHbOf K + 1)) (wR1Hb K)
                  (hb1ArrOfList K (hbSeqPass (hb1SortedList K l))
                    (by rw [hbSeqPass_length, hb1SortedList_length]) (fun _ _ => false))))
              (rec2SortTr K l))
            (flatReg (arity (dHbOf K + 1)) (wR2Hb K) (rec3SortedArr K l)))
          (rec3SortTr K l))

end QuantumLTF.Membership.Supplement


