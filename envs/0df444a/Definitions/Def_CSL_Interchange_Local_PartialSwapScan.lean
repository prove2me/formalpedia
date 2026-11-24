-- Prove2me | Definitions.Def_CSL_Interchange_Local_PartialSwapScan
-- name    : CSL_Interchange_Local_PartialSwapScan
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:57:21.860066+00:00
-- url     : https://prove2.me/theorems/1c0171a2-4d2a-4c53-b35f-4c450b6d4d14
-- title:
--   Coded sorting library: Interchange / Local / PartialSwapScan
-- statement:
--   Module `CodedSorting.Interchange.Local.PartialSwapScan` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Scans in the mixed H / gap / D layout
--
--   The lower-triangular factors of a partial swap may mix H into D.  The gap
--   therefore cannot be moved outside a contiguous 2m-vector without a proof.
--   This module instead exposes one actual H or D coordinate at a time.  Its
--   prefix/field/suffix encoding is proved to be the same physical file index.
--   The resulting passes use the existing executable stream-pass language.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Local.PartialSwapScan

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Memory_AddressLayout
import Definitions.Def_CSL_Shared_Programs_ScanProgramLift

/-!
# Scans in the mixed H / gap / D layout

The lower-triangular factors of a partial swap may mix H into D.  The gap
therefore cannot be moved outside a contiguous 2m-vector without a proof.
This module instead exposes one actual H or D coordinate at a time.  Its
prefix/field/suffix encoding is proved to be the same physical file index.
The resulting passes use the existing executable stream-pass language.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CSL.Construction.PartialSwapScan

open Address SingleCoordinate LexBlocks TriangularStreams
open CommonAddressLayout ScanProgram AffineStreams SequentialArithmetic

noncomputable section

variable {I : Type*} [Fintype I] [LinearOrder I] [WellFoundedLT I]
variable {P Q G S K : ℕ}

abbrev Addr (I : Type*) (P Q G S : ℕ) :=
  FullAddress (Fin P) (I → Fin Q) (Fin G) (Fin S)

abbrev HighPrefixSize (P Q : ℕ) (i : I) := P * BeforeCount Q i
abbrev HighSuffixSize (Q G S : ℕ) (i : I) :=
  AfterCount Q i * (G * (FieldCount I Q * S))

abbrev LowPrefixSize (P Q G : ℕ) (i : I) :=
  (P * (FieldCount I Q * G)) * BeforeCount Q i
abbrev LowSuffixSize (Q S : ℕ) (i : I) := AfterCount Q i * S

def highPrefix (i : I) (a : Addr I P Q G S) : Fin (HighPrefixSize P Q i) :=
  finProdFinEquiv (a.prefixCoord,subvectorEncode (fun k : Before i => a.high k.val))

def highSuffix (i : I) (a : Addr I P Q G S) : Fin (HighSuffixSize Q G S i) :=
  tripleEncode (subvectorEncode (fun k : After i => a.high k.val),a.gap,
    finProdFinEquiv (subvectorEncode a.low,a.suffix))

def lowPrefix (i : I) (a : Addr I P Q G S) : Fin (LowPrefixSize P Q G i) :=
  finProdFinEquiv (tripleEncode (a.prefixCoord,subvectorEncode a.high,a.gap),
    subvectorEncode (fun k : Before i => a.low k.val))

def lowSuffix (i : I) (a : Addr I P Q G S) : Fin (LowSuffixSize Q S i) :=
  finProdFinEquiv (subvectorEncode (fun k : After i => a.low k.val),a.suffix)

theorem highVolume (i : I) :
    HighPrefixSize P Q i * (Q * HighSuffixSize Q G S i) = Volume I P Q G S := by
  unfold HighPrefixSize HighSuffixSize Volume
  calc
    _ = (P * ((BeforeCount Q i * (Q * AfterCount Q i)) * G)) *
      (FieldCount I Q * S) := by ring
    _ = _ := by rw [CommonAddressLayout.blockCard i]

theorem lowVolume (i : I) :
    LowPrefixSize P Q G i * (Q * LowSuffixSize Q S i) = Volume I P Q G S := by
  unfold LowPrefixSize LowSuffixSize Volume
  calc
    _ = (P * (FieldCount I Q * G)) *
      ((BeforeCount Q i * (Q * AfterCount Q i)) * S) := by ring
    _ = _ := by rw [CommonAddressLayout.blockCard i]

/-- The gap and every unselected coordinate keep their original position. -/
theorem high_layout (i : I) (a : Addr I P Q G S) :
    finCongr (highVolume (P := P) (G := G) (S := S) (Q := Q) i)
      (tripleEncode (highPrefix i a,a.high i,highSuffix i a)) = longLayout a := by
  apply Fin.ext
  rw [CommonAddressLayout.longLayout_val,CommonAddressLayout.field_layout_val i a.high]
  simp only [highPrefix,highSuffix,tripleEncode_val,finCongr_apply_coe,
    HighPrefixSize,HighSuffixSize]
  simp only [finProdFinEquiv,Equiv.coe_fn_mk,Prod.fst,Prod.snd]
  generalize (subvectorEncode a.low).val = d
  rw [← CommonAddressLayout.blockCard (Q := Q) i]
  ring

/-- Exposing a low coordinate retains the complete H / gap prefix. -/
theorem low_layout (i : I) (a : Addr I P Q G S) :
    finCongr (lowVolume (P := P) (G := G) (S := S) (Q := Q) i)
      (tripleEncode (lowPrefix i a,a.low i,lowSuffix i a)) = longLayout a := by
  apply Fin.ext
  rw [CommonAddressLayout.longLayout_val,CommonAddressLayout.field_layout_val i a.low]
  simp only [lowPrefix,lowSuffix,tripleEncode_val,finCongr_apply_coe,
    LowPrefixSize,LowSuffixSize]
  simp only [finProdFinEquiv,Equiv.coe_fn_mk,Prod.fst,Prod.snd]
  simp only [tripleEncode_val]
  generalize (subvectorEncode a.high).val = h
  rw [← CommonAddressLayout.blockCard (Q := Q) i]
  ring

def updateHigh (i : I) (v : Fin Q) (a : Addr I P Q G S) : Addr I P Q G S :=
  ⟨a.prefixCoord,Function.update a.high i v,a.gap,a.low,a.suffix⟩

def updateLow (i : I) (v : Fin Q) (a : Addr I P Q G S) : Addr I P Q G S :=
  ⟨a.prefixCoord,a.high,a.gap,Function.update a.low i v,a.suffix⟩

@[simp] theorem highPrefix_updateHigh (i : I) (v : Fin Q) (a : Addr I P Q G S) :
    highPrefix i (updateHigh i v a) = highPrefix i a := by
  unfold highPrefix updateHigh
  apply congrArg finProdFinEquiv
  apply Prod.ext
  · rfl
  · apply congrArg subvectorEncode
    funext k
    exact Function.update_of_ne (ne_of_lt k.property) _ _

@[simp] theorem highSuffix_updateHigh (i : I) (v : Fin Q) (a : Addr I P Q G S) :
    highSuffix i (updateHigh i v a) = highSuffix i a := by
  unfold highSuffix updateHigh
  apply congrArg tripleEncode
  apply Prod.ext
  · apply congrArg subvectorEncode
    funext k
    exact Function.update_of_ne (ne_of_gt k.property) _ _
  · rfl

@[simp] theorem lowPrefix_updateLow (i : I) (v : Fin Q) (a : Addr I P Q G S) :
    lowPrefix i (updateLow i v a) = lowPrefix i a := by
  unfold lowPrefix updateLow
  apply congrArg finProdFinEquiv
  apply Prod.ext
  · rfl
  · apply congrArg subvectorEncode
    funext k
    exact Function.update_of_ne (ne_of_lt k.property) _ _

@[simp] theorem lowSuffix_updateLow (i : I) (v : Fin Q) (a : Addr I P Q G S) :
    lowSuffix i (updateLow i v a) = lowSuffix i a := by
  unfold lowSuffix updateLow
  apply congrArg finProdFinEquiv
  apply Prod.ext
  · apply congrArg subvectorEncode
    funext k
    exact Function.update_of_ne (ne_of_gt k.property) _ _
  · rfl

section Cast
variable {V W A C : ℕ}

/-- A finite-index cast is not a data permutation. -/
def castPass (h : V = W) (p : Pass V) : Pass W := h ▸ p

theorem castPass_encoded (h : V = W) (p : Pass V) (x : Fin V) :
    (castPass h p).permutation (finCongr h x) = finCongr h (p.permutation x) := by
  subst W
  rfl

@[simp] theorem castPass_constant (h : V = W) (p : Pass V) :
    (castPass h p).constant = p.constant := by
  subst W
  rfl

/-- All physical prefixes share one fixed family of increasing streams. -/
def slotPass (h : A * (Q * C) = V) (e : Fin A → Equiv.Perm (Fin Q))
    (key : Fin A → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y) : Pass V :=
  castPass h (.streams K (globalFieldEquiv (S := C) e) (globalKey key)
    (global_increasing_streams e key hinc))

theorem slotPass_encoded (h : A * (Q * C) = V)
    (e : Fin A → Equiv.Perm (Fin Q)) (key : Fin A → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y)
    (p : Fin A) (x : Fin Q) (s : Fin C) :
    (slotPass h e key hinc).permutation (finCongr h (tripleEncode (p,x,s))) =
      finCongr h (tripleEncode (p,e p x,s)) := by
  rw [slotPass,castPass_encoded]
  exact congrArg (finCongr h) (globalFieldEquiv_encoded e (p,x,s))

@[simp] theorem slotPass_constant (h : A * (Q * C) = V)
    (e : Fin A → Equiv.Perm (Fin Q)) (key : Fin A → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y) :
    (slotPass h e key hinc).constant = 2 * K + 6 := by
  rw [slotPass,castPass_constant]
  rfl

end Cast

def highPass (i : I) (e : Fin (HighPrefixSize P Q i) → Equiv.Perm (Fin Q))
    (key : Fin (HighPrefixSize P Q i) → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y) :
    Pass (Volume I P Q G S) :=
  slotPass (highVolume i) e key hinc

def lowPass (i : I) (e : Fin (LowPrefixSize P Q G i) → Equiv.Perm (Fin Q))
    (key : Fin (LowPrefixSize P Q G i) → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y) :
    Pass (Volume I P Q G S) :=
  slotPass (lowVolume i) e key hinc

theorem highPass_encoded (i : I)
    (e : Fin (HighPrefixSize P Q i) → Equiv.Perm (Fin Q))
    (key : Fin (HighPrefixSize P Q i) → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y)
    (a : Addr I P Q G S) :
    (highPass i e key hinc).permutation (longLayout a) =
      longLayout (updateHigh i (e (highPrefix i a) (a.high i)) a) := by
  rw [← high_layout i a]
  rw [highPass,slotPass_encoded]
  rw [← high_layout i (updateHigh i (e (highPrefix i a) (a.high i)) a)]
  rw [highPrefix_updateHigh,highSuffix_updateHigh]
  simp only [updateHigh,Function.update_self]

theorem lowPass_encoded (i : I)
    (e : Fin (LowPrefixSize P Q G i) → Equiv.Perm (Fin Q))
    (key : Fin (LowPrefixSize P Q G i) → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y)
    (a : Addr I P Q G S) :
    (lowPass i e key hinc).permutation (longLayout a) =
      longLayout (updateLow i (e (lowPrefix i a) (a.low i)) a) := by
  rw [← low_layout i a]
  rw [lowPass,slotPass_encoded]
  rw [← low_layout i (updateLow i (e (lowPrefix i a) (a.low i)) a)]
  rw [lowPrefix_updateLow,lowSuffix_updateLow]
  simp only [updateLow,Function.update_self]

/-- This is an actual disk-stream pass with its supplied input file contents. -/
theorem highPass_execution {Value : Type*} [Inhabited Value] (i : I)
    (e : Fin (HighPrefixSize P Q i) → Equiv.Perm (Fin Q))
    (key : Fin (HighPrefixSize P Q i) → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y)
    (input : Fin (Volume I P Q G S) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, StepEvidence (highPass i e key hinc) input B hB cost ∧
      cost ≤ (2 * K + 6) * (Volume I P Q G S / B + 1) := by
  simpa only [highPass,slotPass_constant] using
    pass_correct (highPass i e key hinc) input B hB

theorem lowPass_execution {Value : Type*} [Inhabited Value] (i : I)
    (e : Fin (LowPrefixSize P Q G i) → Equiv.Perm (Fin Q))
    (key : Fin (LowPrefixSize P Q G i) → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y)
    (input : Fin (Volume I P Q G S) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, StepEvidence (lowPass i e key hinc) input B hB cost ∧
      cost ≤ (2 * K + 6) * (Volume I P Q G S / B + 1) := by
  simpa only [lowPass,slotPass_constant] using
    pass_correct (lowPass i e key hinc) input B hB

def highAdd (i : I) (offset : Fin (HighPrefixSize P Q i) → Fin Q) :
    Pass (Volume I P Q G S) :=
  highPass i (fun p => additionEquiv (offset p)) (fun p => additionRun (offset p))
    (fun p x y hxy hr => addition_increasing_in_run (offset p) x y hxy hr)

def lowAdd (i : I) (offset : Fin (LowPrefixSize P Q G i) → Fin Q) :
    Pass (Volume I P Q G S) :=
  lowPass i (fun p => additionEquiv (offset p)) (fun p => additionRun (offset p))
    (fun p x y hxy hr => addition_increasing_in_run (offset p) x y hxy hr)

theorem highAdd_encoded (i : I) (offset : Fin (HighPrefixSize P Q i) → Fin Q)
    (a : Addr I P Q G S) :
    (highAdd i offset).permutation (longLayout a) =
      longLayout (updateHigh i (a.high i + offset (highPrefix i a)) a) := by
  rw [highAdd]
  erw [highPass_encoded]
  rw [CoordinateScans.additionEquiv_apply_add]

theorem lowAdd_encoded (i : I) (offset : Fin (LowPrefixSize P Q G i) → Fin Q)
    (a : Addr I P Q G S) :
    (lowAdd i offset).permutation (longLayout a) =
      longLayout (updateLow i (a.low i + offset (lowPrefix i a)) a) := by
  rw [lowAdd]
  erw [lowPass_encoded]
  rw [CoordinateScans.additionEquiv_apply_add]

/-- Fixed integer multipliers retain a constant number of global streams. -/
def highMultiply {z : ℕ} (hz : 0 < z) (hQ : 0 < Q) (hc : z.Coprime Q) (i : I) :
    Pass (Volume I P Q G S) :=
  highPass i (fun _ => multiplicationEquiv hQ hc) (fun _ => multiplicationRun hz hQ)
    (fun _ x y hxy hr => multiplication_increasing_in_run hz hQ x y hxy hr)

def lowMultiply {z : ℕ} (hz : 0 < z) (hQ : 0 < Q) (hc : z.Coprime Q) (i : I) :
    Pass (Volume I P Q G S) :=
  lowPass i (fun _ => multiplicationEquiv hQ hc) (fun _ => multiplicationRun hz hQ)
    (fun _ x y hxy hr => multiplication_increasing_in_run hz hQ x y hxy hr)

def highInverseMultiply {z : ℕ} (hz : 0 < z) (hQ : 0 < Q)
    (hc : z.Coprime Q) (i : I) : Pass (Volume I P Q G S) :=
  highPass i (fun _ => (multiplicationEquiv hQ hc).symm)
    (fun _ x => multiplicationRun hz hQ ((multiplicationEquiv hQ hc).symm x))
    (fun _ => inverse_increasing_streams _ _
      (fun x y hxy hr => multiplication_increasing_in_run hz hQ x y hxy hr))

def lowInverseMultiply {z : ℕ} (hz : 0 < z) (hQ : 0 < Q)
    (hc : z.Coprime Q) (i : I) : Pass (Volume I P Q G S) :=
  lowPass i (fun _ => (multiplicationEquiv hQ hc).symm)
    (fun _ x => multiplicationRun hz hQ ((multiplicationEquiv hQ hc).symm x))
    (fun _ => inverse_increasing_streams _ _
      (fun x y hxy hr => multiplication_increasing_in_run hz hQ x y hxy hr))

/-- Reflections are two charged physical passes, not an arbitrary permutation. -/
def highReflection (i : I) (hQ : 0 < Q) (hG : 0 < G) (hS : 0 < S) :
    List (Pass (Volume I P Q G S)) :=
  ScanProgramLift.fieldReflections (HighPrefixSize P Q i) Q (HighSuffixSize Q G S i)
    hQ (mul_pos (pow_pos hQ _) (mul_pos hG (mul_pos (pow_pos hQ _) hS))) (highVolume i)

def lowReflection (i : I) (hQ : 0 < Q) (hS : 0 < S) :
    List (Pass (Volume I P Q G S)) :=
  ScanProgramLift.fieldReflections (LowPrefixSize P Q G i) Q (LowSuffixSize Q S i)
    hQ (mul_pos (pow_pos hQ _) hS) (lowVolume i)

theorem highReflection_encoded (i : I) (hQ : 0 < Q) (hG : 0 < G) (hS : 0 < S)
    (a : Addr I P Q G S) :
    destination (highReflection i hQ hG hS) (longLayout a) =
      longLayout (updateHigh i (a.high i).rev a) := by
  rw [← high_layout i a]
  rw [highReflection,ScanProgramLift.fieldReflections_destination,globalFieldEquiv_encoded]
  rw [← high_layout i (updateHigh i (a.high i).rev a)]
  rw [highPrefix_updateHigh,highSuffix_updateHigh]
  simp only [updateHigh,Function.update_self,Fin.revPerm_apply]

theorem lowReflection_encoded (i : I) (hQ : 0 < Q) (hS : 0 < S)
    (a : Addr I P Q G S) :
    destination (lowReflection i hQ hS) (longLayout a) =
      longLayout (updateLow i (a.low i).rev a) := by
  rw [← low_layout i a]
  rw [lowReflection,ScanProgramLift.fieldReflections_destination,globalFieldEquiv_encoded]
  rw [← low_layout i (updateLow i (a.low i).rev a)]
  rw [lowPrefix_updateLow,lowSuffix_updateLow]
  simp only [updateLow,Function.update_self,Fin.revPerm_apply]

section CrossAddition

/-- All of H occurs in the physical prefix of every low coordinate. -/
def highFromLowPrefix (i : I) (p : Fin (LowPrefixSize P Q G i)) : I → Fin Q :=
  subvectorEncode.symm (tripleEncode.symm (finProdFinEquiv.symm p).1).2.1

@[simp] theorem highFromLowPrefix_encoded (i : I) (a : Addr I P Q G S) :
    highFromLowPrefix i (lowPrefix i a) = a.high := by
  simp only [highFromLowPrefix,lowPrefix,Equiv.symm_apply_apply]

variable [NeZero Q]

def crossOffset (C : Matrix I I (Fin Q)) (i : I)
    (p : Fin (LowPrefixSize P Q G i)) : Fin Q :=
  C.mulVec (highFromLowPrefix i p) i

def crossPass (C : Matrix I I (Fin Q)) (i : I) : Pass (Volume I P Q G S) :=
  lowAdd i (crossOffset C i)

theorem crossPass_encoded (C : Matrix I I (Fin Q)) (i : I) (a : Addr I P Q G S) :
    (crossPass C i).permutation (longLayout a) =
      longLayout (updateLow i (a.low i + C.mulVec a.high i) a) := by
  rw [crossPass,lowAdd_encoded]
  simp only [crossOffset,highFromLowPrefix_encoded]

@[simp] theorem crossPass_constant (C : Matrix I I (Fin Q)) (i : I) :
    (crossPass (P := P) (G := G) (S := S) C i).constant = 10 := by
  unfold crossPass lowAdd lowPass
  erw [slotPass_constant]

variable {m : ℕ}

/-- The entire cross term B H uses only sequential scans, with zero children. -/
def crossProgram (C : Matrix (Fin m) (Fin m) (Fin Q)) :
    (n : ℕ) → n ≤ m → List (Pass (Volume (Fin m) P Q G S))
  | 0,_ => []
  | n+1,hn => crossPass C ⟨n,by omega⟩ :: crossProgram C n (by omega)

def crossApply (C : Matrix (Fin m) (Fin m) (Fin Q)) :
    (n : ℕ) → n ≤ m → Addr (Fin m) P Q G S → Addr (Fin m) P Q G S
  | 0,_,a => a
  | n+1,hn,a => crossApply C n (by omega)
      (updateLow ⟨n,by omega⟩ (a.low ⟨n,by omega⟩ + C.mulVec a.high ⟨n,by omega⟩) a)

theorem crossProgram_encoded (C : Matrix (Fin m) (Fin m) (Fin Q))
    (n : ℕ) (hn : n ≤ m) (a : Addr (Fin m) P Q G S) :
    destination (crossProgram C n hn) (longLayout a) = longLayout (crossApply C n hn a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [crossProgram,destination,Equiv.trans_apply,crossPass_encoded,crossApply]
    exact ih _ _

theorem crossApply_low (C : Matrix (Fin m) (Fin m) (Fin Q))
    (n : ℕ) (hn : n ≤ m) (a : Addr (Fin m) P Q G S) (k : Fin m) :
    (crossApply C n hn a).low k =
      if k.val < n then a.low k + C.mulVec a.high k else a.low k := by
  induction n generalizing a with
  | zero => simp [crossApply]
  | succ n ih =>
    rw [crossApply,ih]
    simp only [updateLow]
    by_cases hkn : k.val < n
    · have he : k.val ≠ n := Nat.ne_of_lt hkn
      simp [Function.update,Fin.ext_iff,hkn,he,show k.val < n+1 by omega]
    · by_cases he : k.val = n
      · have hk : k = (⟨n,Nat.lt_of_succ_le hn⟩ : Fin m) := Fin.ext he
        rw [hk]
        simp [Function.update,Fin.ext_iff]
      · simp [Function.update,Fin.ext_iff,hkn,he,show ¬ k.val < n+1 by omega]

theorem crossApply_spectators (C : Matrix (Fin m) (Fin m) (Fin Q))
    (n : ℕ) (hn : n ≤ m) (a : Addr (Fin m) P Q G S) :
    (crossApply C n hn a).prefixCoord = a.prefixCoord ∧
    (crossApply C n hn a).high = a.high ∧
    (crossApply C n hn a).gap = a.gap ∧
    (crossApply C n hn a).suffix = a.suffix := by
  induction n generalizing a with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ n ih => exact ih _ _

def crossAddress (C : Matrix (Fin m) (Fin m) (Fin Q))
    (a : Addr (Fin m) P Q G S) : Addr (Fin m) P Q G S :=
  ⟨a.prefixCoord,a.high,a.gap,a.low + C.mulVec a.high,a.suffix⟩

theorem crossApply_complete (C : Matrix (Fin m) (Fin m) (Fin Q))
    (a : Addr (Fin m) P Q G S) :
    crossApply C m (Nat.le_refl m) a = crossAddress C a := by
  have hs := crossApply_spectators C m (Nat.le_refl m) a
  have hl : (crossApply C m (Nat.le_refl m) a).low = a.low + C.mulVec a.high := by
    funext k
    simpa only [if_pos k.isLt,Pi.add_apply] using crossApply_low C m (Nat.le_refl m) a k
  cases h : crossApply C m (Nat.le_refl m) a
  simp only [h] at hs hl
  rcases hs with ⟨hp,hh,hg,hz⟩
  simp only [crossAddress,hp,hh,hg,hz,hl]

theorem crossProgram_complete (C : Matrix (Fin m) (Fin m) (Fin Q))
    (a : Addr (Fin m) P Q G S) :
    destination (crossProgram C m (Nat.le_refl m)) (longLayout a) =
      longLayout (crossAddress C a) := by
  rw [crossProgram_encoded,crossApply_complete]

theorem crossProgram_constant (C : Matrix (Fin m) (Fin m) (Fin Q))
    (n : ℕ) (hn : n ≤ m) :
    totalConstant (crossProgram (P := P) (G := G) (S := S) C n hn) = 10*n := by
  induction n with
  | zero => simp [crossProgram,totalConstant]
  | succ n ih =>
    simp only [crossProgram,totalConstant,List.map_cons,List.sum_cons,crossPass_constant]
    change 10 + totalConstant (crossProgram C n _) = _
    rw [ih]
    omega

theorem crossProgram_execution {Value : Type*} [Inhabited Value]
    (C : Matrix (Fin m) (Fin m) (Fin Q))
    (input : Fin (Volume (Fin m) P Q G S) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, Execution B hB (crossProgram C m (Nat.le_refl m)) input cost ∧
      cost ≤ (10*m) * (Volume (Fin m) P Q G S / B + 1) := by
  simpa only [crossProgram_constant] using
    program_correct (crossProgram C m (Nat.le_refl m)) input B hB

/-- Generic composition with the two already-implemented diagonal-block scans.
The low block is computed first, so the cross term still sees the original H.
The hypotheses are exact meanings of supplied concrete pass lists, not scan
existence or scan-cost axioms. -/
theorem lowerBlockProgram_complete
    (A B C : Matrix (Fin m) (Fin m) (Fin Q))
    (high low : List (Pass (Volume (Fin m) P Q G S)))
    (hh : ∀ a : Addr (Fin m) P Q G S,
      destination high (longLayout a) =
        longLayout ⟨a.prefixCoord,A.mulVec a.high,a.gap,a.low,a.suffix⟩)
    (hl : ∀ a : Addr (Fin m) P Q G S,
      destination low (longLayout a) =
        longLayout ⟨a.prefixCoord,a.high,a.gap,C.mulVec a.low,a.suffix⟩)
    (a : Addr (Fin m) P Q G S) :
    destination (low ++ crossProgram B m (Nat.le_refl m) ++ high) (longLayout a) =
      longLayout ⟨a.prefixCoord,A.mulVec a.high,a.gap,
        C.mulVec a.low + B.mulVec a.high,a.suffix⟩ := by
  rw [ScanProgramLift.destination_append,ScanProgramLift.destination_append,
    Equiv.trans_apply,Equiv.trans_apply,hl,crossProgram_complete,hh]
  rfl

theorem lowerBlockProgram_execution {Value : Type*} [Inhabited Value]
    (B : Matrix (Fin m) (Fin m) (Fin Q))
    (high low : List (Pass (Volume (Fin m) P Q G S)))
    (input : Fin (Volume (Fin m) P Q G S) → Value) (block : ℕ) (hblock : 0 < block) :
    ∃ cost, Execution block hblock
      (low ++ crossProgram B m (Nat.le_refl m) ++ high) input cost ∧
      cost ≤ (totalConstant low + 10*m + totalConstant high) *
        (Volume (Fin m) P Q G S / block + 1) := by
  have happ {V : ℕ} (xs ys : List (Pass V)) :
      totalConstant (xs ++ ys) = totalConstant xs + totalConstant ys := by
    simp only [totalConstant,List.map_append,List.sum_append]
  obtain ⟨cost,he,hc⟩ :=
    program_correct (low ++ crossProgram B m (Nat.le_refl m) ++ high) input block hblock
  rw [happ,happ,crossProgram_constant] at hc
  exact ⟨cost,he,hc⟩

end CrossAddition

end
end CSL.Construction.PartialSwapScan


