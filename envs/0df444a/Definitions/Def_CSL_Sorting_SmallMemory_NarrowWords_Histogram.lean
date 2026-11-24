-- Prove2me | Definitions.Def_CSL_Sorting_SmallMemory_NarrowWords_Histogram
-- name    : CSL_Sorting_SmallMemory_NarrowWords_Histogram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:26:49.011001+00:00
-- url     : https://prove2.me/theorems/7d4c3662-a52d-41f2-97a3-f409e4510e50
-- title:
--   Coded sorting library: Sorting / SmallMemory / NarrowWords / Histogram
-- statement:
--   Module `CodedSorting.Sorting.SmallMemory.NarrowWords.Histogram` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Actual histogram initialization in the public-unrolled model
--
--   Every disk read and write below is an existing two-resident-word command.
--   The input addresses and the zeroing addresses are publicly expanded in the
--   read-only program. Its public program position is not included in `State`;
--   this is not a fixed-size, word-PC implementation of that schedule.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.SmallMemory.NarrowWords.Histogram

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_SmallMemory_NarrowWords_OutputSearch

section Histogram
/-!
# Actual histogram initialization in the public-unrolled model

Every disk read and write below is an existing two-resident-word command.
The input addresses and the zeroing addresses are publicly expanded in the
read-only program. Its public program position is not included in `State`;
this is not a fixed-size, word-PC implementation of that schedule.
-/

set_option autoImplicit false
namespace CSL.TwoWordGeneralHistogram
open TwoWordPhysicalAddresses TwoWordGeneralCounter

def inputBase (w digits : ℕ) : ℕ := 3 + digits * 2^w

theorem address_below (w digits j : ℕ) (key : Word w) (hj : j < digits) :
    address w j key < 2 + digits * 2^w := by
  have hm := Nat.mul_le_mul_right (2^w) (show j+1 ≤ digits by omega)
  have hk := key.isLt
  unfold address
  rw [Nat.add_mul] at hm
  omega

theorem address_key_injective (w i j : ℕ) (x y : Word w)
    (he : address w i x = address w j y) : x = y := by
  have he' : i * 2^w + x.val = j * 2^w + y.val := by
    unfold address at he
    omega
  have hm := congrArg (fun a => a % 2^w) he'
  apply Fin.ext
  simpa [Nat.add_mod, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] using hm

def zeroCode (w start : ℕ) : ℕ → List (Command (Word w))
  | 0 => []
  | count+1 => [.localOp (fun r => (0,r.2)), .writeLeft start] ++
      zeroCode w (start+1) count

theorem zero_cost (w start count : ℕ) : transfers (zeroCode w start count) = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [zeroCode, transfers_append, ih]
    simp [transfers, cost, Nat.add_comm]

theorem zero_disk (w start count : ℕ) (s : State (Word w)) (a : ℕ) :
    (execute (zeroCode w start count) s).disk a =
      if start ≤ a ∧ a < start+count then 0 else s.disk a := by
  induction count generalizing start s with
  | zero =>
    simp only [zeroCode, execute, Nat.add_zero]
    rw [if_neg (by omega)]
  | succ count ih =>
    rw [zeroCode, execute_append, ih]
    simp only [execute, step]
    by_cases he : a = start
    · subst a
      simp
    · by_cases hr : start+1 ≤ a ∧ a < start+1+count
      · have hr' : start ≤ a ∧ a < start+(count+1) := by omega
        simp [hr, hr']
      · have hr' : ¬(start ≤ a ∧ a < start+(count+1)) := by omega
        simp [hr, hr', Function.update_of_ne he]
        try (intro h1 h2; exact absurd ⟨by omega, h2⟩ hr)

theorem initialized_value (w digits : ℕ) (s : State (Word w)) (key : Word w) :
    value w key 0 digits (execute (zeroCode w 2 (digits*2^w)) s).disk = 0 := by
  apply (value_zero_iff w key 0 digits _).2
  intro j hj
  have hlo := address_large w j key
  have hhi := address_below w digits j key hj
  simp only [Nat.zero_add, zero_disk]
  simp [hlo, hhi]

theorem initialized_frame (w digits : ℕ) (s : State (Word w)) (a : ℕ)
    (ha : 2 + digits*2^w ≤ a) :
    (execute (zeroCode w 2 (digits*2^w)) s).disk a = s.disk a := by
  rw [zero_disk]
  rw [if_neg (by omega)]

def one (w : ℕ) (hw : 0 < w) : Word w := ⟨1, Nat.one_lt_two_pow hw.ne'⟩

/-- Read the input key, spill it, and initialize the carry with charged writes. -/
def setKeyCode (w : ℕ) (hw : 0 < w) (input : ℕ) : List (Command (Word w)) :=
  [.readLeft input, .writeLeft 0, .localOp (fun r => (one w hw,r.2)), .writeLeft 1]

def setKey (w : ℕ) (hw : 0 < w) (input : ℕ) (s : State (Word w)) : State (Word w) :=
  execute (setKeyCode w hw input) s

theorem setKey_cost (w : ℕ) (hw : 0 < w) (input : ℕ) :
    transfers (setKeyCode w hw input) = 3 := rfl

theorem setKey_disk (w : ℕ) (hw : 0 < w) (input : ℕ) (s : State (Word w)) :
    (setKey w hw input s).disk =
      Function.update (Function.update s.disk 0 (s.disk input)) 1 (one w hw) := rfl

@[simp] theorem setKey_key (w : ℕ) (hw : 0 < w) (input : ℕ) (s : State (Word w)) :
    (setKey w hw input s).disk 0 = s.disk input := by
  rw [setKey_disk]
  simp

@[simp] theorem setKey_carry (w : ℕ) (hw : 0 < w) (input : ℕ) (s : State (Word w)) :
    (setKey w hw input s).disk 1 = one w hw := by
  rw [setKey_disk]
  simp

theorem setKey_frame (w : ℕ) (hw : 0 < w) (input : ℕ) (s : State (Word w))
    (a : ℕ) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    (setKey w hw input s).disk a = s.disk a := by
  rw [setKey_disk]
  simp [Function.update_of_ne, h0, h1]

theorem setKey_value (w : ℕ) (hw : 0 < w) (input digits : ℕ)
    (s : State (Word w)) (key : Word w) :
    value w key 0 digits (setKey w hw input s).disk = value w key 0 digits s.disk := by
  apply value_eq
  intro j hj
  have ha := address_large w (0+j) key
  exact setKey_frame w hw input s _ (by omega) (by omega)

end CSL.TwoWordGeneralHistogram
end Histogram

section HistogramScan
/-! Actual, publicly unrolled input scan. The code depends on the input
length and fixed addresses, never on the input values. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CSL.TwoWordGeneralHistogram
open TwoWordPhysicalAddresses TwoWordGeneralCounter

def incrementCode (w : ℕ) (hw : 0 < w) (digits input : ℕ) :
    List (Command (Word w)) :=
  setKeyCode w hw input ++ code w 0 (addDigit w hw) digits

def increment (w : ℕ) (hw : 0 < w) (digits input : ℕ)
    (s : State (Word w)) : State (Word w) :=
  effect w 0 (addDigit w hw) digits (setKey w hw input s)

theorem execute_increment (w : ℕ) (hw : 0 < w) (digits input : ℕ)
    (s : State (Word w)) : execute (incrementCode w hw digits input) s =
      increment w hw digits input s := by
  rw [incrementCode, execute_append, execute_code]
  rfl

theorem increment_cost (w : ℕ) (hw : 0 < w) (digits input : ℕ) :
    transfers (incrementCode w hw digits input) = 3 + 6*digits := by
  rw [incrementCode, transfers_append, setKey_cost, code_cost]

theorem increment_frame (w : ℕ) (hw : 0 < w) (digits input : ℕ)
    (s : State (Word w)) (a : ℕ) (ha : 2 + digits*2^w ≤ a) :
    (increment w hw digits input s).disk a = s.disk a := by
  unfold increment
  rw [effect_frame]
  · exact setKey_frame w hw input s a (by omega) (by omega)
  · omega
  · intro j hj
    have hhi := address_below w digits j ((setKey w hw input s).disk 0) hj
    simpa only [Nat.zero_add] using (show a ≠ address w j
      ((setKey w hw input s).disk 0) by omega)

theorem increment_value (w : ℕ) (hw : 0 < w) (digits input : ℕ)
    (s : State (Word w))
    (hcap : value w (s.disk input) 0 digits s.disk + 1 < (2^w)^digits)
    (key : Word w) :
    value w key 0 digits (increment w hw digits input s).disk =
      value w key 0 digits s.disk + if key = s.disk input then 1 else 0 := by
  by_cases he : key = s.disk input
  · subst key
    have hcap' : value w ((setKey w hw input s).disk 0) 0 digits
        (setKey w hw input s).disk + ((setKey w hw input s).disk 1).val < (2^w)^digits := by
      simpa only [setKey_key, setKey_carry, setKey_value, one] using hcap
    have h := (add_no_overflow w hw 0 digits (setKey w hw input s) hcap').1
    simpa only [increment, setKey_key, setKey_carry, setKey_value, one,
      ↓reduceIte] using h
  · rw [if_neg he, Nat.add_zero]
    calc
      value w key 0 digits (increment w hw digits input s).disk =
          value w key 0 digits (setKey w hw input s).disk := by
        apply value_eq
        intro j hj
        apply effect_frame
        · have ha := address_large w (0+j) key
          omega
        · intro i hi
          rw [setKey_key]
          exact fun h => he (address_key_injective w (0+j) (0+i) key (s.disk input) h)
      _ = value w key 0 digits s.disk := setKey_value w hw input digits s key

def File {w : ℕ} (disk : ℕ → Word w) (base : ℕ) (xs : List (Word w)) : Prop :=
  ∀ i (hi : i < xs.length), disk (base+i) = xs[i]

def Histogram {w : ℕ} (digits : ℕ) (disk : ℕ → Word w) (xs : List (Word w)) : Prop :=
  ∀ key, value w key 0 digits disk = xs.count key

def scanCode (w : ℕ) (hw : 0 < w) (digits base : ℕ) :
    ℕ → List (Command (Word w))
  | 0 => []
  | n+1 => incrementCode w hw digits base ++ scanCode w hw digits (base+1) n

theorem scan_cost (w : ℕ) (hw : 0 < w) (digits base n : ℕ) :
    transfers (scanCode w hw digits base n) = (3+6*digits)*n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    rw [scanCode, transfers_append, increment_cost, ih]
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- The histogram and the unchanged input region describe the same execution. -/
theorem scan_correct (w : ℕ) (hw : 0 < w) (digits base : ℕ)
    (s : State (Word w)) (xs ys : List (Word w))
    (hbase : 2 + digits*2^w ≤ base) (hin : File s.disk base xs)
    (hhist : Histogram digits s.disk ys)
    (hcap : ys.length + xs.length < (2^w)^digits) :
    Histogram digits (execute (scanCode w hw digits base xs.length) s).disk (ys ++ xs) ∧
    ∀ a, 2 + digits*2^w ≤ a →
      (execute (scanCode w hw digits base xs.length) s).disk a = s.disk a := by
  induction xs generalizing base s ys with
  | nil =>
    simpa [scanCode, execute, Histogram] using
      (show Histogram digits s.disk ys ∧ ∀ a, 2+digits*2^w ≤ a → s.disk a = s.disk a
        from ⟨hhist, fun _ _ => rfl⟩)
  | cons x xs ih =>
    have hx : s.disk base = x := by first
      | exact hin 0 (by simp)
      | (have h_sx := hin 0 (by simp); simp  at h_sx ⊢; exact h_sx)
      | (have h_sx := hin 0 (by simp); simp  at h_sx; exact h_sx)
      | (simp ; exact hin 0 (by simp))
    have hinc : value w (s.disk base) 0 digits s.disk + 1 < (2^w)^digits := by
      rw [hhist]
      have hc : ys.count (s.disk base) ≤ ys.length := List.count_le_length
      simp only [List.length_cons] at hcap
      omega
    let mid := increment w hw digits base s
    have hmid : Histogram digits mid.disk (ys ++ [x]) := by
      intro key
      try dsimp only [mid]
      rw [increment_value w hw digits base s hinc, hhist, hx]
      rw [List.count_append]
      by_cases hk : key = x
      · subst key
        simp
      · simp [List.count_cons, hk, Ne.symm hk]
    have hfile : File mid.disk (base+1) xs := by
      intro i hi
      have hf := increment_frame w hw digits base s (base+1+i) (by omega)
      have hs := hin (i+1) (by simp; omega)
      have hs' : s.disk (base+1+i) = xs[i] := by
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using hs
      exact hf.trans hs'
    have hcap' : (ys ++ [x]).length + xs.length < (2^w)^digits := by
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm 1 xs.length] using hcap
    obtain ⟨ht, hf⟩ := ih (base+1) mid (ys ++ [x]) (by omega) hfile hmid hcap'
    simp only [List.length_cons, scanCode, execute_append, execute_increment]
    constructor
    · simpa [List.append_assoc] using ht
    · intro a ha
      exact (hf a ha).trans (increment_frame w hw digits base s a ha)

def histogramCode (w : ℕ) (hw : 0 < w) (digits n : ℕ) :
    List (Command (Word w)) :=
  zeroCode w 2 (digits*2^w) ++ scanCode w hw digits (inputBase w digits) n

theorem histogram_cost (w : ℕ) (hw : 0 < w) (digits n : ℕ) :
    transfers (histogramCode w hw digits n) = digits*2^w + (3+6*digits)*n := by
  rw [histogramCode, transfers_append, zero_cost, scan_cost]

theorem histogram_correct (w : ℕ) (hw : 0 < w) (digits : ℕ)
    (s : State (Word w)) (xs : List (Word w))
    (hin : File s.disk (inputBase w digits) xs)
    (hcap : xs.length < (2^w)^digits) :
    Histogram digits (execute (histogramCode w hw digits xs.length) s).disk xs ∧
    ∀ a, 2 + digits*2^w ≤ a →
      (execute (histogramCode w hw digits xs.length) s).disk a = s.disk a := by
  let mid := execute (zeroCode w 2 (digits*2^w)) s
  have hfile : File mid.disk (inputBase w digits) xs := by
    intro i hi
    rw [initialized_frame]
    · exact hin i hi
    · unfold inputBase
      omega
  have hhist : Histogram digits mid.disk [] := by
    intro key
    simpa only [List.count_nil] using initialized_value w digits s key
  obtain ⟨ht, hf⟩ := scan_correct w hw digits (inputBase w digits) mid xs []
    (by unfold inputBase; omega) hfile hhist (by simpa using hcap)
  rw [histogramCode, execute_append]
  constructor
  · simpa using ht
  · intro a ha
    exact (hf a ha).trans (initialized_frame w digits s a ha)

end CSL.TwoWordGeneralHistogram
end HistogramScan

section OutputEmit
/-!
# Actual output write and spilled-counter decrement

The output index is a public command field. The key is read from disk cell 0,
written to the designated output cell, and retained in cell 0. The borrow is
explicitly initialized by a charged write; all counter digits are then updated
by the existing six-I/O digit macro. No input value or correctness witness
selects the emitted program.
-/

set_option autoImplicit false
namespace CSL.TwoWordGeneralOutputEmit
open TwoWordPhysicalAddresses TwoWordGeneralCounter TwoWordGeneralHistogram

def putCode (w : ℕ) (hw : 0 < w) (digits i : ℕ) : List (Command (Word w)) :=
  [.readLeft 0, .writeLeft (inputBase w digits+i),
   .localOp (fun r => (one w hw,r.2)), .writeLeft 1]

def putState (w : ℕ) (hw : 0 < w) (digits i : ℕ)
    (s : State (Word w)) : State (Word w) :=
  ⟨one w hw,s.right,
    Function.update (Function.update s.disk (inputBase w digits+i) (s.disk 0))
      1 (one w hw)⟩

theorem execute_put (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w)) :
    execute (putCode w hw digits i) s = putState w hw digits i s := rfl

theorem put_cost (w : ℕ) (hw : 0 < w) (digits i : ℕ) :
    transfers (putCode w hw digits i) = 3 := rfl

theorem put_frame (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w))
    (a : ℕ) (h1 : a ≠ 1) (hout : a ≠ inputBase w digits+i) :
    (putState w hw digits i s).disk a = s.disk a := by
  simp [putState,Function.update_of_ne h1,Function.update_of_ne hout]

@[simp] theorem put_key (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w)) :
    (putState w hw digits i s).disk 0 = s.disk 0 := by
  apply put_frame
  · omega
  · unfold inputBase
    omega

@[simp] theorem put_carry (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w)) :
    (putState w hw digits i s).disk 1 = one w hw := by
  simp [putState]

theorem put_output (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w)) :
    (putState w hw digits i s).disk (inputBase w digits+i) = s.disk 0 := by
  have h : inputBase w digits+i ≠ 1 := by unfold inputBase; omega
  simp [putState,Function.update_of_ne h]

theorem put_value (w : ℕ) (hw : 0 < w) (digits i : ℕ)
    (s : State (Word w)) (key : Word w) :
    value w key 0 digits (putState w hw digits i s).disk =
      value w key 0 digits s.disk := by
  apply value_eq
  intro j hj
  have hlo := address_large w (0+j) key
  have hhi := address_below w digits j key hj
  apply put_frame
  · omega
  · unfold inputBase
    simp only [Nat.zero_add]
    omega

def emitCode (w : ℕ) (hw : 0 < w) (digits i : ℕ) : List (Command (Word w)) :=
  putCode w hw digits i ++ code w 0 (subDigit w hw) digits

def emit (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w)) : State (Word w) :=
  effect w 0 (subDigit w hw) digits (putState w hw digits i s)

theorem execute_emit (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w)) :
    execute (emitCode w hw digits i) s = emit w hw digits i s := by
  rw [emitCode,execute_append,execute_put,execute_code]
  rfl

theorem emit_cost (w : ℕ) (hw : 0 < w) (digits i : ℕ) :
    transfers (emitCode w hw digits i) = 3+6*digits := by
  rw [emitCode,transfers_append,put_cost,code_cost]

theorem emit_key (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w)) :
    (emit w hw digits i s).disk 0 = s.disk 0 := by
  rw [emit,effect_key,put_key]

theorem emit_output (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w)) :
    (emit w hw digits i s).disk (inputBase w digits+i) = s.disk 0 := by
  unfold emit
  rw [effect_frame]
  · exact put_output w hw digits i s
  · unfold inputBase
    omega
  · intro j hj
    have hhi := address_below w digits j ((putState w hw digits i s).disk 0) hj
    simp only [Nat.zero_add]
    unfold inputBase
    omega

theorem emit_frame (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w))
    (a : ℕ) (ha : inputBase w digits ≤ a) (hout : a ≠ inputBase w digits+i) :
    (emit w hw digits i s).disk a = s.disk a := by
  have hbase : 3+digits*2^w ≤ a := ha
  unfold emit
  rw [effect_frame]
  · exact put_frame w hw digits i s a (by omega) hout
  · omega
  · intro j hj
    have hhi := address_below w digits j ((putState w hw digits i s).disk 0) hj
    simp only [Nat.zero_add]
    omega

theorem emit_selected (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w))
    (hpos : 0 < value w (s.disk 0) 0 digits s.disk) :
    value w (s.disk 0) 0 digits (emit w hw digits i s).disk =
      value w (s.disk 0) 0 digits s.disk - 1 := by
  have hsmall : ((putState w hw digits i s).disk 1).val ≤
      value w ((putState w hw digits i s).disk 0) 0 digits
        (putState w hw digits i s).disk := by
    first
    | exact hpos
    | (have h_sx := hpos; simp only [put_carry,put_key,put_value,one] at h_sx ⊢; exact h_sx)
    | (have h_sx := hpos; simp only [put_carry,put_key,put_value,one] at h_sx; exact h_sx)
    | (simp only [put_carry,put_key,put_value,one]; exact hpos)
  have h := (sub_no_underflow w hw 0 digits (putState w hw digits i s) hsmall).1
  simpa only [emit,put_key,put_carry,put_value,one] using h

theorem emit_other (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w))
    (key : Word w) (hne : key ≠ s.disk 0) :
    value w key 0 digits (emit w hw digits i s).disk =
      value w key 0 digits s.disk := by
  calc
    value w key 0 digits (emit w hw digits i s).disk =
        value w key 0 digits (putState w hw digits i s).disk := by
      apply value_eq
      intro j hj
      apply effect_frame
      · have h := address_large w (0+j) key
        omega
      · intro k hk
        rw [put_key]
        exact fun h => hne (address_key_injective w (0+j) (0+k) key (s.disk 0) h)
    _ = value w key 0 digits s.disk := put_value w hw digits i s key

/-- Exact update of the entire count function, for the actual emitted state. -/
theorem emit_counts (w : ℕ) (hw : 0 < w) (digits i : ℕ) (s : State (Word w))
    (hpos : 0 < value w (s.disk 0) 0 digits s.disk) :
    (fun key => value w key 0 digits (emit w hw digits i s).disk) =
      Function.update (fun key => value w key 0 digits s.disk) (s.disk 0)
        (value w (s.disk 0) 0 digits s.disk - 1) := by
  funext key
  by_cases hkey : key = s.disk 0
  · subst key
    simpa using emit_selected w hw digits i s hpos
  · simpa [Function.update_of_ne hkey] using emit_other w hw digits i s key hkey

end CSL.TwoWordGeneralOutputEmit
end OutputEmit


