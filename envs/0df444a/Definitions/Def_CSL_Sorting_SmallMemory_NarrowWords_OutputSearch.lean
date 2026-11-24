-- Prove2me | Definitions.Def_CSL_Sorting_SmallMemory_NarrowWords_OutputSearch
-- name    : CSL_Sorting_SmallMemory_NarrowWords_OutputSearch
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:13:24.932924+00:00
-- url     : https://prove2.me/theorems/34299ffa-fffb-4e30-9336-232bf7c0c4a1
-- title:
--   Coded sorting library: Sorting / SmallMemory / NarrowWords / OutputSearch
-- statement:
--   Module `CodedSorting.Sorting.SmallMemory.NarrowWords.OutputSearch` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Spilled digits for a general-word counting sorter
--
--   This module uses exactly the existing natural-addressed two-word command
--   semantics. Cell 0 holds a one-word key, cell 1 holds a carry, and digit j of
--   the key's counter is at 2 + j * 2^w + key. A digit's region is a fixed field
--   of its command; no multi-word indirect-address primitive is introduced.
--
--   This is a counter component, not a sorting endpoint. In particular it does
--   not claim that a public N-stage output schedule has a word-sized program
--   counter. Such an extension must explicitly retain the public-unrolled
--   program convention of TwoWordRadixPreparedBuild.Stage.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.SmallMemory.NarrowWords.OutputSearch

import Definitions.Def_CSL_Compat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_CSL_Sorting_SmallMemory_Radix_Initialize

section Counter
/-!
# Spilled digits for a general-word counting sorter

This module uses exactly the existing natural-addressed two-word command
semantics. Cell 0 holds a one-word key, cell 1 holds a carry, and digit j of
the key's counter is at 2 + j * 2^w + key. A digit's region is a fixed field
of its command; no multi-word indirect-address primitive is introduced.

This is a counter component, not a sorting endpoint. In particular it does
not claim that a public N-stage output schedule has a word-sized program
counter. Such an extension must explicitly retain the public-unrolled
program convention of TwoWordRadixPreparedBuild.Stage.
-/

set_option autoImplicit false
namespace CSL.TwoWordGeneralCounter
open TwoWordPhysicalAddresses

abbrev Word (w : ℕ) := Fin (2^w)

def address (w digit : ℕ) (key : Word w) : ℕ := 2 + digit * 2^w + key.val

theorem address_large (w digit : ℕ) (key : Word w) : 2 ≤ address w digit key := by
  unfold address
  omega

theorem address_ne (w i j : ℕ) (key : Word w) (h : i ≠ j) :
    address w i key ≠ address w j key := by
  have hb : 0 < 2^w := by positivity
  unfold address
  intro he
  have hm : i * 2^w = j * 2^w := by omega
  exact h (Nat.eq_of_mul_eq_mul_right hb hm)

/-- One carry and one digit are the entire resident arithmetic operand. -/
def addDigit (w : ℕ) (hw : 0 < w) (r : Word w × Word w) : Word w × Word w :=
  let b := 2^w
  let total := r.1.val + r.2.val
  (⟨if total < b then 0 else 1, by
      have hb : 1 < 2^w := Nat.one_lt_two_pow hw.ne'
      split <;> omega⟩,
   ⟨total % b, Nat.mod_lt _ (by positivity)⟩)

theorem addDigit_value (w : ℕ) (hw : 0 < w) (r : Word w × Word w) :
    (addDigit w hw r).2.val + 2^w * (addDigit w hw r).1.val =
      r.1.val + r.2.val := by
  have h1 := r.1.isLt
  have h2 := r.2.isLt
  try dsimp [addDigit]
  split
  · rename_i h
    simp [Nat.mod_eq_of_lt h]
  · rename_i h
    have hq : (r.1.val + r.2.val) / 2^w = 1 :=
      (Nat.div_eq_iff (by positivity)).2 (by omega)
    have he := Nat.mod_add_div (r.1.val + r.2.val) (2^w)
    simpa only [hq, Nat.mul_one] using he

/-- The pointer and carry are genuinely reloaded and spilled. Six I/Os. -/
def digitCode (w digit : ℕ) (f : Word w × Word w → Word w × Word w) :
    List (Command (Word w)) :=
  [.readLeft 0,
   .readRightAt (fun r => address w digit r.1),
   .readLeft 1,
   .localOp f,
   .writeLeft 1,
   .readLeft 0,
   .writeRight (fun r => address w digit r.1)]

def digitEffect (w digit : ℕ) (f : Word w × Word w → Word w × Word w)
    (s : State (Word w)) : State (Word w) :=
  let key := s.disk 0
  let target := address w digit key
  let result := f (s.disk 1, s.disk target)
  ⟨key, result.2, Function.update (Function.update s.disk 1 result.1) target result.2⟩

theorem execute_digit (w digit : ℕ) (f : Word w × Word w → Word w × Word w)
    (s : State (Word w)) : execute (digitCode w digit f) s = digitEffect w digit f s := by
  have h0 : (0 : ℕ) ≠ address w digit (s.disk 0) := by
    have := address_large w digit (s.disk 0)
    omega
  simp [digitCode, execute, step, digitEffect, Function.update_apply, h0]

theorem digit_cost (w digit : ℕ) (f : Word w × Word w → Word w × Word w) :
    transfers (digitCode w digit f) = 6 := rfl

theorem digit_key (w digit : ℕ) (f : Word w × Word w → Word w × Word w)
    (s : State (Word w)) : (digitEffect w digit f s).disk 0 = s.disk 0 := by
  have h0 : (0 : ℕ) ≠ address w digit (s.disk 0) := by
    have := address_large w digit (s.disk 0)
    omega
  simp [digitEffect, Function.update_apply, h0]

theorem digit_carry (w digit : ℕ) (f : Word w × Word w → Word w × Word w)
    (s : State (Word w)) :
    (digitEffect w digit f s).disk 1 = (f (s.disk 1, s.disk (address w digit (s.disk 0)))).1 := by
  have h1 : (1 : ℕ) ≠ address w digit (s.disk 0) := by
    have := address_large w digit (s.disk 0)
    omega
  simp [digitEffect, Function.update_apply, h1]

theorem digit_value (w digit : ℕ) (f : Word w × Word w → Word w × Word w)
    (s : State (Word w)) :
    (digitEffect w digit f s).disk (address w digit (s.disk 0)) =
      (f (s.disk 1, s.disk (address w digit (s.disk 0)))).2 := by
  simp [digitEffect]

theorem digit_frame (w digit : ℕ) (f : Word w × Word w → Word w × Word w)
    (s : State (Word w)) (a : ℕ) (hc : a ≠ 1)
    (ht : a ≠ address w digit (s.disk 0)) :
    (digitEffect w digit f s).disk a = s.disk a := by
  simp [digitEffect, Function.update_apply, hc, ht]

def code (w start : ℕ) (f : Word w × Word w → Word w × Word w) :
    ℕ → List (Command (Word w))
  | 0 => []
  | count + 1 => digitCode w start f ++ code w (start+1) f count

def effect (w start : ℕ) (f : Word w × Word w → Word w × Word w) :
    ℕ → State (Word w) → State (Word w)
  | 0, s => s
  | count+1, s => effect w (start+1) f count (digitEffect w start f s)

theorem execute_append {W : Type*} [DecidableEq W]
    (a b : List (Command W)) (s : State W) :
    execute (a ++ b) s = execute b (execute a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons a rest ih => exact ih (step a s)

theorem transfers_append {W : Type*} (a b : List (Command W)) :
    transfers (a ++ b) = transfers a + transfers b := by
  induction a with
  | nil => simp [transfers]
  | cons a rest ih => simp only [List.cons_append, transfers, ih, Nat.add_assoc]

theorem execute_code (w start count : ℕ) (f : Word w × Word w → Word w × Word w)
    (s : State (Word w)) : execute (code w start f count) s = effect w start f count s := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih => rw [code, execute_append, execute_digit, ih]; rfl

theorem code_cost (w start count : ℕ) (f : Word w × Word w → Word w × Word w) :
    transfers (code w start f count) = 6 * count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => rw [code, transfers_append, digit_cost, ih]; omega

theorem effect_key (w start count : ℕ) (f : Word w × Word w → Word w × Word w)
    (s : State (Word w)) : (effect w start f count s).disk 0 = s.disk 0 := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih => rw [effect, ih, digit_key]

theorem effect_frame (w start count : ℕ) (f : Word w × Word w → Word w × Word w)
    (s : State (Word w)) (a : ℕ) (hc : a ≠ 1)
    (ht : ∀ j < count, a ≠ address w (start+j) (s.disk 0)) :
    (effect w start f count s).disk a = s.disk a := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih =>
    rw [effect, ih]
    · exact digit_frame w start f s a hc (by simpa using ht 0 (by omega))
    · intro j hj
      rw [digit_key]
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using ht (j+1) (by omega)

def value (w : ℕ) (key : Word w) (start : ℕ) : ℕ → (ℕ → Word w) → ℕ
  | 0, _ => 0
  | count+1, disk => (disk (address w start key)).val +
      2^w * value w key (start+1) count disk

theorem value_bound (w : ℕ) (key : Word w) (start count : ℕ) (disk : ℕ → Word w) :
    value w key start count disk < (2^w)^count := by
  induction count generalizing start with
  | zero => simp [value]
  | succ count ih =>
    have hv := (disk (address w start key)).isLt
    have ht := ih (start+1)
    have hb : 0 < 2^w := by positivity
    rw [value, pow_succ]
    nlinarith

theorem value_eq (w : ℕ) (key : Word w) (start count : ℕ) (a b : ℕ → Word w)
    (h : ∀ j < count, a (address w (start+j) key) = b (address w (start+j) key)) :
    value w key start count a = value w key start count b := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [value, value, show a (address w start key) = b (address w start key) from
      by simpa using h 0 (by omega), ih]
    intro j hj
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using h (j+1) (by omega)

theorem value_zero_iff (w : ℕ) (key : Word w) (start count : ℕ) (disk : ℕ → Word w) :
    value w key start count disk = 0 ↔
      ∀ j < count, disk (address w (start+j) key) = 0 := by
  induction count generalizing start with
  | zero => simp [value]
  | succ count ih =>
    have hb : (2^w : ℕ) ≠ 0 := by positivity
    rw [value, Nat.add_eq_zero_iff, Nat.mul_eq_zero, or_iff_right hb, ih]
    constructor
    · rintro ⟨hh, ht⟩ j hj
      cases j with
      | zero => simpa using (Fin.ext hh : disk (address w start key) = 0)
      | succ j => simpa [Nat.add_assoc, Nat.add_comm 1 j] using ht j (by omega)
    · intro h
      constructor
      · exact congrArg Fin.val (by simpa using h 0 (by omega))
      · intro j hj
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using h (j+1) (by omega)

theorem value_digit_later (w start count digit : ℕ)
    (f : Word w × Word w → Word w × Word w) (s : State (Word w))
    (hl : digit < start) :
    value w (s.disk 0) start count (digitEffect w digit f s).disk =
      value w (s.disk 0) start count s.disk := by
  apply value_eq
  intro j hj
  apply digit_frame
  · have := address_large w (start+j) (s.disk 0)
    omega
  · exact address_ne w (start+j) digit (s.disk 0) (by omega)

/-- Base-b carry conservation for the *actual* six-I/O-per-digit execution. -/
theorem add_value (w : ℕ) (hw : 0 < w) (start count : ℕ) (s : State (Word w)) :
    value w (s.disk 0) start count (effect w start (addDigit w hw) count s).disk +
        (2^w)^count * ((effect w start (addDigit w hw) count s).disk 1).val =
      value w (s.disk 0) start count s.disk + (s.disk 1).val := by
  induction count generalizing start s with
  | zero => simp [effect, value]
  | succ count ih =>
    let mid := digitEffect w start (addDigit w hw) s
    have hkey : mid.disk 0 = s.disk 0 := digit_key _ _ _ _
    have ht := ih (start+1) mid
    rw [hkey, value_digit_later w (start+1) count start _ s (by omega)] at ht
    have hfirst : (effect w (start+1) (addDigit w hw) count mid).disk
        (address w start (s.disk 0)) = mid.disk (address w start (s.disk 0)) := by
      apply effect_frame
      · have := address_large w start (s.disk 0); omega
      · intro j hj
        rw [hkey]
        exact address_ne w start (start+1+j) (s.disk 0) (by omega)
    have hd := addDigit_value w hw (s.disk 1, s.disk (address w start (s.disk 0)))
    have hc := digit_carry w start (addDigit w hw) s
    have hv := digit_value w start (addDigit w hw) s
    change mid.disk 1 = _ at hc
    change mid.disk (address w start (s.disk 0)) = _ at hv
    rw [← hc, ← hv] at hd
    change value w (s.disk 0) start (count+1)
      (effect w (start+1) (addDigit w hw) count mid).disk +
      (2^w)^(count+1) * ((effect w (start+1) (addDigit w hw) count mid).disk 1).val = _
    rw [value, value, hfirst, pow_succ]
    try dsimp only [Prod.fst, Prod.snd] at hd
    have hm := congrArg (fun n : ℕ => 2^w * n) ht
    nlinarith only [hm, hd]

theorem add_no_overflow (w : ℕ) (hw : 0 < w) (start count : ℕ) (s : State (Word w))
    (hsmall : value w (s.disk 0) start count s.disk + (s.disk 1).val < (2^w)^count) :
    value w (s.disk 0) start count (effect w start (addDigit w hw) count s).disk =
      value w (s.disk 0) start count s.disk + (s.disk 1).val ∧
    (effect w start (addDigit w hw) count s).disk 1 = 0 := by
  have he := add_value w hw start count s
  have hb : 0 < (2^w)^count := by positivity
  have hc : ((effect w start (addDigit w hw) count s).disk 1).val = 0 := by
    nlinarith
  constructor
  · simpa only [hc, Nat.mul_zero, Nat.add_zero] using he
  · exact Fin.ext hc

def subDigit (w : ℕ) (hw : 0 < w) (r : Word w × Word w) : Word w × Word w :=
  if h : r.1.val ≤ r.2.val then
    (0, ⟨r.2.val - r.1.val, lt_of_le_of_lt (Nat.sub_le _ _) r.2.isLt⟩)
  else
    (⟨1, Nat.one_lt_two_pow hw.ne'⟩,
     ⟨2^w + r.2.val - r.1.val, by have := r.1.isLt; have := r.2.isLt; omega⟩)

theorem subDigit_value (w : ℕ) (hw : 0 < w) (r : Word w × Word w) :
    (subDigit w hw r).2.val + r.1.val =
      r.2.val + 2^w * (subDigit w hw r).1.val := by
  unfold subDigit
  split <;> dsimp <;> have := r.1.isLt <;> omega

theorem sub_value (w : ℕ) (hw : 0 < w) (start count : ℕ) (s : State (Word w)) :
    value w (s.disk 0) start count (effect w start (subDigit w hw) count s).disk +
        (s.disk 1).val =
      value w (s.disk 0) start count s.disk +
        (2^w)^count * ((effect w start (subDigit w hw) count s).disk 1).val := by
  induction count generalizing start s with
  | zero => simp [effect, value]
  | succ count ih =>
    let mid := digitEffect w start (subDigit w hw) s
    have hkey : mid.disk 0 = s.disk 0 := digit_key _ _ _ _
    have ht := ih (start+1) mid
    rw [hkey, value_digit_later w (start+1) count start _ s (by omega)] at ht
    have hfirst : (effect w (start+1) (subDigit w hw) count mid).disk
        (address w start (s.disk 0)) = mid.disk (address w start (s.disk 0)) := by
      apply effect_frame
      · have := address_large w start (s.disk 0); omega
      · intro j hj
        rw [hkey]
        exact address_ne w start (start+1+j) (s.disk 0) (by omega)
    have hd := subDigit_value w hw (s.disk 1, s.disk (address w start (s.disk 0)))
    have hc := digit_carry w start (subDigit w hw) s
    have hv := digit_value w start (subDigit w hw) s
    change mid.disk 1 = _ at hc
    change mid.disk (address w start (s.disk 0)) = _ at hv
    rw [← hc, ← hv] at hd
    change value w (s.disk 0) start (count+1)
      (effect w (start+1) (subDigit w hw) count mid).disk + _ =
      _ + (2^w)^(count+1) * ((effect w (start+1) (subDigit w hw) count mid).disk 1).val
    rw [value, value, hfirst, pow_succ]
    try dsimp only [Prod.fst, Prod.snd] at hd
    have hm := congrArg (fun n : ℕ => 2^w * n) ht
    nlinarith only [hm, hd]

theorem sub_no_underflow (w : ℕ) (hw : 0 < w) (start count : ℕ) (s : State (Word w))
    (hsmall : (s.disk 1).val ≤ value w (s.disk 0) start count s.disk) :
    value w (s.disk 0) start count (effect w start (subDigit w hw) count s).disk =
      value w (s.disk 0) start count s.disk - (s.disk 1).val ∧
    (effect w start (subDigit w hw) count s).disk 1 = 0 := by
  have he := sub_value w hw start count s
  have hb : 0 < (2^w)^count := by positivity
  have hv := value_bound w (s.disk 0) start count (effect w start (subDigit w hw) count s).disk
  have hc : ((effect w start (subDigit w hw) count s).disk 1).val = 0 := by
    nlinarith
  constructor
  · rw [hc, Nat.mul_zero, Nat.add_zero] at he
    omega
  · exact Fin.ext hc

end CSL.TwoWordGeneralCounter
end Counter

section OutputTest
/-! A charged zero test of a spilled counter. The two resident words are
unchanged in width. Only the external carry and test flag may be modified. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace CSL.TwoWordGeneralOutput
open TwoWordPhysicalAddresses TwoWordGeneralCounter

def one (w : ℕ) (hw : 0<w) : Word w := ⟨1,Nat.one_lt_two_pow hw.ne'⟩
@[simp] theorem one_ne_zero (w : ℕ) (hw : 0<w) : one w hw≠0 := by
  intro h
  have := congrArg Fin.val h
  simpa [one] using this

def flagAddress (w d : ℕ) : ℕ := 2+d*2^w

def orDigit (w : ℕ) (hw : 0<w) (r : Word w × Word w) : Word w × Word w :=
  (if r.1=0 ∧ r.2=0 then 0 else one w hw,r.2)

theorem or_digit_frame (w : ℕ) (hw : 0<w) (digit : ℕ)
    (s : State (Word w)) (a : ℕ) (ha : a≠1) :
    (digitEffect w digit (orDigit w hw) s).disk a=s.disk a := by
  by_cases ht : a=address w digit (s.disk 0)
  · rw [ht,digit_value];rfl
  · exact digit_frame w digit (orDigit w hw) s a ha ht

theorem or_frame (w : ℕ) (hw : 0<w) (start count : ℕ)
    (s : State (Word w)) (a : ℕ) (ha : a≠1) :
    (effect w start (orDigit w hw) count s).disk a=s.disk a := by
  induction count generalizing start s with
  | zero => rfl
  | succ count ih => rw [effect,ih,or_digit_frame w hw start s a ha]

theorem value_or_digit (w : ℕ) (hw : 0<w) (digit start count : ℕ)
    (s : State (Word w)) (key : Word w) :
    value w key start count (digitEffect w digit (orDigit w hw) s).disk=
      value w key start count s.disk := by
  apply value_eq
  intro j hj
  exact or_digit_frame w hw digit s _ (by have:=address_large w (start+j) key;omega)

theorem or_zero (w : ℕ) (hw : 0<w) (start count : ℕ) (s : State (Word w)) :
    (effect w start (orDigit w hw) count s).disk 1=0 ↔
      s.disk 1=0 ∧ value w (s.disk 0) start count s.disk=0 := by
  induction count generalizing start s with
  | zero => simp [effect,value]
  | succ count ih =>
    rw [effect,ih,digit_key,value_or_digit,digit_carry]
    have hb : (2^w : ℕ)≠0 := by positivity
    simp only [orDigit,Prod.fst,ite_eq_left_iff,one_ne_zero,imp_false,not_not,
      value,Nat.add_eq_zero_iff,Nat.mul_eq_zero,or_iff_right hb]
    constructor
    · rintro ⟨⟨hc,hd⟩,ht⟩
      exact ⟨hc,congrArg Fin.val hd,ht⟩
    · rintro ⟨hc,hd,ht⟩
      exact ⟨⟨hc,Fin.ext hd⟩,ht⟩

def testCode (w : ℕ) (hw : 0<w) (d : ℕ) : List (Command (Word w)) :=
  [.localOp (fun r=>(0,r.2)),.writeLeft 1] ++
  code w 0 (orDigit w hw) d ++
  [.readLeft 1,.localOp (fun r=>(if r.1=0 then 0 else one w hw,r.2)),
   .writeLeft (flagAddress w d)]

def clearCarry (w : ℕ) (s : State (Word w)) : State (Word w) :=
  ⟨0,s.right,Function.update s.disk 1 0⟩

def testState (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w)) : State (Word w) :=
  let t:=effect w 0 (orDigit w hw) d (clearCarry w s)
  let bit : Word w:=if t.disk 1=0 then 0 else one w hw
  ⟨bit,t.right,Function.update t.disk (flagAddress w d) bit⟩

theorem execute_test (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w)) :
    execute (testCode w hw d) s=testState w hw d s := by
  simp only [testCode,execute_append,execute_code,execute,step]
  rfl

theorem test_cost (w : ℕ) (hw : 0<w) (d : ℕ) :
    transfers (testCode w hw d)=6*d+3 := by
  simp only [testCode,transfers_append,code_cost,transfers,cost]
  omega

theorem test_frame (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w))
    (a : ℕ) (ha : a≠1) (hf : a≠flagAddress w d) :
    (testState w hw d s).disk a=s.disk a := by
  simp only [testState,Function.update_of_ne hf,or_frame w hw 0 d _ a ha,
    clearCarry,Function.update_of_ne ha]

theorem test_key (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w)) :
    (testState w hw d s).disk 0=s.disk 0 :=
  test_frame w hw d s 0 (by decide) (by unfold flagAddress;omega)

theorem clear_value (w : ℕ) (key : Word w) (start count : ℕ) (s : State (Word w)) :
    value w key start count (clearCarry w s).disk=value w key start count s.disk := by
  apply value_eq
  intro j hj
  exact Function.update_of_ne (by have:=address_large w (start+j) key;omega) _ _

theorem test_flag (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w)) :
    (testState w hw d s).disk (flagAddress w d)=
      if value w (s.disk 0) 0 d s.disk=0 then 0 else one w hw := by
  have hz:=or_zero w hw 0 d (clearCarry w s)
  simp only [clearCarry,Function.update_self,Function.update_of_ne (by decide : (0:ℕ)≠1),
    true_and] at hz
  have hv:=clear_value w (s.disk 0) 0 d s
  change value w (s.disk 0) 0 d (Function.update s.disk 1 0)=_ at hv
  rw [hv] at hz
  simp only [testState,Function.update_self,clearCarry]
  simp only [hz]

theorem counter_below_flag (w d j : ℕ) (key : Word w) (hj : j<d) :
    address w j key<flagAddress w d := by
  have hk:=key.isLt
  have hb : 0<2^w := by positivity
  have hm:=Nat.mul_le_mul_right (2^w) (show j+1≤d by omega)
  rw [Nat.add_mul,Nat.one_mul] at hm
  unfold address flagAddress
  omega

theorem test_value (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w)) (key : Word w) :
    value w key 0 d (testState w hw d s).disk=value w key 0 d s.disk := by
  apply value_eq
  intro j hj
  simp only [Nat.zero_add]
  exact test_frame w hw d s _ (by have:=address_large w j key;omega)
    (ne_of_lt (counter_below_flag w d j key hj))

end CSL.TwoWordGeneralOutput
end OutputTest

section OutputSearch
/-! A real read-flag while loop searches for the next nonempty counter.
Only the enclosing output position is publicly unrolled; the key search
is data dependent and every test, digit read and increment is charged. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CSL.TwoWordGeneralOutput
open TwoWordPhysicalAddresses TwoWordGeneralCounter
open TwoWordUniformLoop

def advanceCode (w : ℕ) : List (Command (Word w)) :=
  [.readLeft 0,.localOp (fun r=>(⟨(r.1.val+1)%(2^w),Nat.mod_lt _ (by positivity)⟩,r.2)),
   .writeLeft 0]

def advanceState (w : ℕ) (s : State (Word w)) : State (Word w) :=
  let key : Word w:=⟨((s.disk 0).val+1)%(2^w),Nat.mod_lt _ (by positivity)⟩
  ⟨key,s.right,Function.update s.disk 0 key⟩

theorem execute_advance (w : ℕ) (s : State (Word w)) :
    execute (advanceCode w) s=advanceState w s := rfl

def searchProgram (w : ℕ) (hw : 0<w) (d : ℕ) : Physical.Program (Word w) :=
  ⟨flagAddress w d,one w hw,advanceCode w ++ testCode w hw d⟩

theorem search_body_cost (w : ℕ) (hw : 0<w) (d : ℕ) :
    transfers (searchProgram w hw d).body=6*d+5 := by
  change transfers (advanceCode w ++ testCode w hw d)=_
  rw [transfers_append,test_cost]
  change 2+(6*d+3)=6*d+5
  omega

theorem advance_value (w d : ℕ) (s : State (Word w)) (key : Word w) :
    value w key 0 d (advanceState w s).disk=value w key 0 d s.disk := by
  apply value_eq
  intro j hj
  exact Function.update_of_ne (by have:=address_large w (0+j) key;omega) _ _

theorem check_disk (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w)) :
    (Physical.check (searchProgram w hw d) s).disk=s.disk := rfl

theorem next_eq (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w)) :
    Physical.next (searchProgram w hw d) s=
      testState w hw d (advanceState w (Physical.check (searchProgram w hw d) s)) := by
  unfold Physical.next searchProgram
  rw [execute_append,execute_test,execute_advance]

theorem advance_test_key (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w))
    (h : (s.disk 0).val+1<2^w) :
    ((advanceState w (Physical.check (searchProgram w hw d)
      (testState w hw d s))).disk 0).val=(s.disk 0).val+1 := by
  simp only [advanceState,Function.update_self,check_disk,test_key]
  exact Nat.mod_eq_of_lt h

theorem advanced_value (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w)) (key : Word w) :
    value w key 0 d (advanceState w (Physical.check (searchProgram w hw d)
      (testState w hw d s))).disk=value w key 0 d s.disk := by
  rw [advance_value,check_disk,test_value]

theorem advanced_frame (w : ℕ) (hw : 0<w) (d : ℕ) (s : State (Word w))
    (a : ℕ) (h0 : a≠0) (h1 : a≠1) (hf : a≠flagAddress w d) :
    (advanceState w (Physical.check (searchProgram w hw d)
      (testState w hw d s))).disk a=s.disk a := by
  simp only [advanceState,Function.update_of_ne h0,check_disk]
  exact test_frame w hw d s a h1 hf

/-- The exact number of search iterations is the increase in the key.
The counter digits and all input/output cells remain unchanged. -/
theorem search (w : ℕ) (hw : 0<w) (d steps : ℕ)
    (s : State (Word w)) (target : Word w)
    (hdiff : target.val=(s.disk 0).val+steps)
    (hzero : ∀key : Word w,(s.disk 0).val≤key.val → key.val<target.val →
      value w key 0 d s.disk=0)
    (hpos : 0<value w target 0 d s.disk) :
    ∃ t,Physical.Executes (searchProgram w hw d) (testState w hw d s) t
        ((6*d+6)*steps+1) ∧ t.disk 0=target ∧
      (∀a,a≠0 → a≠1 → a≠flagAddress w d → t.disk a=s.disk a) := by
  induction steps generalizing s with
  | zero =>
    have hk : s.disk 0=target := Fin.ext (by omega)
    have hp : value w (s.disk 0) 0 d s.disk≠0 := by rw [hk];omega
    let t:=Physical.check (searchProgram w hw d) (testState w hw d s)
    refine ⟨t,?_,?_,?_⟩
    · have hh : (Physical.check (searchProgram w hw d) (testState w hw d s)).left=
          (searchProgram w hw d).halt := by
        change (testState w hw d s).disk (flagAddress w d)=one w hw
        rw [test_flag,if_neg hp]
      simpa using Physical.Executes.stop (p:=searchProgram w hw d) (testState w hw d s) hh
    · exact (test_key w hw d s).trans hk
    · intro a h0 h1 hf
      exact test_frame w hw d s a h1 hf
  | succ steps ih =>
    have hklt : (s.disk 0).val<target.val := by omega
    have hkcap : (s.disk 0).val+1<2^w := by have:=target.isLt;omega
    have hz := hzero (s.disk 0) le_rfl hklt
    let mid:=advanceState w (Physical.check (searchProgram w hw d) (testState w hw d s))
    have hmkey : (mid.disk 0).val=(s.disk 0).val+1 := advance_test_key w hw d s hkcap
    obtain ⟨t,hr,hkey,hframe⟩ := ih mid (by omega)
      (fun key hlo hhi=> by
        rw [advanced_value]
        exact hzero key (by omega) hhi)
      (by rw [advanced_value];exact hpos)
    refine ⟨t,?_,hkey,?_⟩
    · have hc : Physical.continues (searchProgram w hw d) (testState w hw d s) := by
        change (testState w hw d s).disk (flagAddress w d)≠one w hw
        rw [test_flag,if_pos hz]
        exact (one_ne_zero w hw).symm
      have hr' : Physical.Executes (searchProgram w hw d)
          (Physical.next (searchProgram w hw d) (testState w hw d s)) t
          ((6*d+6)*steps+1) := by rw [next_eq];exact hr
      have he:=Physical.Executes.more (p:=searchProgram w hw d) (testState w hw d s) t _ hc hr'
      rw [search_body_cost] at he
      convert he using 1 <;> simp only [Nat.mul_succ] <;> omega
    · intro a h0 h1 hf
      exact (hframe a h0 h1 hf).trans (advanced_frame w hw d s a h0 h1 hf)

end CSL.TwoWordGeneralOutput
end OutputSearch

section OutputStages
/-! The charged preparation and true while-search as two existing stages.
The search itself has no public input-dependent iteration schedule. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace CSL.TwoWordGeneralOutput
open TwoWordPhysicalAddresses TwoWordGeneralCounter TwoWordRadixPreparedBuild

noncomputable def searchStages (w : ℕ) (hw : 0<w) (d : ℕ) : List (Stage (Word w)) :=
  [.straight (testCode w hw d),.loop (searchProgram w hw d)]

def searchCost {w : ℕ} (d : ℕ) (a target : Word w) : ℕ :=
  6*d+4+(6*d+6)*(target.val-a.val)

theorem searchCost_le {w : ℕ} (d : ℕ) (a target : Word w) :
    searchCost d a target≤(6*d+6)*(target.val-a.val+1) := by
  unfold searchCost
  rw [Nat.mul_add,Nat.mul_one]
  omega

/-- Only key, carry and the test flag may change. Every spilled counter
and every input/output cell retains its value during the search. -/
theorem search_complete (w : ℕ) (hw : 0<w) (d : ℕ)
    (s : State (Word w)) (target : Word w)
    (ha : (s.disk 0).val≤target.val)
    (hzero : ∀key : Word w,(s.disk 0).val≤key.val → key.val<target.val →
      value w key 0 d s.disk=0)
    (hpos : 0<value w target 0 d s.disk) :
    ∃ t,Executes (searchStages w hw d) s t (searchCost d (s.disk 0) target) ∧
      t.disk 0=target ∧
      (∀key : Word w,value w key 0 d t.disk=value w key 0 d s.disk) ∧
      (∀a,a≠0 → a≠1 → a≠flagAddress w d → t.disk a=s.disk a) := by
  obtain ⟨t,ht,hkey,hframe⟩ := search w hw d (target.val-(s.disk 0).val) s target
    (by omega) hzero hpos
  refine ⟨t,?_,hkey,?_,hframe⟩
  · have hh:=Executes.loop (searchProgram w hw d) [] (testState w hw d s) t t _ 0
      ht (Executes.done t)
    have hs:=Executes.straight (testCode w hw d) [.loop (searchProgram w hw d)] s t
      (((6*d+6)*(target.val-(s.disk 0).val)+1)+0)
      (by rw [execute_test];exact hh)
    change Executes (searchStages w hw d) s t _ at hs
    rw [test_cost] at hs
    convert hs using 1 <;> unfold searchCost <;> omega
  · intro key
    apply value_eq
    intro j hj
    simp only [Nat.zero_add]
    have hl:=address_large w j key
    exact hframe _ (by omega) (by omega)
      (ne_of_lt (counter_below_flag w d j key hj))

end CSL.TwoWordGeneralOutput
end OutputStages


