-- Prove2me | Definitions.Def_CSLB_NarrowSlots
-- name    : CSLB_NarrowSlots
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:15:47.488091+00:00
-- url     : https://prove2.me/theorems/631b594d-e26a-48aa-9995-ff0ccba66bd8
-- title:
--   Coded sorting bridge: NarrowSlots
-- statement:
--   # Counting-sort output with a predetermined schedule (narrow words)
--
--   After the histogram phase of the two-word counting sort (`TwoWordGeneralHistogram`), the
--   counter of key `k` holds the multiplicity of `k` in the input. This module writes the sorted
--   output with a *fixed* sequence of `n + 2^w - 1` slots, so that the position in the program is a
--   function of time only. Slot `s` reads the current key `k` (cell 0), tests whether its remaining
--   count is zero, writes `k` to output position `s - k`, decrements the count when it was positive,
--   and advances `k` when it was zero. Each slot either emits one key or advances the key, so after
--   `n + 2^w - 1` slots every output position below `n` holds the sorted input.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Definitions.Def_CSL_Sorting_SmallMemory_NarrowWords_PublicUnrolledComplete

/-! # Counting-sort output with a predetermined schedule (narrow words)

After the histogram phase of the two-word counting sort (`TwoWordGeneralHistogram`), the
counter of key `k` holds the multiplicity of `k` in the input. This module writes the sorted
output with a *fixed* sequence of `n + 2^w - 1` slots, so that the position in the program is a
function of time only. Slot `s` reads the current key `k` (cell 0), tests whether its remaining
count is zero, writes `k` to output position `s - k`, decrements the count when it was positive,
and advances `k` when it was zero. Each slot either emits one key or advances the key, so after
`n + 2^w - 1` slots every output position below `n` holds the sorted input. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CSLB.NarrowSlots
open CSL CSL.TwoWordPhysicalAddresses CSL.TwoWordGeneralCounter CSL.TwoWordGeneralHistogram
open CSL.TwoWordGeneralOutput CSL.TwoWordGeneralOutputList

section
variable (w : ℕ) (hw : 0 < w) (d : ℕ)

/-- Write the current key (cell 0) to output position `s - key`. -/
def putCode (s : ℕ) : List (Command (Word w)) :=
  [.readRight 0, .writeRight (fun r => inputBase w d + (s - r.2.val))]

/-- Copy the test flag into the borrow cell 1. -/
def borrowCode : List (Command (Word w)) :=
  [.readLeft (flagAddress w d), .writeLeft 1]

/-- Advance the key when the test flag is zero. -/
def advanceCode : List (Command (Word w)) :=
  [.readLeft (flagAddress w d), .readRight 0,
   .localOp (fun r => (r.1, if r.1 = 0 then r.2 + TwoWordGeneralOutput.one w hw else r.2)),
   .writeRight (fun _ => 0)]

def slotCode (s : ℕ) : List (Command (Word w)) :=
  testCode w hw d ++ putCode w d s ++ borrowCode w d ++ code w 0 (subDigit w hw) d ++
    advanceCode w hw d

/-- The first `S` slots. -/
def outputCode : ℕ → List (Command (Word w))
  | 0 => []
  | S + 1 => outputCode S ++ slotCode w hw d S

theorem slot_cost (s : ℕ) : transfers (slotCode w hw d s) = 12 * d + 10 := by
  simp only [slotCode, transfers_append, test_cost, code_cost]
  simp only [putCode, borrowCode, advanceCode, transfers, cost]
  omega

theorem outputCode_cost (S : ℕ) : transfers (outputCode w hw d S) = (12 * d + 10) * S := by
  induction S with
  | zero => rfl
  | succ S ih => rw [outputCode, transfers_append, ih, slot_cost, Nat.mul_succ]

end

theorem flag_ne_zero_addr (w d : ℕ) : flagAddress w d ≠ 0 := by unfold flagAddress; omega
theorem flag_ne_one_addr (w d : ℕ) : flagAddress w d ≠ 1 := by unfold flagAddress; omega
theorem base_gt_flag (w d i : ℕ) : flagAddress w d < inputBase w d + i := by
  unfold flagAddress inputBase; omega
theorem counter_lt_base (w d j i : ℕ) (key : Word w) (hj : j < d) :
    address w j key < inputBase w d + i := by
  have := address_below w d j key hj
  unfold inputBase; omega

/-- The key-independent part of one slot, as a state function. -/
def slotState (w : ℕ) (hw : 0 < w) (d s : ℕ) (st : State (Word w)) : State (Word w) :=
  execute (slotCode w hw d s) st

section Effects
variable (w : ℕ) (hw : 0 < w) (d s : ℕ) (st : State (Word w))

/-- State after test and put. -/
def afterPut : State (Word w) :=
  let t := testState w hw d st
  ⟨t.left, t.disk 0, Function.update t.disk (inputBase w d + (s - (t.disk 0).val)) (t.disk 0)⟩

theorem execute_put :
    execute (testCode w hw d ++ putCode w d s) st = afterPut w hw d s st := by
  rw [execute_append, execute_test]
  rfl

def afterBorrow : State (Word w) :=
  let t := afterPut w hw d s st
  ⟨t.disk (flagAddress w d), t.right, Function.update t.disk 1 (t.disk (flagAddress w d))⟩

theorem execute_borrow :
    execute (testCode w hw d ++ putCode w d s ++ borrowCode w d) st =
      afterBorrow w hw d s st := by
  rw [execute_append, execute_put]
  rfl

def afterSub : State (Word w) := effect w 0 (subDigit w hw) d (afterBorrow w hw d s st)

def afterAdvance : State (Word w) :=
  let t := afterSub w hw d s st
  let f := t.disk (flagAddress w d)
  let k := t.disk 0
  let k' := if f = 0 then k + TwoWordGeneralOutput.one w hw else k
  ⟨f, k', Function.update t.disk 0 k'⟩

theorem execute_slot : slotState w hw d s st = afterAdvance w hw d s st := by
  unfold slotState slotCode
  rw [execute_append, execute_append, execute_borrow, execute_code]
  rfl

/-! Cell facts. -/

theorem put_disk_ne (a : ℕ) (ha : a ≠ inputBase w d + (s - ((testState w hw d st).disk 0).val)) :
    (afterPut w hw d s st).disk a = (testState w hw d st).disk a := by
  simp [afterPut, Function.update_of_ne ha]

theorem borrow_disk_ne (a : ℕ) (ha : a ≠ 1) :
    (afterBorrow w hw d s st).disk a = (afterPut w hw d s st).disk a := by
  simp [afterBorrow, Function.update_of_ne ha]

theorem key_testState : (testState w hw d st).disk 0 = st.disk 0 := test_key w hw d st

theorem key_afterPut : (afterPut w hw d s st).disk 0 = st.disk 0 := by
  rw [put_disk_ne]
  · exact key_testState w hw d st
  · unfold inputBase; omega

theorem key_afterBorrow : (afterBorrow w hw d s st).disk 0 = st.disk 0 := by
  rw [borrow_disk_ne _ _ _ _ _ _ (by omega), key_afterPut]

theorem key_afterSub : (afterSub w hw d s st).disk 0 = st.disk 0 := by
  unfold afterSub
  rw [effect_key, key_afterBorrow]

theorem flag_afterPut : (afterPut w hw d s st).disk (flagAddress w d) =
    if value w (st.disk 0) 0 d st.disk = 0 then 0 else TwoWordGeneralOutput.one w hw := by
  rw [put_disk_ne, test_flag]
  · exact ne_of_lt (base_gt_flag w d _)

theorem carry_afterBorrow : (afterBorrow w hw d s st).disk 1 =
    if value w (st.disk 0) 0 d st.disk = 0 then 0 else TwoWordGeneralOutput.one w hw := by
  simp only [afterBorrow, Function.update_self]
  exact flag_afterPut w hw d s st

theorem flag_afterSub : (afterSub w hw d s st).disk (flagAddress w d) =
    if value w (st.disk 0) 0 d st.disk = 0 then 0 else TwoWordGeneralOutput.one w hw := by
  unfold afterSub
  rw [effect_frame]
  · rw [borrow_disk_ne _ _ _ _ _ _ (flag_ne_one_addr w d)]
    exact flag_afterPut w hw d s st
  · exact flag_ne_one_addr w d
  · intro j hj
    exact ne_of_gt (counter_below_flag w d (0 + j) _ (by omega))

/-- Values of every counter after test, put, and borrow are the original ones. -/
theorem value_afterBorrow (key : Word w) :
    value w key 0 d (afterBorrow w hw d s st).disk = value w key 0 d st.disk := by
  rw [← test_value w hw d st key]
  apply value_eq
  intro j hj
  have hlo := address_large w (0 + j) key
  rw [borrow_disk_ne _ _ _ _ _ _ (by omega), put_disk_ne]
  exact ne_of_lt (counter_lt_base w d (0 + j) _ key (by omega))

theorem value_afterSub_self :
    value w (st.disk 0) 0 d (afterSub w hw d s st).disk =
      value w (st.disk 0) 0 d st.disk -
        (if value w (st.disk 0) 0 d st.disk = 0 then 0 else 1) := by
  have hsmall : ((afterBorrow w hw d s st).disk 1).val ≤
      value w ((afterBorrow w hw d s st).disk 0) 0 d (afterBorrow w hw d s st).disk := by
    rw [carry_afterBorrow, key_afterBorrow, value_afterBorrow]
    split_ifs with h
    · simp
    · simp only [TwoWordGeneralOutput.one]; omega
  have h := (sub_no_underflow w hw 0 d (afterBorrow w hw d s st) hsmall).1
  rw [key_afterBorrow, value_afterBorrow, carry_afterBorrow] at h
  unfold afterSub
  rw [h]
  split_ifs <;> simp [TwoWordGeneralOutput.one]

theorem value_afterSub_other (key : Word w) (hne : key ≠ st.disk 0) :
    value w key 0 d (afterSub w hw d s st).disk = value w key 0 d st.disk := by
  rw [← value_afterBorrow w hw d s st key]
  apply value_eq
  intro j hj
  unfold afterSub
  apply effect_frame
  · have := address_large w (0 + j) key; omega
  · intro i hi
    rw [key_afterBorrow]
    exact fun h => hne (address_key_injective w (0 + j) (0 + i) key (st.disk 0) h)

theorem output_afterSub (i : ℕ) :
    (afterSub w hw d s st).disk (inputBase w d + i) =
      Function.update st.disk (inputBase w d + (s - (st.disk 0).val)) (st.disk 0)
        (inputBase w d + i) := by
  unfold afterSub
  rw [effect_frame]
  · rw [borrow_disk_ne _ _ _ _ _ _ (by unfold inputBase; omega)]
    simp only [afterPut, key_testState]
    by_cases hi : inputBase w d + i = inputBase w d + (s - (st.disk 0).val)
    · rw [hi]; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact test_frame w hw d st _ (by unfold inputBase; omega)
        (ne_of_gt (base_gt_flag w d i))
  · unfold inputBase; omega
  · intro j hj
    exact ne_of_gt (counter_lt_base w d (0 + j) i _ (by omega))

/-! Facts about the full slot. -/

theorem slot_key : (slotState w hw d s st).disk 0 =
    if value w (st.disk 0) 0 d st.disk = 0 then st.disk 0 + TwoWordGeneralOutput.one w hw else st.disk 0 := by
  rw [execute_slot]
  simp only [afterAdvance, Function.update_self, flag_afterSub, key_afterSub]
  split_ifs with h1 h2 <;> simp_all [TwoWordGeneralOutput.one_ne_zero]

theorem slot_value (key : Word w) :
    value w key 0 d (slotState w hw d s st).disk =
      if key = st.disk 0 then
        value w key 0 d st.disk - (if value w key 0 d st.disk = 0 then 0 else 1)
      else value w key 0 d st.disk := by
  rw [execute_slot]
  have hfr : value w key 0 d (afterAdvance w hw d s st).disk =
      value w key 0 d (afterSub w hw d s st).disk := by
    apply value_eq
    intro j hj
    have := address_large w (0 + j) key
    simp only [afterAdvance]
    exact Function.update_of_ne (by omega) _ _
  rw [hfr]
  by_cases hk : key = st.disk 0
  · subst hk; rw [if_pos rfl]; exact value_afterSub_self w hw d s st
  · rw [if_neg hk]; exact value_afterSub_other w hw d s st key hk

theorem slot_output (i : ℕ) :
    (slotState w hw d s st).disk (inputBase w d + i) =
      Function.update st.disk (inputBase w d + (s - (st.disk 0).val)) (st.disk 0)
        (inputBase w d + i) := by
  rw [execute_slot]
  simp only [afterAdvance]
  rw [Function.update_of_ne (by unfold inputBase; omega)]
  exact output_afterSub w hw d s st i

end Effects

/-! The slot invariant. -/

section Invariant
variable (w : ℕ) (hw : 0 < w) (d : ℕ)

def counts (disk : ℕ → Word w) : Word w → ℕ := fun key => value w key 0 d disk

/-- `E` is the emitted prefix of the sorted output `ys` after `s` slots. -/
structure Inv (ys : List (Word w)) (s : ℕ) (st : State (Word w)) (E : List (Word w)) : Prop where
  key_le : (st.disk 0).val ≤ s
  length : E.length = s - (st.disk 0).val
  split : ys = E ++ sortedCounts (counts w d st.disk)
  lower : ∀ key, key < st.disk 0 → counts w d st.disk key = 0
  written : ∀ i (hi : i < E.length), st.disk (inputBase w d + i) = E[i]

theorem counts_slot (s : ℕ) (st : State (Word w)) :
    counts w d (slotState w hw d s st).disk =
      Function.update (counts w d st.disk) (st.disk 0)
        (counts w d st.disk (st.disk 0) -
          (if counts w d st.disk (st.disk 0) = 0 then 0 else 1)) := by
  funext key
  simp only [counts]
  rw [slot_value]
  by_cases hk : key = st.disk 0
  · subst hk; rw [if_pos rfl, Function.update_self]; rfl
  · rw [if_neg hk, Function.update_of_ne hk]; rfl

theorem inv_step (ys : List (Word w)) (s : ℕ) (st : State (Word w)) (E : List (Word w))
    (h : Inv w d ys s st E) (hs : s < ys.length + 2^w - 1) :
    ∃ E', Inv w d ys (s + 1) (slotState w hw d s st) E' := by
  set k := st.disk 0 with hkdef
  have hlen : ys.length = E.length + (sortedCounts (counts w d st.disk)).length := by
    rw [h.split, List.length_append]
  by_cases hz : counts w d st.disk k = 0
  · -- advance the key
    have hzv : value w k 0 d st.disk = 0 := hz
    have hk1 : k.val + 1 < 2^w := by
      by_contra hcon
      have hkmax : k.val = 2^w - 1 := by have := k.isLt; omega
      have hall : ∀ key, counts w d st.disk key = 0 := by
        intro key
        rcases lt_or_eq_of_le (show key ≤ k from by
          change key.val ≤ k.val; have := key.isLt; omega) with hlt | heq
        · exact h.lower key hlt
        · rw [heq]; exact hz
      have hnil := (nil_iff (counts w d st.disk)).mpr hall
      rw [hnil, List.length_nil] at hlen
      have := h.length
      have := h.key_le
      omega
    have hkey' : (slotState w hw d s st).disk 0 = ⟨k.val + 1, hk1⟩ := by
      rw [slot_key, ← hkdef, if_pos hzv]
      apply Fin.ext
      simp only [Fin.val_add, TwoWordGeneralOutput.one]
      exact Nat.mod_eq_of_lt hk1
    have hcounts : counts w d (slotState w hw d s st).disk = counts w d st.disk := by
      rw [counts_slot, ← hkdef, hz]
      simp only [if_pos rfl, Nat.zero_sub]
      exact Function.update_eq_self_iff.mpr hz.symm
    refine ⟨E, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hkey']; have := h.key_le; simp only; omega
    · rw [hkey', h.length]; simp only; omega
    · rw [hcounts]; exact h.split
    · intro key hkey
      rw [hcounts]
      rw [hkey'] at hkey
      rcases lt_or_eq_of_le (show key ≤ k from by
        change key.val ≤ k.val; have : key.val < k.val + 1 := hkey; omega) with hlt | heq
      · exact h.lower key hlt
      · rw [heq]; exact hz
    · intro i hi
      rw [slot_output, Function.update_of_ne]
      · exact h.written i hi
      · have := h.length; rw [← hkdef]; omega
  · -- emit the key
    have hzv : value w k 0 d st.disk ≠ 0 := hz
    have hpos : 0 < counts w d st.disk k := Nat.pos_of_ne_zero hz
    have hkey' : (slotState w hw d s st).disk 0 = k := by
      rw [slot_key, ← hkdef, if_neg hzv]
    have hcounts : counts w d (slotState w hw d s st).disk =
        Function.update (counts w d st.disk) k (counts w d st.disk k - 1) := by
      rw [counts_slot, ← hkdef, if_neg hz]
    refine ⟨E ++ [k], ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hkey']; have := h.key_le; omega
    · rw [hkey', List.length_append, h.length]; simp only [List.length_singleton]
      have := h.key_le; omega
    · rw [hcounts]
      exact emitted_prefix_step ys E (counts w d st.disk) k hpos h.lower h.split
    · intro key hkey
      rw [hkey'] at hkey
      rw [hcounts, Function.update_of_ne (ne_of_lt hkey)]
      exact h.lower key hkey
    · intro i hi
      rw [slot_output]
      rw [List.length_append, List.length_singleton] at hi
      by_cases hie : i = E.length
      · subst hie
        have hp : s - (st.disk 0).val = E.length := h.length.symm
        rw [hp, Function.update_self, List.getElem_append_right (le_refl _)]
        simp [hkdef]
      · have hi' : i < E.length := by omega
        rw [Function.update_of_ne (by rw [← hkdef]; have := h.length; omega)]
        rw [List.getElem_append_left hi']
        exact h.written i hi'

theorem inv_run (ys : List (Word w)) (S : ℕ) (hS : S ≤ ys.length + 2^w - 1)
    (st : State (Word w)) (h0 : Inv w d ys 0 st []) :
    ∃ E, Inv w d ys S (execute (outputCode w hw d S) st) E := by
  induction S with
  | zero => exact ⟨[], h0⟩
  | succ S ih =>
    obtain ⟨E, hE⟩ := ih (by omega)
    obtain ⟨E', hE'⟩ := inv_step w hw d ys S _ E hE (by omega)
    refine ⟨E', ?_⟩
    rw [outputCode, execute_append]
    exact hE'

theorem inv_final (ys : List (Word w)) (st : State (Word w)) (E : List (Word w))
    (h : Inv w d ys (ys.length + 2^w - 1) st E) : E = ys := by
  have hlen : ys.length = E.length + (sortedCounts (counts w d st.disk)).length := by
    rw [h.split, List.length_append]
  have hk := (st.disk 0).isLt
  have hl := h.length
  have hb : 0 < 2^w := by positivity
  have hzero : (sortedCounts (counts w d st.disk)).length = 0 := by omega
  rw [List.length_eq_zero_iff] at hzero
  rw [h.split, hzero, List.append_nil]

end Invariant

/-- The complete output phase, from a state whose counters hold the histogram of `xs` and
whose key cell is `0`. -/
theorem output_correct (w : ℕ) (hw : 0 < w) (d : ℕ) (st : State (Word w)) (xs : List (Word w))
    (hhist : Histogram d st.disk (TwoWordGeneralPublicUnrolled.output w xs))
    (hkey : st.disk 0 = 0) :
    File (execute (outputCode w hw d (xs.length + 2^w - 1)) st).disk (inputBase w d)
      (TwoWordGeneralPublicUnrolled.output w xs) := by
  set ys := TwoWordGeneralPublicUnrolled.output w xs with hys
  have hylen : ys.length = xs.length := TwoWordGeneralPublicUnrolled.output_length w xs
  have hsc : sortedCounts (counts w d st.disk) = ys :=
    unique (counts w d st.disk) ys (fun key => hhist key)
      (TwoWordGeneralPublicUnrolled.output_sorted w xs)
  have h0 : Inv w d ys 0 st [] := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hkey]; simp
    · rw [hkey]; simp
    · rw [hsc]; simp
    · intro key hk
      rw [hkey] at hk
      exact absurd hk (Fin.not_lt_zero _)
    · intro i hi; simp at hi
  obtain ⟨E, hE⟩ := inv_run w hw d ys (ys.length + 2^w - 1) le_rfl st h0
  have hEq := inv_final w d ys _ E hE
  rw [hylen] at hE
  intro i hi
  have := hE.written i (by rw [hEq]; exact hi)
  rw [this]
  simp only [hEq]

end CSLB.NarrowSlots


