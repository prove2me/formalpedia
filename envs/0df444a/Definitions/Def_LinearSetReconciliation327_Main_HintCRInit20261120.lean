-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintCRInit20261120
-- name    : LinearSetReconciliation327_Main_HintCRInit20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:23:25.524992+00:00
-- url     : https://prove2.me/theorems/912d377f-7f86-403c-a2b6-c5a565ae557d
-- title:
--   LinearSetReconciliation327 — HintCRInit (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintCRInit20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintCROutput20261120
import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def crRFZeroCell (i : ℕ) : List Instr := [.imm 2 i, .add 2 8 2, .store 2 0]
def crRFZeroCode (count : ℕ) : List Instr := (List.range count).flatMap crRFZeroCell
theorem crRFZeroCode_succ (n : ℕ) :
    crRFZeroCode (n + 1) = crRFZeroCode n ++ crRFZeroCell n := by
  simp [crRFZeroCode, List.range_succ]
theorem crRFZeroCell_spec (E : RAMEnv) (p : RAMState) (file i : ℕ) (hI : i < 16)
    (hPtr : p.regs 8 = file) (hZero : p.regs 0 = 0) (hFile : file + 16 ≤ 2 ^ E.W) :
    let out := runBlock (crRFZeroCell i) E p
    out.pc = p.pc + 3 ∧ (∀ r, r ≠ 2 → out.regs r = p.regs r) ∧
      out.mem = Function.update p.mem (file + i) 0 := by
  have h16 : 16 ≤ 2 ^ E.W := by omega
  have hAddr : p.regs 8 + (⟨i, hI⟩ : Fin 16).val < 2 ^ E.W := by rw [hPtr]; omega
  have h := crSpillWrite_spec E p (⟨i, hI⟩ : Fin 16) 0 (by decide) h16 hAddr
  have hCode : crRFZeroCell i = crSpillWrite (⟨i, hI⟩ : Fin 16) 0 := rfl
  rw [hCode]
  obtain ⟨hPc, h2, hFrame, hMem⟩ := h
  exact ⟨hPc, hFrame, by simpa only [hPtr, hZero] using hMem⟩
theorem crRFZero_spec (E : RAMEnv) (p : RAMState) (file : ℕ)
    (hPtr : p.regs 8 = file) (hZero : p.regs 0 = 0) (hFile : file + 16 ≤ 2 ^ E.W) :
    ∀ n : ℕ, n ≤ 16 →
      let out := runBlock (crRFZeroCode n) E p
      out.pc = p.pc + 3 * n ∧ (∀ r, r ≠ 2 → out.regs r = p.regs r) ∧
        out.mem = fun a => if file ≤ a ∧ a < file + n then 0 else p.mem a := by
  intro n
  induction n with
  | zero =>
    intro hn
    refine ⟨rfl, by intro r hr; rfl, ?_⟩
    funext a
    split_ifs with h
    · exfalso; omega
    · rfl
  | succ n ih =>
    intro hn
    generalize hu : runBlock (crRFZeroCode n) E p = u
    have hU := ih (by omega)
    rw [hu] at hU
    obtain ⟨hUpc, hUfr, hUmem⟩ := hU
    have hU8 : u.regs 8 = file := (hUfr 8 (by decide)).trans hPtr
    have hU0 : u.regs 0 = 0 := (hUfr 0 (by decide)).trans hZero
    generalize ho : runBlock (crRFZeroCell n) E u = out
    have hO := crRFZeroCell_spec E u file n (by omega) hU8 hU0 hFile
    rw [ho] at hO
    obtain ⟨hOpc, hOfr, hOmem⟩ := hO
    have hRun : runBlock (crRFZeroCode (n + 1)) E p = out := by
      rw [crRFZeroCode_succ, runBlock_append, hu, ho]
    dsimp only
    rw [hRun]
    refine ⟨by omega, ?_, ?_⟩
    · intro r hr
      exact (hOfr r hr).trans (hUfr r hr)
    · rw [hOmem, hUmem]
      funext a
      by_cases ha : a = file + n
      · subst a
        simp only [Function.update_self]
        split_ifs with h
        · rfl
        · exfalso; omega
      · simp only [Function.update_of_ne ha]
        split_ifs <;> first | rfl | omega
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def crRFInit : List Instr :=
  ([.imm 0 0] ++ crRFZeroCode 16) ++ ([.add 0 1 0] ++ crSpillWrite 1 0)
theorem crRFInit_spec (E : RAMEnv) (p : RAMState) (file : ℕ)
    (hPtr : p.regs 8 = file) (hFile : file + 16 ≤ 2 ^ E.W) (hWords : p.regs 1 < 2 ^ E.W) :
    let out := runBlock crRFInit E p
    out.pc = p.pc + 53 ∧ out.regs 0 = p.regs 1 ∧
      (∀ r, r ≠ 0 → r ≠ 2 → out.regs r = p.regs r) ∧
      out.mem = Function.update (fun a => if file ≤ a ∧ a < file + 16 then 0 else p.mem a)
        (file + 1) (p.regs 1) := by
  have h16 : 16 ≤ 2 ^ E.W := by omega
  generalize hu : runBlock [.imm 0 0] E p = u
  have hU : u = {p with pc := p.pc + 1, regs := Function.update p.regs 0 0} := by
    rw [← hu]
    simp [runBlock, execInstr]
  have hUpc : u.pc = p.pc + 1 := congrArg RAMState.pc hU
  have hU8 : u.regs 8 = file := by simpa only [hU, Function.update_of_ne (by decide : (8 : Fin 16) ≠ 0)] using hPtr
  have hU0 : u.regs 0 = 0 := by simp only [hU, Function.update_self]
  have hU1 : u.regs 1 = p.regs 1 := by simp only [hU, Function.update_of_ne (by decide : (1 : Fin 16) ≠ 0)]
  have hUmem : u.mem = p.mem := by simp only [hU]
  generalize hv : runBlock (crRFZeroCode 16) E u = v
  have hV := crRFZero_spec E u file hU8 hU0 hFile 16 le_rfl
  rw [hv] at hV
  obtain ⟨hVpc, hVfr, hVmem⟩ := hV
  have hV8 : v.regs 8 = file := (hVfr 8 (by decide)).trans hU8
  have hV0 : v.regs 0 = 0 := (hVfr 0 (by decide)).trans hU0
  have hV1 : v.regs 1 = p.regs 1 := (hVfr 1 (by decide)).trans hU1
  generalize hq : runBlock [.add 0 1 0] E v = q
  have hQ : q = {v with pc := v.pc + 1, regs := Function.update v.regs 0 (p.regs 1)} := by
    rw [← hq]
    simp only [runBlock, List.foldl_cons, List.foldl_nil, execInstr, hV0, Nat.add_zero, hV1, Nat.mod_eq_of_lt hWords]
  have hQpc : q.pc = v.pc + 1 := congrArg RAMState.pc hQ
  have hQ8 : q.regs 8 = file := by simpa only [hQ, Function.update_of_ne (by decide : (8 : Fin 16) ≠ 0)] using hV8
  have hQ0 : q.regs 0 = p.regs 1 := by simp only [hQ, Function.update_self]
  have hQmem : q.mem = v.mem := by simp only [hQ]
  generalize ho : runBlock (crSpillWrite 1 0) E q = out
  have hO := crSpillWrite_spec E q 1 0 (by decide) h16 (by rw [hQ8]; omega)
  rw [ho] at hO
  obtain ⟨hOpc, hO2, hOfr, hOmem⟩ := hO
  have hFirst : runBlock ([.imm 0 0] ++ crRFZeroCode 16) E p = v := by
    rw [runBlock_append, hu, hv]
  have hLast : runBlock ([.add 0 1 0] ++ crSpillWrite 1 0) E v = out := by
    rw [runBlock_append, hq, ho]
  have hRun : runBlock crRFInit E p = out := by
    rw [crRFInit, runBlock_append, hFirst, hLast]
  dsimp only
  rw [hRun]
  refine ⟨by omega, (hOfr 0 (by decide)).trans hQ0, ?_, ?_⟩
  · intro r hr0 hr2
    have hQr : q.regs r = v.regs r := by simp only [hQ, Function.update_of_ne hr0]
    have hUr : u.regs r = p.regs r := by simp only [hU, Function.update_of_ne hr0]
    exact (hOfr r hr2).trans (hQr.trans ((hVfr r hr2).trans hUr))
  · rw [hOmem, hQmem, hVmem, hUmem, hQ8, hQ0]
    simp
theorem crRFInit_registers (E : RAMEnv) (p : RAMState) (file : ℕ)
    (hPtr : p.regs 8 = file) (hFile : file + 16 ≤ 2 ^ E.W) (hWords : p.regs 1 < 2 ^ E.W)
    (r : Fin 16) :
    (runBlock crRFInit E p).mem (file + r.val) = if r = 1 then p.regs 1 else 0 := by
  have h := crRFInit_spec E p file hPtr hFile hWords
  rw [h.2.2.2]
  by_cases hr : r = 1
  · subst r
    simp
  · have hAddr : file + r.val ≠ file + 1 := by
      intro he
      exact hr (Fin.ext (Nat.add_left_cancel he))
    rw [Function.update_of_ne hAddr, if_neg hr]
    have hIn : file ≤ file + r.val ∧ file + r.val < file + 16 :=
      ⟨Nat.le_add_right _ _, Nat.add_lt_add_left r.isLt file⟩
    rw [if_pos hIn]
theorem crRFInit_mem_frame (E : RAMEnv) (p : RAMState) (file a : ℕ)
    (hPtr : p.regs 8 = file) (hFile : file + 16 ≤ 2 ^ E.W) (hWords : p.regs 1 < 2 ^ E.W)
    (hOutside : a < file ∨ file + 16 ≤ a) :
    (runBlock crRFInit E p).mem a = p.mem a := by
  have h := crRFInit_spec E p file hPtr hFile hWords
  rw [h.2.2.2]
  have hAddr : a ≠ file + 1 := by omega
  have hNot : ¬ (file ≤ a ∧ a < file + 16) := by omega
  rw [Function.update_of_ne hAddr, if_neg hNot]
end LinearSetReconciliation327.Main
end
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def bitAt (m : ℕ → ℕ) (W base v : ℕ) : ℕ := ((m (base + v / W)) % 2 ^ W) / 2 ^ (v % W) % 2
def crReadInputBit : List Instr :=
  [.add 1 5 12, .mod 2 1 11, .div 1 1 11, .load 0 1, .shr 0 0 2, .mod 0 0 13]
theorem crReadInputBit_spec (E : RAMEnv) (p : RAMState) (hW : 0 < E.W)
    (hWidth : p.regs 11 = E.W) (hTwo : p.regs 13 = 2)
    (hIndex : p.regs 5 + p.regs 12 < 2 ^ E.W) :
    let out := runBlock crReadInputBit E p
    out.pc = p.pc + 6 ∧ out.mem = p.mem ∧
      out.regs 0 = bitAt p.mem E.W 0 (p.regs 5 + p.regs 12) ∧
      out.regs 1 = (p.regs 5 + p.regs 12) / E.W ∧
      out.regs 2 = (p.regs 5 + p.regs 12) % E.W ∧
      ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → out.regs r = p.regs r := by
  have hWidthSmall : E.W < 2 ^ E.W := Nat.lt_two_pow_self (n := E.W)
  have hMod : (p.regs 5 + p.regs 12) % E.W < 2 ^ E.W :=
    (Nat.mod_lt _ hW).trans hWidthSmall
  have hDiv : (p.regs 5 + p.regs 12) / E.W < 2 ^ E.W := (Nat.div_le_self _ _).trans_lt hIndex
  have hLoad : p.mem ((p.regs 5 + p.regs 12) / E.W) % 2 ^ E.W < 2 ^ E.W :=
    Nat.mod_lt _ (Nat.two_pow_pos E.W)
  have hShift : (p.mem ((p.regs 5 + p.regs 12) / E.W) % 2 ^ E.W) /
      2 ^ ((p.regs 5 + p.regs 12) % E.W) < 2 ^ E.W := (Nat.div_le_self _ _).trans_lt hLoad
  have hTwoWord : 2 ≤ 2 ^ E.W := by
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ E.W := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hBit : ((p.mem ((p.regs 5 + p.regs 12) / E.W) % 2 ^ E.W) /
      2 ^ ((p.regs 5 + p.regs 12) % E.W)) % 2 < 2 ^ E.W :=
    (Nat.mod_lt _ (by decide : 0 < 2)).trans_le hTwoWord
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [crReadInputBit, runBlock, execInstr, Nat.add_assoc]
  · rfl
  · simp [crReadInputBit, runBlock, execInstr, Function.update, hWidth, hTwo,
      Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hMod, Nat.mod_eq_of_lt hDiv,
      Nat.mod_eq_of_lt hShift, Nat.mod_eq_of_lt hBit, bitAt]
  · simp [crReadInputBit, runBlock, execInstr, Function.update, hWidth,
      Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hDiv]
  · simp [crReadInputBit, runBlock, execInstr, Function.update, hWidth,
      Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hMod]
  · intro r hr0 hr1 hr2
    simp [crReadInputBit, runBlock, execInstr, Function.update, hr0, hr1, hr2]
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def crWriteInputBit : List Instr :=
  [.mod 2 12 7, .shl 0 0 2, .div 1 12 7, .add 1 9 1,
    .load 3 1, .add 3 3 0, .store 1 3, .add 12 12 15]
theorem crWriteInputBit_spec (E : RAMEnv) (p : RAMState) (w memBase k : ℕ)
    (hw : 0 < w) (hWide : w < E.W) (hWidth : p.regs 7 = w) (hBase : p.regs 9 = memBase)
    (hCounter : p.regs 12 = k) (hOne : p.regs 15 = 1) (hBit : p.regs 0 ≤ 1)
    (hAddr : memBase + k / w < 2 ^ E.W) (hNext : k + 1 < 2 ^ E.W)
    (hSum : p.mem (memBase + k / w) + p.regs 0 * 2 ^ (k % w) < 2 ^ E.W) :
    let out := runBlock crWriteInputBit E p
    out.pc = p.pc + 8 ∧ out.regs 12 = k + 1 ∧
      out.mem = Function.update p.mem (memBase + k / w)
        (p.mem (memBase + k / w) + p.regs 0 * 2 ^ (k % w)) ∧
      ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r := by
  have hPow : 2 ^ (k % w) < 2 ^ E.W :=
    Nat.pow_lt_pow_right (by norm_num) ((Nat.mod_lt k hw).trans hWide)
  have hMask : p.regs 0 * 2 ^ (k % w) < 2 ^ E.W := by
    calc p.regs 0 * 2 ^ (k % w) ≤ 1 * 2 ^ (k % w) := Nat.mul_le_mul_right _ hBit
         _ = 2 ^ (k % w) := one_mul _
         _ < 2 ^ E.W := hPow
  have hOld : p.mem (memBase + k / w) < 2 ^ E.W := (Nat.le_add_right _ _).trans_lt hSum
  have hK : k < 2 ^ E.W := by omega
  have hDiv : k / w < 2 ^ E.W := (Nat.div_le_self _ _).trans_lt hK
  have hMod : k % w < 2 ^ E.W := (Nat.mod_lt k hw).trans
    (hWide.trans (Nat.lt_two_pow_self (n := E.W)))
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [crWriteInputBit, runBlock, execInstr, Nat.add_assoc]
  · simp [crWriteInputBit, runBlock, execInstr, Function.update, hCounter, hOne, Nat.mod_eq_of_lt hNext]
  · simp [crWriteInputBit, runBlock, execInstr, Function.update, hWidth, hBase, hCounter,
      Nat.mod_eq_of_lt hMod, Nat.mod_eq_of_lt hMask, Nat.mod_eq_of_lt hDiv,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hOld, Nat.mod_eq_of_lt hSum]
  · intro r hr0 hr1 hr2 hr3 hr12
    simp [crWriteInputBit, runBlock, execInstr, Function.update, hr0, hr1, hr2, hr3, hr12]
end LinearSetReconciliation327.Main
end
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
open Classical
def crPackPrefix {M : ℕ} (y : Fin M → ZMod 2) (k : ℕ) : Fin M → ZMod 2 :=
  fun i => if i.val < k then y i else 0
theorem crPackPrefix_step {M : ℕ} (w : ℕ) (y : Fin M → ZMod 2) (k : ℕ) (hk : k < M) (a : ℕ) :
    packMem w (crPackPrefix y (k + 1)) a = packMem w (crPackPrefix y k) a +
      if k / w = a ∧ y ⟨k, hk⟩ = 1 then 2 ^ (k % w) else 0 := by
  let d : Fin M := ⟨k, hk⟩
  let extra := if k / w = a ∧ y d = 1 then 2 ^ (k % w) else 0
  have hPoint : ∀ i : Fin M,
      (if i.val / w = a ∧ crPackPrefix y (k + 1) i = 1 then 2 ^ (i.val % w) else 0) =
        (if i.val / w = a ∧ crPackPrefix y k i = 1 then 2 ^ (i.val % w) else 0) +
          if i = d then extra else 0 := by
    intro i
    by_cases hi : i = d
    · subst i
      simp [crPackPrefix, d, extra]
    · have hNe : i.val ≠ k := by intro he; exact hi (Fin.ext he)
      have hLt : i.val < k + 1 ↔ i.val < k := by omega
      by_cases hki : i.val < k
      · simp [crPackPrefix, hi, hki, hLt.mpr hki]
      · have hki1 : ¬ i.val < k + 1 := fun h => hki (hLt.mp h)
        simp [crPackPrefix, hi, hki, hki1]
  change (∑ i : Fin M, if i.val / w = a ∧ crPackPrefix y (k + 1) i = 1 then 2 ^ (i.val % w) else 0) = _
  calc
    _ = ∑ i : Fin M,
        ((if i.val / w = a ∧ crPackPrefix y k i = 1 then 2 ^ (i.val % w) else 0) + if i = d then extra else 0) :=
      Finset.sum_congr rfl (fun i _ => hPoint i)
    _ = packMem w (crPackPrefix y k) a + extra := by
      rw [Finset.sum_add_distrib]
      simp [packMem]
theorem crBit_div_lt_words {bit M W : ℕ} (hW : 0 < W) (h : bit < M) : bit / W < wordsOf W M := by
  have h1 : bit + W ≤ M + W - 1 := by omega
  have h2 : (bit + W) / W ≤ (M + W - 1) / W := Nat.div_le_div_right h1
  have h3 : (bit + W) / W = bit / W + 1 := by
    rw [show bit + W = bit + 1 * W by rw [Nat.one_mul]]
    exact Nat.add_mul_div_right bit 1 hW
  rw [wordsOf]
  omega
theorem crPackPrefix_store {w M : ℕ} (hw : 0 < w) (y : Fin M → ZMod 2)
    (k : ℕ) (hk : k < M) (memBase bound : ℕ) (mem : ℕ → ℕ)
    (hAddr : k / w ≤ bound)
    (hView : ∀ a, a ≤ bound → mem (memBase + a) = packMem w (crPackPrefix y k) a) :
    ∀ a, a ≤ bound →
      Function.update mem (memBase + k / w)
        (mem (memBase + k / w) + if y ⟨k, hk⟩ = 1 then 2 ^ (k % w) else 0) (memBase + a) =
        packMem w (crPackPrefix y (k + 1)) a := by
  intro a ha
  by_cases hA : a = k / w
  · subst a
    rw [Function.update_self, hView _ hAddr, crPackPrefix_step w y k hk]
    simp
  · have hM : memBase + a ≠ memBase + k / w := by omega
    rw [Function.update_of_ne hM, hView a ha, crPackPrefix_step w y k hk]
    have hNot : ¬ (k / w = a ∧ y ⟨k, hk⟩ = 1) := fun h => hA h.1.symm
    rw [if_neg hNot, Nat.add_zero]
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def crCopyInputBit : List Instr := crReadInputBit ++ crWriteInputBit
theorem crCopyInputBit_length : crCopyInputBit.length = 14 := rfl
structure CRInputMeta (E : RAMEnv) (w M off memBase : ℕ) (p : RAMState) : Prop where
  offset : p.regs 5 = off
  source_width : p.regs 7 = w
  mem_base : p.regs 9 = memBase
  physical_width : p.regs 11 = E.W
  two : p.regs 13 = 2
  rows : p.regs 14 = M
  one : p.regs 15 = 1
structure CRInputInv (E : RAMEnv) (w M off memBase : ℕ) (y : Fin M → ZMod 2)
    (original : ℕ → ℕ) (k : ℕ) (p : RAMState) : Prop where
  params : CRInputMeta E w M off memBase p
  counter : p.regs 12 = k
  packed : ∀ a, a ≤ 2 ^ (w + 1) → p.mem (memBase + a) = packMem w (crPackPrefix y k) a
  low : ∀ a, a < memBase → p.mem a = original a
theorem crCopyInputBit_spec (E : RAMEnv) (p : RAMState) (w M off memBase k : ℕ)
    (y : Fin M → ZMod 2) (original : ℕ → ℕ) (hw : 0 < w) (hWide : w < E.W)
    (hWords : wordsOf w M ≤ 2 ^ w) (hSpan : off + M < 2 ^ E.W)
    (hMem : memBase + 2 ^ w < 2 ^ E.W)
    (hBelow : (off + M) / E.W < memBase)
    (hBits : ∀ i : Fin M, bitAt original E.W 0 (off + i.val) = if y i = 1 then 1 else 0)
    (hInv : CRInputInv E w M off memBase y original k p) (hk : k < M) :
    let out := runBlock crCopyInputBit E p
    out.pc = p.pc + 14 ∧ CRInputInv E w M off memBase y original (k + 1) out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r) ∧
      out.mem = Function.update p.mem (memBase + k / w) (packMem w (crPackPrefix y (k + 1)) (k / w)) := by
  let bit : ℕ := if y ⟨k, hk⟩ = 1 then 1 else 0
  have hBit : bit ≤ 1 := by dsimp [bit]; split_ifs <;> omega
  have hIndex : p.regs 5 + p.regs 12 < 2 ^ E.W := by rw [hInv.params.offset, hInv.counter]; omega
  have hNext : k + 1 < 2 ^ E.W := by omega
  have hAddressBound : k / w ≤ 2 ^ (w + 1) :=
    ((crBit_div_lt_words hw hk).le.trans hWords).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hAddr : memBase + k / w < 2 ^ E.W :=
    (Nat.add_le_add_left ((crBit_div_lt_words hw hk).le.trans hWords) memBase).trans_lt hMem
  have hReadBelow : (off + k) / E.W < memBase :=
    (Nat.div_le_div_right (by omega : off + k ≤ off + M)).trans_lt hBelow
  have hInput : bitAt p.mem E.W 0 (p.regs 5 + p.regs 12) = bit := by
    rw [hInv.params.offset, hInv.counter]
    have hLow : p.mem (0 + (off + k) / E.W) = original (0 + (off + k) / E.W) := by
      simpa only [Nat.zero_add] using hInv.low _ hReadBelow
    unfold bitAt
    rw [hLow]
    exact hBits ⟨k, hk⟩
  generalize hu : runBlock crReadInputBit E p = u
  have hU := crReadInputBit_spec E p (by omega) hInv.params.physical_width hInv.params.two hIndex
  rw [hu] at hU
  obtain ⟨hUpc, hUmem, hU0, hU1, hU2, hUfr⟩ := hU
  have hUbit : u.regs 0 = bit := hU0.trans hInput
  have hU7 : u.regs 7 = w := (hUfr 7 (by decide) (by decide) (by decide)).trans hInv.params.source_width
  have hU9 : u.regs 9 = memBase := (hUfr 9 (by decide) (by decide) (by decide)).trans hInv.params.mem_base
  have hU12 : u.regs 12 = k := (hUfr 12 (by decide) (by decide) (by decide)).trans hInv.counter
  have hU15 : u.regs 15 = 1 := (hUfr 15 (by decide) (by decide) (by decide)).trans hInv.params.one
  have hMask : bit * 2 ^ (k % w) = if y ⟨k, hk⟩ = 1 then 2 ^ (k % w) else 0 := by
    dsimp [bit]
    split_ifs <;> simp
  have hSumEq : u.mem (memBase + k / w) + u.regs 0 * 2 ^ (k % w) =
      packMem w (crPackPrefix y (k + 1)) (k / w) := by
    rw [hUmem, hUbit, hMask, hInv.packed _ hAddressBound, crPackPrefix_step w y k hk]
    simp
  have hSum : u.mem (memBase + k / w) + u.regs 0 * 2 ^ (k % w) < 2 ^ E.W := by
    rw [hSumEq]
    exact (packMem_lt w hw _ _).trans (Nat.pow_lt_pow_right (by norm_num) hWide)
  generalize ho : runBlock crWriteInputBit E u = out
  have hO := crWriteInputBit_spec E u w memBase k hw hWide hU7 hU9 hU12 hU15
    (by rw [hUbit]; exact hBit) hAddr hNext hSum
  rw [ho] at hO
  obtain ⟨hOpc, hO12, hOmem, hOfr⟩ := hO
  have hFrame : ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r := by
    intro r hr0 hr1 hr2 hr3 hr12
    exact (hOfr r hr0 hr1 hr2 hr3 hr12).trans (hUfr r hr0 hr1 hr2)
  have hMemOut : out.mem = Function.update p.mem (memBase + k / w)
      (p.mem (memBase + k / w) + if y ⟨k, hk⟩ = 1 then 2 ^ (k % w) else 0) := by
    rw [hOmem, hUmem, hUbit, hMask]
  have hExact : out.mem = Function.update p.mem (memBase + k / w)
      (packMem w (crPackPrefix y (k + 1)) (k / w)) := by
    rw [hOmem, hSumEq, hUmem]
  have hRun : runBlock crCopyInputBit E p = out := by rw [crCopyInputBit, runBlock_append, hu, ho]
  dsimp only
  rw [hRun]
  refine ⟨by omega, ?_, hFrame, hExact⟩
  refine ⟨?_, hO12, ?_, ?_⟩
  · exact ⟨(hFrame 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.offset,
      (hFrame 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.source_width,
      (hFrame 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.mem_base,
      (hFrame 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.physical_width,
      (hFrame 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.two,
      (hFrame 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.rows,
      (hFrame 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.one⟩
  · intro a ha
    rw [hMemOut]
    exact crPackPrefix_store hw y k hk memBase (2 ^ (w + 1)) p.mem hAddressBound hInv.packed a ha
  · intro a ha
    rw [hMemOut, Function.update_of_ne (Nat.ne_of_lt (ha.trans_le (Nat.le_add_right memBase (k / w))))]
    exact hInv.low a ha
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
def crCopyInputLoop (base done : ℕ) : List Instr :=
  [.lt 2 12 14, .jz 2 done] ++ (crCopyInputBit ++ [.jmp base])
theorem crInputInv_pc {E : RAMEnv} {w M off memBase k pc : ℕ} {y : Fin M → ZMod 2}
    {original : ℕ → ℕ} {p : RAMState} (h : CRInputInv E w M off memBase y original k p) :
    CRInputInv E w M off memBase y original k {p with pc := pc} := by
  exact ⟨⟨h.params.offset, h.params.source_width, h.params.mem_base, h.params.physical_width,
    h.params.two, h.params.rows, h.params.one⟩, h.counter, h.packed, h.low⟩
theorem crInputInv_reg2 {E : RAMEnv} {w M off memBase k pc value : ℕ} {y : Fin M → ZMod 2}
    {original : ℕ → ℕ} {p : RAMState} (h : CRInputInv E w M off memBase y original k p) :
    CRInputInv E w M off memBase y original k
      {p with pc := pc, regs := Function.update p.regs 2 value} := by
  let q := {p with pc := pc, regs := Function.update p.regs 2 value}
  have hF : ∀ r : Fin 16, r ≠ 2 → q.regs r = p.regs r := by
    intro r hr
    simp only [q, Function.update_of_ne hr]
  exact ⟨⟨(hF 5 (by decide)).trans h.params.offset, (hF 7 (by decide)).trans h.params.source_width,
    (hF 9 (by decide)).trans h.params.mem_base, (hF 11 (by decide)).trans h.params.physical_width,
    (hF 13 (by decide)).trans h.params.two, (hF 14 (by decide)).trans h.params.rows,
    (hF 15 (by decide)).trans h.params.one⟩, (hF 12 (by decide)).trans h.counter, h.packed, h.low⟩
theorem crCopyInput_guard (P : Program) (E : RAMEnv) (p : RAMState) (base done k M : ℕ)
    (hAt : At P base (crCopyInputLoop base done)) (hPc : p.pc = base)
    (hCounter : p.regs 12 = k) (hRows : p.regs 14 = M) (hW : 0 < E.W) :
    (step P E)^[2] p =
      {p with pc := if k < M then base + 2 else done, regs := Function.update p.regs 2 (if k < M then 1 else 0)} := by
  have hF0 : P[p.pc]? = some (.lt 2 12 14) := by
    have h := hAt 0 (by simp [crCopyInputLoop, crCopyInputBit_length])
    simpa only [crCopyInputLoop, List.cons_append, List.nil_append, List.getElem?_cons_zero, Nat.add_zero, hPc] using h
  have hF1 : P[p.pc + 1]? = some (.jz 2 done) := by
    have h := hAt 1 (by simp [crCopyInputLoop, crCopyInputBit_length])
    simpa only [crCopyInputLoop, List.cons_append, List.nil_append, List.getElem?_cons_succ,
      List.getElem?_cons_zero, hPc] using h
  have hOne : 1 < 2 ^ E.W := by
    have hPow : 2 ^ 1 ≤ 2 ^ E.W := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact (by decide : 1 < 2 ^ 1).trans_le hPow
  have hMask : (if k < M then 1 else 0) % 2 ^ E.W = if k < M then 1 else 0 := by
    split_ifs <;> simp [Nat.mod_eq_of_lt hOne]
  have hFirst : step P E p =
      {p with pc := p.pc + 1, regs := Function.update p.regs 2 (if k < M then 1 else 0)} := by
    rw [crStep_fetch P E p _ hF0]
    simp only [execInstr, hCounter, hRows, hMask]
  change step P E (step P E p) = _
  rw [hFirst, crStep_fetch P E {p with pc := p.pc + 1, regs := Function.update p.regs 2 (if k < M then 1 else 0)} _ hF1]
  by_cases hk : k < M <;> simp [execInstr, hk, hPc, Nat.add_assoc]
theorem crCopyInput_iteration (P : Program) (E : RAMEnv) (p : RAMState)
    (w M off memBase k base done : ℕ) (y : Fin M → ZMod 2) (original : ℕ → ℕ)
    (hw : 0 < w) (hWide : w < E.W) (hWords : wordsOf w M ≤ 2 ^ w)
    (hSpan : off + M < 2 ^ E.W) (hMem : memBase + 2 ^ w < 2 ^ E.W)
    (hBelow : (off + M) / E.W < memBase)
    (hBits : ∀ i : Fin M, bitAt original E.W 0 (off + i.val) = if y i = 1 then 1 else 0)
    (hAt : At P base (crCopyInputLoop base done)) (hPc : p.pc = base)
    (hInv : CRInputInv E w M off memBase y original k p) (hk : k < M) :
    ∃ out : RAMState, (step P E)^[17] p = out ∧ out.pc = base ∧
      CRInputInv E w M off memBase y original (k + 1) out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r) ∧
      (∀ a, (a < memBase ∨ memBase + 2 ^ (w + 1) < a) → out.mem a = p.mem a) := by
  let g := {p with pc := base + 2, regs := Function.update p.regs 2 1}
  have hGuard : (step P E)^[2] p = g := by
    have h := crCopyInput_guard P E p base done k M hAt hPc hInv.counter hInv.params.rows (by omega)
    simpa only [if_pos hk] using h
  have hG : CRInputInv E w M off memBase y original k g := crInputInv_reg2 hInv
  have hTail := crAt_suffix P base [.lt 2 12 14, .jz 2 done] (crCopyInputBit ++ [.jmp base]) hAt
  have hTailG : At P g.pc (crCopyInputBit ++ [.jmp base]) := by simpa using hTail
  have hBodyAt := crAt_prefix P g.pc crCopyInputBit [.jmp base] hTailG
  have hEnd := crAt_suffix P g.pc crCopyInputBit [.jmp base] hTailG
  have hJump : P[g.pc + crCopyInputBit.length]? = some (.jmp base) := by
    simpa only [Nat.add_zero, List.getElem?_cons_zero] using hEnd 0 (by simp)
  have hNo : NoBranch crCopyInputBit := by
    simp [crCopyInputBit, crReadInputBit, crWriteInputBit, NoBranch, Instr.NoBranchI]
  have hExec := crExecute_body_jump P E g crCopyInputBit base hNo hBodyAt hJump
  generalize hu : runBlock crCopyInputBit E g = u at hExec
  have hBody := crCopyInputBit_spec E g w M off memBase k y original hw hWide hWords hSpan hMem hBelow hBits hG hk
  rw [hu] at hBody
  obtain ⟨hUpc, hUInv, hFrame, hMemExact⟩ := hBody
  let out := {u with pc := base}
  refine ⟨out, ?_, rfl, crInputInv_pc hUInv, ?_, ?_⟩
  · rw [show 17 = 15 + 2 by omega, Function.iterate_add_apply, hGuard]
    simpa only [crCopyInputBit_length] using hExec
  · intro r hr0 hr1 hr2 hr3 hr12
    have hF := hFrame r hr0 hr1 hr2 hr3 hr12
    simpa only [g, out, Function.update_of_ne hr2] using hF
  · intro a ha
    have hBound : k / w ≤ 2 ^ (w + 1) :=
      ((crBit_div_lt_words hw hk).le.trans hWords).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hNe : a ≠ memBase + k / w := by
      rcases ha with ha | ha
      · exact Nat.ne_of_lt (ha.trans_le (Nat.le_add_right memBase (k / w)))
      · exact (Nat.ne_of_lt ((Nat.add_le_add_left hBound memBase).trans_lt ha)).symm
    change u.mem a = p.mem a
    rw [hMemExact, Function.update_of_ne hNe]
end LinearSetReconciliation327.Main
end
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
open Classical
theorem crPackPrefix_all {M : ℕ} (y : Fin M → ZMod 2) : crPackPrefix y M = y := by
  funext i
  simp [crPackPrefix, i.isLt]
theorem crPackMem_above {w M : ℕ} (hw : 0 < w) (y : Fin M → ZMod 2) (a : ℕ)
    (ha : wordsOf w M ≤ a) : packMem w y a = 0 := by
  unfold packMem
  apply Finset.sum_eq_zero
  intro i hi
  have hI := crBit_div_lt_words hw i.isLt
  have hNe : i.val / w ≠ a := by omega
  rw [if_neg (fun h => hNe h.1)]
theorem crDecoderStart_mem {w M : ℕ} (hw : 0 < w) (y : Fin M → ZMod 2) (a : ℕ) :
    (decoderStart w y []).mem a = packMem w y a := by
  change hintMem w y [] a = _
  unfold hintMem
  split_ifs with h
  · rfl
  · change (0 : ℕ) = packMem w y a
    exact (crPackMem_above hw y a (by omega)).symm
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crCopyInput_remaining (P : Program) (E : RAMEnv)
    (w M off memBase base done : ℕ) (y : Fin M → ZMod 2) (original : ℕ → ℕ)
    (hw : 0 < w) (hWide : w < E.W) (hWords : wordsOf w M ≤ 2 ^ w)
    (hSpan : off + M < 2 ^ E.W) (hMem : memBase + 2 ^ w < 2 ^ E.W)
    (hBelow : (off + M) / E.W < memBase)
    (hBits : ∀ i : Fin M, bitAt original E.W 0 (off + i.val) = if y i = 1 then 1 else 0)
    (hAt : At P base (crCopyInputLoop base done)) :
    ∀ (remaining k : ℕ) (p : RAMState), k + remaining = M → p.pc = base →
      CRInputInv E w M off memBase y original k p →
      ∃ out : RAMState, (step P E)^[17 * remaining + 2] p = out ∧ out.pc = done ∧
        CRInputInv E w M off memBase y original M out ∧
        (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r) ∧
        (∀ a, (a < memBase ∨ memBase + 2 ^ (w + 1) < a) → out.mem a = p.mem a) := by
  intro remaining
  induction remaining with
  | zero =>
    intro k p hEq hPc hInv
    have hKM : k = M := by omega
    subst k
    let out := {p with pc := done, regs := Function.update p.regs 2 0}
    refine ⟨out, ?_, rfl, crInputInv_reg2 hInv, ?_, ?_⟩
    · have h := crCopyInput_guard P E p base done M M hAt hPc hInv.counter hInv.params.rows (by omega)
      simpa only [Nat.mul_zero, Nat.zero_add, if_neg (Nat.lt_irrefl M)] using h
    · intro r hr0 hr1 hr2 hr3 hr12
      simp only [out, Function.update_of_ne hr2]
    · intro a ha
      rfl
  | succ remaining ih =>
    intro k p hEq hPc hInv
    have hk : k < M := by omega
    obtain ⟨mid, hRun, hMidPc, hMidInv, hFrame, hMemFrame⟩ := crCopyInput_iteration P E p
      w M off memBase k base done y original hw hWide hWords hSpan hMem hBelow hBits hAt hPc hInv hk
    obtain ⟨out, hRest, hDone, hFinal, hRestFrame, hRestMem⟩ := ih (k + 1) mid (by omega) hMidPc hMidInv
    refine ⟨out, ?_, hDone, hFinal, ?_, ?_⟩
    · rw [show 17 * (remaining + 1) + 2 = (17 * remaining + 2) + 17 by omega,
        Function.iterate_add_apply, hRun, hRest]
    · intro r hr0 hr1 hr2 hr3 hr12
      exact (hRestFrame r hr0 hr1 hr2 hr3 hr12).trans (hFrame r hr0 hr1 hr2 hr3 hr12)
    · intro a ha
      exact (hRestMem a ha).trans (hMemFrame a ha)
theorem crCopyInput_full (P : Program) (E : RAMEnv) (p : RAMState)
    (w M off memBase base done : ℕ) (y : Fin M → ZMod 2)
    (hw : 0 < w) (hWide : w < E.W) (hWords : wordsOf w M ≤ 2 ^ w)
    (hSpan : off + M < 2 ^ E.W) (hMem : memBase + 2 ^ w < 2 ^ E.W)
    (hBelow : (off + M) / E.W < memBase)
    (hBits : ∀ i : Fin M, bitAt p.mem E.W 0 (off + i.val) = if y i = 1 then 1 else 0)
    (hAt : At P base (crCopyInputLoop base done)) (hPc : p.pc = base)
    (hMeta : CRInputMeta E w M off memBase p) (hCounter : p.regs 12 = 0)
    (hFresh : ∀ a, a ≤ 2 ^ (w + 1) → p.mem (memBase + a) = 0) :
    ∃ out : RAMState, (step P E)^[17 * M + 2] p = out ∧ out.pc = done ∧
      CRInputMeta E w M off memBase out ∧ out.regs 12 = M ∧
      (∀ a, a ≤ 2 ^ (w + 1) → out.mem (memBase + a) = (decoderStart w y []).mem a) ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r) ∧
      (∀ a, (a < memBase ∨ memBase + 2 ^ (w + 1) < a) → out.mem a = p.mem a) := by
  have hStart : CRInputInv E w M off memBase y p.mem 0 p := by
    refine ⟨hMeta, hCounter, ?_, ?_⟩
    · intro a ha
      simpa [packMem, crPackPrefix] using hFresh a ha
    · intro a ha
      rfl
  obtain ⟨out, hRun, hDone, hFinal, hFrame, hMemFrame⟩ := crCopyInput_remaining P E
    w M off memBase base done y p.mem hw hWide hWords hSpan hMem hBelow hBits hAt M 0 p (by omega) hPc hStart
  refine ⟨out, hRun, hDone, hFinal.params, hFinal.counter, ?_, hFrame, hMemFrame⟩
  intro a ha
  have h := hFinal.packed a ha
  rw [crPackPrefix_all] at h
  rw [crDecoderStart_mem hw y a]
  exact h
end LinearSetReconciliation327.Main
end
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
universe u
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crWordsOf_divmod (w M : ℕ) (hw : 0 < w) :
    wordsOf w M = M / w + if M % w = 0 then 0 else 1 := by
  have hOne : 1 ≤ M % w + w := by omega
  have hSplit : M + w - 1 = w * (M / w) + (M % w + w - 1) := by
    have h := Nat.div_add_mod M w
    omega
  rw [wordsOf, hSplit, Nat.mul_add_div hw]
  by_cases hR : M % w = 0
  · rw [hR, Nat.zero_add, if_pos rfl, Nat.div_eq_of_lt (by omega : w - 1 < w)]
  · have hPos : 0 < M % w := Nat.pos_of_ne_zero hR
    have hRem : M % w - 1 < w := (Nat.sub_le _ _).trans_lt (Nat.mod_lt M hw)
    have hNum : M % w + w - 1 = (M % w - 1) + 1 * w := by omega
    rw [if_neg hR, hNum, Nat.add_mul_div_right _ 1 hw, Nat.div_eq_of_lt hRem, Nat.zero_add]
def crWordCount : List Instr := [.div 1 14 7, .mod 0 14 7, .imm 2 0, .lt 0 2 0, .add 1 1 0]
theorem crWordCount_spec (E : RAMEnv) (p : RAMState) (w M : ℕ)
    (hw : 0 < w) (hWide : w < E.W) (hRows : p.regs 14 = M) (hWidth : p.regs 7 = w)
    (hM : M < 2 ^ E.W) (hWords : wordsOf w M ≤ 2 ^ w) :
    let out := runBlock crWordCount E p
    out.pc = p.pc + 5 ∧ out.mem = p.mem ∧ out.regs 1 = wordsOf w M ∧
      ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → out.regs r = p.regs r := by
  have hDiv : M / w < 2 ^ E.W := (Nat.div_le_self _ _).trans_lt hM
  have hMod : M % w < 2 ^ E.W := (Nat.mod_lt M hw).trans
    (hWide.trans (Nat.lt_two_pow_self (n := E.W)))
  have hOne : 1 < 2 ^ E.W :=
    (by decide : 1 < 2 ^ 1).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hCount : wordsOf w M < 2 ^ E.W := hWords.trans_lt (Nat.pow_lt_pow_right (by norm_num) hWide)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [crWordCount, runBlock, execInstr, Nat.add_assoc]
  · rfl
  · by_cases hr : M % w = 0
    · simp [crWordCount, runBlock, execInstr, Function.update, hRows, hWidth,
        Nat.mod_eq_of_lt hDiv, Nat.mod_eq_of_lt hMod, hr, crWordsOf_divmod w M hw]
    · have hPos : 0 < M % w := Nat.pos_of_ne_zero hr
      have hAdd : M / w + 1 < 2 ^ E.W := by simpa only [crWordsOf_divmod w M hw, if_neg hr] using hCount
      simp [crWordCount, runBlock, execInstr, Function.update, hRows, hWidth,
        Nat.mod_eq_of_lt hDiv, Nat.mod_eq_of_lt hMod, Nat.mod_eq_of_lt hOne,
        Nat.mod_eq_of_lt hAdd, hPos, hr, crWordsOf_divmod w M hw]
  · intro r hr0 hr1 hr2
    simp [crWordCount, runBlock, execInstr, Function.update, hr0, hr1, hr2]
end LinearSetReconciliation327.Main
end

#print axioms LinearSetReconciliation327.Main.crRFInit_spec


