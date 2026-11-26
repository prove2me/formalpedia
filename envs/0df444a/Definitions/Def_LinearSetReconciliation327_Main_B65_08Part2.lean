-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_08Part2
-- name    : LinearSetReconciliation327_Main_B65_08Part2
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T07:17:28.653198+00:00
-- url     : https://prove2.me/theorems/25c4cbcd-01f2-5c4e-ac52-7f4e6ec92216
-- title:
--   Theorem 6.5 supporting machine proof B65_08Part2
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_08Part1
set_option autoImplicit false

section S_HintStageBit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintStageWrite_spec (E : RAMEnv) (p : RAMState) (w memBase k : ℕ)
    (hw : 0 < w) (hWide : w ≤ E.W) (hWidth : p.regs 7 = w) (hBase : p.regs 9 = memBase)
    (hCounter : p.regs 12 = k) (hOne : p.regs 15 = 1) (hBit : p.regs 0 ≤ 1)
    (hAddr : memBase + k / w < 2 ^ E.W) (hNext : k + 1 < 2 ^ E.W)
    (hSum : p.mem (memBase + k / w) + p.regs 0 * 2 ^ (k % w) < 2 ^ E.W) :
    let out := runBlock crWriteInputBit E p
    out.pc = p.pc + 8 ∧ out.regs 12 = k + 1 ∧
      out.mem = Function.update p.mem (memBase + k / w)
        (p.mem (memBase + k / w) + p.regs 0 * 2 ^ (k % w)) ∧
      ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r := by
  have hPow : 2 ^ (k % w) < 2 ^ E.W :=
    Nat.pow_lt_pow_right (by norm_num) ((Nat.mod_lt k hw).trans_le hWide)
  have hMask : p.regs 0 * 2 ^ (k % w) < 2 ^ E.W := by
    calc p.regs 0 * 2 ^ (k % w) ≤ 1 * 2 ^ (k % w) := Nat.mul_le_mul_right _ hBit
         _ = 2 ^ (k % w) := one_mul _
         _ < 2 ^ E.W := hPow
  have hOld : p.mem (memBase + k / w) < 2 ^ E.W := (Nat.le_add_right _ _).trans_lt hSum
  have hK : k < 2 ^ E.W := by omega
  have hDiv : k / w < 2 ^ E.W := (Nat.div_le_self _ _).trans_lt hK
  have hMod : k % w < 2 ^ E.W := (Nat.mod_lt k hw).trans
    (hWide.trans_lt (Nat.lt_two_pow_self (n := E.W)))
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [crWriteInputBit, runBlock, execInstr, Nat.add_assoc]
  · simp [crWriteInputBit, runBlock, execInstr, Function.update, hCounter, hOne, Nat.mod_eq_of_lt hNext]
  · simp [crWriteInputBit, runBlock, execInstr, Function.update, hWidth, hBase, hCounter,
      Nat.mod_eq_of_lt hMod, Nat.mod_eq_of_lt hMask, Nat.mod_eq_of_lt hDiv,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hOld, Nat.mod_eq_of_lt hSum]
  · intro r hr0 hr1 hr2 hr3 hr12
    simp [crWriteInputBit, runBlock, execInstr, Function.update, hr0, hr1, hr2, hr3, hr12]

structure HintStageArgs (E : RAMEnv) (w M off memBase : ℕ) (p : RAMState) : Prop where
  offset : p.regs 5 = off
  source_width : p.regs 7 = w
  mem_base : p.regs 9 = memBase
  physical_width : p.regs 11 = E.W
  two : p.regs 13 = 2
  rows : p.regs 6 = M
  one : p.regs 15 = 1

structure HintStageInv (E : RAMEnv) (w M off memBase : ℕ) (y : Fin M → ZMod 2)
    (original : ℕ → ℕ) (k : ℕ) (p : RAMState) : Prop where
  params : HintStageArgs E w M off memBase p
  counter : p.regs 12 = k
  packed : ∀ a < wordsOf w M, p.mem (memBase + a) = packMem w (crPackPrefix y k) a
  frame : CRMemFrame memBase (memBase + wordsOf w M) original p.mem

theorem hintStageBit_spec (E : RAMEnv) (p : RAMState) (w M off memBase k : ℕ)
    (y : Fin M → ZMod 2) (original : ℕ → ℕ) (hw : 0 < w) (hWide : w ≤ E.W)
    (hSpan : off + M < 2 ^ E.W) (hMem : memBase + wordsOf w M ≤ 2 ^ E.W)
    (hBelow : (off + M) / E.W < memBase)
    (hBits : ∀ i : Fin M, bitAt original E.W 0 (off + i.val) = if y i = 1 then 1 else 0)
    (hInv : HintStageInv E w M off memBase y original k p) (hk : k < M) :
    let out := runBlock crCopyInputBit E p
    out.pc = p.pc + 14 ∧ HintStageInv E w M off memBase y original (k + 1) out ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 12 → out.regs r = p.regs r) ∧
      out.mem = Function.update p.mem (memBase + k / w) (packMem w (crPackPrefix y (k + 1)) (k / w)) := by
  let bit : ℕ := if y ⟨k, hk⟩ = 1 then 1 else 0
  have hBit : bit ≤ 1 := by dsimp [bit]; split_ifs <;> omega
  have hIndex : p.regs 5 + p.regs 12 < 2 ^ E.W := by rw [hInv.params.offset, hInv.counter]; omega
  have hNext : k + 1 < 2 ^ E.W := by omega
  have hAddressBound : k / w < wordsOf w M := crBit_div_lt_words hw hk
  have hAddr : memBase + k / w < 2 ^ E.W := by omega
  have hReadBelow : (off + k) / E.W < memBase :=
    (Nat.div_le_div_right (by omega : off + k ≤ off + M)).trans_lt hBelow
  have hInput : bitAt p.mem E.W 0 (p.regs 5 + p.regs 12) = bit := by
    rw [hInv.params.offset, hInv.counter]
    have hLow : p.mem (0 + (off + k) / E.W) = original (0 + (off + k) / E.W) := by
      simpa only [Nat.zero_add] using hInv.frame _ (Or.inl hReadBelow)
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
    exact (packMem_lt w hw _ _).trans_le (Nat.pow_le_pow_right (by norm_num) hWide)
  generalize ho : runBlock crWriteInputBit E u = out
  have hO := hintStageWrite_spec E u w memBase k hw hWide hU7 hU9 hU12 hU15
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
      (hFrame 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.rows,
      (hFrame 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.params.one⟩
  · intro a ha
    rw [hMemOut]
    exact crPackPrefix_store hw y k hk memBase (wordsOf w M - 1) p.mem (by omega)
      (fun t ht => hInv.packed t (by omega)) a (by omega)
  · intro a ha
    have hNe : a ≠ memBase + k / w := by
      rcases ha with h | h
      · exact Nat.ne_of_lt (h.trans_le (Nat.le_add_right _ _))
      · exact Nat.ne_of_gt ((Nat.add_lt_add_left hAddressBound memBase).trans_le h)
    rw [hMemOut, Function.update_of_ne hNe, hInv.frame a ha]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStageBit_spec
end S_HintStageBit20261120
section S_HintStage20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintStageLoop : Stmt := .loop (.lt 2 12 6) (.code crCopyInputBit)
def hintStageStmt : Stmt := .seq (.code [.imm 12 0]) hintStageLoop

structure HintStagePre (E : RAMEnv) (w count off dest : ℕ) : Prop where
  word : 1 < 2 ^ E.W
  width_pos : 0 < w
  width_le : w ≤ E.W
  input_span : off + count < 2 ^ E.W
  destination : dest + wordsOf w count ≤ 2 ^ E.W
  separate : (off + count) / E.W < dest

theorem hintStageLoop_sem (P : Program) (E : RAMEnv) (state initial : RAMState)
    (w count off dest base : ℕ) (pre : HintStagePre E w count off dest)
    (y : Fin count → ZMod 2) (hBits : ∀ i : Fin count,
      bitAt initial.mem E.W 0 (off + i.val) = if y i = 1 then 1 else 0)
    (inv : HintStageInv E w count off dest y initial.mem 0 state)
    (hContext : state.regs 14 = initial.regs 14)
    (hAt : At P base (hintStageLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 17) state (fun k out => k ≤ 17 * count + 2 ∧
      HintStageInv E w count off dest y initial.mem count out ∧ out.regs 14 = initial.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left s => ∃ i, i + left = count ∧
    HintStageInv E w count off dest y initial.mem i s ∧ s.regs 14 = initial.regs 14
  have hIpc : ∀ left s pc, I left s → I left {s with pc := pc} := by
    rintro left s pc ⟨i, hi, h, hc⟩
    exact ⟨i, hi, ⟨⟨h.params.offset, h.params.source_width, h.params.mem_base, h.params.physical_width,
      h.params.two, h.params.rows, h.params.one⟩,
      h.counter, h.packed, h.frame⟩, hc⟩
  have hTest : ∀ left s, I left s → I left (runBlock (Cond.lt 2 12 6).code E s) := by
    rintro left s ⟨i, hi, h, hc⟩
    refine ⟨i, hi, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, h.packed, h.frame⟩, ?_⟩
    all_goals simp [Cond.code, runBlock, execInstr, h.params.offset, h.params.source_width, h.params.mem_base, h.params.physical_width,
      h.params.two, h.params.rows, h.params.one, h.counter, hc]
  have hGo : ∀ left s, I (left + 1) s → (Cond.lt 2 12 6).eval s := by
    rintro left s ⟨i, hi, h, hc⟩
    change s.regs 12 < s.regs 6
    rw [h.counter, h.params.rows]; omega
  have hStop : ∀ s, I 0 s → ¬ (Cond.lt 2 12 6).eval s := by
    rintro s ⟨i, hi, h, hc⟩
    change ¬ s.regs 12 < s.regs 6
    rw [h.counter, h.params.rows]; omega
  have hBodyAt : At P (base + 2) crCopyInputBit := (at_loop hAt).2.2.1
  have hBody : ∀ left s, I (left + 1) s → s.pc = base + (Cond.lt 2 12 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 12 6).code.length + 1)
        (base + (Cond.lt 2 12 6).code.length + 1 + (Stmt.code crCopyInputBit).len) s
        (fun k out => k ≤ 14 ∧ I left out) := by
    rintro left s ⟨i, hi, h, hc⟩ hStart
    have hp : s.pc = base + 2 := by exact hStart
    have hNative := Sem.block P E (base + 2) crCopyInputBit s hBodyAt
      (by simp [crCopyInputBit, crReadInputBit, crWriteInputBit, NoBranch, Instr.NoBranchI]) hp
    apply Sem.mono hNative
    rintro k out ⟨hk, rfl⟩
    obtain ⟨_, hNext, hRegs, _⟩ := hintStageBit_spec E s w count off dest i y initial.mem
      pre.width_pos pre.width_le pre.input_span pre.destination pre.separate hBits h (by omega)
    exact ⟨hk.le, i + 1, by omega, hNext, (hRegs 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 12 6) (.code crCopyInputBit) hAt pre.word I 14
    hIpc hTest hGo hStop hBody count state ⟨0, by omega, inv, hContext⟩ hPc
  apply Sem.mono hNative
  rintro k out ⟨hk, i, hi, h, hc⟩
  have he : i = count := by omega
  exact ⟨hk, he ▸ h, hc⟩

theorem hintStageStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (w count off dest base : ℕ) (pre : HintStagePre E w count off dest)
    (y : Fin count → ZMod 2) (args : HintStageArgs E w count off dest state)
    (hBits : ∀ i : Fin count, bitAt state.mem E.W 0 (off + i.val) = if y i = 1 then 1 else 0)
    (hClear : ∀ a < wordsOf w count, state.mem (dest + a) = 0)
    (hAt : At P base (hintStageStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 18) state (fun k out => k ≤ 17 * count + 3 ∧
      (∀ a < wordsOf w count, out.mem (dest + a) = packMem w y a) ∧
      out.regs 14 = state.regs 14 ∧ CRMemFrame dest (dest + wordsOf w count) state.mem out.mem) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  let mid := runBlock [.imm 12 0] E state
  have hRunI : (step P E)^[1] state = mid :=
    iterate_runBlock_of_at P E [.imm 12 0] state (by rwa [hPc])
      (by simp [NoBranch, Instr.NoBranchI])
  have hInv : HintStageInv E w count off dest y state.mem 0 mid := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun _ _ => rfl⟩
    all_goals simp [mid, runBlock, execInstr, args.offset, args.source_width, args.mem_base,
      args.physical_width, args.two, args.rows, args.one]
    intro a ha
    simpa [crPackPrefix, packMem, mid, runBlock, execInstr] using hClear a ha
  have hPcI : mid.pc = base + 1 := by simp [mid, runBlock, execInstr, hPc]
  obtain ⟨_, k, out, hRun, hEnd, hk, h, hc⟩ :=
    hintStageLoop_sem P E mid state w count off dest (base + 1) pre y hBits hInv rfl hLoopAt hPcI
  refine ⟨hPc, k + 1, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega, ?_, hc, h.frame⟩
  have hPrefix : crPackPrefix y count = y := by
    funext i
    exact if_pos i.isLt
  simpa only [hPrefix] using h.packed

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStageStmt_sem
end S_HintStage20261120
section S_HintUnpackBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintUnpackWrite : List Instr := [.add 3 4 12, .store 3 0, .add 12 12 15]
def hintUnpackBody : List Instr := crReadInputBit ++ hintUnpackWrite

structure HintUnpackArgs (E : RAMEnv) (dest offset count : ℕ) (s : RAMState) : Prop where
  destination : s.regs 4 = dest
  offset_value : s.regs 5 = offset
  length : s.regs 6 = count
  width : s.regs 11 = E.W
  two : s.regs 13 = 2
  one : s.regs 15 = 1

theorem hintUnpackBody_spec (E : RAMEnv) (s : RAMState) (dest offset count i : ℕ)
    (hWidth : 0 < E.W) (hD : dest + i < 2 ^ E.W)
    (hS : offset + i < 2 ^ E.W) (hNext : i + 1 < 2 ^ E.W)
    (args : HintUnpackArgs E dest offset count s) (hIndex : s.regs 12 = i) :
    let out := runBlock hintUnpackBody E s
    out.pc = s.pc + 9 ∧ out.regs 12 = i + 1 ∧ HintUnpackArgs E dest offset count out ∧
      out.regs 14 = s.regs 14 ∧
      out.mem = Function.update s.mem (dest + i) (bitAt s.mem E.W 0 (offset + i)) := by
  have read := crReadInputBit_spec E s hWidth args.width args.two (by rw [args.offset_value, hIndex]; exact hS)
  generalize hr : runBlock crReadInputBit E s = mid at read
  obtain ⟨hPc, hMem, hBit, _, _, hRegs⟩ := read
  have hMid4 := (hRegs 4 (by decide) (by decide) (by decide)).trans args.destination
  have hMid12 := (hRegs 12 (by decide) (by decide) (by decide)).trans hIndex
  have hMid15 := (hRegs 15 (by decide) (by decide) (by decide)).trans args.one
  have hMid0 : mid.regs 0 = bitAt s.mem E.W 0 (offset + i) := by
    rw [hBit, args.offset_value, hIndex]
  dsimp only
  rw [hintUnpackBody, runBlock_append, hr]
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [hintUnpackWrite, runBlock, execInstr, hPc]
  · simp [hintUnpackWrite, runBlock, execInstr, hMid12, hMid15, Nat.mod_eq_of_lt hNext]
  · simpa [hintUnpackWrite, runBlock, execInstr] using hMid4
  · simpa [hintUnpackWrite, runBlock, execInstr] using (hRegs 5 (by decide) (by decide) (by decide)).trans args.offset_value
  · simpa [hintUnpackWrite, runBlock, execInstr] using (hRegs 6 (by decide) (by decide) (by decide)).trans args.length
  · simpa [hintUnpackWrite, runBlock, execInstr] using (hRegs 11 (by decide) (by decide) (by decide)).trans args.width
  · simpa [hintUnpackWrite, runBlock, execInstr] using (hRegs 13 (by decide) (by decide) (by decide)).trans args.two
  · simpa [hintUnpackWrite, runBlock, execInstr] using hMid15
  · simpa [hintUnpackWrite, runBlock, execInstr] using hRegs 14 (by decide) (by decide) (by decide)
  · simp [hintUnpackWrite, runBlock, execInstr, hMid4, hMid12, hMid0, hMem, Nat.mod_eq_of_lt hD]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintUnpackBody_spec
end S_HintUnpackBody20261120
section S_HintUnpack20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintUnpackLoop : Stmt := .loop (.lt 2 12 6) (.code hintUnpackBody)
def hintUnpackStmt : Stmt := .seq (.code [.imm 12 0]) hintUnpackLoop

structure HintUnpackPre (E : RAMEnv) (dest offset count : ℕ) : Prop where
  positive : 0 < E.W
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  destination : dest + count ≤ 2 ^ E.W
  offset_span : offset + count ≤ 2 ^ E.W
  input_before : (offset + count) / E.W < dest

structure HintUnpackInv (E : RAMEnv) (dest offset count index : ℕ)
    (initial : RAMState) (state : RAMState) : Prop where
  args : HintUnpackArgs E dest offset count state
  position : state.regs 12 = index
  context : state.regs 14 = initial.regs 14
  data : ∀ i < index, state.mem (dest + i) = bitAt initial.mem E.W 0 (offset + i)
  frame : CRMemFrame dest (dest + count) initial.mem state.mem

theorem hintUnpackInv_step (E : RAMEnv) (state initial : RAMState)
    (dest offset count i : ℕ) (pre : HintUnpackPre E dest offset count)
    (inv : HintUnpackInv E dest offset count i initial state) (hi : i < count) :
    HintUnpackInv E dest offset count (i + 1) initial (runBlock hintUnpackBody E state) := by
  classical
  have hd : dest + i < 2 ^ E.W := by have := pre.destination; omega
  have hs : offset + i < 2 ^ E.W := by have := pre.offset_span; omega
  have hn : i + 1 < 2 ^ E.W := by have := pre.count_fit; omega
  have hRead : bitAt state.mem E.W 0 (offset + i) = bitAt initial.mem E.W 0 (offset + i) := by
    unfold bitAt
    rw [Nat.zero_add, inv.frame]
    apply Or.inl
    exact (Nat.div_le_div_right (by omega : offset + i ≤ offset + count)).trans_lt pre.input_before
  obtain ⟨_, hIter, hArgs, hCtx, hMem⟩ :=
    hintUnpackBody_spec E state dest offset count i pre.positive hd hs hn inv.args inv.position
  refine ⟨hArgs, hIter, hCtx.trans inv.context, ?_, ?_⟩
  · intro j hj
    by_cases h : j = i
    · subst j; simp [hMem, hRead]
    · rw [hMem, Function.update_of_ne (by omega : dest + j ≠ dest + i)]
      exact inv.data j (by omega)
  · intro address hAway
    have hne : address ≠ dest + i := by rcases hAway with h | h <;> omega
    rw [hMem, Function.update_of_ne hne, inv.frame address hAway]

theorem hintUnpackLoop_sem (P : Program) (E : RAMEnv) (state initial : RAMState)
    (dest offset count base : ℕ) (pre : HintUnpackPre E dest offset count)
    (inv : HintUnpackInv E dest offset count 0 initial state)
    (hAt : At P base (hintUnpackLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 12) state (fun k out => k ≤ 12 * count + 2 ∧
      HintUnpackInv E dest offset count count initial out) := by
  let I : ℕ → RAMState → Prop := fun left s => ∃ i, i + left = count ∧
    HintUnpackInv E dest offset count i initial s
  have hIpc : ∀ left s pc, I left s → I left {s with pc := pc} := by
    rintro left s pc ⟨i, hi, h⟩
    exact ⟨i, hi, ⟨⟨h.args.destination, h.args.offset_value, h.args.length,
      h.args.width, h.args.two, h.args.one⟩,
      h.position, h.context, h.data, h.frame⟩⟩
  have hTest : ∀ left s, I left s → I left (runBlock (Cond.lt 2 12 6).code E s) := by
    rintro left s ⟨i, hi, h⟩
    refine ⟨i, hi, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, h.data, h.frame⟩⟩
    all_goals simp [Cond.code, runBlock, execInstr, h.args.destination, h.args.offset_value,
      h.args.length, h.args.width, h.args.two, h.args.one, h.position, h.context]
  have hGo : ∀ left s, I (left + 1) s → (Cond.lt 2 12 6).eval s := by
    rintro left s ⟨i, hi, h⟩
    change s.regs 12 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hStop : ∀ s, I 0 s → ¬ (Cond.lt 2 12 6).eval s := by
    rintro s ⟨i, hi, h⟩
    change ¬ s.regs 12 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hBodyAt : At P (base + 2) hintUnpackBody := (at_loop hAt).2.2.1
  have hBody : ∀ left s, I (left + 1) s → s.pc = base + (Cond.lt 2 12 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 12 6).code.length + 1)
        (base + (Cond.lt 2 12 6).code.length + 1 + (Stmt.code hintUnpackBody).len) s
        (fun k out => k ≤ 9 ∧ I left out) := by
    rintro left s ⟨i, hi, h⟩ hStart
    have hp : s.pc = base + 2 := by exact hStart
    have hNative := Sem.block P E (base + 2) hintUnpackBody s hBodyAt
      (by simp [hintUnpackBody, crReadInputBit, hintUnpackWrite, NoBranch, Instr.NoBranchI]) hp
    apply Sem.mono hNative
    rintro k out ⟨hk, rfl⟩
    exact ⟨hk.le, i + 1, by omega, hintUnpackInv_step E s initial dest offset count i pre h (by omega)⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 12 6) (.code hintUnpackBody) hAt pre.word I 9
    hIpc hTest hGo hStop hBody count state ⟨0, by omega, inv⟩ hPc
  apply Sem.mono hNative
  rintro k out ⟨hk, i, hi, h⟩
  have he : i = count := by omega
  exact ⟨hk, he ▸ h⟩

theorem hintUnpackStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest offset count base : ℕ) (pre : HintUnpackPre E dest offset count)
    (args : HintUnpackArgs E dest offset count state)
    (hAt : At P base (hintUnpackStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 13) state (fun k out => k ≤ 12 * count + 3 ∧
      HintUnpackInv E dest offset count count state out) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  let mid := runBlock [.imm 12 0] E state
  have hRunI : (step P E)^[1] state = mid :=
    iterate_runBlock_of_at P E [.imm 12 0] state (by rwa [hPc])
      (by simp [NoBranch, Instr.NoBranchI])
  have hInv : HintUnpackInv E dest offset count 0 state mid := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, (by omega), fun _ _ => rfl⟩
    all_goals simp [mid, runBlock, execInstr, args.destination, args.offset_value, args.length, args.width, args.two, args.one]
  have hPcI : mid.pc = base + 1 := by simp [mid, runBlock, execInstr, hPc]
  obtain ⟨_, k, out, hRun, hEnd, hk, h⟩ :=
    hintUnpackLoop_sem P E mid state dest offset count (base + 1) pre hInv hLoopAt hPcI
  exact ⟨hPc, k + 1, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega, h⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintUnpackStmt_sem
end S_HintUnpack20261120
section S_HintUnpackAction20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintUnpackSetup : List Instr :=
  [.imm 15 1, .qDet 4 6, .add 3 6 15, .qDet 5 3, .add 3 3 15, .qDet 11 3,
    .add 3 3 15, .qDet 6 3, .imm 13 2]

def hintUnpackAction : Stmt := .seq (.code hintUnpackSetup) hintUnpackStmt

structure HintUnpackTable (E : RAMEnv) (descriptor dest offset count : ℕ) : Prop where
  word : 2 < 2 ^ E.W
  table_span : descriptor + 3 < 2 ^ E.W
  dest_fit : dest < 2 ^ E.W
  offset_fit : offset < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  dest_address : E.det descriptor = dest
  offset_value : E.det (descriptor + 1) = offset
  word_width : E.det (descriptor + 2) = E.W
  length : E.det (descriptor + 3) = count

theorem hintUnpackSetup_spec (E : RAMEnv) (s : RAMState) (descriptor dest offset count : ℕ)
    (hTable : HintUnpackTable E descriptor dest offset count) (hArg : s.regs 6 = descriptor) :
    let out := runBlock hintUnpackSetup E s
    out.pc = s.pc + 9 ∧ out.mem = s.mem ∧ out.regs 14 = s.regs 14 ∧ HintUnpackArgs E dest offset count out := by
  have hSpan := hTable.table_span
  have hWord := hTable.word
  have hOne : 1 < 2 ^ E.W := by omega
  have h1 : descriptor + 1 < 2 ^ E.W := by omega
  have h2 : descriptor + 1 + 1 < 2 ^ E.W := by omega
  have h3 : descriptor + 1 + 1 + 1 < 2 ^ E.W := by omega
  have hWidth : E.W < 2 ^ E.W := Nat.lt_two_pow_self
  refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintUnpackSetup, runBlock, execInstr, hArg, hTable.dest_address, hTable.offset_value,
      hTable.word_width, hTable.length, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hTable.dest_fit, Nat.mod_eq_of_lt hTable.offset_fit,
      Nat.mod_eq_of_lt hTable.count_fit, Nat.mod_eq_of_lt hWidth]

theorem hintUnpackAction_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor dest offset count base : ℕ) (hTable : HintUnpackTable E descriptor dest offset count)
    (hArg : state.regs 6 = descriptor) (pre : HintUnpackPre E dest offset count)
    (hAt : At P base (hintUnpackAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 22) state (fun k out => k ≤ 12 * count + 12 ∧
      out.regs 14 = state.regs 14 ∧
      (∀ i < count, out.mem (dest + i) = bitAt state.mem E.W 0 (offset + i)) ∧
      CRMemFrame dest (dest + count) state.mem out.mem) := by
  obtain ⟨hSetupAt, hUnpackAt⟩ := At.seqStmt hAt
  change At P base hintUnpackSetup at hSetupAt
  change At P (base + 9) (hintUnpackStmt.compile (base + 9)) at hUnpackAt
  have hSetup := hintUnpackSetup_spec E state descriptor dest offset count hTable hArg
  generalize hS : runBlock hintUnpackSetup E state = start at hSetup
  obtain ⟨hStart, hMem, hCtx, hArgs⟩ := hSetup
  have hRunSetup : (step P E)^[9] state = start := by
    have hh := iterate_runBlock_of_at P E hintUnpackSetup state (by rwa [hPc])
      (by simp [hintUnpackSetup, NoBranch, Instr.NoBranchI])
    rw [hS] at hh
    exact hh
  obtain ⟨_, k, out, hRun, hEnd, hTime, hOut⟩ :=
    hintUnpackStmt_sem P E start dest offset count (base + 9) pre hArgs hUnpackAt (by omega)
  refine ⟨hPc, k + 9, out, hintIterate_then (step P E) hRunSetup hRun, by omega, by omega,
    hOut.context.trans hCtx, ?_, hMem ▸ hOut.frame⟩
  intro i hi
  rw [hOut.data i hi, hMem]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintUnpackAction_sem
end S_HintUnpackAction20261120
section S_HintStageAction20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintStageSetup : List Instr :=
  [.imm 15 1, .qDet 9 6, .add 3 6 15, .qDet 5 3, .add 3 3 15, .qDet 7 3, .qDet 11 3,
    .add 3 3 15, .qDet 6 3, .imm 13 2]

def hintStageAction : Stmt := .seq (.code hintStageSetup) hintStageStmt

theorem hintStageSetup_spec (E : RAMEnv) (s : RAMState) (descriptor dest offset count : ℕ)
    (hTable : HintUnpackTable E descriptor dest offset count) (hArg : s.regs 6 = descriptor) :
    let out := runBlock hintStageSetup E s
    out.pc = s.pc + 10 ∧ out.mem = s.mem ∧ out.regs 14 = s.regs 14 ∧ HintStageArgs E E.W count offset dest out := by
  have hSpan := hTable.table_span
  have hWord := hTable.word
  have hOne : 1 < 2 ^ E.W := by omega
  have h1 : descriptor + 1 < 2 ^ E.W := by omega
  have h2 : descriptor + 1 + 1 < 2 ^ E.W := by omega
  have h3 : descriptor + 1 + 1 + 1 < 2 ^ E.W := by omega
  have hWidth : E.W < 2 ^ E.W := Nat.lt_two_pow_self
  refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintStageSetup, runBlock, execInstr, hArg, hTable.dest_address, hTable.offset_value,
      hTable.word_width, hTable.length, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hTable.dest_fit, Nat.mod_eq_of_lt hTable.offset_fit,
      Nat.mod_eq_of_lt hTable.count_fit, Nat.mod_eq_of_lt hWidth]

theorem hintStageAction_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor dest offset count base : ℕ) (hTable : HintUnpackTable E descriptor dest offset count)
    (hArg : state.regs 6 = descriptor) (pre : HintStagePre E E.W count offset dest)
    (y : Fin count → ZMod 2)
    (hBits : ∀ i : Fin count, bitAt state.mem E.W 0 (offset + i.val) = if y i = 1 then 1 else 0)
    (hFresh : ∀ a < wordsOf E.W count, state.mem (dest + a) = 0)
    (hAt : At P base (hintStageAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 28) state (fun k out => k ≤ 17 * count + 13 ∧
      out.regs 14 = state.regs 14 ∧
      (∀ a < wordsOf E.W count, out.mem (dest + a) = packMem E.W y a) ∧
      CRMemFrame dest (dest + wordsOf E.W count) state.mem out.mem) := by
  obtain ⟨hSetupAt, hStageAt⟩ := At.seqStmt hAt
  change At P base hintStageSetup at hSetupAt
  change At P (base + 10) (hintStageStmt.compile (base + 10)) at hStageAt
  have hSetup := hintStageSetup_spec E state descriptor dest offset count hTable hArg
  generalize hS : runBlock hintStageSetup E state = mid at hSetup
  obtain ⟨hMid, hMem, hCtx, hArgs⟩ := hSetup
  have hRunSetup : (step P E)^[10] state = mid := by
    have hh := iterate_runBlock_of_at P E hintStageSetup state (by rwa [hPc])
      (by simp [hintStageSetup, NoBranch, Instr.NoBranchI])
    rw [hS] at hh
    exact hh
  obtain ⟨_, k, out, hRun, hEnd, hTime, hOut, hContext, hFrame⟩ :=
    hintStageStmt_sem P E mid E.W count offset dest (base + 10) pre y hArgs
      (by rw [hMem]; exact hBits) (by rw [hMem]; exact hFresh) hStageAt (by omega)
  exact ⟨hPc, k + 10, out, hintIterate_then (step P E) hRunSetup hRun, by omega, by omega,
    hContext.trans hCtx, hOut, hMem ▸ hFrame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStageAction_sem
end S_HintStageAction20261120
section S_HintRowRecord20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintRowRecord (E : RAMEnv) (descriptor parent : ℕ) (fields : ℕ → ℕ) : Prop where
  word : 30 < 2 ^ E.W
  table_span : descriptor + 31 ≤ 2 ^ E.W
  memory_span : parent + 30 ≤ 2 ^ E.W
  address : E.det descriptor = parent
  data : ∀ i < 30, E.det (descriptor + 1 + i) = fields i
  fits : ∀ i < 30, fields i < 2 ^ E.W

def hintRowRecordArgs : List Instr :=
  [.imm 15 1, .qDet 4 6, .add 5 6 15, .imm 6 30]

def hintRowRecordCopy : Stmt := .seq (.code hintRowRecordArgs) hintDetCopyStmt

theorem hintRowRecordCopy_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor parent base : ℕ) (fields : ℕ → ℕ)
    (rec : HintRowRecord E descriptor parent fields) (hArg : state.regs 6 = descriptor)
    (hAt : At P base (hintRowRecordCopy.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 13) state (fun k out => k ≤ 247 ∧
      out.regs 14 = state.regs 14 ∧ out.regs 4 = parent ∧
      (∀ i < 30, out.mem (parent + i) = fields i) ∧
      CRMemFrame parent (parent + 30) state.mem out.mem) := by
  obtain ⟨hArgsAt, hCopyAt⟩ := At.seqStmt hAt
  change At P base hintRowRecordArgs at hArgsAt
  change At P (base + 4) (hintDetCopyStmt.compile (base + 4)) at hCopyAt
  let mid := runBlock hintRowRecordArgs E state
  have hWord := rec.word
  have hp : parent < 2 ^ E.W := by have := rec.memory_span; omega
  have hs : descriptor + 1 < 2 ^ E.W := by have := rec.table_span; omega
  have hOne : 1 < 2 ^ E.W := by omega
  have hArgs : HintDetCopyArgs parent (descriptor + 1) 30 mid := by
    constructor <;> simp [mid, hintRowRecordArgs, runBlock, execInstr, hArg, rec.address,
      Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hs]
  have hCopyPre : HintDetCopyPre E parent (descriptor + 1) 30 := by
    refine ⟨hOne, hWord, rec.memory_span, ?_, ?_⟩
    · have := rec.table_span; omega
    · intro i hi
      rw [rec.data i hi]
      exact rec.fits i hi
  have hRunArgs : (step P E)^[4] state = mid :=
    iterate_runBlock_of_at P E hintRowRecordArgs state (by rwa [hPc])
      (by simp [hintRowRecordArgs, NoBranch, Instr.NoBranchI])
  have hPcArgs : mid.pc = base + 4 := by simp [mid, hintRowRecordArgs, runBlock, execInstr, hPc]
  obtain ⟨_, k, out, hRun, hEnd, hCost, h⟩ :=
    hintDetCopyStmt_sem P E mid parent (descriptor + 1) 30 (base + 4) hCopyPre hArgs hCopyAt hPcArgs
  have hC : mid.regs 14 = state.regs 14 := by simp [mid, hintRowRecordArgs, runBlock, execInstr]
  exact ⟨hPc, k + 4, out, hintIterate_then (step P E) hRunArgs hRun, by omega, by omega,
    h.context.trans hC, h.args.destination, fun i hi => (h.data i hi).trans (rec.data i hi), h.frame⟩

def hintRowEnterCode : List Instr :=
  [.imm 15 1, .add 3 4 15, .load 9 3, .sub 9 9 15, .store 9 14, .imm 3 16, .add 14 4 3]

def hintRowLeaveCode : List Instr :=
  [.imm 3 15, .sub 3 14 3, .load 9 3, .imm 15 1, .sub 9 9 15, .load 14 9]

theorem hintRowEnterCode_spec (E : RAMEnv) (state : RAMState) (parent bitmap control : ℕ)
    (hWord : 16 < 2 ^ E.W) (hParent : parent + 16 < 2 ^ E.W)
    (hBitmap : bitmap < 2 ^ E.W) (hPos : 0 < bitmap)
    (hDest : state.regs 4 = parent) (hContext : state.regs 14 = control)
    (hPointer : state.mem (parent + 1) = bitmap) :
    let out := runBlock hintRowEnterCode E state
    out.pc = state.pc + 7 ∧ out.regs 14 = parent + 16 ∧
      out.mem = Function.update state.mem (bitmap - 1) control := by
  have hw : 1 < 2 ^ E.W := by omega
  have hA : parent + 1 < 2 ^ E.W := by omega
  have hSub : bitmap + 2 ^ E.W - 1 = (bitmap - 1) + 2 ^ E.W := by omega
  have hBack : bitmap - 1 < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [hintRowEnterCode, runBlock, execInstr, hDest, hPointer, hContext, hSub,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hParent,
      Nat.mod_eq_of_lt hBack, Nat.mod_eq_of_lt hBitmap]

theorem hintRowLeaveCode_spec (E : RAMEnv) (state : RAMState) (parent bitmap control : ℕ)
    (hWord : 16 < 2 ^ E.W) (hParent : parent + 16 < 2 ^ E.W)
    (hBitmap : bitmap < 2 ^ E.W) (hPos : 0 < bitmap) (hCtrl : control < 2 ^ E.W)
    (hContext : state.regs 14 = parent + 16)
    (hPointer : state.mem (parent + 1) = bitmap) (hSaved : state.mem (bitmap - 1) = control) :
    let out := runBlock hintRowLeaveCode E state
    out.pc = state.pc + 6 ∧ out.regs 14 = control ∧ out.mem = state.mem := by
  have hw : 1 < 2 ^ E.W := by omega
  have hw15 : 15 < 2 ^ E.W := by omega
  have hA : parent + 1 < 2 ^ E.W := by omega
  have hFirst : parent + 16 + 2 ^ E.W - 15 = (parent + 1) + 2 ^ E.W := by omega
  have hSub : bitmap + 2 ^ E.W - 1 = (bitmap - 1) + 2 ^ E.W := by omega
  have hBack : bitmap - 1 < 2 ^ E.W := by omega
  refine ⟨?_, ?_, rfl⟩ <;>
    simp [hintRowLeaveCode, runBlock, execInstr, hContext, hPointer, hSaved, hFirst, hSub,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hw15, Nat.mod_eq_of_lt hA,
      Nat.mod_eq_of_lt hBack, Nat.mod_eq_of_lt hBitmap, Nat.mod_eq_of_lt hCtrl]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowRecordCopy_sem
#print axioms LinearSetReconciliation327.Main.hintRowEnterCode_spec
#print axioms LinearSetReconciliation327.Main.hintRowLeaveCode_spec
end S_HintRowRecord20261120
section S_HintRunRow20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRunRowStmt (row : Stmt) : Stmt :=
  .seq hintRowRecordCopy (.seq (.code hintRowEnterCode) (.seq row (.code hintRowLeaveCode)))

theorem hintRunRowStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (row : Stmt) (descriptor parent bitmap control base budget : ℕ) (fields : ℕ → ℕ)
    (Q : (ℕ → ℕ) → Prop)
    (rec : HintRowRecord E descriptor parent fields) (hArg : state.regs 6 = descriptor)
    (hBitmap : fields 1 = bitmap) (hPos : 0 < bitmap) (hSeparate : bitmap ≤ parent)
    (hContext : state.regs 14 = control) (hControl : control < 2 ^ E.W)
    (hAt : At P base ((hintRunRowStmt row).compile base)) (hPc : state.pc = base)
    (hWork : ∀ st, At P (base + 20) (row.compile (base + 20)) → st.pc = base + 20 →
      st.regs 14 = parent + 16 →
      (∀ i < 30, st.mem (parent + i) = fields i) → st.mem (bitmap - 1) = control →
      (∀ addr, (addr < parent ∨ parent + 30 ≤ addr) → addr ≠ bitmap - 1 → st.mem addr = state.mem addr) →
      Sem P E (base + 20) (base + 20 + row.len) st (fun k out => k ≤ budget ∧
        out.regs 14 = parent + 16 ∧ out.mem (parent + 1) = bitmap ∧
        out.mem (bitmap - 1) = control ∧ Q out.mem)) :
    Sem P E base (base + (hintRunRowStmt row).len) state (fun k out =>
      k ≤ budget + 260 ∧ out.regs 14 = control ∧ Q out.mem) := by
  have hWord := rec.word
  have hSpan := rec.memory_span
  have hBitmapFit : bitmap < 2 ^ E.W := (hBitmap ▸ rec.fits 1 (by decide))
  have hParent : parent + 16 < 2 ^ E.W := by omega
  obtain ⟨hCopyAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintRowRecordCopy.compile base) at hCopyAt
  change At P (base + 13) ((Stmt.seq (.code hintRowEnterCode)
    (.seq row (.code hintRowLeaveCode))).compile (base + 13)) at hRestAt
  obtain ⟨hEnterAt, hWorkLeaveAt⟩ := At.seqStmt hRestAt
  change At P (base + 13) hintRowEnterCode at hEnterAt
  change At P (base + 20) ((Stmt.seq row (.code hintRowLeaveCode)).compile (base + 20)) at hWorkLeaveAt
  obtain ⟨hWorkAt, hLeaveAt⟩ := At.seqStmt hWorkLeaveAt
  change At P (base + 20) (row.compile (base + 20)) at hWorkAt
  change At P (base + 20 + row.len) hintRowLeaveCode at hLeaveAt
  obtain ⟨_, kCopy, copied, hRunCopy, hPcCopy, hKCopy, hCtrlCopy, hParentCopy, hData, hFrame⟩ :=
    hintRowRecordCopy_sem P E state descriptor parent base fields rec hArg hCopyAt hPc
  have hEnter := hintRowEnterCode_spec E copied parent bitmap control (by omega) hParent hBitmapFit
    hPos hParentCopy (hCtrlCopy.trans hContext) ((hData 1 (by decide)).trans hBitmap)
  generalize hE : runBlock hintRowEnterCode E copied = entered at hEnter
  obtain ⟨hPcEnter, hContextEnter, hMemEnter⟩ := hEnter
  have hRunEnter : (step P E)^[7] copied = entered := by
    have hh := iterate_runBlock_of_at P E hintRowEnterCode copied (by rwa [hPcCopy])
      (by simp [hintRowEnterCode, NoBranch, Instr.NoBranchI])
    rw [hE] at hh
    exact hh
  have hDataEnter : ∀ i < 30, entered.mem (parent + i) = fields i := by
    intro i hi
    rw [hMemEnter, Function.update_of_ne (by omega : parent + i ≠ bitmap - 1)]
    exact hData i hi
  have hSaved : entered.mem (bitmap - 1) = control := by rw [hMemEnter]; simp
  have hFrameEnter (addr : ℕ) (hAway : addr < parent ∨ parent + 30 ≤ addr)
      (hOther : addr ≠ bitmap - 1) : entered.mem addr = state.mem addr := by
    rw [hMemEnter, Function.update_of_ne hOther, hFrame addr hAway]
  obtain ⟨_, kWork, done, hRunWork, hPcWork, hKWork, hContextWork, hPtrWork, hSavedWork, hResult⟩ :=
    hWork entered hWorkAt (by omega) hContextEnter hDataEnter hSaved hFrameEnter
  have hLeave := hintRowLeaveCode_spec E done parent bitmap control (by omega) hParent hBitmapFit
    hPos hControl hContextWork hPtrWork hSavedWork
  generalize hL : runBlock hintRowLeaveCode E done = out at hLeave
  obtain ⟨hPcLeave, hContextLeave, hMemLeave⟩ := hLeave
  have hRunLeave : (step P E)^[6] done = out := by
    have hh := iterate_runBlock_of_at P E hintRowLeaveCode done (by rwa [hPcWork])
      (by simp [hintRowLeaveCode, NoBranch, Instr.NoBranchI])
    rw [hL] at hh
    exact hh
  refine ⟨hPc, 6 + (kWork + (7 + kCopy)), out,
    hintIterate_then (step P E) (hintIterate_then (step P E)
      (hintIterate_then (step P E) hRunCopy hRunEnter) hRunWork) hRunLeave, ?_, by omega,
    hContextLeave, hMemLeave ▸ hResult⟩
  change out.pc = base + (13 + (7 + (row.len + 6)))
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRunRowStmt_sem
end S_HintRunRow20261120


