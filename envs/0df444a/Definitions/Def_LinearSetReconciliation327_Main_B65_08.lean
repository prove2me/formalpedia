-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_08
-- name    : LinearSetReconciliation327_Main_B65_08
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T07:36:49.465579+00:00
-- url     : https://prove2.me/theorems/29e07443-3395-5a31-af94-17839633a495
-- title:
--   Theorem 6.5 supporting machine proof B65_08
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_08Part2
set_option autoImplicit false

section S_HintWriteColumn20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintPredictionBits : List Instr :=
  [.imm 15 1, .imm 9 2, .lt 6 1 15, .lt 7 15 1, .add 6 6 7, .bxor 7 6 15,
    .mod 8 8 9, .mul 8 8 7]

theorem hintPredictionBits_spec (E : RAMEnv) (state : RAMState) (hWord : 2 < 2 ^ E.W) :
    let out := runBlock hintPredictionBits E state
    out.pc = state.pc + 8 ∧ out.mem = state.mem ∧
      out.regs 6 = hintTruth (hintRowOutput state = none) ∧
      out.regs 8 = hintTruth (hintRowOutput state = some 1) ∧
      out.regs 14 = state.regs 14 := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hBit : state.regs 8 % 2 < 2 ^ E.W := (Nat.mod_lt _ (by decide)).trans hWord
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [hintPredictionBits, runBlock, execInstr]
  · by_cases hLt : state.regs 1 < 1
    · have hNot : ¬ 1 < state.regs 1 := by omega
      have hNe : state.regs 1 ≠ 1 := by omega
      simp [hintPredictionBits, runBlock, execInstr, hLt, hNot, hNe, hintRowOutput,
        hintTruth, Nat.mod_eq_of_lt hOne]
    · by_cases hGt : 1 < state.regs 1
      · have hNe : state.regs 1 ≠ 1 := by omega
        simp [hintPredictionBits, runBlock, execInstr, hLt, hGt, hNe, hintRowOutput,
          hintTruth, Nat.mod_eq_of_lt hOne]
      · have hEq : state.regs 1 = 1 := by omega
        simp [hintPredictionBits, runBlock, execInstr, hEq, hintRowOutput, hintTruth, Nat.mod_eq_of_lt hOne]
  · by_cases hLt : state.regs 1 < 1
    · have hNot : ¬ 1 < state.regs 1 := by omega
      have hNe : state.regs 1 ≠ 1 := by omega
      simp [hintPredictionBits, runBlock, execInstr, hLt, hNot, hNe, hintRowOutput, hintTruth,
        Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hWord]
    · by_cases hGt : 1 < state.regs 1
      · have hNe : state.regs 1 ≠ 1 := by omega
        simp [hintPredictionBits, runBlock, execInstr, hLt, hGt, hNe, hintRowOutput, hintTruth,
          Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hWord]
      · have hEq : state.regs 1 = 1 := by omega
        have hCast : ((state.regs 8 : ZMod 2) = 1) ↔ state.regs 8 % 2 = 1 := by
          constructor
          · intro h
            have hOneVal : (1 : ZMod 2).val = 1 := rfl
            simpa only [ZMod.val_natCast, hOneVal] using congrArg ZMod.val h
          · intro h
            apply ZMod.val_injective
            rw [ZMod.val_natCast, h]
            rfl
        have hMod : state.regs 8 % 2 = 0 ∨ state.regs 8 % 2 = 1 := by have := Nat.mod_lt (state.regs 8) (by decide : 0 < 2); omega
        rcases hMod with h | h <;>
          simp [hintPredictionBits, runBlock, execInstr, hEq, hintRowOutput, hintTruth,
            hCast, h, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hWord]
  · simp [hintPredictionBits, runBlock, execInstr]


def hintWriteColumnTail : List Instr :=
  hintParentLoad 4 14 ++ hintParentLoad 5 15 ++ hintParentLoad 10 27 ++
    [.add 4 4 10, .add 5 5 10, .store 4 8, .store 5 6]
def hintWriteColumnCode : List Instr := hintPredictionBits ++ hintScanParent ++ hintWriteColumnTail

theorem hintWriteColumnCode_length : hintWriteColumnCode.length = 23 := rfl

theorem hintWriteColumnTail_spec (E : RAMEnv) (s : RAMState) (parent prediction abstention row bit blank : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W) (h11 : s.regs 11 = parent) (h14 : s.regs 14 = parent + 16)
    (h8 : s.regs 8 = bit) (h6 : s.regs 6 = blank)
    (hReadPred : s.mem (parent + 14) = prediction) (hReadAbst : s.mem (parent + 15) = abstention)
    (hReadRow : s.mem (parent + 27) = row)
    (hPredFit : prediction + row < 2 ^ E.W) (hAbstFit : abstention + row < 2 ^ E.W) :
    let out := runBlock hintWriteColumnTail E s
    out.pc = s.pc + 13 ∧
      out.mem = Function.update (Function.update s.mem (prediction + row) bit) (abstention + row) blank ∧
      out.regs 14 = parent + 16 := by
  have h14Fit : 14 < 2 ^ E.W := by omega
  have h15Fit : 15 < 2 ^ E.W := by omega
  have h27Fit : 27 < 2 ^ E.W := by omega
  have hA14 : parent + 14 < 2 ^ E.W := by omega
  have hA15 : parent + 15 < 2 ^ E.W := by omega
  have hA27 : parent + 27 < 2 ^ E.W := by omega
  have hPFit : prediction < 2 ^ E.W := by omega
  have hAFit : abstention < 2 ^ E.W := by omega
  have hRFit : row < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [hintWriteColumnTail, hintParentLoad, runBlock, execInstr, h11, h14, h8, h6,
      hReadPred, hReadAbst, hReadRow,
      Nat.mod_eq_of_lt h14Fit, Nat.mod_eq_of_lt h15Fit, Nat.mod_eq_of_lt h27Fit,
      Nat.mod_eq_of_lt hA14, Nat.mod_eq_of_lt hA15, Nat.mod_eq_of_lt hA27,
      Nat.mod_eq_of_lt hPFit, Nat.mod_eq_of_lt hAFit, Nat.mod_eq_of_lt hRFit,
      Nat.mod_eq_of_lt hPredFit, Nat.mod_eq_of_lt hAbstFit]

theorem hintWriteColumnCode_spec (E : RAMEnv) (state : RAMState) (parent prediction abstention row : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W) (hCtx : state.regs 14 = parent + 16)
    (hReadPred : state.mem (parent + 14) = prediction) (hReadAbst : state.mem (parent + 15) = abstention)
    (hReadRow : state.mem (parent + 27) = row)
    (hPredFit : prediction + row < 2 ^ E.W) (hAbstFit : abstention + row < 2 ^ E.W) :
    let out := runBlock hintWriteColumnCode E state
    out.pc = state.pc + 23 ∧
      out.mem = Function.update
        (Function.update state.mem (prediction + row) (hintTruth (hintRowOutput state = some 1)))
        (abstention + row) (hintTruth (hintRowOutput state = none)) ∧ out.regs 14 = parent + 16 := by
  have hBits := hintPredictionBits_spec E state (by omega)
  generalize hB : runBlock hintPredictionBits E state = sB at hBits
  obtain ⟨hPcB, hMemB, h6, h8, hCtxB⟩ := hBits
  have hP := hintScanParent_spec E sB parent (by omega) (hCtxB.trans hCtx)
  have h6P : (runBlock hintScanParent E sB).regs 6 = sB.regs 6 := by simp [hintScanParent, runBlock, execInstr]
  have h8P : (runBlock hintScanParent E sB).regs 8 = sB.regs 8 := by simp [hintScanParent, runBlock, execInstr]
  generalize hPExec : runBlock hintScanParent E sB = sP at hP h6P h8P
  obtain ⟨hPcP, hMemP, h11P, h14P⟩ := hP
  have hTail := hintWriteColumnTail_spec E sP parent prediction abstention row
    (hintTruth (hintRowOutput state = some 1)) (hintTruth (hintRowOutput state = none)) hSpan
    h11P h14P (h8P.trans h8) (h6P.trans h6)
    (by rw [hMemP, hMemB]; exact hReadPred) (by rw [hMemP, hMemB]; exact hReadAbst)
    (by rw [hMemP, hMemB]; exact hReadRow) hPredFit hAbstFit
  generalize hT : runBlock hintWriteColumnTail E sP = out at hTail
  obtain ⟨hPcT, hMemT, hCtxT⟩ := hTail
  have hRun : runBlock hintWriteColumnCode E state = out := by
    rw [hintWriteColumnCode, runBlock_append, runBlock_append, hB, hPExec, hT]
  rw [hRun]
  exact ⟨by omega, by rw [hMemT, hMemP, hMemB], hCtxT⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintWriteColumnCode_spec
end S_HintWriteColumn20261120
section S_HintScatter20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintScatterBody : List Instr :=
  [.mul 8 0 7, .add 8 8 10, .qPermInv 8 12 8, .add 8 4 8,
    .add 3 5 0, .load 9 3, .store 8 9, .add 0 0 15]

theorem hintScatterBody_spec (E : RAMEnv) (s : RAMState)
    (dest source rows row node count q coord bit : ℕ)
    (hArgs : HintGatherArgs dest source rows row node count s) (hQ : s.regs 0 = q)
    (hPos : row + q * rows < 2 ^ E.W) (hDest : dest + coord < 2 ^ E.W) (hSource : source + q < 2 ^ E.W)
    (hBit : bit < 2 ^ E.W) (hInv : E.permInv node (row + q * rows) = coord)
    (hRead : s.mem (source + q) = bit) (hNext : q + 1 < 2 ^ E.W) :
    let out := runBlock hintScatterBody E s
    out.pc = s.pc + 8 ∧ out.mem = Function.update s.mem (dest + coord) bit ∧
      out.regs 0 = q + 1 ∧ HintGatherArgs dest source rows row node count out ∧
      out.regs 14 = s.regs 14 := by
  have hMul : q * rows < 2 ^ E.W := by omega
  have hAddr : q * rows + row < 2 ^ E.W := by omega
  have hCoord : coord < 2 ^ E.W := by omega
  have hLookup : E.permInv node (q * rows + row) = coord := by simpa [Nat.add_comm] using hInv
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintScatterBody, runBlock, execInstr, hQ, hArgs.dest_value, hArgs.source_value,
      hArgs.rows_value, hArgs.row_value, hArgs.node_value, hArgs.count_value, hArgs.one_value,
      hLookup, hRead, Nat.mod_eq_of_lt hMul, Nat.mod_eq_of_lt hAddr,
      Nat.mod_eq_of_lt hCoord, Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hSource,
      Nat.mod_eq_of_lt hBit, Nat.mod_eq_of_lt hNext]

structure HintScatterSource (E : RAMEnv) (dest source rows row node count : ℕ)
    (coord bits : ℕ → ℕ) (original : ℕ → ℕ) : Prop where
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  disjoint : source + count ≤ dest
  position_fit : ∀ q < count, row + q * rows < 2 ^ E.W
  dest_fit : ∀ q < count, dest + coord q < 2 ^ E.W
  source_fit : ∀ q < count, source + q < 2 ^ E.W
  inverse : ∀ q < count, E.permInv node (row + q * rows) = coord q
  injective : ∀ i < count, ∀ j < count, coord i = coord j → i = j
  bit_fit : ∀ q < count, bits q < 2 ^ E.W
  read : ∀ q < count, original (source + q) = bits q

structure HintScatterInv (dest source rows row node count q : ℕ) (coord bits : ℕ → ℕ)
    (original : ℕ → ℕ) (s : RAMState) : Prop where
  args : HintGatherArgs dest source rows row node count s
  index : s.regs 0 = q
  stored : ∀ i < q, s.mem (dest + coord i) = bits i
  frame : ∀ addr, (∀ i < q, addr ≠ dest + coord i) → s.mem addr = original addr

theorem hintScatterInv_step (E : RAMEnv) (s : RAMState)
    (dest source rows row node count q : ℕ) (coord bits : ℕ → ℕ) (original : ℕ → ℕ)
    (hSource : HintScatterSource E dest source rows row node count coord bits original)
    (hq : q < count) (hInv : HintScatterInv dest source rows row node count q coord bits original s) :
    let out := runBlock hintScatterBody E s
    HintScatterInv dest source rows row node count (q + 1) coord bits original out ∧ out.regs 14 = s.regs 14 := by
  have hSep := hSource.disjoint
  have hCount := hSource.count_fit
  have hRead : s.mem (source + q) = bits q :=
    (hInv.frame (source + q) (by intro i hi; omega)).trans (hSource.read q hq)
  have hBlock := hintScatterBody_spec E s dest source rows row node count q (coord q) (bits q)
    hInv.args hInv.index (hSource.position_fit q hq) (hSource.dest_fit q hq) (hSource.source_fit q hq)
    (hSource.bit_fit q hq) (hSource.inverse q hq) hRead (by omega)
  generalize hExec : runBlock hintScatterBody E s = out at hBlock
  obtain ⟨_, hMemory, hIndex, hArgs, hCtx⟩ := hBlock
  refine ⟨⟨hArgs, hIndex, ?_, ?_⟩, hCtx⟩
  · intro i hi
    rw [hMemory]
    by_cases heq : i = q
    · subst i
      simp
    · have hiq : i < q := by omega
      have hNe : dest + coord i ≠ dest + coord q := by
        intro hEq
        exact heq (hSource.injective i (by omega) q hq (by omega))
      rw [Function.update_of_ne hNe, hInv.stored i hiq]
  · intro addr hAway
    rw [hMemory, Function.update_of_ne (hAway q (by omega))]
    exact hInv.frame addr (fun i hi => hAway i (by omega))

theorem HintScatterInv.pc {dest source rows row node count q : ℕ}
    {coord bits : ℕ → ℕ} {original : ℕ → ℕ} {s : RAMState}
    (h : HintScatterInv dest source rows row node count q coord bits original s) (pc : ℕ) :
    HintScatterInv dest source rows row node count q coord bits original {s with pc := pc} :=
  ⟨⟨h.args.dest_value, h.args.source_value, h.args.rows_value, h.args.row_value,
    h.args.node_value, h.args.count_value, h.args.one_value⟩, h.index, h.stored, h.frame⟩

theorem HintScatterInv.test {dest source rows row node count q : ℕ}
    {coord bits : ℕ → ℕ} {original : ℕ → ℕ} {s : RAMState}
    (h : HintScatterInv dest source rows row node count q coord bits original s) (E : RAMEnv) :
    HintScatterInv dest source rows row node count q coord bits original (runBlock (Cond.lt 2 0 6).code E s) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.args.dest_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.source_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.rows_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.row_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.node_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.count_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.one_value
  · simpa [Cond.code, runBlock, execInstr] using h.index
  · simpa [Cond.code, runBlock, execInstr] using h.stored
  · simpa [Cond.code, runBlock, execInstr] using h.frame

def hintScatterLoop : Stmt := .loop (.lt 2 0 6) (.code hintScatterBody)

theorem hintScatterLoop_len : hintScatterLoop.len = 11 := rfl

theorem hintScatterLoop_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source rows row node count base : ℕ) (coord bits : ℕ → ℕ) (original : ℕ → ℕ)
    (hSource : HintScatterSource E dest source rows row node count coord bits original)
    (hInv : HintScatterInv dest source rows row node count 0 coord bits original state)
    (hAt : At P base (hintScatterLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 11) state (fun k out => k ≤ 11 * count + 2 ∧
      HintScatterInv dest source rows row node count count coord bits original out ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ q, q + left = count ∧
    HintScatterInv dest source rows row node count q coord bits original st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintScatterBody := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨q, hQ, hData, hCtx⟩ := hI
    exact ⟨q, hQ, hData.pc pc, hCtx⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 0 6).code E st) := by
    intro left st hI
    obtain ⟨q, hQ, hData, hCtx⟩ := hI
    exact ⟨q, hQ, hData.test E, by simpa [Cond.code, runBlock, execInstr] using hCtx⟩
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 0 6).eval st := by
    intro left st hI
    obtain ⟨q, hQ, hData, _⟩ := hI
    change st.regs 0 < st.regs 6
    rw [hData.index, hData.args.count_value]; omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 6).eval st := by
    intro st hI
    obtain ⟨q, hQ, hData, _⟩ := hI
    change ¬ st.regs 0 < st.regs 6
    rw [hData.index, hData.args.count_value]; omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintScatterBody).len) st
        (fun k out => k ≤ 8 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨q, hQ, hData, hCtx⟩ := hI
    have hStep := hintScatterInv_step E st dest source rows row node count q coord bits original hSource
      (by omega) hData
    generalize hMid : runBlock hintScatterBody E st = mid at hStep
    have hNative := Sem.block P E (base + 2) hintScatterBody st hBodyAt
      (by simp [hintScatterBody, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨hCost.le, q + 1, by omega, hStep.1, hStep.2.trans hCtx⟩
  have hInitial : I count state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintScatterBody) hAt hSource.word I 8
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, q, hQ, hFinal, hCtx⟩ := hOut
  have hEq : q = count := by omega
  rw [hEq] at hFinal
  exact ⟨hCost, hFinal, hCtx⟩

def hintScatterInit : List Instr := [.imm 0 0]
def hintScatterStmt : Stmt := .seq (.code hintScatterInit) hintScatterLoop

theorem hintScatterStmt_len : hintScatterStmt.len = 12 := rfl

/-- Write the estimate of one row to its positions in the node bitmap. -/
theorem hintScatterStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source rows row node count base : ℕ) (coord bits : ℕ → ℕ)
    (hSource : HintScatterSource E dest source rows row node count coord bits state.mem)
    (hArgs : HintGatherArgs dest source rows row node count state)
    (hAt : At P base (hintScatterStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 12) state (fun k out => k ≤ 11 * count + 3 ∧
      HintScatterInv dest source rows row node count count coord bits state.mem out ∧ out.regs 14 = state.regs 14) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintScatterInit at hInitAt
  change At P (base + 1) (hintScatterLoop.compile (base + 1)) at hLoopAt
  have hInit : let out := runBlock hintScatterInit E state
      out.pc = state.pc + 1 ∧ out.regs 14 = state.regs 14 ∧
      HintScatterInv dest source rows row node count 0 coord bits state.mem out := by
    refine ⟨?_, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
    · simp [hintScatterInit, runBlock, execInstr]
    · simp [hintScatterInit, runBlock, execInstr]
    · simpa [hintScatterInit, runBlock, execInstr] using hArgs.dest_value
    · simpa [hintScatterInit, runBlock, execInstr] using hArgs.source_value
    · simpa [hintScatterInit, runBlock, execInstr] using hArgs.rows_value
    · simpa [hintScatterInit, runBlock, execInstr] using hArgs.row_value
    · simpa [hintScatterInit, runBlock, execInstr] using hArgs.node_value
    · simpa [hintScatterInit, runBlock, execInstr] using hArgs.count_value
    · simpa [hintScatterInit, runBlock, execInstr] using hArgs.one_value
    · simp [hintScatterInit, runBlock, execInstr]
    · intro i hi
      omega
    · intro addr hAway
      rfl
  generalize hI : runBlock hintScatterInit E state = mid at hInit
  obtain ⟨hPcI, hCtxI, hInvI⟩ := hInit
  have hRunI : (step P E)^[1] state = mid := by
    have hh := iterate_runBlock_of_at P E hintScatterInit state (by rwa [hPc])
      (by simp [hintScatterInit, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  obtain ⟨_, k, out, hRun, hPcOut, hCost, hInvOut, hCtx⟩ :=
    hintScatterLoop_sem P E mid dest source rows row node count (base + 1) coord bits state.mem
      hSource hInvI hLoopAt (by omega)
  exact ⟨hPc, k + 1, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega,
    hInvOut, hCtx.trans hCtxI⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintScatterStmt_sem
end S_HintScatter20261120
section S_HintScatterRow20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- Reassemble one row's estimate in the original coordinate system. -/
theorem hintScatterRow_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (N m row node dest source base : ℕ) (π : Equiv.Perm (Fin N)) (est : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (hWord : 1 < 2 ^ E.W)
    (hCount : rowLen N m row < 2 ^ E.W) (hSep : source + rowLen N m row ≤ dest)
    (hDest : dest + N ≤ 2 ^ E.W) (hSource : source + rowLen N m row ≤ 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv node p.val = (π.symm p).val)
    (hBits : ∀ q < rowLen N m row, state.mem (source + q) = hintTruth (q ∈ est))
    (hArgs : HintGatherArgs dest source m row node (rowLen N m row) state)
    (hAt : At P base (hintScatterStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 12) state (fun k out => k ≤ 11 * rowLen N m row + 3 ∧
      (∀ i : Fin N, (π i).val % m = row →
        out.mem (dest + i.val) = hintTruth ((π i).val / m ∈ est)) ∧
      (∀ addr, (∀ i : Fin N, (π i).val % m = row → addr ≠ dest + i.val) →
        out.mem addr = state.mem addr) ∧ out.regs 14 = state.regs 14) := by
  classical
  let count := rowLen N m row
  let position (q : ℕ) (hq : q < count) : Fin N :=
    ⟨row + q * m, HintRowCoordinates.index_lt N m row q hm hRow hq⟩
  let coord : ℕ → ℕ := fun q =>
    if hq : q < count then (π.symm (position q hq)).val else 0
  have hSrc : HintScatterSource E dest source m row node count coord (fun q => hintTruth (q ∈ est)) state.mem := by
    refine ⟨hWord, hCount, hSep, ?_, ?_, ?_, ?_, ?_, ?_, hBits⟩
    · intro q hq
      have := (position q hq).isLt
      change row + q * m < N at this
      omega
    · intro q hq
      have h := (π.symm (position q hq)).isLt
      simp only [coord, dif_pos hq]
      omega
    · intro q hq
      change q < rowLen N m row at hq
      omega
    · intro q hq
      simp only [coord, dif_pos hq]
      exact hPerm (position q hq)
    · intro i hi j hj heq
      simp only [coord, dif_pos hi, dif_pos hj] at heq
      have hp := π.symm.injective (Fin.ext heq)
      have hv : row + i * m = row + j * m := congrArg Fin.val hp
      exact Nat.eq_of_mul_eq_mul_right hm (Nat.add_left_cancel hv)
    · intro q hq
      by_cases h : q ∈ est <;> simp [hintTruth, h, hWord, Nat.zero_lt_of_lt hWord]
  have hNative := hintScatterStmt_sem P E state dest source m row node count base coord
    (fun q => hintTruth (q ∈ est)) hSrc hArgs hAt hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, hInv, hContext⟩ := hOut
  refine ⟨hCost, ?_, ?_, hContext⟩
  · intro i hRowI
    let q := (π i).val / m
    have hDec : row + q * m = (π i).val := by
      dsimp [q]
      rw [← hRowI, Nat.mul_comm, Nat.mod_add_div]
    have hQ : q < count := by
      change q < rowLen N m row
      rw [HintRowCoordinates.count_eq_rowLen N m row hm hRow,
        HintRowCoordinates.lt_count_iff N m row q hm, hDec]
      exact (π i).isLt
    have hPosition : position q hQ = π i := Fin.ext hDec
    have hCoord : coord q = i.val := by
      simp only [coord, dif_pos hQ, hPosition, Equiv.symm_apply_apply]
    have hResult := hInv.stored q hQ
    rw [hCoord] at hResult
    exact hResult
  · intro addr hAway
    apply hInv.frame
    intro q hq
    let i := π.symm (position q hq)
    have hI : (π i).val % m = row := by
      dsimp only [i]
      rw [Equiv.apply_symm_apply]
      change (row + q * m) % m = row
      simp [Nat.add_mod, Nat.mod_eq_of_lt hRow]
    have hCoord : coord q = i.val := by simp [coord, hq, i]
    rw [hCoord]
    exact hAway i hI

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintScatterRow_sem
end S_HintScatterRow20261120
section S_HintRowScatter20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintScatterFetch : List Instr :=
  hintParentLoad 4 14 ++ hintParentLoad 5 1 ++ hintParentLoad 7 10 ++
    hintParentLoad 10 27 ++ hintParentLoad 12 26 ++ hintParentLoad 6 2 ++ [.imm 15 1]

def hintScatterSetup : List Instr := hintScanParent ++ hintScatterFetch

theorem hintScatterSetup_length : hintScatterSetup.length = 21 := rfl

structure HintScatterMetadata (parent dest source rows row node count : ℕ) (memory : ℕ → ℕ) : Prop where
  dest_value : memory (parent + 14) = dest
  source_value : memory (parent + 1) = source
  rows_value : memory (parent + 10) = rows
  row_value : memory (parent + 27) = row
  node_value : memory (parent + 26) = node
  count_value : memory (parent + 2) = count

theorem hintScatterSetup_spec (E : RAMEnv) (s : RAMState)
    (parent dest source rows row node count : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W) (hContext : s.regs 14 = parent + 16)
    (hMeta : HintScatterMetadata parent dest source rows row node count s.mem)
    (hDest : dest < 2 ^ E.W) (hSrc : source < 2 ^ E.W) (hRows : rows < 2 ^ E.W)
    (hRow : row < 2 ^ E.W) (hNode : node < 2 ^ E.W) (hCount : count < 2 ^ E.W) :
    let out := runBlock hintScatterSetup E s
    out.pc = s.pc + 21 ∧ out.mem = s.mem ∧ HintGatherArgs dest source rows row node count out ∧
      out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hParent := hintScanParent_spec E s parent (by omega) hContext
  generalize hP : runBlock hintScanParent E s = mid at hParent
  obtain ⟨hPcP, hMemP, h11, h14⟩ := hParent
  have hFetch : let out := runBlock hintScatterFetch E mid
      out.pc = mid.pc + 19 ∧ out.mem = mid.mem ∧ HintGatherArgs dest source rows row node count out ∧
        out.regs 14 = parent + 16 := by
    have hRead14 : mid.mem (parent + 14) = dest := by
      rw [hMemP]
      exact hMeta.dest_value
    have hOff14 : 14 < 2 ^ E.W := by omega
    have hAddr14 : parent + 14 < 2 ^ E.W := by omega
    have hRead1 : mid.mem (parent + 1) = source := by
      rw [hMemP]
      exact hMeta.source_value
    have hOff1 : 1 < 2 ^ E.W := by omega
    have hAddr1 : parent + 1 < 2 ^ E.W := by omega
    have hRead10 : mid.mem (parent + 10) = rows := by
      rw [hMemP]
      exact hMeta.rows_value
    have hOff10 : 10 < 2 ^ E.W := by omega
    have hAddr10 : parent + 10 < 2 ^ E.W := by omega
    have hRead27 : mid.mem (parent + 27) = row := by
      rw [hMemP]
      exact hMeta.row_value
    have hOff27 : 27 < 2 ^ E.W := by omega
    have hAddr27 : parent + 27 < 2 ^ E.W := by omega
    have hRead26 : mid.mem (parent + 26) = node := by
      rw [hMemP]
      exact hMeta.node_value
    have hOff26 : 26 < 2 ^ E.W := by omega
    have hAddr26 : parent + 26 < 2 ^ E.W := by omega
    have hRead2 : mid.mem (parent + 2) = count := by
      rw [hMemP]
      exact hMeta.count_value
    have hOff2 : 2 < 2 ^ E.W := by omega
    have hAddr2 : parent + 2 < 2 ^ E.W := by omega
    refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp [hintScatterFetch, hintParentLoad, runBlock, execInstr, h11, h14,
        hRead14, hRead1, hRead10, hRead27, hRead26, hRead2,
        Nat.mod_eq_of_lt hOff14, Nat.mod_eq_of_lt hAddr14, Nat.mod_eq_of_lt hOff1,
        Nat.mod_eq_of_lt hAddr1, Nat.mod_eq_of_lt hOff10, Nat.mod_eq_of_lt hAddr10,
        Nat.mod_eq_of_lt hOff27, Nat.mod_eq_of_lt hAddr27, Nat.mod_eq_of_lt hOff26,
        Nat.mod_eq_of_lt hAddr26, Nat.mod_eq_of_lt hOff2, Nat.mod_eq_of_lt hAddr2,
        Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hSrc, Nat.mod_eq_of_lt hRows,
        Nat.mod_eq_of_lt hRow, Nat.mod_eq_of_lt hNode, Nat.mod_eq_of_lt hCount,
        Nat.mod_eq_of_lt hWord]
  generalize hF : runBlock hintScatterFetch E mid = out at hFetch
  obtain ⟨hPcF, hMemF, hArgsF, hCtxF⟩ := hFetch
  have hRun : runBlock hintScatterSetup E s = out := by
    rw [hintScatterSetup, runBlock_append, hP, hF]
  rw [hRun]
  exact ⟨by omega, hMemF.trans hMemP, hArgsF, hCtxF⟩


def hintRowScatterStmt : Stmt := .seq (.code hintScatterSetup) hintScatterStmt

theorem hintRowScatterStmt_len : hintRowScatterStmt.len = 33 := rfl

theorem hintRowScatterStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (N m row node parent dest source base : ℕ) (π : Equiv.Perm (Fin N)) (est : Finset ℕ)
    (hm : 0 < m) (hRow : row < m)
    (hSpan : parent + 29 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hMeta : HintScatterMetadata parent dest source m row node (rowLen N m row) state.mem)
    (hDestFit : dest < 2 ^ E.W) (hSrcFit : source < 2 ^ E.W)
    (hRows : m < 2 ^ E.W) (hNode : node < 2 ^ E.W)
    (hCount : rowLen N m row < 2 ^ E.W) (hSep : source + rowLen N m row ≤ dest)
    (hDest : dest + N ≤ 2 ^ E.W) (hSource : source + rowLen N m row ≤ 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv node p.val = (π.symm p).val)
    (hBits : ∀ q < rowLen N m row, state.mem (source + q) = hintTruth (q ∈ est))
    (hAt : At P base (hintRowScatterStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 33) state (fun k out => k ≤ 11 * rowLen N m row + 24 ∧
      (∀ i : Fin N, (π i).val % m = row →
        out.mem (dest + i.val) = hintTruth ((π i).val / m ∈ est)) ∧
      (∀ addr, (∀ i : Fin N, (π i).val % m = row → addr ≠ dest + i.val) →
        out.mem addr = state.mem addr) ∧ out.regs 14 = parent + 16) := by
  obtain ⟨hSetupAt, hScatterAt⟩ := At.seqStmt hAt
  change At P base hintScatterSetup at hSetupAt
  change At P (base + 21) (hintScatterStmt.compile (base + 21)) at hScatterAt
  have hSetup := hintScatterSetup_spec E state parent dest source m row node (rowLen N m row)
    hSpan hContext hMeta hDestFit hSrcFit hRows (hRow.trans hRows) hNode hCount
  generalize hS : runBlock hintScatterSetup E state = mid at hSetup
  obtain ⟨hPcS, hMemS, hArgsS, hCtxS⟩ := hSetup
  have hRunS : (step P E)^[21] state = mid := by
    have hh := iterate_runBlock_of_at P E hintScatterSetup state (by rwa [hPc])
      (by simp [hintScatterSetup, hintScatterFetch, hintScanParent, hintParentLoad, NoBranch, Instr.NoBranchI])
    simpa only [hintScatterSetup_length, hS] using hh
  obtain ⟨_, kG, out, hRunG, hPcG, hCost, hBitsOut, hFrame, hCtx⟩ :=
    hintScatterRow_sem P E mid N m row node dest source (base + 21) π est hm hRow (by omega)
      hCount hSep hDest hSource hPerm (by rw [hMemS]; exact hBits) hArgsS hScatterAt (by omega)
  refine ⟨hPc, kG + 21, out, hintIterate_then (step P E) hRunS hRunG, by omega, by omega,
    hBitsOut, ?_, hCtx.trans hCtxS⟩
  rw [← hMemS]
  exact hFrame

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowScatterStmt_sem
end S_HintRowScatter20261120
section S_HintRowActions20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintPredictAction : Stmt := .seq hintPreparedPredictStmt (.code hintWriteColumnCode)
def hintFinalAction : Stmt := .seq hintPreparedFinalStmt hintRowScatterStmt

theorem hintPredictAction_len : hintPredictAction.len = 1607 := rfl
theorem hintFinalAction_len : hintFinalAction.len = 1686 := rfl

theorem hintPredictAction_sem (P : Program) (E : RAMEnv) (state : RAMState) (base budget : ℕ)
    (parent lo hi row predBase abstBase : ℕ) (pred : Option (ZMod 2))
    (hSpan : parent + 29 < 2 ^ E.W)
    (hPredFit : predBase + row < 2 ^ E.W) (hAbstFit : abstBase + row < 2 ^ E.W)
    (hDisjoint : predBase + row ≠ abstBase + row)
    (hKeepPred : parent + 1 ≠ predBase + row) (hKeepAbst : parent + 1 ≠ abstBase + row)
    (hAt : At P base (hintPredictAction.compile base)) (hPc : state.pc = base)
    (hWork : At P base (hintPreparedPredictStmt.compile base) →
      Sem P E base (base + 1584) state (fun k out => k ≤ budget ∧ hintRowOutput out = pred ∧
        out.regs 14 = parent + 16 ∧ out.mem (parent + 14) = predBase ∧ out.mem (parent + 15) = abstBase ∧
        out.mem (parent + 27) = row ∧ out.mem (parent + 1) = state.mem (parent + 1) ∧
        CRMemFrame lo hi state.mem out.mem)) :
    Sem P E base (base + 1607) state (fun k out => k ≤ budget + 23 ∧
      out.mem (predBase + row) = hintTruth (pred = some 1) ∧
      out.mem (abstBase + row) = hintTruth (pred = none) ∧ out.regs 14 = parent + 16 ∧
      out.mem (parent + 1) = state.mem (parent + 1) ∧
      (∀ addr, (addr < lo ∨ hi ≤ addr) → addr ≠ predBase + row → addr ≠ abstBase + row →
        out.mem addr = state.mem addr)) := by
  obtain ⟨hWorkerAt, hWriteAt⟩ := At.seqStmt hAt
  change At P base (hintPreparedPredictStmt.compile base) at hWorkerAt
  change At P (base + 1584) hintWriteColumnCode at hWriteAt
  obtain ⟨_, k, mid, hRun, hPcMid, hCost, hPred, hCtx, hPredBase, hAbstBase, hRow, hKeep, hFrame⟩ :=
    hWork hWorkerAt
  have hWrite := hintWriteColumnCode_spec E mid parent predBase abstBase row
    hSpan hCtx hPredBase hAbstBase hRow hPredFit hAbstFit
  generalize hW : runBlock hintWriteColumnCode E mid = out at hWrite
  obtain ⟨hPcOut, hMemOut, hCtxOut⟩ := hWrite
  have hRunW : (step P E)^[23] mid = out := by
    have hs := iterate_runBlock_of_at P E hintWriteColumnCode mid (by rwa [hPcMid])
      (by simp [hintWriteColumnCode, hintPredictionBits, hintScanParent, hintWriteColumnTail,
        hintParentLoad, NoBranch, Instr.NoBranchI])
    simpa only [hintWriteColumnCode_length, hW] using hs
  rw [hPred] at hMemOut
  refine ⟨hPc, 23 + k, out, hintIterate_then (step P E) hRun hRunW, by omega, by omega,
    ?_, ?_, hCtxOut, ?_, ?_⟩
  · rw [hMemOut, Function.update_of_ne hDisjoint]
    simp
  · rw [hMemOut]
    simp
  · rw [hMemOut, Function.update_of_ne hKeepAbst, Function.update_of_ne hKeepPred, hKeep]
  · intro addr hOutside hNotPred hNotAbst
    rw [hMemOut, Function.update_of_ne hNotAbst, Function.update_of_ne hNotPred, hFrame addr hOutside]

theorem hintFinalAction_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (base budget N m row node parent lo hi dest source : ℕ)
    (π : Equiv.Perm (Fin N)) (est : Finset ℕ) (hm : 0 < m) (hRow : row < m)
    (hSpan : parent + 29 < 2 ^ E.W)
    (hDestFit : dest < 2 ^ E.W) (hSrcFit : source < 2 ^ E.W)
    (hRows : m < 2 ^ E.W) (hNode : node < 2 ^ E.W) (hCount : rowLen N m row < 2 ^ E.W)
    (hSep : source + rowLen N m row ≤ dest) (hNoAlias : parent + 1 < dest)
    (hDest : dest + N ≤ 2 ^ E.W) (hSource : source + rowLen N m row ≤ 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv node p.val = (π.symm p).val)
    (hAt : At P base (hintFinalAction.compile base)) (hPc : state.pc = base)
    (hWork : At P base (hintPreparedFinalStmt.compile base) →
      Sem P E base (base + 1653) state (fun k out => k ≤ budget ∧ out.regs 14 = parent + 16 ∧
        HintScatterMetadata parent dest source m row node (rowLen N m row) out.mem ∧
        (∀ q < rowLen N m row, out.mem (source + q) = hintTruth (q ∈ est)) ∧
        CRMemFrame lo hi state.mem out.mem)) :
    Sem P E base (base + 1686) state (fun k out => k ≤ budget + 11 * rowLen N m row + 24 ∧
      (∀ i : Fin N, (π i).val % m = row →
        out.mem (dest + i.val) = hintTruth ((π i).val / m ∈ est)) ∧ out.regs 14 = parent + 16 ∧
      out.mem (parent + 1) = source ∧
      (∀ addr, (addr < lo ∨ hi ≤ addr) →
        (∀ i : Fin N, (π i).val % m = row → addr ≠ dest + i.val) → out.mem addr = state.mem addr)) := by
  obtain ⟨hWorkerAt, hWriteAt⟩ := At.seqStmt hAt
  change At P base (hintPreparedFinalStmt.compile base) at hWorkerAt
  change At P (base + 1653) (hintRowScatterStmt.compile (base + 1653)) at hWriteAt
  obtain ⟨_, kW, mid, hRunW, hPcMid, hCostW, hContext, hMeta, hBits, hFrameW⟩ := hWork hWorkerAt
  obtain ⟨_, kS, out, hRunS, hPcOut, hCostS, hBitsOut, hFrameS, hCtxOut⟩ :=
    hintRowScatterStmt_sem P E mid N m row node parent dest source (base + 1653) π est hm hRow
      hSpan hContext hMeta hDestFit hSrcFit hRows hNode hCount hSep hDest hSource hPerm hBits hWriteAt hPcMid
  refine ⟨hPc, kS + kW, out, hintIterate_then (step P E) hRunW hRunS, by omega, by omega,
    hBitsOut, hCtxOut, ?_, ?_⟩
  · exact (hFrameS (parent + 1) (by intro i hi; omega)).trans hMeta.source_value
  · intro addr hOutside hNotRow
    exact (hFrameS addr hNotRow).trans (hFrameW addr hOutside)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPredictAction_sem
#print axioms LinearSetReconciliation327.Main.hintFinalAction_sem
end S_HintRowActions20261120
section S_HintRowFields20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintRowFields where
  outsideBase : ℕ
  bitmapBase : ℕ
  rowLength : ℕ
  transcriptBase : ℕ
  rowCount : ℕ
  hintBase : ℕ
  hintLimit : ℕ
  outsideLimit : ℕ
  thresholdTable : ℕ
  outputBase : ℕ
  abstentionBase : ℕ

/-- A deterministic row record. The current hint count is computed by the row
gatherer, so the table can be built independently of the input hint. -/
def HintRowFields.value (F : HintRowFields) (G : HintGaussArea) (i : ℕ) : ℕ :=
  if 16 ≤ i then
    if i = 17 then 0 else hintGaussHeaderValue G 0 (i - 16)
  else match i with
    | 0 => F.outsideBase
    | 1 => F.bitmapBase
    | 2 => F.rowLength
    | 6 => F.hintLimit
    | 9 => F.transcriptBase
    | 10 => F.rowCount
    | 11 => F.hintBase
    | 12 => F.outsideLimit
    | 13 => F.thresholdTable
    | 14 => F.outputBase
    | 15 => F.abstentionBase
    | _ => 0

theorem HintRowFields.bitmap_eq (F : HintRowFields) (G : HintGaussArea) :
    F.value G 1 = F.bitmapBase := rfl

theorem HintRowFields.hints_irrel (F : HintRowFields) (G : HintGaussArea) (n i : ℕ) (hi : i < 30) :
    F.value {G with hints := n} i = F.value G i := by
  interval_cases i <;> rfl

theorem HintRowFields.prepare (F : HintRowFields) (G : HintGaussArea) (parent : ℕ) (mem : ℕ → ℕ)
    (hParent : parent + 16 = G.context)
    (hData : ∀ i < 30, mem (parent + i) = F.value G i) :
    HintRowPrepareMetadata G parent F.rowLength F.rowCount F.outsideBase F.bitmapBase F.hintBase
      F.transcriptBase F.hintLimit F.outsideLimit F.thresholdTable (mem F.outsideBase) mem := by
  have hd (i : ℕ) (hi : i < 30) := hData i hi
  refine ⟨⟨hd 25 (by decide), hd 11 (by decide), hd 10 (by decide), hd 27 (by decide),
    hd 26 (by decide), hd 2 (by decide)⟩, ?_, hd 1 (by decide), rfl, hd 9 (by decide),
    hd 6 (by decide), hd 12 (by decide), hd 13 (by decide), 0, ?_⟩
  · exact hd 0 (by decide)
  · intro i hi hne
    rw [← hParent, Nat.add_assoc, hd (16 + i) (by omega)]
    simp [HintRowFields.value, show 16 ≤ 16 + i by omega, show 16 + i ≠ 17 by omega]

theorem HintRowFields.output_eq (F : HintRowFields) (G : HintGaussArea) (parent : ℕ) (mem : ℕ → ℕ)
    (hData : ∀ i < 30, mem (parent + i) = F.value G i) :
    mem (parent + 14) = F.outputBase ∧ mem (parent + 15) = F.abstentionBase :=
  ⟨hData 14 (by decide), hData 15 (by decide)⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintRowFields.prepare
end S_HintRowFields20261120


