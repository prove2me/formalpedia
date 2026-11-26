-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_06
-- name    : LinearSetReconciliation327_Main_B65_06
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T04:54:52.126321+00:00
-- url     : https://prove2.me/theorems/c8a1d1bd-d92b-5863-bb85-474aca4ada1b
-- title:
--   Theorem 6.5 supporting machine proof B65_06
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_04
set_option autoImplicit false

section S_HintGatherBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintGatherArgs (dest source rows row node count : ℕ) (s : RAMState) : Prop where
  dest_value : s.regs 4 = dest
  source_value : s.regs 5 = source
  rows_value : s.regs 7 = rows
  row_value : s.regs 10 = row
  node_value : s.regs 12 = node
  count_value : s.regs 6 = count
  one_value : s.regs 15 = 1

def hintGatherHead : List Instr :=
  [.mul 8 0 7, .add 8 8 10, .qPermInv 8 12 8, .add 8 5 8, .load 9 8]
def hintGatherTail : List Instr :=
  [.add 3 4 1, .store 3 0, .add 1 1 9, .add 0 0 15]
def hintGatherBody : List Instr := hintGatherHead ++ hintGatherTail

theorem hintGatherHead_spec (E : RAMEnv) (s : RAMState)
    (dest source rows row node count q coord flag : ℕ)
    (hArgs : HintGatherArgs dest source rows row node count s) (hQ : s.regs 0 = q)
    (hPos : row + q * rows < 2 ^ E.W) (hSource : source + coord < 2 ^ E.W)
    (hFlag : flag < 2 ^ E.W) (hInv : E.permInv node (row + q * rows) = coord)
    (hRead : s.mem (source + coord) = flag) :
    let out := runBlock hintGatherHead E s
    out.pc = s.pc + 5 ∧ out.mem = s.mem ∧ out.regs 9 = flag ∧
      (∀ r : Fin 16, r ≠ 8 → r ≠ 9 → out.regs r = s.regs r) := by
  have hMul : q * rows < 2 ^ E.W := by omega
  have hAddr : q * rows + row < 2 ^ E.W := by omega
  have hCoord : coord < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [hintGatherHead, runBlock, execInstr]
  · have hLookup : E.permInv node (q * rows + row) = coord := by simpa [Nat.add_comm] using hInv
    simp [hintGatherHead, runBlock, execInstr, hQ, hArgs.rows_value, hArgs.row_value,
      hArgs.node_value, hArgs.source_value, hLookup, hRead, Nat.mod_eq_of_lt hMul,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hCoord, Nat.mod_eq_of_lt hSource,
      Nat.mod_eq_of_lt hFlag]
  · intro r h8 h9
    simp [hintGatherHead, runBlock, execInstr, h8, h9]

theorem hintGatherTail_spec (E : RAMEnv) (s : RAMState)
    (dest source rows row node count q used flag : ℕ)
    (hArgs : HintGatherArgs dest source rows row node count s)
    (hQ : s.regs 0 = q) (hUsed : s.regs 1 = used) (hFlag : s.regs 9 = flag)
    (hDest : dest + used < 2 ^ E.W) (hNext : q + 1 < 2 ^ E.W) (hUsedNext : used + flag < 2 ^ E.W) :
    let out := runBlock hintGatherTail E s
    out.pc = s.pc + 4 ∧ out.mem = Function.update s.mem (dest + used) q ∧
      out.regs 0 = q + 1 ∧ out.regs 1 = used + flag ∧
      (∀ r : Fin 16, r ≠ 0 → r ≠ 1 → r ≠ 3 → out.regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hintGatherTail, runBlock, execInstr]
  · simp [hintGatherTail, runBlock, execInstr, hArgs.dest_value, hUsed, hQ, Nat.mod_eq_of_lt hDest]
  · simp [hintGatherTail, runBlock, execInstr, hQ, hArgs.one_value, Nat.mod_eq_of_lt hNext]
  · simp [hintGatherTail, runBlock, execInstr, hUsed, hFlag, Nat.mod_eq_of_lt hUsedNext]
  · intro r h0 h1 h3
    simp [hintGatherTail, runBlock, execInstr, h0, h1, h3]

theorem hintGatherBody_spec (E : RAMEnv) (s : RAMState)
    (dest source rows row node count q used coord flag : ℕ)
    (hArgs : HintGatherArgs dest source rows row node count s)
    (hQ : s.regs 0 = q) (hUsed : s.regs 1 = used)
    (hPos : row + q * rows < 2 ^ E.W) (hSource : source + coord < 2 ^ E.W)
    (hFlag : flag < 2 ^ E.W) (hInv : E.permInv node (row + q * rows) = coord)
    (hRead : s.mem (source + coord) = flag)
    (hDest : dest + used < 2 ^ E.W) (hNext : q + 1 < 2 ^ E.W) (hUsedNext : used + flag < 2 ^ E.W) :
    let out := runBlock hintGatherBody E s
    out.pc = s.pc + 9 ∧ out.mem = Function.update s.mem (dest + used) q ∧
      out.regs 0 = q + 1 ∧ out.regs 1 = used + flag ∧
      HintGatherArgs dest source rows row node count out ∧ out.regs 14 = s.regs 14 := by
  have hHead := hintGatherHead_spec E s dest source rows row node count q coord flag
    hArgs hQ hPos hSource hFlag hInv hRead
  generalize hHeadExec : runBlock hintGatherHead E s = mid at hHead
  obtain ⟨hPcH, hMemH, hFlagH, hRegsH⟩ := hHead
  have hPreserveH (r : Fin 16) (hr : r ≠ 8) (hr' : r ≠ 9) (value : ℕ)
      (h : s.regs r = value) : mid.regs r = value := (hRegsH r hr hr').trans h
  have hArgsH : HintGatherArgs dest source rows row node count mid :=
    ⟨hPreserveH 4 (by decide) (by decide) _ hArgs.dest_value,
      hPreserveH 5 (by decide) (by decide) _ hArgs.source_value,
      hPreserveH 7 (by decide) (by decide) _ hArgs.rows_value,
      hPreserveH 10 (by decide) (by decide) _ hArgs.row_value,
      hPreserveH 12 (by decide) (by decide) _ hArgs.node_value,
      hPreserveH 6 (by decide) (by decide) _ hArgs.count_value,
      hPreserveH 15 (by decide) (by decide) _ hArgs.one_value⟩
  have hTail := hintGatherTail_spec E mid dest source rows row node count q used flag hArgsH
    (hPreserveH 0 (by decide) (by decide) _ hQ) (hPreserveH 1 (by decide) (by decide) _ hUsed)
    hFlagH hDest hNext hUsedNext
  generalize hTailExec : runBlock hintGatherTail E mid = out at hTail
  obtain ⟨hPcT, hMemT, hQOut, hUsedOut, hRegsT⟩ := hTail
  have hPreserveT (r : Fin 16) (h0 : r ≠ 0) (h1 : r ≠ 1) (h3 : r ≠ 3) (value : ℕ)
      (h : mid.regs r = value) : out.regs r = value := (hRegsT r h0 h1 h3).trans h
  have hRun : runBlock hintGatherBody E s = out := by
    rw [hintGatherBody, runBlock_append, hHeadExec, hTailExec]
  rw [hRun]
  refine ⟨by omega, by rw [hMemT, hMemH], hQOut, hUsedOut, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hPreserveT 4 (by decide) (by decide) (by decide) _ hArgsH.dest_value
  · exact hPreserveT 5 (by decide) (by decide) (by decide) _ hArgsH.source_value
  · exact hPreserveT 7 (by decide) (by decide) (by decide) _ hArgsH.rows_value
  · exact hPreserveT 10 (by decide) (by decide) (by decide) _ hArgsH.row_value
  · exact hPreserveT 12 (by decide) (by decide) (by decide) _ hArgsH.node_value
  · exact hPreserveT 6 (by decide) (by decide) (by decide) _ hArgsH.count_value
  · exact hPreserveT 15 (by decide) (by decide) (by decide) _ hArgsH.one_value
  · exact hPreserveT 14 (by decide) (by decide) (by decide) _ (hRegsH 14 (by decide) (by decide))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGatherBody_spec
end S_HintGatherBody20261120
section S_HintGather20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintGatherList (accept : ℕ → Bool) (q : ℕ) : List ℕ := (List.range q).filter accept

theorem hintGatherList_length_le (accept : ℕ → Bool) (q : ℕ) :
    (hintGatherList accept q).length ≤ q := by
  simpa [hintGatherList] using List.length_filter_le accept (List.range q)

theorem hintGatherList_succ (accept : ℕ → Bool) (q : ℕ) :
    hintGatherList accept (q + 1) = hintGatherList accept q ++ (if accept q then [q] else []) := by
  cases hb : accept q <;> simp [hintGatherList, List.range_succ, hb]

structure HintGatherSource (E : RAMEnv) (dest source rows row node count : ℕ)
    (coord : ℕ → ℕ) (accept : ℕ → Bool) (original : ℕ → ℕ) : Prop where
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  dest_end : dest + count ≤ source
  destination_fit : dest + count ≤ 2 ^ E.W
  position_fit : ∀ q < count, row + q * rows < 2 ^ E.W
  source_fit : ∀ q < count, source + coord q < 2 ^ E.W
  inverse : ∀ q < count, E.permInv node (row + q * rows) = coord q
  hint_bit : ∀ q < count, original (source + coord q) = if accept q then 1 else 0

structure HintGatherInv (dest source rows row node count q : ℕ) (accept : ℕ → Bool)
    (original : ℕ → ℕ) (s : RAMState) : Prop where
  args : HintGatherArgs dest source rows row node count s
  index : s.regs 0 = q
  used : s.regs 1 = (hintGatherList accept q).length
  stored : ∀ (i : ℕ) (hi : i < (hintGatherList accept q).length),
    s.mem (dest + i) = (hintGatherList accept q)[i]
  frame : CRMemFrame dest (dest + count) original s.mem

theorem hintGatherInv_step (E : RAMEnv) (s : RAMState)
    (dest source rows row node count q : ℕ) (coord : ℕ → ℕ) (accept : ℕ → Bool) (original : ℕ → ℕ)
    (hSource : HintGatherSource E dest source rows row node count coord accept original)
    (hq : q < count) (hInv : HintGatherInv dest source rows row node count q accept original s) :
    let out := runBlock hintGatherBody E s
    HintGatherInv dest source rows row node count (q + 1) accept original out ∧ out.regs 14 = s.regs 14 := by
  let L := hintGatherList accept q
  let flag : ℕ := if accept q then 1 else 0
  have hLen : L.length ≤ q := hintGatherList_length_le accept q
  have hCount := hSource.count_fit
  have hDest := hSource.destination_fit
  have hEnd := hSource.dest_end
  have hWord := hSource.word
  have hFlag : flag ≤ 1 := by dsimp [flag]; split <;> omega
  have hRead : s.mem (source + coord q) = flag :=
    (hInv.frame _ (Or.inr (by omega))).trans (hSource.hint_bit q hq)
  have hBlock := hintGatherBody_spec E s dest source rows row node count q L.length (coord q) flag
    hInv.args hInv.index hInv.used (hSource.position_fit q hq) (hSource.source_fit q hq)
    (by omega) (hSource.inverse q hq) hRead (by omega) (by omega) (by omega)
  generalize hExec : runBlock hintGatherBody E s = out at hBlock
  obtain ⟨_, hMem, hQ, hUsed, hArgs, hCtx⟩ := hBlock
  have hSucc : hintGatherList accept (q + 1) = L ++ (if accept q then [q] else []) :=
    hintGatherList_succ accept q
  refine ⟨⟨hArgs, hQ, ?_, ?_, ?_⟩, hCtx⟩
  · rw [hUsed, hSucc]
    cases hb : accept q <;> simp [flag, hb]
  · intro i hi
    rw [hMem]
    have transfer (a b : List ℕ) (heq : a = b) (j : ℕ) (hj : j < a.length) :
        a[j] = b[j]'(heq ▸ hj) := by
      subst b
      rfl
    have hAt : ∀ (j : ℕ) (hj : j < (hintGatherList accept (q + 1)).length),
        (hintGatherList accept (q + 1))[j] = (L ++ (if accept q then [q] else []))[j]'(hSucc ▸ hj) := by
      intro j hj
      exact transfer _ _ hSucc j hj
    rw [hAt i hi]
    by_cases hOld : i < L.length
    · rw [Function.update_of_ne (by omega : dest + i ≠ dest + L.length)]
      rw [List.getElem_append_left hOld]
      exact hInv.stored i hOld
    · have hNew : i = L.length := by
        have hh := hintGatherList_length_le accept (q + 1)
        have hLen' : (hintGatherList accept (q + 1)).length ≤ L.length + 1 := by
          rw [hSucc]
          cases hb : accept q <;> simp [hb]
        omega
      have hYes : accept q = true := by
        cases hb : accept q with
        | false =>
          have hEqLen : (hintGatherList accept (q + 1)).length = L.length := by simp [hSucc, hb]
          omega
        | true => rfl
      subst i
      simp [hYes]
  · intro addr hAway
    have hNe : addr ≠ dest + L.length := by rcases hAway with hBefore | hAfter <;> omega
    rw [hMem, Function.update_of_ne hNe, hInv.frame addr hAway]


theorem HintGatherInv.pc {dest source rows row node count q : ℕ}
    {accept : ℕ → Bool} {original : ℕ → ℕ} {s : RAMState}
    (h : HintGatherInv dest source rows row node count q accept original s) (pc : ℕ) :
    HintGatherInv dest source rows row node count q accept original {s with pc := pc} :=
  ⟨⟨h.args.dest_value, h.args.source_value, h.args.rows_value, h.args.row_value,
    h.args.node_value, h.args.count_value, h.args.one_value⟩, h.index, h.used, h.stored, h.frame⟩

theorem HintGatherInv.test {dest source rows row node count q : ℕ}
    {accept : ℕ → Bool} {original : ℕ → ℕ} {s : RAMState}
    (h : HintGatherInv dest source rows row node count q accept original s) (E : RAMEnv) :
    HintGatherInv dest source rows row node count q accept original (runBlock (Cond.lt 2 0 6).code E s) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.args.dest_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.source_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.rows_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.row_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.node_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.count_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.one_value
  · simpa [Cond.code, runBlock, execInstr] using h.index
  · simpa [Cond.code, runBlock, execInstr] using h.used
  · simpa [Cond.code, runBlock, execInstr] using h.stored
  · simpa [Cond.code, runBlock, execInstr] using h.frame

def hintGatherLoop : Stmt := .loop (.lt 2 0 6) (.code hintGatherBody)

theorem hintGatherLoop_len : hintGatherLoop.len = 12 := rfl

theorem hintGatherLoop_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source rows row node count base : ℕ) (coord : ℕ → ℕ) (accept : ℕ → Bool) (original : ℕ → ℕ)
    (hSource : HintGatherSource E dest source rows row node count coord accept original)
    (hInv : HintGatherInv dest source rows row node count 0 accept original state)
    (hAt : At P base (hintGatherLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 12) state (fun k out => k ≤ 12 * count + 2 ∧
      HintGatherInv dest source rows row node count count accept original out ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ q, q + left = count ∧
    HintGatherInv dest source rows row node count q accept original st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintGatherBody := (at_loop hAt).2.2.1
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
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintGatherBody).len) st
        (fun k out => k ≤ 9 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨q, hQ, hData, hCtx⟩ := hI
    have hStep := hintGatherInv_step E st dest source rows row node count q coord accept original hSource
      (by omega) hData
    generalize hMid : runBlock hintGatherBody E st = mid at hStep
    have hNative := Sem.block P E (base + 2) hintGatherBody st hBodyAt
      (by simp [hintGatherBody, hintGatherHead, hintGatherTail, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨hCost.le, q + 1, by omega, hStep.1, hStep.2.trans hCtx⟩
  have hInitial : I count state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintGatherBody) hAt hSource.word I 9
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, q, hQ, hFinal, hCtx⟩ := hOut
  have hEq : q = count := by omega
  rw [hEq] at hFinal
  exact ⟨hCost, hFinal, hCtx⟩

def hintGatherInit : List Instr := [.imm 0 0, .imm 1 0]
def hintGatherStmt : Stmt := .seq (.code hintGatherInit) hintGatherLoop

theorem hintGatherStmt_len : hintGatherStmt.len = 14 := rfl

/-- Gather the accepted row-local coordinates in ascending order. The physical
array is scratch space with capacity equal to the length of the whole row. -/
theorem hintGatherStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source rows row node count base : ℕ) (coord : ℕ → ℕ) (accept : ℕ → Bool)
    (hSource : HintGatherSource E dest source rows row node count coord accept state.mem)
    (hArgs : HintGatherArgs dest source rows row node count state)
    (hAt : At P base (hintGatherStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 14) state (fun k out => k ≤ 12 * count + 4 ∧
      HintGatherInv dest source rows row node count count accept state.mem out ∧ out.regs 14 = state.regs 14) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintGatherInit at hInitAt
  change At P (base + 2) (hintGatherLoop.compile (base + 2)) at hLoopAt
  have hInit : let out := runBlock hintGatherInit E state
      out.pc = state.pc + 2 ∧ out.regs 14 = state.regs 14 ∧
      HintGatherInv dest source rows row node count 0 accept state.mem out := by
    refine ⟨?_, ?_, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
    · simp [hintGatherInit, runBlock, execInstr]
    · simp [hintGatherInit, runBlock, execInstr]
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.dest_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.source_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.rows_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.row_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.node_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.count_value
    · simpa [hintGatherInit, runBlock, execInstr] using hArgs.one_value
    · simp [hintGatherInit, runBlock, execInstr]
    · simp [hintGatherInit, runBlock, execInstr, hintGatherList]
    · intro i hi
      simp [hintGatherList] at hi
    · intro addr hAway
      rfl
  generalize hI : runBlock hintGatherInit E state = mid at hInit
  obtain ⟨hPcI, hCtxI, hInvI⟩ := hInit
  have hRunI : (step P E)^[2] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGatherInit state (by rwa [hPc])
      (by simp [hintGatherInit, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  obtain ⟨_, k, out, hRun, hPcOut, hCost, hInvOut, hCtx⟩ :=
    hintGatherLoop_sem P E mid dest source rows row node count (base + 2) coord accept state.mem
      hSource hInvI hLoopAt (by omega)
  exact ⟨hPc, k + 2, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega,
    hInvOut, hCtx.trans hCtxI⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGatherStmt_sem
end S_HintGather20261120
section S_HintRowCoordinates20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

namespace HintRowCoordinates

def count (N m row : ℕ) : ℕ :=
  if row < N then (N - 1 - row) / m + 1 else 0

theorem lt_count_iff (N m row q : ℕ) (hm : 0 < m) :
    q < count N m row ↔ row + q * m < N := by
  unfold count
  split
  next hRow =>
    have hDiv : q ≤ (N - 1 - row) / m ↔ q * m ≤ N - 1 - row := Nat.le_div_iff_mul_le hm
    omega
  next hRow =>
    omega

theorem count_eq_rowLen (N m row : ℕ) (hm : 0 < m) (hRow : row < m) :
    rowLen N m row = count N m row := by
  classical
  have hInj : Function.Injective (fun q : ℕ => row + q * m) := by
    intro x y heq
    exact Nat.eq_of_mul_eq_mul_right hm (Nat.add_left_cancel heq)
  have hSet : (Finset.range N).filter (fun p => p % m = row) =
      (Finset.range (count N m row)).image (fun q => row + q * m) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpN, hmod⟩ := Finset.mem_filter.mp hp
      have hDecomp : row + (p / m) * m = p := by
        rw [← hmod, Nat.mul_comm]
        exact Nat.mod_add_div p m
      refine Finset.mem_image.mpr ⟨p / m, Finset.mem_range.mpr ?_, hDecomp⟩
      rw [lt_count_iff N m row _ hm, hDecomp]
      exact Finset.mem_range.mp hpN
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((lt_count_iff N m row q hm).mp (Finset.mem_range.mp hq)),
          by simp [Nat.add_mod, Nat.mod_eq_of_lt hRow]⟩
  unfold rowLen
  rw [hSet, Finset.card_image_of_injective _ hInj, Finset.card_range]

theorem index_lt (N m row q : ℕ) (hm : 0 < m) (hRow : row < m) (hq : q < rowLen N m row) :
    row + q * m < N := by
  rw [count_eq_rowLen N m row hm hRow] at hq
  exact (lt_count_iff N m row q hm).mp hq

theorem mem_rowImage_iff (N m row q : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (hq : q < rowLen N m row) :
    q ∈ rowImage N m π row J ↔
      (π.symm ⟨row + q * m, index_lt N m row q hm hRow hq⟩).val ∈ J := by
  classical
  let p : Fin N := ⟨row + q * m, index_lt N m row q hm hRow hq⟩
  change q ∈ rowImage N m π row J ↔ (π.symm p).val ∈ J
  unfold rowImage
  constructor
  · intro h
    obtain ⟨i, hi, hDiv⟩ := Finset.mem_image.mp h
    obtain ⟨_, hiJ, hMod⟩ := Finset.mem_filter.mp hi
    have heq : π i = p := by
      apply Fin.ext
      change (π i).val = row + q * m
      rw [← hMod, ← hDiv, Nat.mul_comm ((π i).val / m) m, Nat.mod_add_div]
    have hSame : i = π.symm p := by rw [← heq, Equiv.symm_apply_apply]
    exact hSame ▸ hiJ
  · intro h
    refine Finset.mem_image.mpr ⟨π.symm p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, ?_⟩, ?_⟩
    · rw [Equiv.apply_symm_apply]
      change (row + q * m) % m = row
      simp [Nat.add_mod, Nat.mod_eq_of_lt hRow]
    · rw [Equiv.apply_symm_apply]
      change (row + q * m) / m = q
      rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hRow, Nat.zero_add]

theorem mem_rowImage_lt (N m row q : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (hq : q ∈ rowImage N m π row J) :
    q < rowLen N m row := by
  obtain ⟨i, hi, hDiv⟩ := Finset.mem_image.mp hq
  have hMod := (Finset.mem_filter.mp hi).2.2
  have hDecomp : row + q * m = (π i).val := by
    rw [← hMod, ← hDiv, Nat.mul_comm, Nat.mod_add_div]
  rw [count_eq_rowLen N m row hm hRow, lt_count_iff N m row q hm, hDecomp]
  exact (π i).isLt

end HintRowCoordinates
end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintRowCoordinates.mem_rowImage_iff
end S_HintRowCoordinates20261120
section S_HintGatherRowImage20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

open Classical in
noncomputable def hintRowMembers (N m row : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ) : List ℕ :=
  hintGatherList (fun q => decide (q ∈ rowImage N m π row J)) (rowLen N m row)

theorem hintRowMembers_mem (N m row : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (q : ℕ) :
    q ∈ hintRowMembers N m row π J ↔ q ∈ rowImage N m π row J := by
  classical
  simp only [hintRowMembers, hintGatherList, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨And.right, fun hq => ⟨HintRowCoordinates.mem_rowImage_lt N m row q π J hm hRow hq, hq⟩⟩

theorem hintRowMembers_nodup (N m row : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ) :
    (hintRowMembers N m row π J).Nodup := by
  unfold hintRowMembers hintGatherList
  exact List.Nodup.filter _ List.nodup_range

theorem hintRowMembers_coords (N m row K : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (hK : rowLen N m row ≤ K) :
    let L := hintRowMembers N m row π J
    ∃ coords : Fin L.length → Fin K,
      Function.Injective coords ∧
      (∀ i : Fin L.length, (coords i).val = L[i.val] ∧ (coords i).val < rowLen N m row) ∧
      Finset.univ.image (fun i => (coords i).val) = rowImage N m π row J := by
  classical
  let L := hintRowMembers N m row π J
  have hIndex (i : Fin L.length) : L[i.val] < rowLen N m row := by
    have hMem := List.getElem_mem (l := L) i.isLt
    exact HintRowCoordinates.mem_rowImage_lt N m row L[i.val] π J hm hRow
      ((hintRowMembers_mem N m row π J hm hRow _).mp hMem)
  let coords : Fin L.length → Fin K := fun i => ⟨L[i.val], (hIndex i).trans_le hK⟩
  refine ⟨coords, ?_, fun i => ⟨rfl, hIndex i⟩, ?_⟩
  · intro i i' hEq
    apply Fin.ext
    exact (hintRowMembers_nodup N m row π J).getElem_inj_iff.mp (congrArg Fin.val hEq)
  · ext q
    constructor
    · intro h
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact (hintRowMembers_mem N m row π J hm hRow _).mp (List.getElem_mem (l := L) i.isLt)
    · intro h
      have hMem : q ∈ L := (hintRowMembers_mem N m row π J hm hRow q).mpr h
      obtain ⟨i, hi, hq⟩ := List.mem_iff_getElem.mp hMem
      exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hq⟩

/-- Apply the actual gathering code to a bitmap in the node's original coordinates. -/
theorem hintGatherRowImage_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (N m row node dest source base : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m) (hWord : 1 < 2 ^ E.W)
    (hCount : rowLen N m row < 2 ^ E.W) (hEnd : dest + rowLen N m row ≤ source)
    (hSourceSpan : source + N ≤ 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (source + c.val) = hintTruth (c.val ∈ J))
    (hArgs : HintGatherArgs dest source m row node (rowLen N m row) state)
    (hAt : At P base (hintGatherStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 14) state (fun k out => k ≤ 12 * rowLen N m row + 4 ∧
      out.regs 1 = (hintRowMembers N m row π J).length ∧
      (∀ (i : ℕ) (hi : i < (hintRowMembers N m row π J).length),
        out.mem (dest + i) = (hintRowMembers N m row π J)[i]) ∧
      CRMemFrame dest (dest + rowLen N m row) state.mem out.mem ∧ out.regs 14 = state.regs 14) := by
  classical
  let count := rowLen N m row
  let coord : ℕ → ℕ := fun q =>
    if hq : q < count then (π.symm ⟨row + q * m, HintRowCoordinates.index_lt N m row q hm hRow hq⟩).val
    else 0
  let accept : ℕ → Bool := fun q => decide (q ∈ rowImage N m π row J)
  have hSrc : HintGatherSource E dest source m row node count coord accept state.mem := by
    refine ⟨hWord, hCount, hEnd, by dsimp [count]; omega, ?_, ?_, ?_, ?_⟩
    · intro q hq
      have h := HintRowCoordinates.index_lt N m row q hm hRow hq
      omega
    · intro q hq
      simp only [coord, dif_pos hq]
      have h := (π.symm ⟨row + q * m, HintRowCoordinates.index_lt N m row q hm hRow hq⟩).isLt
      omega
    · intro q hq
      simp only [coord, dif_pos hq]
      exact hPerm ⟨row + q * m, HintRowCoordinates.index_lt N m row q hm hRow hq⟩
    · intro q hq
      simp only [coord, dif_pos hq]
      rw [hBits, ← hintTruth_congr (HintRowCoordinates.mem_rowImage_iff N m row q π J hm hRow hq)]
      simp [accept, hintTruth]
  have hNative := hintGatherStmt_sem P E state dest source m row node count base coord accept hSrc hArgs hAt hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, hInv, hCtx⟩ := hOut
  exact ⟨hCost, hInv.used, hInv.stored, hInv.frame, hCtx⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGatherRowImage_sem
end S_HintGatherRowImage20261120
section S_HintRowGather20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintGatherFetch : List Instr :=
  hintParentLoad 4 25 ++ hintParentLoad 5 11 ++ hintParentLoad 7 10 ++
    hintParentLoad 10 27 ++ hintParentLoad 12 26 ++ hintParentLoad 6 2 ++ [.imm 15 1]

def hintGatherSetup : List Instr := hintScanParent ++ hintGatherFetch

theorem hintGatherSetup_length : hintGatherSetup.length = 21 := rfl

structure HintGatherMetadata (parent dest source rows row node count : ℕ) (memory : ℕ → ℕ) : Prop where
  dest_value : memory (parent + 25) = dest
  source_value : memory (parent + 11) = source
  rows_value : memory (parent + 10) = rows
  row_value : memory (parent + 27) = row
  node_value : memory (parent + 26) = node
  count_value : memory (parent + 2) = count

theorem hintGatherSetup_spec (E : RAMEnv) (s : RAMState)
    (parent dest source rows row node count : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W) (hContext : s.regs 14 = parent + 16)
    (hMeta : HintGatherMetadata parent dest source rows row node count s.mem)
    (hDest : dest < 2 ^ E.W) (hSrc : source < 2 ^ E.W) (hRows : rows < 2 ^ E.W)
    (hRow : row < 2 ^ E.W) (hNode : node < 2 ^ E.W) (hCount : count < 2 ^ E.W) :
    let out := runBlock hintGatherSetup E s
    out.pc = s.pc + 21 ∧ out.mem = s.mem ∧ HintGatherArgs dest source rows row node count out ∧
      out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hParent := hintScanParent_spec E s parent (by omega) hContext
  generalize hP : runBlock hintScanParent E s = mid at hParent
  obtain ⟨hPcP, hMemP, h11, h14⟩ := hParent
  have hFetch : let out := runBlock hintGatherFetch E mid
      out.pc = mid.pc + 19 ∧ out.mem = mid.mem ∧ HintGatherArgs dest source rows row node count out ∧
        out.regs 14 = parent + 16 := by
    have hRead25 : mid.mem (parent + 25) = dest := by
      rw [hMemP]
      exact hMeta.dest_value
    have hOff25 : 25 < 2 ^ E.W := by omega
    have hAddr25 : parent + 25 < 2 ^ E.W := by omega
    have hRead11 : mid.mem (parent + 11) = source := by
      rw [hMemP]
      exact hMeta.source_value
    have hOff11 : 11 < 2 ^ E.W := by omega
    have hAddr11 : parent + 11 < 2 ^ E.W := by omega
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
      simp [hintGatherFetch, hintParentLoad, runBlock, execInstr, h11, h14,
        hRead25, hRead11, hRead10, hRead27, hRead26, hRead2,
        Nat.mod_eq_of_lt hOff25, Nat.mod_eq_of_lt hAddr25, Nat.mod_eq_of_lt hOff11,
        Nat.mod_eq_of_lt hAddr11, Nat.mod_eq_of_lt hOff10, Nat.mod_eq_of_lt hAddr10,
        Nat.mod_eq_of_lt hOff27, Nat.mod_eq_of_lt hAddr27, Nat.mod_eq_of_lt hOff26,
        Nat.mod_eq_of_lt hAddr26, Nat.mod_eq_of_lt hOff2, Nat.mod_eq_of_lt hAddr2,
        Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hSrc, Nat.mod_eq_of_lt hRows,
        Nat.mod_eq_of_lt hRow, Nat.mod_eq_of_lt hNode, Nat.mod_eq_of_lt hCount,
        Nat.mod_eq_of_lt hWord]
  generalize hF : runBlock hintGatherFetch E mid = out at hFetch
  obtain ⟨hPcF, hMemF, hArgsF, hCtxF⟩ := hFetch
  have hRun : runBlock hintGatherSetup E s = out := by
    rw [hintGatherSetup, runBlock_append, hP, hF]
  rw [hRun]
  exact ⟨by omega, hMemF.trans hMemP, hArgsF, hCtxF⟩


def hintRowGatherStmt : Stmt := .seq (.code hintGatherSetup) hintGatherStmt

theorem hintRowGatherStmt_len : hintRowGatherStmt.len = 35 := rfl

theorem hintRowGatherStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (N m row node parent dest source base : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (hm : 0 < m) (hRow : row < m)
    (hSpan : parent + 29 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hMeta : HintGatherMetadata parent dest source m row node (rowLen N m row) state.mem)
    (hDest : dest < 2 ^ E.W) (hSrc : source < 2 ^ E.W) (hRows : m < 2 ^ E.W) (hNode : node < 2 ^ E.W)
    (hCount : rowLen N m row < 2 ^ E.W) (hEnd : dest + rowLen N m row ≤ source)
    (hSourceSpan : source + N ≤ 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (source + c.val) = hintTruth (c.val ∈ J))
    (hAt : At P base (hintRowGatherStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 35) state (fun k out => k ≤ 12 * rowLen N m row + 25 ∧
      out.regs 1 = (hintRowMembers N m row π J).length ∧
      (∀ (i : ℕ) (hi : i < (hintRowMembers N m row π J).length),
        out.mem (dest + i) = (hintRowMembers N m row π J)[i]) ∧
      CRMemFrame dest (dest + rowLen N m row) state.mem out.mem ∧ out.regs 14 = parent + 16) := by
  obtain ⟨hSetupAt, hGatherAt⟩ := At.seqStmt hAt
  change At P base hintGatherSetup at hSetupAt
  change At P (base + 21) (hintGatherStmt.compile (base + 21)) at hGatherAt
  have hSetup := hintGatherSetup_spec E state parent dest source m row node (rowLen N m row)
    hSpan hContext hMeta hDest hSrc hRows (hRow.trans hRows) hNode hCount
  generalize hS : runBlock hintGatherSetup E state = mid at hSetup
  obtain ⟨hPcS, hMemS, hArgsS, hCtxS⟩ := hSetup
  have hRunS : (step P E)^[21] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGatherSetup state (by rwa [hPc])
      (by simp [hintGatherSetup, hintGatherFetch, hintScanParent, hintParentLoad, NoBranch, Instr.NoBranchI])
    simpa only [hintGatherSetup_length, hS] using hh
  obtain ⟨_, kG, out, hRunG, hPcG, hCost, hLength, hList, hFrame, hCtx⟩ :=
    hintGatherRowImage_sem P E mid N m row node dest source (base + 21) π J hm hRow (by omega)
      hCount hEnd hSourceSpan hPerm (by intro c; rw [hMemS]; exact hBits c) hArgsS hGatherAt (by omega)
  refine ⟨hPc, kG + 21, out, hintIterate_then (step P E) hRunS hRunG, by omega,
    by omega, hLength, hList, ?_, hCtx.trans hCtxS⟩
  rw [← hMemS]
  exact hFrame

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowGatherStmt_sem
end S_HintRowGather20261120


