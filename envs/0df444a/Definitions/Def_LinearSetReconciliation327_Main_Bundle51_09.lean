-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_09
-- name    : LinearSetReconciliation327_Main_Bundle51_09
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T14:23:10.104745+00:00
-- url     : https://prove2.me/theorems/5f3f4d65-7ec0-4fc3-bded-8dbfea1201e5
-- title:
--   LinearSetReconciliation327 — Bundle51_09
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_09` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintChildUpdateAction20261120
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_02
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_07
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_08

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_09
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintScatter20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintScatterRow20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowScatter20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowActions20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowFields20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRunPredict20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRunFinal20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintColumnAdd20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNativeRoot20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintTreeEvents20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintTreeRanges20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDetBlocks20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDetABI20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintCRLayout20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNodeArena20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNodeInfo20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowWorkspace20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowWorkspaceCall20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintWorkspaceRecord20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPackedRead20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintToggleTrace20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPackedNodeRead20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPackedResidual20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDirectBit20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintStageChildExact20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintCombineBitmaps20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintScatter20261120
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
end -- Def_LinearSetReconciliation327_Main_HintScatter20261120

section -- Def_LinearSetReconciliation327_Main_HintScatterRow20261120
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
end -- Def_LinearSetReconciliation327_Main_HintScatterRow20261120

section -- Def_LinearSetReconciliation327_Main_HintRowScatter20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRowScatter20261120

section -- Def_LinearSetReconciliation327_Main_HintRowActions20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRowActions20261120

section -- Def_LinearSetReconciliation327_Main_HintRowFields20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRowFields20261120

section -- Def_LinearSetReconciliation327_Main_HintRunPredict20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

structure HintRowCallPre (E : RAMEnv) (G : HintGaussArea) (F : HintRowFields)
    (coords : Fin G.hints → Fin G.buckets) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (N parent : ℕ) (π : Equiv.Perm (Fin N))
    (J : Finset ℕ) : Prop where
  scan : HintScanPublic E G coords beta hPrefix F.rowLength (min F.outsideLimit (F.rowLength - G.hints))
    parent F.outsideBase F.bitmapBase
  row_bound : G.row < F.rowCount
  row_length : F.rowLength = rowLen N F.rowCount G.row
  hint_count : (hintRowMembers N F.rowCount G.row π J).length = G.hints
  hint_coords : ∀ i : Fin G.hints, (coords i).val =
    (hintRowMembers N F.rowCount G.row π J)[i.val]'(hint_count.symm ▸ i.isLt)
  bitmap_positive : 0 < F.bitmapBase
  record_end : parent + 30 ≤ G.pivotRow + G.rows
  gather_end : G.hintList + F.rowLength ≤ parent
  hint_after : parent + 30 ≤ F.hintBase
  hint_span : F.hintBase + N ≤ 2 ^ E.W
  transcript_after : parent + 30 ≤ F.transcriptBase
  transcript_span : ∀ t : Fin G.rows, F.transcriptBase + t.val * F.rowCount < 2 ^ E.W
  permutation : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val

def hintRunPredict : Stmt := hintRunRowStmt hintPredictAction

theorem hintRunPredict_sem (G : HintGaussArea) (F : HintRowFields)
    (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (N parent descriptor control base c : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (j : Fin F.rowCount)
    (hRow : G.row = j.val) (pre : HintRowCallPre E G F coords beta hPrefix N parent π J)
    (rec : HintRowRecord E descriptor parent (F.value G))
    (hDesc : state.regs 6 = descriptor) (hCtx : state.regs 14 = control)
    (hControl : control < 2 ^ E.W)
    (hBits : ∀ i : Fin N, state.mem (F.hintBase + i.val) = hintTruth (i.val ∈ J))
    (hObservations : ∀ t : Fin G.rows, state.mem (F.transcriptBase + t.val * F.rowCount) = (v t).val)
    (hBY : F.outsideLimit + 1 < 2 ^ E.W)
    (hWaitTable : F.thresholdTable + (F.outsideLimit + 1) * G.hints +
      min F.outsideLimit (F.rowLength - G.hints) < 2 ^ E.W)
    (hLookup : ∀ r ≤ min F.outsideLimit (F.rowLength - G.hints),
      E.det (F.thresholdTable + (F.outsideLimit + 1) * G.hints + r) = min G.steps (sigma G.hints F.rowLength r + c))
    (hCoeff : ∀ hNext : G.rows < G.steps, ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hOutSpan : F.outputBase + G.row < 2 ^ E.W)
    (hAbstSpan : F.abstentionBase + G.row < 2 ^ E.W)
    (hOutAfter : G.pivotRow + G.rows ≤ F.outputBase)
    (hAbstAfter : G.pivotRow + G.rows ≤ F.abstentionBase)
    (hDistinct : F.outputBase + G.row ≠ F.abstentionBase + G.row)
    (hAt : At P base (hintRunPredict.compile base)) (hPc : state.pc = base) :
    let r := min F.outsideLimit (F.rowLength - G.hints)
    let budget := (hintRowOuterBudget G F.rowLength r + 2) * (r + 1) + 12 * F.rowLength + 9 * G.rows + 390
    let pred := workerPredict N F.rowCount G.steps G.buckets F.hintLimit F.outsideLimit c j beta
      (rowImage N F.rowCount π j.val J) (List.ofFn v)
    Sem P E base (base + hintRunPredict.len) state (fun k out =>
      k ≤ budget ∧ out.regs 14 = control ∧
      out.mem (F.outputBase + G.row) = hintTruth (pred = some 1) ∧
      out.mem (F.abstentionBase + G.row) = hintTruth (pred = none) ∧
      (∀ addr, (addr < F.bitmapBase - 1 ∨ G.pivotRow + G.rows ≤ addr) →
        addr ≠ F.outputBase + G.row → addr ≠ F.abstentionBase + G.row → out.mem addr = state.mem addr)) := by
  let r := min F.outsideLimit (F.rowLength - G.hints)
  let budget := (hintRowOuterBudget G F.rowLength r + 2) * (r + 1) + 12 * F.rowLength + 9 * G.rows + 107
  let pred := workerPredict N F.rowCount G.steps G.buckets F.hintLimit F.outsideLimit c j beta
    (rowImage N F.rowCount π j.val J) (List.ofFn v)
  let Q := fun (memory : ℕ → ℕ) =>
    memory (F.outputBase + G.row) = hintTruth (pred = some 1) ∧
    memory (F.abstentionBase + G.row) = hintTruth (pred = none) ∧
    ∀ addr, (addr < F.bitmapBase - 1 ∨ G.pivotRow + G.rows ≤ addr) →
      addr ≠ F.outputBase + G.row → addr ≠ F.abstentionBase + G.row → memory addr = state.mem addr
  have hParent := pre.scan.parent_eq
  have hBitmap := pre.scan.bitmap_span
  have hOutside := pre.scan.outside_span
  have hSource := pre.scan.source
  have hRecordEnd := pre.record_end
  have hFit := rec.memory_span
  have hGather := pre.gather_end
  have hHintSpan := pre.hint_span
  have hHintAfter := pre.hint_after
  have hTranscriptAfter := pre.transcript_after
  have hNj : 0 < F.rowLength := pre.scan.positive
  have hRowBound := pre.row_bound
  have hCountFit : F.rowLength < 2 ^ E.W := rec.fits 2 (by decide)
  have hRowsFit : F.rowCount < 2 ^ E.W := rec.fits 10 (by decide)
  have hBXFit : F.hintLimit < 2 ^ E.W := rec.fits 6 (by decide)
  have hHintFit : F.hintBase < 2 ^ E.W := rec.fits 11 (by decide)
  have hObsFit : F.transcriptBase < 2 ^ E.W := rec.fits 9 (by decide)
  have hBitmapParent : F.bitmapBase ≤ parent := by omega
  change Sem P E base (base + (hintRunRowStmt hintPredictAction).len) state
    (fun k out => k ≤ budget + 23 + 260 ∧ out.regs 14 = control ∧ Q out.mem)
  apply hintRunRowStmt_sem P E state hintPredictAction descriptor parent F.bitmapBase control base
    (budget + 23) (F.value G) Q rec hDesc (F.bitmap_eq G) pre.bitmap_positive hBitmapParent hCtx hControl hAt hPc
  intro st hAtS hPcS hCtxS hFields hSaved hFrameS
  have hMeta := F.prepare G parent st.mem hParent hFields
  obtain ⟨hOutPtr, hAbstPtr⟩ := F.output_eq G parent st.mem hFields
  have hBitsS (i : Fin N) : st.mem (F.hintBase + i.val) = hintTruth (i.val ∈ J) := by
    rw [hFrameS _ (Or.inr (by omega)) (by omega), hBits]
  have hObsS (t : Fin G.rows) : st.mem (F.transcriptBase + t.val * F.rowCount) = (v t).val := by
    rw [hFrameS _ (Or.inr (by omega)) (by omega), hObservations]
  have hNative := hintPredictAction_sem P E st (base + 20) budget parent F.bitmapBase (G.pivotRow + G.rows)
    G.row F.outputBase F.abstentionBase pred (by omega) hOutSpan hAbstSpan hDistinct (by omega) (by omega)
    hAtS hPcS (by
      intro hWorkAt
      have hWork := hintPreparedPredictStmt_stable_sem G coords v beta hPrefix c N F.rowCount F.rowLength parent
        F.outsideBase F.bitmapBase F.hintBase F.transcriptBase F.hintLimit F.outsideLimit F.thresholdTable
        (st.mem F.outsideBase) π J P E st (base + 20) (hCtxS.trans hParent) pre.scan j hRow hBXFit hMeta
        (by omega) hRowBound pre.row_length pre.hint_count pre.hint_coords hRowsFit hCountFit hBY (by omega)
        hGather (by omega) hHintFit hHintSpan (by omega) (by omega) (by omega) hObsFit pre.transcript_span
        pre.permutation hBitsS hObsS hWaitTable hLookup hCoeff hWorkAt hPcS
      apply Sem.mono hWork
      rintro k out ⟨hCost, hPred, hContext, hFrame, ⟨count, hInput⟩, ⟨idx, hHeader⟩, hStable⟩
      refine ⟨hCost, hPred, hContext.trans hParent.symm, (hStable 14 (by decide) (by decide)).trans hOutPtr,
        (hStable 15 (by decide) (by decide)).trans hAbstPtr, ?_,
        hInput.bitmap_pointer.trans hMeta.bitmap_pointer.symm, hFrame⟩
      rw [show parent + 27 = G.context + 11 by omega, hHeader 11 (by decide)]
      rfl)
  apply Sem.mono hNative
  rintro k out ⟨hk, hp, ha, hCtxOut, hPtrOut, hFrameOut⟩
  have hSavedOut : out.mem (F.bitmapBase - 1) = control := by
    rw [hFrameOut _ (Or.inl (by have := pre.bitmap_positive; omega)) (by omega) (by omega), hSaved]
  refine ⟨hk, hCtxOut, hPtrOut.trans hMeta.bitmap_pointer, hSavedOut, hp, ha, ?_⟩
  intro addr hAway hNotP hNotA
  rw [hFrameOut addr (by rcases hAway with h | h <;> omega) hNotP hNotA]
  apply hFrameS
  · rcases hAway with hs | hs
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hAway with hs | hs <;> omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRunPredict_sem
end -- Def_LinearSetReconciliation327_Main_HintRunPredict20261120

section -- Def_LinearSetReconciliation327_Main_HintRunFinal20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintRunFinal : Stmt := hintRunRowStmt hintFinalAction

theorem hintRunFinal_sem (G : HintGaussArea) (F : HintRowFields)
    (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (N parent descriptor control base : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (j : Fin F.rowCount)
    (hRow : G.row = j.val) (pre : HintRowCallPre E G F coords beta hPrefix N parent π J)
    (rec : HintRowRecord E descriptor parent (F.value G))
    (hDesc : state.regs 6 = descriptor) (hCtx : state.regs 14 = control)
    (hControl : control < 2 ^ E.W)
    (hBits : ∀ i : Fin N, state.mem (F.hintBase + i.val) = hintTruth (i.val ∈ J))
    (hObservations : ∀ t : Fin G.rows, state.mem (F.transcriptBase + t.val * F.rowCount) = (v t).val)
    (hBY : F.outsideLimit + 1 < 2 ^ E.W)
    (hTableFit : F.thresholdTable + (F.outsideLimit + 1) * G.hints < 2 ^ E.W)
    (hOutFit : F.outputBase < 2 ^ E.W)
    (hOutSpan : F.outputBase + N ≤ 2 ^ E.W)
    (hOutAfter : G.pivotRow + G.rows ≤ F.outputBase)
    (hAt : At P base (hintRunFinal.compile base)) (hPc : state.pc = base) :
    let r := min F.outsideLimit (F.rowLength - G.hints)
    let budget := (hintFinalBudget G F.rowLength r + 2) * (r + 1) + hintFinalBudget G F.rowLength r +
      37 * F.rowLength + 9 * G.rows + 18 * G.hints + 8 * r + 470
    let est := workerFinal N F.rowCount G.steps G.buckets F.hintLimit F.outsideLimit j beta
      (rowImage N F.rowCount π j.val J) (List.ofFn v)
    Sem P E base (base + hintRunFinal.len) state (fun k out =>
      k ≤ budget ∧ out.regs 14 = control ∧
      (∀ i : Fin N, (π i).val % F.rowCount = G.row →
        out.mem (F.outputBase + i.val) = hintTruth ((π i).val / F.rowCount ∈ est)) ∧
      (∀ addr, (addr < F.bitmapBase - 1 ∨ G.pivotRow + G.rows ≤ addr) →
        (∀ i : Fin N, (π i).val % F.rowCount = G.row → addr ≠ F.outputBase + i.val) → out.mem addr = state.mem addr)) := by
  let r := min F.outsideLimit (F.rowLength - G.hints)
  let budget := (hintFinalBudget G F.rowLength r + 2) * (r + 1) + hintFinalBudget G F.rowLength r +
    26 * F.rowLength + 9 * G.rows + 18 * G.hints + 8 * r + 186
  let est := workerFinal N F.rowCount G.steps G.buckets F.hintLimit F.outsideLimit j beta
    (rowImage N F.rowCount π j.val J) (List.ofFn v)
  let Q := fun (memory : ℕ → ℕ) =>
    (∀ i : Fin N, (π i).val % F.rowCount = G.row →
      memory (F.outputBase + i.val) = hintTruth ((π i).val / F.rowCount ∈ est)) ∧
    ∀ addr, (addr < F.bitmapBase - 1 ∨ G.pivotRow + G.rows ≤ addr) →
      (∀ i : Fin N, (π i).val % F.rowCount = G.row → addr ≠ F.outputBase + i.val) → memory addr = state.mem addr
  have hParent := pre.scan.parent_eq
  have hBitmap := pre.scan.bitmap_span
  have hOutside := pre.scan.outside_span
  have hSource := pre.scan.source
  have hRecordEnd := pre.record_end
  have hFit := rec.memory_span
  have hGather := pre.gather_end
  have hHintSpan := pre.hint_span
  have hHintAfter := pre.hint_after
  have hTranscriptAfter := pre.transcript_after
  have hNj : 0 < F.rowLength := pre.scan.positive
  have hRowBound := pre.row_bound
  have hRowLength := pre.row_length
  have hCountFit : F.rowLength < 2 ^ E.W := rec.fits 2 (by decide)
  have hRowsFit : F.rowCount < 2 ^ E.W := rec.fits 10 (by decide)
  have hBXFit : F.hintLimit < 2 ^ E.W := rec.fits 6 (by decide)
  have hHintFit : F.hintBase < 2 ^ E.W := rec.fits 11 (by decide)
  have hObsFit : F.transcriptBase < 2 ^ E.W := rec.fits 9 (by decide)
  have hBitmapFit : F.bitmapBase < 2 ^ E.W := rec.fits 1 (by decide)
  have hNodeFit : G.node < 2 ^ E.W := rec.fits 26 (by decide)
  have hBitmapParent : F.bitmapBase ≤ parent := by omega
  set total := budget + 11 * F.rowLength + 24
  have hNativeCall := hintRunRowStmt_sem P E state hintFinalAction descriptor parent F.bitmapBase control base
    total (F.value G) Q rec hDesc (F.bitmap_eq G) pre.bitmap_positive hBitmapParent hCtx hControl hAt hPc
    (by
      intro st hAtS hPcS hCtxS hFields hSaved hFrameS
      have hMeta := F.prepare G parent st.mem hParent hFields
      have hOutPtr := (F.output_eq G parent st.mem hFields).1
      have hBitsS (i : Fin N) : st.mem (F.hintBase + i.val) = hintTruth (i.val ∈ J) := by
        rw [hFrameS _ (Or.inr (by omega)) (by omega), hBits]
      have hObsS (t : Fin G.rows) : st.mem (F.transcriptBase + t.val * F.rowCount) = (v t).val := by
        rw [hFrameS _ (Or.inr (by omega)) (by omega), hObservations]
      have hAction := hintFinalAction_sem P E st (base + 20) budget N F.rowCount G.row G.node parent
        F.bitmapBase (G.pivotRow + G.rows) F.outputBase F.bitmapBase π est (by omega) hRowBound (by omega)
        hOutFit hBitmapFit hRowsFit hNodeFit (by omega) (by omega) (by omega) hOutSpan (by omega)
        pre.permutation hAtS hPcS (by
          intro hWorkAt
          have hWork := hintPreparedFinalStmt_stable_sem G coords v beta hPrefix N F.rowCount F.rowLength parent
            F.outsideBase F.bitmapBase F.hintBase F.transcriptBase F.hintLimit F.outsideLimit F.thresholdTable
            (st.mem F.outsideBase) π J P E st (base + 20) (hCtxS.trans hParent) pre.scan j hRow hBXFit hMeta
            (by omega) hRowBound pre.row_length pre.hint_count pre.hint_coords hRowsFit hCountFit hBY hTableFit
            hGather (by omega) hHintFit hHintSpan (by omega) (by omega) (by omega) hObsFit pre.transcript_span
            pre.permutation hBitsS hObsS hWorkAt hPcS
          apply Sem.mono hWork
          rintro k out ⟨hk, hBitsOut, hCtxOut, hFrame, ⟨count, hInput⟩, ⟨idx, hHeader⟩, hStable⟩
          have hRowOut : out.mem (parent + 27) = G.row := by
            rw [show parent + 27 = G.context + 11 by omega, hHeader 11 (by decide)]
            rfl
          have hNodeOut : out.mem (parent + 26) = G.node := by
            rw [show parent + 26 = G.context + 10 by omega, hHeader 10 (by decide)]
            rfl
          exact ⟨hk, hCtxOut.trans hParent.symm, ⟨(hStable 14 (by decide) (by decide)).trans hOutPtr,
            hInput.bitmap_pointer, (hStable 10 (by decide) (by decide)).trans hMeta.gather.rows_value,
            hRowOut, hNodeOut, hInput.radix.trans hRowLength⟩, fun q hq => hBitsOut q (by omega), hFrame⟩)
      apply Sem.mono hAction
      rintro k out ⟨hk, hb, hc, hptr, hf⟩
      have hSavedOut : out.mem (F.bitmapBase - 1) = control := by
        rw [hf _ (Or.inl (by have := pre.bitmap_positive; omega)) (by intro i hi; omega), hSaved]
      refine ⟨by dsimp [total]; omega, hc, hptr, hSavedOut, hb, ?_⟩
      intro addr hAway hNot
      rw [hf addr (by rcases hAway with h | h <;> omega) hNot]
      apply hFrameS
      · rcases hAway with hs | hs
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      · rcases hAway with hs | hs <;> omega)
  apply Sem.mono hNativeCall
  rintro k out ⟨hk, hc, hb, hf⟩
  refine ⟨?_, hc, hb, hf⟩
  dsimp [total, budget, r] at hk ⊢
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRunFinal_sem
end -- Def_LinearSetReconciliation327_Main_HintRunFinal20261120

section -- Def_LinearSetReconciliation327_Main_HintColumnAdd20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintColumnAddSetup : List Instr :=
  [.imm 15 1, .qDet 4 6, .add 3 6 15, .qDet 5 3, .add 3 3 15, .qDet 6 3, .imm 8 1]
def hintColumnAddAction : Stmt := .seq (.code hintColumnAddSetup) hintAxpyStmt

structure HintColumnAddTable (E : RAMEnv) (descriptor dest source count : ℕ) : Prop where
  word : 1 < 2 ^ E.W
  span : descriptor + 2 < 2 ^ E.W
  dest_fit : dest < 2 ^ E.W
  source_fit : source < 2 ^ E.W
  dest_span : dest + count ≤ 2 ^ E.W
  source_span : source + count ≤ 2 ^ E.W
  count_fit : count < 2 ^ E.W
  dest_address : E.det descriptor = dest
  source_address : E.det (descriptor + 1) = source
  length : E.det (descriptor + 2) = count

theorem hintColumnAddSetup_spec (E : RAMEnv) (s : RAMState) (descriptor dest source count : ℕ)
    (tbl : HintColumnAddTable E descriptor dest source count) (hArg : s.regs 6 = descriptor) :
    let out := runBlock hintColumnAddSetup E s
    out.pc = s.pc + 7 ∧ out.mem = s.mem ∧ out.regs 14 = s.regs 14 ∧
      HintAxpyParams dest source count 1 out := by
  have h1 : descriptor + 1 < 2 ^ E.W := by have := tbl.span; omega
  have h2 : descriptor + 1 + 1 < 2 ^ E.W := tbl.span
  have hZ : (1 : ZMod 2).val = 1 := by decide
  refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintColumnAddSetup, runBlock, execInstr, hArg, tbl.dest_address, tbl.source_address, tbl.length,
      Nat.mod_eq_of_lt tbl.word, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt tbl.dest_fit,
      Nat.mod_eq_of_lt tbl.source_fit, Nat.mod_eq_of_lt tbl.count_fit, hZ]

/-- Add a decoded child column to the current transcript column in place.
The same action adds a decoded residual to the node's current estimate. -/
theorem hintColumnAddAction_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor dest source count base : ℕ) (f g : ℕ → ZMod 2)
    (tbl : HintColumnAddTable E descriptor dest source count) (hArg : state.regs 6 = descriptor)
    (hF : ∀ j < count, state.mem (dest + j) = (f j).val)
    (hG : ∀ j < count, state.mem (source + j) = (g j).val)
    (hSeparate : dest + count ≤ source ∨ source + count ≤ dest)
    (hAt : At P base (hintColumnAddAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 20) state (fun k out => k ≤ 11 * count + 11 ∧
      out.regs 14 = state.regs 14 ∧
      (∀ j < count, out.mem (dest + j) = (f j + g j).val) ∧
      CRMemFrame dest (dest + count) state.mem out.mem) := by
  obtain ⟨hSetupAt, hAddAt⟩ := At.seqStmt hAt
  change At P base hintColumnAddSetup at hSetupAt
  change At P (base + 7) (hintAxpyStmt.compile (base + 7)) at hAddAt
  have hSetup := hintColumnAddSetup_spec E state descriptor dest source count tbl hArg
  generalize hS : runBlock hintColumnAddSetup E state = mid at hSetup
  obtain ⟨hPcMid, hMem, hCtx, hArgs⟩ := hSetup
  have hRunSetup : (step P E)^[7] state = mid := by
    have hh := iterate_runBlock_of_at P E hintColumnAddSetup state (by rwa [hPc])
      (by simp [hintColumnAddSetup, NoBranch, Instr.NoBranchI])
    rw [hS] at hh
    exact hh
  have hD := tbl.dest_span
  have hSrc := tbl.source_span
  obtain ⟨_, k, out, hRun, hEnd, hTime, _, hOutput, _, hFrame, hRegs⟩ :=
    hintAxpyStmt_sem P E mid dest source count (base + 7) 1 f g tbl.word tbl.count_fit
      (by intro j hj; omega) (by intro j hj; omega) (by rw [hMem]; exact hF) (by rw [hMem]; exact hG)
      hSeparate hAddAt (by omega) hArgs
  have hCtrl := hRegs 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨hPc, k + 7, out, hintIterate_then (step P E) hRunSetup hRun, by omega, by omega,
    hCtrl.trans hCtx, ?_, hMem ▸ hFrame⟩
  intro j hj
  have hInside : dest ≤ dest + j ∧ dest + j < dest + count := by omega
  rw [hOutput]
  simp [hintAxpyMem, hInside]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintColumnAddAction_sem
end -- Def_LinearSetReconciliation327_Main_HintColumnAdd20261120

section -- Def_LinearSetReconciliation327_Main_HintNativeRoot20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintNativeOtherActions : List Stmt :=
  [hintUnpackAction, hintStageAction, hintRunPredict, hintRunFinal, hintToggleGateAction, hintColumnAddAction]

def hintNativeActions (S : CRSourceBundle) : List Stmt :=
  hintActionsWithCR S 75 hintNativeOtherActions hintNormalizeStmt

def hintNativeRoot (S : CRSourceBundle) : Stmt :=
  .seq hintRootEnter (.seq (hintDispatchStmt (hintNativeActions S)) hintRootExit)

def hintNativeProgram (S : CRSourceBundle) : Program := (hintNativeRoot S).compile 0 ++ [.halt]

theorem hintNativeRoot_at (S : CRSourceBundle) : At (hintNativeProgram S) 0 ((hintNativeRoot S).compile 0) := by
  intro i hi
  simp only [hintNativeProgram, Nat.zero_add, List.getElem?_append_left hi]

theorem hintNativeRoot_halt (S : CRSourceBundle) (state : RAMState) (hPc : state.pc = (hintNativeRoot S).len) :
    Halted (hintNativeProgram S) state := by
  unfold Halted
  rw [hPc, ← Stmt.length_compile (hintNativeRoot S) 0]
  simp [hintNativeProgram]

theorem hintNativeRoot_sem (S : CRSourceBundle) (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table N : ℕ) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (accept : ℕ → Bool)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table events.length N)
    (hPc : state.pc = 0) (hWordState : UpWordState E state)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hSpan : state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : state.regs 1 + min (state.regs 2) N ≤ hintMap ∨ hintMap + N < state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hOut : listBase + N ≤ resultMap) (hOutSpan : resultMap + N ≤ 2 ^ E.W)
    (hTable : HintDispatchTable E table events)
    (hTags : ∀ j : Fin events.length, events[j.val].1 < (hintNativeActions S).length)
    (hInit : ∀ mem,
      (∀ q < N, mem (hintMap + q) = hintStampValue E (state.regs 1) (min (state.regs 2) N) state.mem q) →
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → mem address = state.mem address) → I 0 mem)
    (hCursor : ∀ n mem cursor, I n mem → I n (Function.update mem (control + 2) cursor))
    (hActions : HintLocatedActions (hintNativeProgram S) E control table 75 (hintNativeActions S) events budget I)
    (hFinal : ∀ mem, I events.length mem → ∀ q < N, mem (resultMap + q) = if accept q then 1 else 0) :
    Sem (hintNativeProgram S) E 0 (hintNativeRoot S).len state (fun k out =>
      k ≤ hintDispatchBudget (hintNativeActions S) events.length budget + 29 * N + 67 ∧
      outList out = hintGatherList accept N) := by
  let P := hintNativeProgram S
  let actions := hintNativeActions S
  let dispatch := hintDispatchStmt actions
  obtain ⟨hEnterAt, hRestAt⟩ := At.seqStmt (hintNativeRoot_at S)
  change At P 0 (hintRootEnter.compile 0) at hEnterAt
  change At P 56 ((Stmt.seq dispatch hintRootExit).compile 56) at hRestAt
  obtain ⟨hDispatchAt, hExitAt⟩ := At.seqStmt hRestAt
  change At P 56 (dispatch.compile 56) at hDispatchAt
  change At P (56 + dispatch.len) (hintRootExit.compile (56 + dispatch.len)) at hExitAt
  obtain ⟨_, ke, first, hRunFirst, hFirstPc, hFirstCost, hData, hHints, hFrame⟩ :=
    hintRootEnter_sem P E state header control hintMap resultMap listBase table events.length N 0
      hdr hSource hLength hSpan hSeparate hControl hEnterAt hPc
  have hWord := hdr.word
  have hWordFirst : UpWordState E first := hRunFirst ▸ upIterate_word_bound P E state ke hWordState
  obtain ⟨_, kd, middle, hRunDispatch, hMiddlePc, hDispatchCost, hInv, _⟩ :=
    hintLocatedDispatch_sem P E first control table 56 (first.mem (control + 2))
      actions events budget I (by omega) hdr.control_span hdr.count_fit hTable hTags hData
      (hInit _ hHints hFrame) hWordFirst hCursor hActions hDispatchAt hFirstPc
  obtain ⟨_, ko, out, hRunExit, hEnd, hExitCost, hList, _⟩ :=
    hintRootExit_sem P E middle header control hintMap resultMap listBase table events.length N
      (56 + dispatch.len) hdr hOut hOutSpan accept (hFinal _ hInv) hExitAt hMiddlePc
  refine ⟨hPc, ko + (kd + ke), out, hintIterate_then (step P E)
    (hintIterate_then (step P E) hRunFirst hRunDispatch) hRunExit, ?_, ?_, hList⟩
  · change out.pc = 56 + (dispatch.len + 25)
    omega
  · change ko + (kd + ke) ≤ hintDispatchBudget actions events.length budget + 29 * N + 67
    omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNativeRoot_sem
end -- Def_LinearSetReconciliation327_Main_HintNativeRoot20261120

section -- Def_LinearSetReconciliation327_Main_HintTreeEvents20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

inductive HintTreeEvent where
  | store (node offset count : ℕ)
  | directBit (node row column offset : ℕ)
  | childCopy (parent column child offset count : ℕ)
  | residualCopy (node offset count : ℕ)
  | predict (node seedIndex column row : ℕ)
  | finishRow (node seedIndex row : ℕ)
  | childToggle (parent column child seedIndex coordinate : ℕ)
  | residualToggle (node coordinate : ℕ)
  | recoverColumn (parent column child : ℕ)
  | correctEstimate (node : ℕ)
  | decodeLeaf (node offset N t : ℕ)
  | decodeResidual (node N t : ℕ)

def HintTreeEvent.tag : HintTreeEvent → ℕ
  | .store .. | .directBit .. => 0
  | .childCopy .. | .residualCopy .. => 1
  | .predict .. => 2
  | .finishRow .. => 3
  | .childToggle .. | .residualToggle .. => 4
  | .recoverColumn .. | .correctEstimate .. => 5
  | .decodeLeaf .. | .decodeResidual .. => 6

def hintResidualEvents (CR : CRFamily) (node offset N t : ℕ) : List HintTreeEvent :=
  [.residualCopy node offset (CR.rows N t)] ++
    (List.range N).map (.residualToggle node) ++
    [.decodeResidual node N t, .correctEstimate node]

/-- Each recursive child is staged into a fresh word-aligned area. The
physical node index counts all nodes, while seed indices count only nodes
with random tables. A leaf sibling still needs a distinct memory area. -/
noncomputable def hintTreeEvents (CR : CRFamily) (payloadOffset : ℕ → ℕ) :
    (T : Node) → ℕ → ℕ → ℕ → List HintTreeEvent
  | .store N, node, _, offset => [.store node offset N]
  | .cr N t, node, _, offset => [.decodeLeaf node offset N t]
  | .direct sch t, node, seedIndex, offset =>
      (List.ofFn fun j : Fin sch.m => (List.range sch.ℓ).map fun s =>
        HintTreeEvent.directBit node j.val s (offset + j.val * sch.ℓ + s)).flatten ++
        (List.range sch.m).map (.finishRow node seedIndex) ++
        hintResidualEvents CR node (offset + sch.m * sch.ℓ) sch.N t
  | .recursive sch t _ _ children, node, seedIndex, offset =>
      (List.ofFn fun s : Fin sch.ℓ =>
        let childNode := node + 1 + ((List.ofFn fun i => (children i).nodeCount).take s.val).sum
        let childSeed := seedIndex + 1 + ((List.ofFn fun i => (schemeNodes (children i)).length).take s.val).sum
        let childOff := offset + ((List.ofFn fun i => synLen CR (children i)).take s.val).sum
        (List.range sch.m).map (.predict node seedIndex s.val) ++
          [.childCopy node s.val childNode childOff (synLen CR (children s))] ++
          (List.range sch.m).map (.childToggle node s.val childNode childSeed) ++
          hintTreeEvents CR payloadOffset (children s) childNode childSeed (payloadOffset childNode) ++
          [.recoverColumn node s.val childNode]).flatten ++
        (List.range sch.m).map (.finishRow node seedIndex) ++
        hintResidualEvents CR node (offset + ∑ s, synLen CR (children s)) sch.N t

def hintTreeDispatchEntries (events : List HintTreeEvent) (descriptor : HintTreeEvent → ℕ) :
    List (ℕ × ℕ) := events.map (fun e => (e.tag, descriptor e))

theorem hintNativeActions_count (S : CRSourceBundle) : (hintNativeActions S).length = 7 := rfl

theorem hintTreeDispatchEntries_tags (S : CRSourceBundle)
    (events : List HintTreeEvent) (descriptor : HintTreeEvent → ℕ)
    (j : Fin (hintTreeDispatchEntries events descriptor).length) :
    (hintTreeDispatchEntries events descriptor)[j.val].1 < (hintNativeActions S).length := by
  rw [hintNativeActions_count]
  simp only [hintTreeDispatchEntries, List.getElem_map]
  generalize events[j.val]'(by simpa [hintTreeDispatchEntries] using j.isLt) = event
  cases event <;> simp [HintTreeEvent.tag]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeDispatchEntries_tags
end -- Def_LinearSetReconciliation327_Main_HintTreeEvents20261120

section -- Def_LinearSetReconciliation327_Main_HintTreeRanges20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintTakeSum_succ : ∀ (cells : List ℕ) (i : ℕ) (hi : i < cells.length),
    (cells.take (i + 1)).sum = (cells.take i).sum + cells[i]
  | [], _, hi => by simp at hi
  | a :: rest, 0, _ => by simp
  | a :: rest, i + 1, hi => by
      simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]
      rw [hintTakeSum_succ rest i (by simpa using hi)]
      omega

theorem hintTakeSum_mono (cells : List ℕ) {i j : ℕ} (hLe : i ≤ j) :
    (cells.take i).sum ≤ (cells.take j).sum := by
  have hSplit := List.take_append_drop i (cells.take j)
  rw [List.take_take, Nat.min_eq_left hLe] at hSplit
  have hEq := congrArg List.sum hSplit
  rw [List.sum_append] at hEq
  omega

def hintChildPhysicalIndex {arity : ℕ} (children : Fin arity → Node) (base : ℕ)
    (s : Fin arity) : ℕ :=
  base + 1 + ((List.ofFn fun i => (children i).nodeCount).take s.val).sum

theorem hintChildPhysicalIndex_end {arity : ℕ} (children : Fin arity → Node) (base : ℕ)
    (s : Fin arity) : hintChildPhysicalIndex children base s + (children s).nodeCount ≤
      base + 1 + ∑ i, (children i).nodeCount := by
  let cells := List.ofFn (fun i => (children i).nodeCount)
  have hS : s.val < cells.length := by simpa [cells] using s.isLt
  have hSucc := hintTakeSum_succ cells s.val hS
  have hx : cells[s.val] = (children s).nodeCount := by simp [cells]
  have hSum : cells.sum = ∑ i, (children i).nodeCount := List.sum_ofFn
  have hLe := hintTakeSum_mono cells (Nat.succ_le_of_lt hS)
  rw [List.take_of_length_le le_rfl, hSucc, hx, hSum] at hLe
  change base + 1 + (cells.take s.val).sum + (children s).nodeCount ≤ _
  omega

theorem hintChildPhysicalIndex_disjoint {arity : ℕ} (children : Fin arity → Node) (base : ℕ)
    (s t : Fin arity) (hSt : s.val < t.val) :
    hintChildPhysicalIndex children base s + (children s).nodeCount ≤
      hintChildPhysicalIndex children base t := by
  let cells := List.ofFn (fun i => (children i).nodeCount)
  have hS : s.val < cells.length := by simpa [cells] using s.isLt
  have hSucc := hintTakeSum_succ cells s.val hS
  have hx : cells[s.val] = (children s).nodeCount := by simp [cells]
  have hLe := hintTakeSum_mono cells (Nat.succ_le_of_lt hSt)
  rw [hSucc, hx] at hLe
  change base + 1 + (cells.take s.val).sum + (children s).nodeCount ≤
    base + 1 + (cells.take t.val).sum
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildPhysicalIndex_disjoint
end -- Def_LinearSetReconciliation327_Main_HintTreeRanges20261120

section -- Def_LinearSetReconciliation327_Main_HintDetBlocks20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- A finite interval of the deterministic table, represented by its length and
a function on the offsets in the interval. This also represents large lookup tables. -/
structure HintDetBlock where
  length : ℕ
  value : ℕ → ℕ

def hintDetBlockOffset (blocks : List HintDetBlock) (i : ℕ) : ℕ :=
  ((blocks.take i).map HintDetBlock.length).sum

def hintDetBlockRead : List HintDetBlock → ℕ → ℕ
  | [], _ => 0
  | block :: rest, a =>
      if a < block.length then block.value a else hintDetBlockRead rest (a - block.length)

theorem hintDetBlockRead_at :
    ∀ (blocks : List HintDetBlock) (i : ℕ) (hi : i < blocks.length) (j : ℕ),
      j < blocks[i].length →
      hintDetBlockRead blocks (hintDetBlockOffset blocks i + j) = blocks[i].value j
  | [], _, hi, _, _ => by simp at hi
  | block :: rest, 0, _, j, hj => by
      have hb : j < block.length := hj
      simp [hintDetBlockRead, hintDetBlockOffset, hb]
  | block :: rest, i + 1, hi, j, hj => by
      have ht : i < rest.length := by simpa using hi
      have hOff : hintDetBlockOffset (block :: rest) (i + 1) =
          block.length + hintDetBlockOffset rest i := rfl
      have hRest : j < rest[i].length := hj
      rw [hOff]
      have hNeg : ¬block.length + hintDetBlockOffset rest i + j < block.length := by omega
      have hSub : block.length + hintDetBlockOffset rest i + j - block.length =
          hintDetBlockOffset rest i + j := by omega
      simp only [hintDetBlockRead, if_neg hNeg, hSub, List.getElem_cons_succ]
      exact hintDetBlockRead_at rest i ht j hRest

def hintAssembledDet (up : ℕ → ℕ) (header : ℕ) (blocks : List HintDetBlock) (a : ℕ) : ℕ :=
  if a = 3 then header
  else if a < header then up a
  else hintDetBlockRead blocks (a - header)

theorem hintAssembledDet_anchor (up : ℕ → ℕ) (header : ℕ) (blocks : List HintDetBlock) :
    hintAssembledDet up header blocks 3 = header := by simp [hintAssembledDet]

theorem hintAssembledDet_up (up : ℕ → ℕ) (header : ℕ) (blocks : List HintDetBlock)
    (a : ℕ) (ha : a < header) (hne : a ≠ 3) :
    hintAssembledDet up header blocks a = up a := by simp [hintAssembledDet, ha, hne]

theorem hintAssembledDet_at (up : ℕ → ℕ) (header : ℕ) (blocks : List HintDetBlock)
    (hHeader : 3 < header) (i : ℕ) (hi : i < blocks.length) (j : ℕ) (hj : j < blocks[i].length) :
    hintAssembledDet up header blocks (header + hintDetBlockOffset blocks i + j) =
      blocks[i].value j := by
  have h3 : header + hintDetBlockOffset blocks i + j ≠ 3 := by omega
  have hBefore : ¬header + hintDetBlockOffset blocks i + j < header := by omega
  have hSub : header + hintDetBlockOffset blocks i + j - header = hintDetBlockOffset blocks i + j := by omega
  rw [hintAssembledDet, if_neg h3, if_neg hBefore, hSub]
  exact hintDetBlockRead_at blocks i hi j hj

def hintDispatchDetBlock (events : List (ℕ × ℕ)) : HintDetBlock where
  length := 2 * events.length
  value := fun j =>
    let event := events.getD (j / 2) (0, 0)
    if j % 2 = 0 then event.1 else event.2

theorem hintDispatchDetBlock_tag (events : List (ℕ × ℕ)) (j : Fin events.length) :
    (hintDispatchDetBlock events).value (2 * j.val) = events[j.val].1 := by
  have hDiv : (2 * j.val) / 2 = j.val := by omega
  have hMod : (2 * j.val) % 2 = 0 := by omega
  simp only [hintDispatchDetBlock, hDiv, hMod, if_true, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem j.isLt, Option.getD_some]

theorem hintDispatchDetBlock_descriptor (events : List (ℕ × ℕ)) (j : Fin events.length) :
    (hintDispatchDetBlock events).value (2 * j.val + 1) = events[j.val].2 := by
  have hDiv : (2 * j.val + 1) / 2 = j.val := by omega
  have hMod : (2 * j.val + 1) % 2 ≠ 0 := by omega
  simp only [hintDispatchDetBlock, hDiv, if_neg hMod, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem j.isLt, Option.getD_some]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintAssembledDet_at
end -- Def_LinearSetReconciliation327_Main_HintDetBlocks20261120

section -- Def_LinearSetReconciliation327_Main_HintDetABI20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintDetBlock.At (block : HintDetBlock) (E : RAMEnv) (start : ℕ) : Prop :=
  ∀ j < block.length, E.det (start + j) = block.value j

theorem hintAssembledDet_block (E : RAMEnv) (up : ℕ → ℕ) (header : ℕ)
    (blocks : List HintDetBlock) (hDet : E.det = hintAssembledDet up header blocks)
    (hHeader : 3 < header) (i : ℕ) (hi : i < blocks.length) :
    blocks[i].At E (header + hintDetBlockOffset blocks i) := by
  intro j hj
  rw [hDet]
  exact hintAssembledDet_at up header blocks hHeader i hi j hj

theorem HintDispatchTable.of_block (E : RAMEnv) (table : ℕ) (events : List (ℕ × ℕ))
    (hAt : (hintDispatchDetBlock events).At E table)
    (hSpan : table + 2 * events.length ≤ 2 ^ E.W)
    (hFits : ∀ j : Fin events.length, events[j.val].1 < 2 ^ E.W ∧ events[j.val].2 < 2 ^ E.W) :
    HintDispatchTable E table events := by
  refine ⟨hSpan, ?_, ?_, hFits⟩
  · intro j
    have hj := j.isLt
    exact (hAt (2 * j.val) (by change 2 * j.val < 2 * events.length; omega)).trans
      (hintDispatchDetBlock_tag events j)
  · intro j
    have hj := j.isLt
    have h := hAt (2 * j.val + 1) (by change 2 * j.val + 1 < 2 * events.length; omega)
    simpa only [← Nat.add_assoc, hintDispatchDetBlock_descriptor] using h

def hintRootDetBlock (previous : ℕ → ℕ) (control hintMap resultMap listBase table count N : ℕ) :
    HintDetBlock where
  length := 16
  value := fun i =>
    match i with
    | 9 => hintMap
    | 10 => N
    | 11 => control
    | 12 => table
    | 13 => count
    | 14 => resultMap
    | 15 => listBase
    | _ => previous i

theorem HintRootHeader.of_block (E : RAMEnv) (previous : ℕ → ℕ)
    (header control hintMap resultMap listBase table count N : ℕ)
    (hAnchor : E.det 3 = header)
    (hAt : (hintRootDetBlock previous control hintMap resultMap listBase table count N).At E header)
    (hWord : 15 < 2 ^ E.W) (hSpan : header + 15 < 2 ^ E.W)
    (hControl : control + 2 < 2 ^ E.W) (hHint : hintMap + N < 2 ^ E.W)
    (hTable : table < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hResult : resultMap < 2 ^ E.W) (hList : listBase < 2 ^ E.W) :
    HintRootHeader E header control hintMap resultMap listBase table count N := by
  refine ⟨hWord, hSpan, hAnchor, hControl, ?_, hAt 12 (by change 12 < 16; decide), hAt 13 (by change 13 < 16; decide),
    hAt 14 (by change 14 < 16; decide), hAt 15 (by change 15 < 16; decide), hTable, hCount, hResult, hList⟩
  exact ⟨by omega, by omega, hAt 9 (by change 9 < 16; decide), hAt 10 (by change 10 < 16; decide), hAt 11 (by change 11 < 16; decide),
    hHint, by omega⟩

def hintUnpackDetBlock (dest offset W count : ℕ) : HintDetBlock where
  length := 4
  value
    | 0 => dest
    | 1 => offset
    | 2 => W
    | 3 => count
    | _ => 0

theorem HintUnpackTable.of_block (E : RAMEnv) (descriptor dest offset count : ℕ)
    (hAt : (hintUnpackDetBlock dest offset E.W count).At E descriptor)
    (hWord : 2 < 2 ^ E.W) (hSpan : descriptor + 3 < 2 ^ E.W)
    (hDest : dest < 2 ^ E.W) (hOffset : offset < 2 ^ E.W) (hCount : count < 2 ^ E.W) :
    HintUnpackTable E descriptor dest offset count :=
  ⟨hWord, hSpan, hDest, hOffset, hCount, hAt 0 (by change 0 < 4; decide), hAt 1 (by change 1 < 4; decide),
    hAt 2 (by change 2 < 4; decide), hAt 3 (by change 3 < 4; decide)⟩

def hintRowDetBlock (parent : ℕ) (fields : ℕ → ℕ) : HintDetBlock where
  length := 31
  value
    | 0 => parent
    | i + 1 => fields i

theorem HintRowRecord.of_block (E : RAMEnv) (descriptor parent : ℕ) (fields : ℕ → ℕ)
    (hAt : (hintRowDetBlock parent fields).At E descriptor)
    (hWord : 30 < 2 ^ E.W) (hSpan : descriptor + 31 ≤ 2 ^ E.W)
    (hParent : parent + 30 ≤ 2 ^ E.W) (hFits : ∀ j < 30, fields j < 2 ^ E.W) :
    HintRowRecord E descriptor parent fields := by
  refine ⟨hWord, hSpan, hParent, hAt 0 (by change 0 < 31; decide), ?_, hFits⟩
  intro i hi
  have h := hAt (i + 1) (by change i + 1 < 31; omega)
  simpa only [hintRowDetBlock, Nat.add_assoc, Nat.add_comm 1 i] using h

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintRootHeader.of_block
#print axioms LinearSetReconciliation327.Main.HintRowRecord.of_block
end -- Def_LinearSetReconciliation327_Main_HintDetABI20261120

section -- Def_LinearSetReconciliation327_Main_HintCRLayout20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintCRArea (w offset registers table descriptor destination control : ℕ) : HintCRNodeArea where
  offset := offset
  registers := registers
  memory := registers + 16
  table := table
  log := registers + 16 + 2 ^ (w + 1) + 1
  descriptor := descriptor
  destination := destination
  control := control

def hintCRTableBlock (w : ℕ) (det : ℕ → ℕ) : HintDetBlock :=
  ⟨2 ^ w + 1, det⟩

def hintCRCallBlock (A : HintCRNodeArea) (hostWidth w rows budget N : ℕ) : HintDetBlock where
  length := 12
  value
    | 0 => w
    | 1 => rows
    | 2 => A.offset
    | 3 => A.registers
    | 4 => A.memory
    | 5 => A.table
    | 6 => hostWidth
    | 7 => A.log
    | 8 => budget
    | 9 => A.destination
    | 10 => N
    | 11 => A.control
    | _ => 0

theorem hintCRArea_pre (S : CRSourceBundle) (E : RAMEnv) (N t offset registers table descriptor destination control : ℕ)
    (hN : 1 ≤ N) (ht : t ≤ N)
    (hWide : (S.data N t).W + 1 < E.W)
    (hWord : 11 < 2 ^ E.W) (hDescriptor : descriptor + 11 < 2 ^ E.W)
    (hControl : control < 2 ^ E.W)
    (hSpace : registers + 16 + 2 ^ ((S.data N t).W + 1) + 1 + crSourceSteps S N t + 1 < 2 ^ E.W)
    (hTableSpace : table + 2 ^ (S.data N t).W < 2 ^ E.W)
    (hOutput : destination + N < registers)
    (hInput : offset + (S.data N t).R < 2 ^ E.W)
    (hBefore : (offset + (S.data N t).R) / E.W < registers + 16)
    (hTable : (hintCRTableBlock (S.data N t).W (S.data N t).det).At E table)
    (hDescriptorData : (hintCRCallBlock
      (hintCRArea (S.data N t).W offset registers table descriptor destination control)
      E.W (S.data N t).W (S.data N t).R (crSourceSteps S N t) N).At E descriptor) :
    HintCRNodePre S E N t (hintCRArea (S.data N t).W offset registers table descriptor destination control) := by
  let A := hintCRArea (S.data N t).W offset registers table descriptor destination control
  let fields := hintCRCallBlock A E.W (S.data N t).W (S.data N t).R (crSourceSteps S N t) N
  have hGet (j : ℕ) (hj : j < 12) : E.det (descriptor + j) = fields.value j :=
    hDescriptorData j hj
  have hPow : 0 < 2 ^ (S.data N t).W := Nat.two_pow_pos _
  have hHost := (Nat.lt_two_pow_self : E.W < 2 ^ E.W)
  have hMod (j val : ℕ) (hj : j < 12) (hEq : fields.value j = val) (hVal : val < 2 ^ E.W) :
      E.det (descriptor + j) % 2 ^ E.W = val := by
    rw [hGet j hj, hEq, Nat.mod_eq_of_lt hVal]
  refine ⟨hN, ht, ⟨hWide, le_rfl, ?_, hSpace, hTableSpace, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨hWord, hDescriptor, hGet 9 (by decide), hGet 10 (by decide), hGet 11 (by decide), by change destination + N < 2 ^ E.W; omega, hControl⟩,
    hOutput, hInput, hBefore⟩
  · change registers + 16 + 2 ^ ((S.data N t).W + 1) < registers + 16 + 2 ^ ((S.data N t).W + 1) + 1
    omega
  · intro q hq
    exact hTable q (by change q < 2 ^ (S.data N t).W + 1; omega)
  · change E.det descriptor % 2 ^ E.W = (S.data N t).W
    simpa only [Nat.add_zero] using hMod 0 (S.data N t).W (by decide) rfl (by omega)
  · exact hMod 1 (S.data N t).R (by decide) rfl (by omega)
  · exact hMod 2 offset (by decide) rfl (by omega)
  · exact hMod 3 registers (by decide) rfl (by omega)
  · exact hMod 4 (registers + 16) (by decide) rfl (by omega)
  · exact hMod 5 table (by decide) rfl (by omega)
  · exact hMod 6 E.W (by decide) rfl hHost
  · exact hMod 7 (registers + 16 + 2 ^ ((S.data N t).W + 1) + 1) (by decide) rfl (by omega)
  · exact hMod 8 (crSourceSteps S N t) (by decide) rfl (by omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCRArea_pre
end -- Def_LinearSetReconciliation327_Main_HintCRLayout20261120

section -- Def_LinearSetReconciliation327_Main_HintNodeArena20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintNodeArena where
  payload : ℕ
  workStart : ℕ
  saveOffset : ℕ
  transcript : ℕ
  hints : ℕ
  result : ℕ
  residual : ℕ
  residualBitmap : ℕ
  crRegisters : ℕ
  limit : ℕ

def hintNodeArena (start W bits schemes m cols N R crWidth crSteps : ℕ) : HintNodeArena :=
  let workStart := wordsOf W bits + 1
  let saveOffset := workStart + 2 * schemes
  let transcript := start + saveOffset + 2
  let hints := transcript + m * cols
  let result := hints + N + 1
  let residual := result + N + 1
  let residualBitmap := residual + wordsOf W R + 1
  let crRegisters := residualBitmap + N + 1
  let limit := crRegisters + 16 + (2 ^ (crWidth + 1) + 1) + crSteps + 1
  ⟨start, workStart, saveOffset, transcript, hints, result, residual, residualBitmap, crRegisters, limit⟩

theorem hintNodeArena_order (start W bits schemes m cols N R crWidth crSteps : ℕ) :
    let A := hintNodeArena start W bits schemes m cols N R crWidth crSteps
    A.payload + wordsOf W bits < A.payload + A.workStart ∧
    A.payload + A.saveOffset + 2 ≤ A.transcript ∧
    A.transcript + m * cols ≤ A.hints ∧
    A.hints + N < A.result ∧
    A.result + N < A.residual ∧
    A.residual + wordsOf W R < A.residualBitmap ∧
    A.residualBitmap + N < A.crRegisters ∧
    A.crRegisters < A.limit := by
  dsimp [hintNodeArena]
  have hPow := Nat.zero_le (2 ^ crWidth)
  omega

theorem hintNodeArena_input_before (start W bits schemes m cols N R crWidth crSteps : ℕ)
    (hW : 0 < W) (input : ℕ) (hInput : input ≤ start) :
    let A := hintNodeArena start W bits schemes m cols N R crWidth crSteps
    (input * W + bits) / W < A.transcript := by
  let A := hintNodeArena start W bits schemes m cols N R crWidth crSteps
  have hCover := up_words_cover_budget W bits hW
  have hMul := Nat.div_le_div_right (c := W) hCover
  rw [Nat.mul_comm (wordsOf W bits), Nat.mul_div_cancel_left _ hW] at hMul
  change (input * W + bits) / W < A.transcript
  rw [Nat.mul_comm input W, Nat.mul_add_div hW]
  dsimp only [A, hintNodeArena]
  omega

def hintArenaStart (start stride node : ℕ) : ℕ := start + stride * node

theorem hintArenaStart_disjoint (start stride i j : ℕ) (hij : i < j) :
    hintArenaStart start stride i + stride ≤ hintArenaStart start stride j := by
  have h := Nat.mul_le_mul_left stride hij
  change stride * (i + 1) ≤ stride * j at h
  rw [Nat.mul_add, Nat.mul_one] at h
  unfold hintArenaStart
  omega

theorem hintArenaStage_separate (start stride parent child W bits : ℕ)
    (hW : 0 < W) (hNode : parent < child)
    (hPayload : wordsOf W bits < stride) :
    (hintArenaStart start stride parent * W + bits) / W < hintArenaStart start stride child := by
  rw [Nat.mul_comm (hintArenaStart start stride parent) W, Nat.mul_add_div hW]
  have hCover := Nat.div_le_div_right (c := W) (up_words_cover_budget W bits hW)
  rw [Nat.mul_comm (wordsOf W bits), Nat.mul_div_cancel_left _ hW] at hCover
  have hBefore := hintArenaStart_disjoint start stride parent child hNode
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNodeArena_order
#print axioms LinearSetReconciliation327.Main.hintNodeArena_input_before
#print axioms LinearSetReconciliation327.Main.hintArenaStage_separate
end -- Def_LinearSetReconciliation327_Main_HintNodeArena20261120

section -- Def_LinearSetReconciliation327_Main_HintNodeInfo20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintNodeInfo where
  universeSize : ℕ
  residualCapacity : ℕ
  payloadBits : ℕ
  schemes : ℕ
  rowParams : Option (ℕ × ℕ)
  children : List ℕ
  isCR : Bool
  subtree : Node
  seedIndex : ℕ

noncomputable def hintNodeInfo {P : HintParams} (CR : CRFamily) :
    {T : Node} → IsSchemeTree P T → ℕ → ℕ → HintNodeInfo
  | _, .store N, _, seed => ⟨N, 0, N, 0, none, [], false, .store N, seed⟩
  | _, .cr N t, _, seed => ⟨N, t, CR.rows N t, 0, none, [], true, .cr N t, seed⟩
  | _, .direct N X Y t, _, seed =>
      let T := Node.direct (P.scheme N X Y) t
      ⟨N, t, synLen CR T, 1, some (X, Y), [], false, T, seed⟩
  | _, .recursive N X Y t Xs Ys children _, node, seed =>
      let T := Node.recursive (P.scheme N X Y) t Xs Ys children
      ⟨N, t, synLen CR T, (schemeNodes T).length, some (X, Y),
        List.ofFn (hintChildPhysicalIndex children node), false, T, seed⟩

def hintChildSchemeIndex {ell : ℕ} (children : Fin ell → Node) (seed : ℕ) (s : Fin ell) : ℕ :=
  seed + 1 + ((List.ofFn fun z => (schemeNodes (children z)).length).take s.val).sum

noncomputable def hintNodeInfos {P : HintParams} (CR : CRFamily) :
    {T : Node} → IsSchemeTree P T → ℕ → ℕ → List HintNodeInfo
  | _, .store N, node, seed => [hintNodeInfo CR (.store (P := P) N) node seed]
  | _, .cr N t, node, seed => [hintNodeInfo CR (.cr (P := P) N t) node seed]
  | _, .direct N X Y t, node, seed => [hintNodeInfo CR (.direct (P := P) N X Y t) node seed]
  | _, .recursive N X Y t Xs Ys children hchild, node, seed =>
      hintNodeInfo CR (.recursive N X Y t Xs Ys children hchild) node seed ::
        (List.ofFn fun s => hintNodeInfos CR (hchild s) (hintChildPhysicalIndex children node s)
          (hintChildSchemeIndex children seed s)).flatten

theorem hintNodeInfos_length {P : HintParams} (CR : CRFamily) {T : Node} (h : IsSchemeTree P T) :
    ∀ node seed, (hintNodeInfos CR h node seed).length = T.nodeCount := by
  induction h with
  | store N => intro _ _; rfl
  | cr N t => intro _ _; rfl
  | direct N X Y t => intro _ _; rfl
  | recursive N X Y t Xs Ys children hchild ih =>
      intro node seed
      let f := fun s => hintNodeInfos CR (hchild s) (hintChildPhysicalIndex children node s)
        (hintChildSchemeIndex children seed s)
      have hLen : (List.ofFn f).flatten.length = ∑ s, (children s).nodeCount := by
        simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_apply, f, ih]
      simp only [hintNodeInfos, List.length_cons, Node.nodeCount]
      change (List.ofFn f).flatten.length + 1 = 1 + ∑ s, (children s).nodeCount
      rw [hLen, Nat.add_comm]

theorem hintNodeInfos_child {P : HintParams} (CR : CRFamily)
    (N X Y t : ℕ) (Xs Ys : Fin (P.scheme N X Y).ℓ → ℕ)
    (children : Fin (P.scheme N X Y).ℓ → Node) (hchild : ∀ s, IsSchemeTree P (children s))
    (node seed : ℕ) (s : Fin (P.scheme N X Y).ℓ) (i : ℕ) (hi : i < (children s).nodeCount) :
    (hintNodeInfos CR (.recursive N X Y t Xs Ys children hchild) node seed)[1 + ((List.ofFn fun z => (children z).nodeCount).take s.val).sum + i]? =
    (hintNodeInfos CR (hchild s) (hintChildPhysicalIndex children node s) (hintChildSchemeIndex children seed s))[i]? := by
  let f := fun z => hintNodeInfos CR (hchild z) (hintChildPhysicalIndex children node z)
    (hintChildSchemeIndex children seed z)
  have hLen (z) : (f z).length = (children z).nodeCount :=
    hintNodeInfos_length CR (hchild z) _ _
  have hGet := getElem?_flatten_ofFn' _ f s i (by rw [hLen]; exact hi)
  simp only [hLen] at hGet
  rw [hintNodeInfos]
  rw [show 1 + ((List.ofFn fun z => (children z).nodeCount).take s.val).sum + i =
      (((List.ofFn fun z => (children z).nodeCount).take s.val).sum + i).succ by omega]
  exact hGet

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNodeInfos_length
#print axioms LinearSetReconciliation327.Main.hintNodeInfos_child
end -- Def_LinearSetReconciliation327_Main_HintNodeInfo20261120

section -- Def_LinearSetReconciliation327_Main_HintRowWorkspace20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintRowWorkspace where
  bitmap : ℕ
  outside : ℕ
  parent : ℕ
  gauss : HintGaussArea

/-- Allocate the row arrays using the public bucket bound. The actual number
of hints changes the dimensions of the solve while the addresses stay fixed. -/
def hintRowWorkspace (start a K BY node row steps h : ℕ) : HintRowWorkspace :=
  let bitmap := start + 1
  let outside := bitmap + K
  let hints := outside + 1 + BY
  let parent := hints + K + 2 * steps
  let gauss := hintGaussDenseArea (parent + 16) a K hints node row K steps
  ⟨bitmap, outside, parent, { gauss with hints := h }⟩

theorem hintRowWorkspace_geometry (E : RAMEnv) (start a K BY node row steps h : ℕ)
    (hHints : h ≤ K)
    (hSpace : (hintRowWorkspace start a K BY node row steps K).gauss.pivotRow + a < 2 ^ E.W) :
    HintGaussGeometry E (hintRowWorkspace start a K BY node row steps h).gauss := by
  let S := hintRowWorkspace start a K BY node row steps K
  have hDense := hintGaussDenseArea_geometry E S.gauss.context a K S.gauss.hintList node row K steps (by
    dsimp only [S, hintRowWorkspace, hintGaussDenseArea] at hSpace ⊢
    omega)
  change HintGaussGeometry E S.gauss at hDense
  have hMul := Nat.mul_le_mul_right a hHints
  refine ⟨hDense.header_before, hDense.residual_before, ?_, hDense.column_before,
    hDense.residualVec_before, ?_, hDense.span⟩
  · exact (Nat.add_le_add_left hMul S.gauss.lift).trans hDense.lift_before
  · exact (Nat.add_le_add_left hHints S.gauss.kernelVec).trans hDense.kernelVec_before

theorem hintRowWorkspace_headerFits (E : RAMEnv) (start a K BY node row steps h : ℕ)
    (hHints : h ≤ K) (hA : a ≤ steps) (hK : K < 2 ^ E.W)
    (hNode : node < 2 ^ E.W) (hRow : row < 2 ^ E.W) (hSteps : steps < 2 ^ E.W)
    (hSpace : (hintRowWorkspace start a K BY node row steps K).gauss.pivotRow + a < 2 ^ E.W) :
    HintGaussHeaderFits E (hintRowWorkspace start a K BY node row steps h).gauss 0 := by
  have hPos := Nat.two_pow_pos E.W
  constructor
  · dsimp only [hintRowWorkspace, hintGaussDenseArea] at hSpace ⊢
    omega
  · intro i hi
    dsimp only [hintRowWorkspace, hintGaussDenseArea] at hSpace
    interval_cases i <;> simp only [hintGaussHeaderValue, hintRowWorkspace, hintGaussDenseArea] <;> omega

theorem hintRowWorkspace_addresses (start a K BY node row steps h Nj r : ℕ)
    (hA : a ≤ steps) (hHints : h ≤ K) (hNj : Nj ≤ K) (hR : r ≤ BY) :
    let S := hintRowWorkspace start a K BY node row steps h
    0 < S.bitmap ∧ S.bitmap + Nj ≤ S.outside ∧ S.outside + 1 + r ≤ S.gauss.hintList ∧
      S.gauss.hintList + h + 2 * a ≤ S.parent ∧ S.gauss.hintList + Nj ≤ S.parent ∧
      S.parent + 16 = S.gauss.context ∧ S.gauss.context + 16 ≤ S.gauss.residual ∧
      S.parent + 30 ≤ S.gauss.pivotRow + a := by
  dsimp only [hintRowWorkspace, hintGaussDenseArea]
  exact ⟨by omega, by omega, by omega, by omega, by omega, rfl, le_rfl, by omega⟩

noncomputable def hintWaitDetBlock (K Nj BY steps slack : ℕ) : HintDetBlock where
  length := (K + 1) * (BY + 1)
  value := fun i => min steps (HintParams.sigma (i / (BY + 1)) Nj (i % (BY + 1)) + slack)

theorem hintWaitDetBlock_read (E : RAMEnv) (K Nj BY steps slack address h limit : ℕ)
    (hAt : (hintWaitDetBlock K Nj BY steps slack).At E address)
    (hSpace : address + (K + 1) * (BY + 1) ≤ 2 ^ E.W)
    (hHints : h ≤ K) (hLimit : limit ≤ BY) :
    address + (BY + 1) * h + limit < 2 ^ E.W ∧
      ∀ r ≤ limit,
        E.det (address + (BY + 1) * h + r) = min steps (HintParams.sigma h Nj r + slack) := by
  have hNext := Nat.mul_le_mul_right (BY + 1) (Nat.succ_le_succ hHints)
  rw [Nat.succ_mul] at hNext
  change h * (BY + 1) + (BY + 1) ≤ (K + 1) * (BY + 1) at hNext
  have hRange (r : ℕ) (hr : r ≤ limit) : (BY + 1) * h + r < (K + 1) * (BY + 1) := by
    rw [Nat.mul_comm (BY + 1) h]
    omega
  refine ⟨by have := hRange limit le_rfl; omega, ?_⟩
  intro r hr
  have hr' : r < BY + 1 := by omega
  rw [Nat.add_assoc, hAt _ (hRange r hr)]
  simp only [hintWaitDetBlock, Nat.mul_add_div (by omega : 0 < BY + 1),
    Nat.div_eq_of_lt hr', Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hr']

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowWorkspace_geometry
#print axioms LinearSetReconciliation327.Main.hintWaitDetBlock_read
end -- Def_LinearSetReconciliation327_Main_HintRowWorkspace20261120

section -- Def_LinearSetReconciliation327_Main_HintRowWorkspaceCall20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintRowWorkspace.fields (S : HintRowWorkspace)
    (Nj m hintMap transcript BX BY threshold output abstentions : ℕ) : HintRowFields :=
  ⟨S.outside, S.bitmap, Nj, transcript, m, hintMap, BX, BY, threshold, output, abstentions⟩

theorem hintRowWorkspace_callPre (E : RAMEnv)
    (start a K BY node row steps N m hintMap transcript BX threshold output abstentions : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (beta : Fin steps → Fin K → ZMod 2)
    (ha : a ≤ steps) (hSteps : 0 < steps) (hRow : row < m) (hm : m ≤ N)
    (hK : rowLen N m row ≤ K) (hKFit : K < 2 ^ E.W) (hNode : node < 2 ^ E.W)
    (hStepsFit : steps < 2 ^ E.W)
    (hSpace : (hintRowWorkspace start a K BY node row steps K).gauss.pivotRow + a < 2 ^ E.W)
    (hHintAfter : (hintRowWorkspace start a K BY node row steps K).parent + 30 ≤ hintMap)
    (hHintSpan : hintMap + N ≤ 2 ^ E.W)
    (hTranscriptAfter : (hintRowWorkspace start a K BY node row steps K).parent + 30 ≤ transcript)
    (hTranscriptSpan : transcript + a * m ≤ 2 ^ E.W)
    (hCoeffSpace : (row + 1) * steps * K ≤ 2 ^ E.W)
    (hCoeff : ∀ c : Fin K, ∀ t : Fin a,
      E.coeff node (row * steps * K + c.val + t.val * K) =
        (beta ⟨t.val, t.isLt.trans_le ha⟩ c).val)
    (hPerm : ∀ p : Fin N, E.permInv node p.val = (π.symm p).val) :
    let L := hintRowMembers N m row π J
    let S := hintRowWorkspace start a K BY node row steps L.length
    let F := S.fields (rowLen N m row) m hintMap transcript BX BY threshold output abstentions
    ∃ coords : Fin L.length → Fin K,
      HintRowCallPre E S.gauss F coords beta ha N S.parent π J := by
  classical
  dsimp only
  let L := hintRowMembers N m row π J
  let Nj := rowLen N m row
  let S := hintRowWorkspace start a K BY node row steps L.length
  let F := S.fields Nj m hintMap transcript BX BY threshold output abstentions
  change ∃ coords : Fin L.length → Fin K, HintRowCallPre E S.gauss F coords beta ha N S.parent π J
  have hmPos : 0 < m := by omega
  have hPos : 0 < Nj := by
    dsimp [Nj]
    rw [HintRowCoordinates.count_eq_rowLen N m row hmPos hRow]
    simp [HintRowCoordinates.count, show row < N by omega]
  have hLen : L.length ≤ Nj := by
    simpa only [L, Nj, hintRowMembers] using
      hintGatherList_length_le (fun q => decide (q ∈ rowImage N m π row J)) Nj
  have hHints : L.length ≤ K := hLen.trans hK
  have hRowFit : row < 2 ^ E.W := by omega
  obtain ⟨coords, hInjective, hCoords, _⟩ := hintRowMembers_coords N m row K π J hmPos hRow hK
  have hGeom := hintRowWorkspace_geometry E start a K BY node row steps L.length hHints hSpace
  have hFits := hintRowWorkspace_headerFits E start a K BY node row steps L.length hHints ha hKFit
    hNode hRowFit hStepsFit hSpace
  obtain ⟨hBitmap, hBitmapSpan, hOutside, hSource, hGather, hParent, hReserve, hRecordEnd⟩ :=
    hintRowWorkspace_addresses start a K BY node row steps L.length Nj (min BY (Nj - L.length))
      ha hHints hK (min_le_left _ _)
  refine ⟨coords, ⟨?_, hRow, rfl, rfl, fun i => (hCoords i).1, hBitmap, hRecordEnd,
    hGather, hHintAfter, hHintSpan, hTranscriptAfter, ?_, hPerm⟩⟩
  · exact ⟨hGeom, hReserve, hParent, hSource, hOutside, hBitmapSpan, hInjective,
      fun i => (hCoords i).2, hK, hPos, hFits, hSteps, hCoeffSpace, hCoeff⟩
  · intro t
    change transcript + t.val * m < 2 ^ E.W
    have ht : t.val < a := t.isLt
    exact (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right ht hmPos) transcript).trans_le hTranscriptSpan

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowWorkspace_callPre
end -- Def_LinearSetReconciliation327_Main_HintRowWorkspaceCall20261120

section -- Def_LinearSetReconciliation327_Main_HintWorkspaceRecord20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintRowWorkspace_record (E : RAMEnv) (descriptor start a K BY node row steps h : ℕ)
    (F : HintRowFields)
    (hAt : let S := hintRowWorkspace start a K BY node row steps K
      (hintRowDetBlock S.parent (F.value S.gauss)).At E descriptor)
    (hWord : 30 < 2 ^ E.W) (hDet : descriptor + 31 ≤ 2 ^ E.W)
    (hParent : (hintRowWorkspace start a K BY node row steps K).parent + 30 ≤ 2 ^ E.W)
    (hFits : ∀ i < 30,
      F.value (hintRowWorkspace start a K BY node row steps K).gauss i < 2 ^ E.W) :
    let S := hintRowWorkspace start a K BY node row steps h
    HintRowRecord E descriptor S.parent (F.value S.gauss) := by
  let S := hintRowWorkspace start a K BY node row steps h
  let Smax := hintRowWorkspace start a K BY node row steps K
  have hValues (i : ℕ) (hi : i < 30) : F.value S.gauss i = F.value Smax.gauss i :=
    HintRowFields.hints_irrel F Smax.gauss h i hi
  refine HintRowRecord.of_block E descriptor S.parent (F.value S.gauss) ?_ hWord hDet hParent ?_
  · intro i hi
    cases i with
    | zero =>
        exact hAt 0 (by change 0 < 31; decide)
    | succ i =>
        have hi' : i < 30 := by change i + 1 < 31 at hi; omega
        change E.det (descriptor + (i + 1)) = F.value S.gauss i
        rw [hValues i hi']
        exact hAt (i + 1) hi
  · intro i hi
    rw [hValues i hi]
    exact hFits i hi

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowWorkspace_record
end -- Def_LinearSetReconciliation327_Main_HintWorkspaceRecord20261120

section -- Def_LinearSetReconciliation327_Main_HintPackedRead20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintBitAt_aligned {M : ℕ} (mem : ℕ → ℕ) (W base : ℕ)
    (y : Fin M → ZMod 2) (i : Fin M) (hw : 0 < W)
    (hPacked : ∀ a < wordsOf W M, mem (base + a) = packMem W y a) :
    bitAt mem W 0 (base * W + i.val) = if y i = 1 then 1 else 0 := by
  classical
  have hDiv : (base * W + i.val) / W = base + i.val / W := by
    rw [Nat.mul_comm base W, Nat.mul_add_div hw]
  have hMod : (base * W + i.val) % W = i.val % W := by
    rw [Nat.mul_comm base W, Nat.mul_add_mod]
  have hAddr := crBit_div_lt_words hw i.isLt
  unfold bitAt
  rw [Nat.zero_add, hDiv, hMod, hPacked _ hAddr, Nat.mod_eq_of_lt (packMem_lt W hw y _)]
  have hParts : i.val / W * W + i.val % W = i.val := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod _ _
  let b := packMem W y (i.val / W) / 2 ^ (i.val % W) % 2
  have hTest : decide (b = 1) = decide (∃ p : Fin M, p.val = i.val ∧ y p = 1) := by
    dsimp only [b]
    rw [← Nat.testBit_eq_decide_div_mod_eq, testBit_packMem W hw y _ _ (Nat.mod_lt _ hw), hParts]
  change b = if y i = 1 then 1 else 0
  by_cases hY : y i = 1
  · rw [if_pos hY]
    apply of_decide_eq_true
    rw [hTest]
    exact decide_eq_true ⟨i, rfl, hY⟩
  · have hNo : ¬ ∃ p : Fin M, p.val = i.val ∧ y p = 1 := by
      rintro ⟨p, hpi, hp⟩
      have he : p = i := Fin.ext hpi
      exact hY (he ▸ hp)
    have hNe : b ≠ 1 := by
      intro h
      rw [decide_eq_true h, decide_eq_false hNo] at hTest
      cases hTest
    have hBound : b < 2 := Nat.mod_lt _ (by decide)
    rw [if_neg hY]
    omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintBitAt_aligned
end -- Def_LinearSetReconciliation327_Main_HintPackedRead20261120

section -- Def_LinearSetReconciliation327_Main_HintToggleTrace20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintSketchVector (CR : CRFamily) (T : Node) (r : T.Seed) (X : Finset ℕ) :
    Fin (synLen CR T) → ZMod 2 :=
  fun i => bitVal CR T r i X

theorem hintSketchVector_empty (CR : CRFamily) (T : Node) (r : T.Seed) :
    hintSketchVector CR T r ∅ = 0 := by
  funext i
  exact bitVal_empty CR T r i

theorem hintSketchVector_xor (CR : CRFamily) (T : Node) (r : T.Seed) (X Y : Finset ℕ) :
    hintSketchVector CR T r (symmDiff X Y) =
      hintSketchVector CR T r X + hintSketchVector CR T r Y := by
  funext i
  exact bitVal_symmDiff CR T r i X Y

theorem hintToggleTrace_step (CR : CRFamily) (T : Node) (r : T.Seed) (P : Finset ℕ)
    (y : Fin (synLen CR T) → ZMod 2) (i : Fin T.N) :
    (if hintTruth (i.val ∈ P) = 0 then y + hintSketchVector CR T r (P ∩ Finset.range i.val)
      else y + hintSketchVector CR T r (P ∩ Finset.range i.val) + hintChildToggleVec CR T r i) =
      y + hintSketchVector CR T r (P ∩ Finset.range (i.val + 1)) := by
  classical
  by_cases hi : i.val ∈ P
  · have hSet : P ∩ Finset.range (i.val + 1) =
        symmDiff (P ∩ Finset.range i.val) {i.val} := by
      ext q
      by_cases hq : q = i.val
      · subst q
        simp [hi, Finset.mem_symmDiff]
      · have hlt : q < i.val + 1 ↔ q < i.val := by omega
        simp [Finset.mem_symmDiff, hq, hlt]
    rw [hSet, hintSketchVector_xor]
    simp only [hintTruth, if_pos hi, Nat.one_ne_zero, if_false]
    change y + hintSketchVector CR T r (P ∩ Finset.range i.val) + hintSketchVector CR T r {i.val} = _
    exact add_assoc _ _ _
  · have hSet : P ∩ Finset.range (i.val + 1) = P ∩ Finset.range i.val := by
      ext q
      by_cases hq : q = i.val
      · subst q
        simp [hi]
      · have hlt : q < i.val + 1 ↔ q < i.val := by omega
        simp [hlt]
    rw [hSet]
    simp [hintTruth, hi]

theorem hintToggleTrace_end (CR : CRFamily) (T : Node) (r : T.Seed) (P : Finset ℕ)
    (hP : P ⊆ Finset.range T.N) :
    hintSketchVector CR T r (P ∩ Finset.range T.N) = hintSketchVector CR T r P := by
  rw [Finset.inter_eq_left.mpr hP]

theorem hintRecoverColumn_exact (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) (j : Fin sch.m) :
    (if j.val ∈ sch.exactP lr x J s then (1 : ZMod 2) else 0) +
      (if j.val ∈ sch.exactChildInput lr x J s then 1 else 0) =
      (if j.val ∈ sch.column lr x s then 1 else 0) := by
  classical
  rw [RowScheme.exactChildInput, ite_mem_symmDiff]
  by_cases h : j.val ∈ sch.exactP lr x J s <;>
    by_cases hCol : j.val ∈ sch.column lr x s <;> simp [h, hCol] <;> decide

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintToggleTrace_step
#print axioms LinearSetReconciliation327.Main.hintRecoverColumn_exact
end -- Def_LinearSetReconciliation327_Main_HintToggleTrace20261120

section -- Def_LinearSetReconciliation327_Main_HintPackedNodeRead20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDirectPackedBit {CR : CRFamily} (E : RAMEnv) (mem : ℕ → ℕ)
    (word : ℕ) (sch : RowScheme) (t : ℕ) (r : sch.LocalSeed) (x : Finset ℕ)
    (j : Fin sch.m) (s : Fin sch.ℓ) (hW : 0 < E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.direct sch t)),
      mem (word + a) = packMem E.W (hintSketchVector CR (.direct sch t) r x) a) :
    bitAt mem E.W 0 (word * E.W + j.val * sch.ℓ + s.val) =
      (sch.code j (r.2 j) (sch.rowOf r x j) s).val := by
  let q := finProdFinEquiv (j, s)
  let i : Fin (synLen CR (.direct sch t)) := Fin.castAdd (CR.rows sch.N t) q
  have hI : i.val = j.val * sch.ℓ + s.val := by
    change s.val + sch.ℓ * j.val = j.val * sch.ℓ + s.val
    rw [Nat.mul_comm sch.ℓ, Nat.add_comm]
  have hCode : hintSketchVector CR (.direct sch t) r x i = sch.code j (r.2 j) (sch.rowOf r x j) s := by
    unfold hintSketchVector
    change bitVal CR (.direct sch t) r (Fin.castAdd (CR.rows sch.N t) (finProdFinEquiv (j, s))) x = _
    simpa only [q, Equiv.symm_apply_apply] using
      (bitVal_direct_left (CR := CR) (sch := sch) (t := t) r x q)
  have hRead := hintBitAt_aligned mem E.W word _ i hW hPacked
  rw [hCode, hI, ← Nat.add_assoc] at hRead
  have hBinary : ∀ bit : ZMod 2, bit = 0 ∨ bit = 1 := by decide
  rcases hBinary (sch.code j (r.2 j) (sch.rowOf r x j) s) with h | h
  · rw [h] at hRead ⊢
    simpa using hRead
  · rw [h] at hRead ⊢
    simpa only [if_true, eq_self, show (1 : ZMod 2).val = 1 by decide] using hRead

theorem hintRecursivePackedChild {CR : CRFamily} (E : RAMEnv) (mem : ℕ → ℕ)
    (word : ℕ) (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ)
    (child : Fin sch.ℓ → Node) (r : Node.Seed (.recursive sch t Xs Ys child)) (x : Finset ℕ)
    (s : Fin sch.ℓ) (j : Fin (synLen CR (child s))) (hW : 0 < E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.recursive sch t Xs Ys child)),
      mem (word + a) = packMem E.W (hintSketchVector CR (.recursive sch t Xs Ys child) r x) a) :
    bitAt mem E.W 0
      (word * E.W + ((List.ofFn fun z => synLen CR (child z)).take s.val).sum + j.val) =
      if hintSketchVector CR (child s) (r.2 s) (sch.column r.1 x s) j = 1 then 1 else 0 := by
  let q := finSigmaFinEquiv (⟨s, j⟩ : Sigma fun z : Fin sch.ℓ => Fin (synLen CR (child z)))
  let i : Fin (synLen CR (.recursive sch t Xs Ys child)) := Fin.castAdd (CR.rows sch.N t) q
  have hI : i.val = ((List.ofFn fun z => synLen CR (child z)).take s.val).sum + j.val :=
    finSigmaFinEquiv_val (fun z => synLen CR (child z)) s j
  have hChild : hintSketchVector CR (.recursive sch t Xs Ys child) r x i =
      hintSketchVector CR (child s) (r.2 s) (sch.column r.1 x s) j := by
    unfold hintSketchVector
    change bitVal CR (.recursive sch t Xs Ys child) r
      (Fin.castAdd (CR.rows sch.N t)
        (finSigmaFinEquiv (⟨s, j⟩ : Sigma fun z : Fin sch.ℓ => Fin (synLen CR (child z))))) x = _
    rw [bitVal_rec_left, Equiv.symm_apply_apply]
  have hRead := hintBitAt_aligned mem E.W word _ i hW hPacked
  simpa only [hChild, hI, Nat.add_assoc] using hRead

theorem hintTruePrefix_ofFn (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ)
    (a : ℕ) (ha : a ≤ sch.ℓ) (j : Fin sch.m) :
    List.ofFn (fun s : Fin a => sch.code j (lr.2 j) (sch.rowOf lr x j) ⟨s.val, s.isLt.trans_le ha⟩) =
      sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) a := by
  unfold RowScheme.truePrefix
  apply List.ext_getElem
  · simp [Nat.min_eq_left ha]
  · intro k hk0 hk1
    simp [List.getElem_map, List.getElem_take, List.getElem_finRange, List.getElem_ofFn]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectPackedBit
#print axioms LinearSetReconciliation327.Main.hintRecursivePackedChild
#print axioms LinearSetReconciliation327.Main.hintTruePrefix_ofFn
end -- Def_LinearSetReconciliation327_Main_HintPackedNodeRead20261120

section -- Def_LinearSetReconciliation327_Main_HintPackedResidual20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintPackedRight {CR : CRFamily} (E : RAMEnv) (T : Node) (r : T.Seed)
    (x : Finset ℕ) (mem : ℕ → ℕ) (word leftLen N t : ℕ)
    (hLen : synLen CR T = leftLen + CR.rows N t) (hW : 0 < E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen CR T),
      mem (word + a) = packMem E.W (hintSketchVector CR T r x) a)
    (hRight : ∀ q : Fin (CR.rows N t),
      bitVal CR T r (Fin.cast hLen.symm (Fin.natAdd leftLen q)) x =
        if q.val ∈ CR.sketch N t x then 1 else 0)
    (q : Fin (CR.rows N t)) :
    bitAt mem E.W 0 (word * E.W + leftLen + q.val) =
      hintTruth (q.val ∈ CR.sketch N t x) := by
  let i : Fin (synLen CR T) := Fin.cast hLen.symm (Fin.natAdd leftLen q)
  have hRead := hintBitAt_aligned mem E.W word (hintSketchVector CR T r x) i hW hPacked
  change bitAt mem E.W 0 (word * E.W + (leftLen + q.val)) =
    (if bitVal CR T r i x = 1 then 1 else 0) at hRead
  dsimp only [i] at hRead
  rw [hRight q] at hRead
  by_cases h : q.val ∈ CR.sketch N t x <;> simpa [h, hintTruth, Nat.add_assoc] using hRead

theorem hintDirectPackedResidual {CR : CRFamily} (E : RAMEnv) (mem : ℕ → ℕ) (word : ℕ)
    (sch : RowScheme) (t : ℕ) (r : (Node.direct sch t).Seed) (x : Finset ℕ) (hW : 0 < E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.direct sch t)),
      mem (word + a) = packMem E.W (hintSketchVector CR (.direct sch t) r x) a)
    (q : Fin (CR.rows sch.N t)) :
    bitAt mem E.W 0 (word * E.W + sch.m * sch.ℓ + q.val) =
      hintTruth (q.val ∈ CR.sketch sch.N t x) :=
  hintPackedRight E (.direct sch t) r x mem word (sch.m * sch.ℓ) sch.N t rfl hW hPacked
    (fun z => bitVal_direct_right (CR := CR) (sch := sch) (t := t) r x z) q

theorem hintRecursivePackedResidual {CR : CRFamily} (E : RAMEnv) (mem : ℕ → ℕ) (word : ℕ)
    (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ) (child : Fin sch.ℓ → Node)
    (r : (Node.recursive sch t Xs Ys child).Seed) (x : Finset ℕ) (hW : 0 < E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.recursive sch t Xs Ys child)),
      mem (word + a) = packMem E.W (hintSketchVector CR (.recursive sch t Xs Ys child) r x) a)
    (q : Fin (CR.rows sch.N t)) :
    bitAt mem E.W 0 (word * E.W + (∑ s, synLen CR (child s)) + q.val) =
      hintTruth (q.val ∈ CR.sketch sch.N t x) :=
  hintPackedRight E (.recursive sch t Xs Ys child) r x mem word (∑ s, synLen CR (child s))
    sch.N t rfl hW hPacked
    (fun z => bitVal_rec_right (CR := CR) (sch := sch) (t := t) (child := child) r x z) q

theorem hintCRBit_eq (S : CRSourceBundle) (N t : ℕ) (x : Finset ℕ)
    (hx : x ⊆ Finset.range N) (q : Fin (S.data N t).R) :
    hintTruth (q.val ∈ (crFamily S).sketch N t x) =
      if (S.data N t).H (crInput N x) q = 1 then 1 else 0 := by
  rw [crFamily_sketch S N t x hx]
  classical
  have h : q.val ∈ support ((S.data N t).H (crInput N x)) ↔
      (S.data N t).H (crInput N x) q = 1 := by
    unfold support
    constructor
    · intro h
      obtain ⟨i, hi, hiq⟩ := Finset.mem_image.mp h
      have he : i = q := Fin.ext hiq
      subst i
      exact (Finset.mem_filter.mp hi).2
    · intro h
      exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  simp only [hintTruth, h]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectPackedResidual
#print axioms LinearSetReconciliation327.Main.hintRecursivePackedResidual
#print axioms LinearSetReconciliation327.Main.hintCRBit_eq
end -- Def_LinearSetReconciliation327_Main_HintPackedResidual20261120

section -- Def_LinearSetReconciliation327_Main_HintDirectBit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintTranscriptCell (transcript rows row column : ℕ) : ℕ :=
  transcript + column * rows + row

def hintDirectBitBlock (W transcript rows row column offset : ℕ) : HintDetBlock :=
  hintUnpackDetBlock (hintTranscriptCell transcript rows row column) offset W 1

theorem hintDirectBit_sem {CR : CRFamily} (P : Program) (E : RAMEnv) (state : RAMState)
    (sch : RowScheme) (t : ℕ) (r : sch.LocalSeed) (x : Finset ℕ)
    (j : Fin sch.m) (s : Fin sch.ℓ) (word transcript descriptor base : ℕ)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.direct sch t)),
      state.mem (word + a) = packMem E.W (hintSketchVector CR (.direct sch t) r x) a)
    (hArg : state.regs 6 = descriptor)
    (hWord : 2 < 2 ^ E.W) (hDescSpan : descriptor + 3 < 2 ^ E.W)
    (hRead : (hintDirectBitBlock E.W transcript sch.m j.val s.val
      (word * E.W + j.val * sch.ℓ + s.val)).At E descriptor)
    (pre : HintUnpackPre E (hintTranscriptCell transcript sch.m j.val s.val)
      (word * E.W + j.val * sch.ℓ + s.val) 1)
    (hAt : At P base (hintUnpackAction.compile base)) (hPc : state.pc = base) :
    let dest := hintTranscriptCell transcript sch.m j.val s.val
    Sem P E base (base + 22) state (fun k out => k ≤ 24 ∧
      out.regs 14 = state.regs 14 ∧
      out.mem dest = (sch.code j (r.2 j) (sch.rowOf r x j) s).val ∧
      CRMemFrame dest (dest + 1) state.mem out.mem) := by
  let dest := hintTranscriptCell transcript sch.m j.val s.val
  let offset := word * E.W + j.val * sch.ℓ + s.val
  have hDest : dest < 2 ^ E.W := Nat.lt_of_succ_le pre.destination
  have hOffset : offset < 2 ^ E.W := Nat.lt_of_succ_le pre.offset_span
  have hTable := HintUnpackTable.of_block E descriptor dest offset 1 hRead
    hWord hDescSpan hDest hOffset pre.count_fit
  apply Sem.mono (hintUnpackAction_sem P E state descriptor dest offset 1 base hTable hArg pre hAt hPc)
  rintro k out ⟨hk, hCtx, hData, hFrame⟩
  have hBit := hintDirectPackedBit (CR := CR) E state.mem word sch t r x j s pre.positive hPacked
  have hCell := hData 0 (by decide)
  simp only [Nat.add_zero] at hCell
  exact ⟨by simpa using hk, hCtx, hCell.trans hBit, hFrame⟩

theorem hintExactEstimate_mem (sch : RowScheme) (lr : sch.LocalSeed)
    (x J : Finset ℕ) (i : Fin sch.N) (j : Fin sch.m)
    (hRow : (lr.1 i).val % sch.m = j.val) :
    i.val ∈ sch.exactEstimate lr x J ↔ (lr.1 i).val / sch.m ∈ sch.exactRowEst lr x J j := by
  classical
  unfold RowScheme.exactEstimate RowScheme.assembled assemble
  constructor
  · intro hi
    obtain ⟨u, hu, hui⟩ := Finset.mem_image.mp hi
    have he : u = i := Fin.ext hui
    subst u
    have h := (Finset.mem_filter.mp hu).2
    simpa only [hRow, dif_pos j.isLt, RowScheme.exactRowEst] using h
  · intro hi
    refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    simpa only [hRow, dif_pos j.isLt, RowScheme.exactRowEst] using hi

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectBit_sem
#print axioms LinearSetReconciliation327.Main.hintExactEstimate_mem
end -- Def_LinearSetReconciliation327_Main_HintDirectBit20261120

section -- Def_LinearSetReconciliation327_Main_HintStageChildExact20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintStageChild_exact {CR : CRFamily} (P : Program) (E : RAMEnv) (state : RAMState)
    (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ) (child : Fin sch.ℓ → Node)
    (r : (Node.recursive sch t Xs Ys child).Seed) (x : Finset ℕ) (s : Fin sch.ℓ)
    (word dest descriptor base : ℕ)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.recursive sch t Xs Ys child)),
      state.mem (word + a) = packMem E.W (hintSketchVector CR (.recursive sch t Xs Ys child) r x) a)
    (hWord : 2 < 2 ^ E.W) (hSpan : descriptor + 3 < 2 ^ E.W) (hDest : dest < 2 ^ E.W)
    (hTable : let off := word * E.W + ((List.ofFn fun z => synLen CR (child z)).take s.val).sum
      (hintUnpackDetBlock dest off E.W (synLen CR (child s))).At E descriptor)
    (pre : let off := word * E.W + ((List.ofFn fun z => synLen CR (child z)).take s.val).sum
      HintStagePre E E.W (synLen CR (child s)) off dest)
    (hFresh : ∀ a < wordsOf E.W (synLen CR (child s)), state.mem (dest + a) = 0)
    (hArg : state.regs 6 = descriptor)
    (hAt : At P base (hintStageAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 28) state (fun k out =>
      k ≤ 17 * synLen CR (child s) + 13 ∧
      out.regs 14 = state.regs 14 ∧
      (∀ a < wordsOf E.W (synLen CR (child s)), out.mem (dest + a) =
        packMem E.W (hintSketchVector CR (child s) (r.2 s) (sch.column r.1 x s)) a) ∧
      CRMemFrame dest (dest + wordsOf E.W (synLen CR (child s))) state.mem out.mem) := by
  let off := word * E.W + ((List.ofFn fun z => synLen CR (child z)).take s.val).sum
  let count := synLen CR (child s)
  have span : off + count < 2 ^ E.W := pre.input_span
  have hAbi := HintUnpackTable.of_block E descriptor dest off count hTable hWord hSpan hDest (by omega) (by omega)
  apply hintStageAction_sem P E state descriptor dest off count base hAbi hArg pre
    (hintSketchVector CR (child s) (r.2 s) (sch.column r.1 x s)) _ hFresh hAt hPc
  intro i
  exact hintRecursivePackedChild E state.mem word sch t Xs Ys child r x s i pre.width_pos hPacked

theorem hintCRStage_exact (S : CRSourceBundle) (P : Program) (E : RAMEnv) (state : RAMState)
    (N t descriptor dest offset base : ℕ) (x : Finset ℕ) (hx : x ⊆ Finset.range N)
    (hWord : 2 < 2 ^ E.W) (hSpan : descriptor + 3 < 2 ^ E.W) (hDest : dest < 2 ^ E.W)
    (hTable : (hintUnpackDetBlock dest offset E.W (S.data N t).R).At E descriptor)
    (pre : HintStagePre E E.W (S.data N t).R offset dest)
    (hBits : ∀ q : Fin (S.data N t).R, bitAt state.mem E.W 0 (offset + q.val) =
      hintTruth (q.val ∈ (crFamily S).sketch N t x))
    (hFresh : ∀ a < wordsOf E.W (S.data N t).R, state.mem (dest + a) = 0)
    (hArg : state.regs 6 = descriptor)
    (hAt : At P base (hintStageAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 28) state (fun k out =>
      k ≤ 17 * (S.data N t).R + 13 ∧ out.regs 14 = state.regs 14 ∧
      (∀ a < wordsOf E.W (S.data N t).R, out.mem (dest + a) =
        packMem E.W ((S.data N t).H (crInput N x)) a) ∧
      CRMemFrame dest (dest + wordsOf E.W (S.data N t).R) state.mem out.mem) := by
  have span := pre.input_span
  have hAbi := HintUnpackTable.of_block E descriptor dest offset _ hTable hWord hSpan hDest
    (by omega) (by omega)
  apply hintStageAction_sem P E state descriptor dest offset _ base hAbi hArg pre
    ((S.data N t).H (crInput N x)) _ hFresh hAt hPc
  intro q
  exact (hBits q).trans (hintCRBit_eq S N t x hx q)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStageChild_exact
#print axioms LinearSetReconciliation327.Main.hintCRStage_exact
end -- Def_LinearSetReconciliation327_Main_HintStageChildExact20261120

section -- Def_LinearSetReconciliation327_Main_HintCombineBitmaps20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintColumnAddBlock (dest source count : ℕ) : HintDetBlock where
  length := 3
  value
    | 0 => dest
    | 1 => source
    | 2 => count
    | _ => 0

theorem HintColumnAddTable.of_block (E : RAMEnv) (descriptor dest source count : ℕ)
    (hAt : (hintColumnAddBlock dest source count).At E descriptor)
    (hWord : 1 < 2 ^ E.W) (hSpan : descriptor + 2 < 2 ^ E.W)
    (hDest : dest < 2 ^ E.W) (hSource : source < 2 ^ E.W)
    (hDestSpan : dest + count ≤ 2 ^ E.W) (hSourceSpan : source + count ≤ 2 ^ E.W)
    (hCount : count < 2 ^ E.W) :
    HintColumnAddTable E descriptor dest source count :=
  ⟨hWord, hSpan, hDest, hSource, hDestSpan, hSourceSpan, hCount,
    hAt 0 (by change 0 < 3; decide), hAt 1 (by change 1 < 3; decide), hAt 2 (by change 2 < 3; decide)⟩

def hintGateBlock (gate coordinate detBase payBase : ℕ) : HintDetBlock where
  length := 4
  value
    | 0 => gate
    | 1 => coordinate
    | 2 => detBase
    | 3 => payBase
    | _ => 0

theorem HintToggleGateTable.of_block (E : RAMEnv) (descriptor gate coordinate detBase payBase control : ℕ)
    (hAt : (hintGateBlock gate coordinate detBase payBase).At E descriptor)
    (hWord : 3 < 2 ^ E.W) (hSpan : descriptor + 3 < 2 ^ E.W)
    (hTable : detBase + 3 < 2 ^ E.W)
    (hGate : gate < 2 ^ E.W) (hCoordinate : coordinate < 2 ^ E.W)
    (hPayload : payBase < 2 ^ E.W) (hControl : control < 2 ^ E.W)
    (hReturn : E.det (detBase + 3) = control) :
    HintToggleGateTable E descriptor gate coordinate detBase payBase control :=
  ⟨hWord, hSpan, hTable, hGate, hCoordinate, hPayload, hControl,
    hAt 0 (by change 0 < 4; decide), hAt 1 (by change 1 < 4; decide),
    hAt 2 (by change 2 < 4; decide), hAt 3 (by change 3 < 4; decide), hReturn⟩

def HintBitmap (mem : ℕ → ℕ) (base N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ i < N, mem (base + i) = hintTruth (i ∈ A)

theorem hintAddBitmaps_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor dest source N base : ℕ) (X Y : Finset ℕ)
    (tbl : HintColumnAddTable E descriptor dest source N) (hArg : state.regs 6 = descriptor)
    (hX : HintBitmap state.mem dest N X) (hY : HintBitmap state.mem source N Y)
    (hSeparate : dest + N ≤ source ∨ source + N ≤ dest)
    (hAt : At P base (hintColumnAddAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 20) state (fun k out =>
      k ≤ 11 * N + 11 ∧ out.regs 14 = state.regs 14 ∧
      HintBitmap out.mem dest N (symmDiff X Y) ∧
      CRMemFrame dest (dest + N) state.mem out.mem) := by
  let f := fun j : ℕ => if j ∈ X then (1 : ZMod 2) else 0
  let g := fun j : ℕ => if j ∈ Y then (1 : ZMod 2) else 0
  have hBit (j : ℕ) (S : Finset ℕ) :
      (if j ∈ S then (1 : ZMod 2) else 0).val = hintTruth (j ∈ S) := by
    by_cases h : j ∈ S
    · rw [if_pos h, hintTruth, if_pos h]
      decide
    · rw [if_neg h, hintTruth, if_neg h]
      decide
  have hf (i : ℕ) (hi : i < N) : state.mem (dest + i) = (f i).val :=
    (hX i hi).trans (hBit i X).symm
  have hg (i : ℕ) (hi : i < N) : state.mem (source + i) = (g i).val :=
    (hY i hi).trans (hBit i Y).symm
  apply Sem.mono (hintColumnAddAction_sem P E state descriptor dest source N base f g tbl hArg
    hf hg hSeparate hAt hPc)
  rintro k out ⟨hk, hc, hOut, hFrame⟩
  refine ⟨hk, hc, ?_, hFrame⟩
  intro i hi
  rw [hOut i hi, ← hBit]
  change (f i + g i).val = _
  unfold f g
  rw [ite_mem_symmDiff]

theorem hintPlusResidual (x estimate : Finset ℕ) : symmDiff estimate (symmDiff x estimate) = x := by
  ext a
  simp only [Finset.mem_symmDiff]
  tauto

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintToggleGateTable.of_block
#print axioms LinearSetReconciliation327.Main.hintAddBitmaps_sem
#print axioms LinearSetReconciliation327.Main.hintPlusResidual
end -- Def_LinearSetReconciliation327_Main_HintCombineBitmaps20261120


