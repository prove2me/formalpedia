-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_08EmitCore
-- name    : LinearSetReconciliation327_Main_B65_08EmitCore
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T06:53:25.281451+00:00
-- url     : https://prove2.me/theorems/4f46a4c4-9601-4ae0-b176-d2c802f8653d
-- title:
--   Theorem 6.5 supporting machine proof B65_08EmitCore
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_06
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Definitions.Def_LinearSetReconciliation327_Main_HintCRFrame20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintGaussInit20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintLoopFuel20261120
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
set_option autoImplicit false

section S_HintEmitBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintEmitBody : List Instr :=
  [.add 3 5 0, .load 9 3, .add 3 4 1, .store 3 0, .add 1 1 9, .add 0 0 15]

structure HintEmitArgs (dest source count : ℕ) (s : RAMState) : Prop where
  destination : s.regs 4 = dest
  source_value : s.regs 5 = source
  length : s.regs 6 = count
  one : s.regs 15 = 1

theorem hintEmitBody_spec (E : RAMEnv) (s : RAMState) (dest source count q used flag : ℕ)
    (args : HintEmitArgs dest source count s) (hQ : s.regs 0 = q) (hUsed : s.regs 1 = used)
    (hSource : source + q < 2 ^ E.W) (hDest : dest + used < 2 ^ E.W)
    (hRead : s.mem (source + q) = flag) (hFlag : flag < 2 ^ E.W)
    (hNext : q + 1 < 2 ^ E.W) (hUsedNext : used + flag < 2 ^ E.W) :
    let out := runBlock hintEmitBody E s
    out.pc = s.pc + 6 ∧ out.mem = Function.update s.mem (dest + used) q ∧
      out.regs 0 = q + 1 ∧ out.regs 1 = used + flag ∧ HintEmitArgs dest source count out ∧
      out.regs 14 = s.regs 14 := by
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintEmitBody, runBlock, execInstr, args.destination, args.source_value, args.length, args.one,
      hQ, hUsed, hRead, Nat.mod_eq_of_lt hSource, Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hFlag,
      Nat.mod_eq_of_lt hNext, Nat.mod_eq_of_lt hUsedNext]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEmitBody_spec
end S_HintEmitBody20261120
section S_HintEmit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintEmitSource (E : RAMEnv) (dest source count : ℕ)
    (accept : ℕ → Bool) (original : ℕ → ℕ) : Prop where
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  dest_end : dest + count ≤ source
  destination_fit : dest + count ≤ 2 ^ E.W
  source_fit : ∀ q < count, source + q < 2 ^ E.W
  hint_bit : ∀ q < count, original (source + q) = if accept q then 1 else 0

structure HintEmitInv (dest source count q : ℕ) (accept : ℕ → Bool)
    (original : ℕ → ℕ) (s : RAMState) : Prop where
  args : HintEmitArgs dest source count s
  index : s.regs 0 = q
  used : s.regs 1 = (hintGatherList accept q).length
  stored : ∀ (i : ℕ) (hi : i < (hintGatherList accept q).length),
    s.mem (dest + i) = (hintGatherList accept q)[i]
  frame : CRMemFrame dest (dest + count) original s.mem

theorem hintEmitInv_step (E : RAMEnv) (s : RAMState)
    (dest source count q : ℕ) (accept : ℕ → Bool) (original : ℕ → ℕ)
    (hSource : HintEmitSource E dest source count accept original)
    (hq : q < count) (hInv : HintEmitInv dest source count q accept original s) :
    let out := runBlock hintEmitBody E s
    HintEmitInv dest source count (q + 1) accept original out ∧ out.regs 14 = s.regs 14 := by
  let L := hintGatherList accept q
  let flag : ℕ := if accept q then 1 else 0
  have hLen : L.length ≤ q := hintGatherList_length_le accept q
  have hCount := hSource.count_fit
  have hDest := hSource.destination_fit
  have hEnd := hSource.dest_end
  have hWord := hSource.word
  have hFlag : flag ≤ 1 := by dsimp [flag]; split <;> omega
  have hRead : s.mem (source + q) = flag :=
    (hInv.frame _ (Or.inr (by omega))).trans (hSource.hint_bit q hq)
  have hBlock := hintEmitBody_spec E s dest source count q L.length flag
    hInv.args hInv.index hInv.used (hSource.source_fit q hq) (by omega) hRead (by omega) (by omega) (by omega)
  generalize hExec : runBlock hintEmitBody E s = out at hBlock
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


theorem HintEmitInv.pc {dest source count q : ℕ}
    {accept : ℕ → Bool} {original : ℕ → ℕ} {s : RAMState}
    (h : HintEmitInv dest source count q accept original s) (pc : ℕ) :
    HintEmitInv dest source count q accept original {s with pc := pc} :=
  ⟨⟨h.args.destination, h.args.source_value, h.args.length, h.args.one⟩, h.index, h.used, h.stored, h.frame⟩

theorem HintEmitInv.test {dest source count q : ℕ}
    {accept : ℕ → Bool} {original : ℕ → ℕ} {s : RAMState}
    (h : HintEmitInv dest source count q accept original s) (E : RAMEnv) :
    HintEmitInv dest source count q accept original (runBlock (Cond.lt 2 0 6).code E s) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.args.destination
  · simpa [Cond.code, runBlock, execInstr] using h.args.source_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.length
  · simpa [Cond.code, runBlock, execInstr] using h.args.one
  · simpa [Cond.code, runBlock, execInstr] using h.index
  · simpa [Cond.code, runBlock, execInstr] using h.used
  · simpa [Cond.code, runBlock, execInstr] using h.stored
  · simpa [Cond.code, runBlock, execInstr] using h.frame

def hintEmitLoop : Stmt := .loop (.lt 2 0 6) (.code hintEmitBody)

theorem hintEmitLoop_len : hintEmitLoop.len = 9 := rfl

theorem hintEmitLoop_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source count base : ℕ) (accept : ℕ → Bool) (original : ℕ → ℕ)
    (hSource : HintEmitSource E dest source count accept original)
    (hInv : HintEmitInv dest source count 0 accept original state)
    (hAt : At P base (hintEmitLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 9) state (fun k out => k ≤ 9 * count + 2 ∧
      HintEmitInv dest source count count accept original out ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ q, q + left = count ∧
    HintEmitInv dest source count q accept original st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintEmitBody := (at_loop hAt).2.2.1
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
    rw [hData.index, hData.args.length]; omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 6).eval st := by
    intro st hI
    obtain ⟨q, hQ, hData, _⟩ := hI
    change ¬ st.regs 0 < st.regs 6
    rw [hData.index, hData.args.length]; omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintEmitBody).len) st
        (fun k out => k ≤ 6 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨q, hQ, hData, hCtx⟩ := hI
    have hStep := hintEmitInv_step E st dest source count q accept original hSource
      (by omega) hData
    generalize hMid : runBlock hintEmitBody E st = mid at hStep
    have hNative := Sem.block P E (base + 2) hintEmitBody st hBodyAt
      (by simp [hintEmitBody, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨hCost.le, q + 1, by omega, hStep.1, hStep.2.trans hCtx⟩
  have hInitial : I count state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintEmitBody) hAt hSource.word I 6
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, q, hQ, hFinal, hCtx⟩ := hOut
  have hEq : q = count := by omega
  rw [hEq] at hFinal
  exact ⟨hCost, hFinal, hCtx⟩

def hintEmitInit : List Instr := [.imm 0 0, .imm 1 0]
def hintEmitStmt : Stmt := .seq (.code hintEmitInit) hintEmitLoop

theorem hintEmitStmt_len : hintEmitStmt.len = 11 := rfl

/-- Write the support of an explicit bitmap in increasing order. The output
buffer reserves enough space for all indices, including tentative writes. -/
theorem hintEmitStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source count base : ℕ) (accept : ℕ → Bool)
    (hSource : HintEmitSource E dest source count accept state.mem)
    (hArgs : HintEmitArgs dest source count state)
    (hAt : At P base (hintEmitStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 11) state (fun k out => k ≤ 9 * count + 4 ∧
      HintEmitInv dest source count count accept state.mem out ∧ out.regs 14 = state.regs 14) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintEmitInit at hInitAt
  change At P (base + 2) (hintEmitLoop.compile (base + 2)) at hLoopAt
  have hInit : let out := runBlock hintEmitInit E state
      out.pc = state.pc + 2 ∧ out.regs 14 = state.regs 14 ∧
      HintEmitInv dest source count 0 accept state.mem out := by
    refine ⟨?_, ?_, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
    · simp [hintEmitInit, runBlock, execInstr]
    · simp [hintEmitInit, runBlock, execInstr]
    · simpa [hintEmitInit, runBlock, execInstr] using hArgs.destination
    · simpa [hintEmitInit, runBlock, execInstr] using hArgs.source_value
    · simpa [hintEmitInit, runBlock, execInstr] using hArgs.length
    · simpa [hintEmitInit, runBlock, execInstr] using hArgs.one
    · simp [hintEmitInit, runBlock, execInstr]
    · simp [hintEmitInit, runBlock, execInstr, hintGatherList]
    · intro i hi
      simp [hintGatherList] at hi
    · intro addr hAway
      rfl
  generalize hI : runBlock hintEmitInit E state = mid at hInit
  obtain ⟨hPcI, hCtxI, hInvI⟩ := hInit
  have hRunI : (step P E)^[2] state = mid := by
    have hh := iterate_runBlock_of_at P E hintEmitInit state (by rwa [hPc])
      (by simp [hintEmitInit, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  obtain ⟨_, k, out, hRun, hPcOut, hCost, hInvOut, hCtx⟩ :=
    hintEmitLoop_sem P E mid dest source count (base + 2) accept state.mem
      hSource hInvI hLoopAt (by omega)
  exact ⟨hPc, k + 2, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega,
    hInvOut, hCtx.trans hCtxI⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEmitStmt_sem
end S_HintEmit20261120
section S_HintEmitFinish20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintEmitFinish : List Instr := [.imm 3 0, .add 0 4 3]
def hintEmitResult : Stmt := .seq hintEmitStmt (.code hintEmitFinish)

theorem hintEmitResult_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source count base : ℕ) (accept : ℕ → Bool)
    (hSource : HintEmitSource E dest source count accept state.mem) (hFit : dest < 2 ^ E.W)
    (hArgs : HintEmitArgs dest source count state)
    (hAt : At P base (hintEmitResult.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 13) state (fun k out => k ≤ 9 * count + 6 ∧
      out.regs 14 = state.regs 14 ∧ outList out = hintGatherList accept count ∧
      CRMemFrame dest (dest + count) state.mem out.mem) := by
  obtain ⟨hEmitAt, hFinishAt⟩ := At.seqStmt hAt
  change At P base (hintEmitStmt.compile base) at hEmitAt
  change At P (base + 11) hintEmitFinish at hFinishAt
  obtain ⟨_, k, mid, hRun, hPcMid, hCost, hInv, hContext⟩ :=
    hintEmitStmt_sem P E state dest source count base accept hSource hArgs hEmitAt hPc
  let out := runBlock hintEmitFinish E mid
  have hRunF : (step P E)^[2] mid = out :=
    iterate_runBlock_of_at P E hintEmitFinish mid (by rwa [hPcMid])
      (by simp [hintEmitFinish, NoBranch, Instr.NoBranchI])
  have hOutPc : out.pc = base + 13 := by simp [out, hintEmitFinish, runBlock, execInstr, hPcMid]
  have hCtx : out.regs 14 = state.regs 14 := by simp [out, hintEmitFinish, runBlock, execInstr, hContext]
  have hPointer : out.regs 0 = dest := by
    simp [out, hintEmitFinish, runBlock, execInstr, hInv.args.destination, Nat.mod_eq_of_lt hFit]
  have hCount : out.regs 1 = (hintGatherList accept count).length := by
    simp [out, hintEmitFinish, runBlock, execInstr, hInv.used]
  refine ⟨hPc, 2 + k, out, hintIterate_then (step P E) hRun hRunF, hOutPc, by omega, hCtx, ?_, hInv.frame⟩
  apply List.ext_getElem
  · simp [outList, hCount]
  · intro j hJ hJ'
    have hMem : out.mem = mid.mem := rfl
    simpa [outList, hPointer, hMem] using hInv.stored j hJ'

theorem hintEmitResult_support {N : ℕ} (state : RAMState) (x : Fin N → ZMod 2) (accept : ℕ → Bool)
    (hAccept : ∀ i : Fin N, accept i.val = true ↔ x i = 1)
    (hList : outList state = hintGatherList accept N) : OutputsSupport state x := by
  rw [OutputsSupport, hList]
  constructor
  · exact List.Nodup.filter _ List.nodup_range
  · intro j
    simp only [hintGatherList, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hj, hA⟩
      exact ⟨⟨j, hj⟩, rfl, (hAccept ⟨j, hj⟩).mp hA⟩
    · rintro ⟨i, rfl, hI⟩
      exact ⟨i.isLt, (hAccept i).mpr hI⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEmitResult_sem
#print axioms LinearSetReconciliation327.Main.hintEmitResult_support
end S_HintEmitFinish20261120


