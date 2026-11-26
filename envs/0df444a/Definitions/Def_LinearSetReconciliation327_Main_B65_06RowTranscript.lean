-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_06RowTranscript
-- name    : LinearSetReconciliation327_Main_B65_06RowTranscript
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T04:32:44.411281+00:00
-- url     : https://prove2.me/theorems/3b95830a-fed1-54ae-9aa8-1a872fc10be4
-- title:
--   Theorem 6.5 supporting machine proof B65_06RowTranscript
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_03
set_option autoImplicit false

section S_HintTranscript20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintTranscriptFetch : List Instr :=
  hintParentLoad 4 25 ++ hintParentLoad 5 9 ++ hintParentLoad 7 10 ++
    hintParentLoad 6 16 ++ hintParentLoad 8 17
def hintTranscriptTail : List Instr := [.add 4 4 8, .add 4 4 6, .imm 15 1]
def hintTranscriptSetup : List Instr := hintScanParent ++ hintTranscriptFetch ++ hintTranscriptTail

theorem hintTranscriptSetup_length : hintTranscriptSetup.length = 20 := rfl

theorem hintTranscriptSetup_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState)
    (parent src stride index : ℕ)
    (hParent : parent + 16 = G.context) (hContext : state.regs 14 = G.context)
    (hHeader : HintGaussHeader G index state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hSrc : src < 2 ^ E.W) (hStride : stride < 2 ^ E.W)
    (hReadSrc : state.mem (parent + 9) = src) (hReadStride : state.mem (parent + 10) = stride)
    (hDest : G.hintList + G.hints + G.rows < 2 ^ E.W) :
    let out := runBlock hintTranscriptSetup E state
    out.pc = state.pc + 20 ∧ out.mem = state.mem ∧
      HintCopyParams (G.hintList + G.hints + G.rows) src stride G.rows out ∧ out.regs 14 = G.context := by
  have hSpan := hFits.span
  have hWord : 1 < 2 ^ E.W := by omega
  have hFirstAddr : G.hintList + G.hints < 2 ^ E.W := by omega
  have hP := hintScanParent_spec E state parent (by omega) (hContext.trans hParent.symm)
  generalize hPExec : runBlock hintScanParent E state = sP at hP
  obtain ⟨hPcP, hMemP, hPointerP, hCtxP⟩ := hP
  have hFetch : let out := runBlock hintTranscriptFetch E sP
      out.pc = sP.pc + 15 ∧ out.mem = sP.mem ∧
      out.regs 4 = G.hintList ∧ out.regs 5 = src ∧ out.regs 7 = stride ∧
      out.regs 6 = G.rows ∧ out.regs 8 = G.hints ∧ out.regs 14 = parent + 16 := by
    have hRead25 : sP.mem (parent + 25) = G.hintList := by
      rw [hMemP, show parent + 25 = G.context + 9 by omega]
      exact hHeader 9 (by decide)
    have hVal25 : G.hintList < 2 ^ E.W := hFits.values 9 (by decide)
    have hOff25 : 25 < 2 ^ E.W := by omega
    have hAddr25 : parent + 25 < 2 ^ E.W := by omega
    have hRead9 : sP.mem (parent + 9) = src := by rw [hMemP]; exact hReadSrc
    have hOff9 : 9 < 2 ^ E.W := by omega
    have hAddr9 : parent + 9 < 2 ^ E.W := by omega
    have hRead10 : sP.mem (parent + 10) = stride := by rw [hMemP]; exact hReadStride
    have hOff10 : 10 < 2 ^ E.W := by omega
    have hAddr10 : parent + 10 < 2 ^ E.W := by omega
    have hRead16 : sP.mem (parent + 16) = G.rows := by
      rw [hMemP, show parent + 16 = G.context + 0 by omega]
      exact hHeader 0 (by decide)
    have hVal16 : G.rows < 2 ^ E.W := hFits.values 0 (by decide)
    have hOff16 : 16 < 2 ^ E.W := by omega
    have hAddr16 : parent + 16 < 2 ^ E.W := by omega
    have hRead17 : sP.mem (parent + 17) = G.hints := by
      rw [hMemP, show parent + 17 = G.context + 1 by omega]
      exact hHeader 1 (by decide)
    have hVal17 : G.hints < 2 ^ E.W := hFits.values 1 (by decide)
    have hOff17 : 17 < 2 ^ E.W := by omega
    have hAddr17 : parent + 17 < 2 ^ E.W := by omega
    refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hintTranscriptFetch, hintParentLoad, runBlock, execInstr, hPointerP, hCtxP,
        hRead25, hRead9, hRead10, hRead16, hRead17,
        Nat.mod_eq_of_lt hOff25, Nat.mod_eq_of_lt hAddr25, Nat.mod_eq_of_lt hOff9,
        Nat.mod_eq_of_lt hAddr9, Nat.mod_eq_of_lt hOff10, Nat.mod_eq_of_lt hAddr10,
        Nat.mod_eq_of_lt hOff16, Nat.mod_eq_of_lt hAddr16, Nat.mod_eq_of_lt hOff17,
        Nat.mod_eq_of_lt hAddr17, Nat.mod_eq_of_lt hVal25, Nat.mod_eq_of_lt hVal16,
        Nat.mod_eq_of_lt hVal17, Nat.mod_eq_of_lt hSrc, Nat.mod_eq_of_lt hStride]

  generalize hFExec : runBlock hintTranscriptFetch E sP = sF at hFetch
  obtain ⟨hPcF, hMemF, h4, h5, h7, h6, h8, h14⟩ := hFetch
  have hTail : let out := runBlock hintTranscriptTail E sF
      out.pc = sF.pc + 3 ∧ out.mem = sF.mem ∧
        HintCopyParams (G.hintList + G.hints + G.rows) src stride G.rows out ∧ out.regs 14 = G.context := by
    refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp [hintTranscriptTail, runBlock, execInstr, h4, h5, h7, h6, h8, h14, hParent,
        Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hFirstAddr, Nat.mod_eq_of_lt hDest]
  generalize hTExec : runBlock hintTranscriptTail E sF = out at hTail
  obtain ⟨hPcT, hMemT, hArgsT, hCtxT⟩ := hTail
  have hRun : runBlock hintTranscriptSetup E state = out := by
    rw [hintTranscriptSetup, runBlock_append, runBlock_append, hPExec, hFExec, hTExec]
  rw [hRun]
  exact ⟨by omega, hMemT.trans (hMemF.trans hMemP), hArgsT, hCtxT⟩

/-- Copy one row of the column-major transcript into the row worker's prefix backup. -/
def hintTranscriptStmt : Stmt := .seq (.code hintTranscriptSetup) hintCopyStmt

theorem hintTranscriptStmt_len : hintTranscriptStmt.len = 30 := rfl

theorem hintTranscriptStmt_sem (G : HintGaussArea) (v : HintVec G.rows)
    (parent src stride : ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hParent : parent + 16 = G.context) (hContext : state.regs 14 = G.context)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hSrc : src < 2 ^ E.W) (hStride : stride < 2 ^ E.W)
    (hReadSrc : state.mem (parent + 9) = src) (hReadStride : state.mem (parent + 10) = stride)
    (hDestEnd : G.hintList + G.hints + 2 * G.rows ≤ parent)
    (hSeparate : G.hintList + G.hints + 2 * G.rows ≤ src)
    (hSource : ∀ t : Fin G.rows, src + t.val * stride < 2 ^ E.W)
    (hValues : ∀ t : Fin G.rows, state.mem (src + t.val * stride) = (v t).val)
    (hAt : At P base (hintTranscriptStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 30) state (fun k out =>
      k = 9 * G.rows + 23 ∧
      (∀ t : Fin G.rows, out.mem (G.hintList + G.hints + G.rows + t.val) = (v t).val) ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      CRMemFrame (G.hintList + G.hints + G.rows) (G.hintList + G.hints + 2 * G.rows) state.mem out.mem) := by
  let dest := G.hintList + G.hints + G.rows
  let f : ℕ → ZMod 2 := fun t => if ht : t < G.rows then v ⟨t, ht⟩ else 0
  have hSpan := hFits.span
  have hWord : 1 < 2 ^ E.W := by omega
  have hCount : G.rows < 2 ^ E.W := hFits.values 0 (by decide)
  obtain ⟨index, hHead⟩ := hHeader
  obtain ⟨hSetupAt, hCopyAt⟩ := At.seqStmt hAt
  change At P base hintTranscriptSetup at hSetupAt
  change At P (base + 20) (hintCopyStmt.compile (base + 20)) at hCopyAt
  have hSetup := hintTranscriptSetup_spec E G state parent src stride index hParent hContext
    hHead hFits hSrc hStride hReadSrc hReadStride (by omega)
  generalize hS : runBlock hintTranscriptSetup E state = sS at hSetup
  obtain ⟨hPcS, hMemS, hArgsS, hCtxS⟩ := hSetup
  have hRunS : (step P E)^[20] state = sS := by
    have hh := iterate_runBlock_of_at P E hintTranscriptSetup state (by rwa [hPc])
      (by simp [hintTranscriptSetup, hintScanParent, hintTranscriptFetch, hintParentLoad,
        hintTranscriptTail, NoBranch, Instr.NoBranchI])
    simpa only [hintTranscriptSetup_length, hS] using hh
  have hDestFit : ∀ t < G.rows, dest + t < 2 ^ E.W := by
    intro t ht
    dsimp only [dest]
    omega
  have hOutside : ∀ t < G.rows, src + t * stride < dest ∨ dest + G.rows ≤ src + t * stride := by
    intro t ht
    right
    dsimp only [dest]
    omega
  have hReads : ∀ t < G.rows, sS.mem (src + t * stride) = (f t).val := by
    intro t ht
    rw [hMemS]
    simpa [f, ht] using hValues ⟨t, ht⟩
  obtain ⟨_, kC, out, hRunC, hPcC, hCostC, _, hMemC, _, hFrameC, hRegsC⟩ :=
    hintCopyStmt_sem P E sS dest src stride G.rows (base + 20) f hWord hCount
      hDestFit (fun t ht => hSource ⟨t, ht⟩) hOutside hReads hCopyAt (by omega) hArgsS
  have hFrame : CRMemFrame (G.hintList + G.hints + G.rows)
      (G.hintList + G.hints + 2 * G.rows) state.mem out.mem := by
    intro addr hAway
    rw [hFrameC addr (by
      dsimp only [dest]
      rcases hAway with hBefore | hAfter
      · exact Or.inl hBefore
      · exact Or.inr (by omega)), hMemS]
  refine ⟨hPc, kC + 20, out, hintIterate_then (step P E) hRunS hRunC,
    by omega, by omega, ?_, ⟨index, ?_⟩,
    (hRegsC 14 (by decide) (by decide) (by decide) (by decide)).trans hCtxS, hFrame⟩
  · intro t
    have hRange : dest ≤ dest + t.val ∧ dest + t.val < dest + G.rows := by
      have := t.isLt
      omega
    change out.mem (dest + t.val) = _
    rw [hMemC]
    simp only [hintCopyMem, hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, zero_mul, add_zero, f, dif_pos t.isLt]
  · intro i hi
    rw [hFrame _ (Or.inr (by omega))]
    exact hHead i hi

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTranscriptStmt_sem
end S_HintTranscript20261120


