-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_06RowReplay
-- name    : LinearSetReconciliation327_Main_B65_06RowReplay
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T04:34:12.975789+00:00
-- url     : https://prove2.me/theorems/fbe03061-2983-5036-92a8-a687bc1a30b2
-- title:
--   Theorem 6.5 supporting machine proof B65_06RowReplay
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_05
set_option autoImplicit false

section S_HintFinalCandidate20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintFinalCandidate (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj maxR parent outsideBase bitmapBase : ℕ)
    (v : HintVec G.rows) (memory : ℕ → ℕ) : Prop :=
  ∃ r ≤ maxR, ∃ outside : Fin r → Fin Nj, ∃ z : HintVec G.hints,
    HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v memory ∧
    (∀ t : Fin G.hints, memory (G.kernelVec + t.val) = (z t).val) ∧
    (∀ i : Fin r, memory (outsideBase + 1 + i.val) = (outside i).val) ∧
    let C := hintBitsSet (fun j => (coords j).val) z ∪ hintTupleSet outside
    C ∈ hintFinalUnion G coords beta Nj maxR v ∧ ∀ D ∈ hintFinalUnion G coords beta Nj maxR v, D = C

theorem hintFinalCandidate_of_replay (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj maxR parent outsideBase bitmapBase r : ℕ)
    (v : HintVec G.rows) (hPos : 0 < Nj) (target : Fin (Nj ^ r)) (memory : ℕ → ℕ)
    (hr : r ≤ maxR) (hUnion : (hintFinalUnion G coords beta Nj maxR v).card = 1)
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v memory)
    (hSolution : HintScanSolution G coords beta Nj r (hintTupleSet (hintOdometerEnumeration Nj r hPos target)) v memory)
    (hArray : ∀ i < r, memory (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i) :
    HintFinalCandidate G coords beta Nj maxR parent outsideBase bitmapBase v memory := by
  classical
  let outside := hintOdometerEnumeration Nj r hPos target
  obtain ⟨z, hStored, hClass, _⟩ := hSolution
  let C := hintBitsSet (fun j => (coords j).val) z ∪ hintTupleSet outside
  have hCU : C ∈ hintFinalUnion G coords beta Nj maxR v :=
    Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr (by omega), hClass.1⟩
  obtain ⟨only, hUEq⟩ := Finset.card_eq_one.mp hUnion
  have hCEq : C = only := by simpa only [hUEq, Finset.mem_singleton] using hCU
  refine ⟨r, hr, outside, z, hData, hStored, ?_, hCU, ?_⟩
  · intro i
    exact (hArray i.val i.isLt).trans (hintOdometerEnumeration_val Nj r hPos target i).symm
  · intro D hD
    have hDEq : D = only := by simpa only [hUEq, Finset.mem_singleton] using hD
    exact hDEq.trans hCEq.symm

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalCandidate_of_replay
end S_HintFinalCandidate20261120
section S_HintFinalRecover20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalRecoverStmt : Stmt := .seq hintFinalScanStmt
  (.seq (.code hintFinalCheckCode) (.ite (.neqz 1) hintFinalReplayStmt (.code hintReplayStop)))
theorem hintFinalRecoverStmt_len : hintFinalRecoverStmt.len = 1435 := rfl

theorem hintFinalRecoverStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj parent outsideBase bitmapBase maxR oldCount : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hLimit : state.mem (parent + 4) = maxR)
    (hAt : At P base (hintFinalRecoverStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1435) state (fun k out =>
      k ≤ (hintFinalBudget G Nj maxR + 2) * (maxR + 1) + hintFinalBudget G Nj maxR + 7 * Nj + 8 * G.hints + 46 ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
      (out.regs 1 = 1 ↔ (hintFinalUnion G coords beta Nj maxR v).card = 1) ∧
      (out.regs 1 = 1 → HintFinalCandidate G coords beta Nj maxR parent outsideBase bitmapBase v out.mem) ∧
      (∃ count, HintScanReadOnly G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem) := by
  classical
  let U := hintFinalUnion G coords beta Nj maxR v
  let total := min 2 (hintFinalRawPrefix G coords beta Nj (maxR + 1) v hPos)
  have hParent := hPublic.parent_eq
  have hSpan := hPublic.fits.span
  have hZeroBudget : hintFinalBodyTime G Nj 0 ≤ hintFinalBudget G Nj maxR :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have hBudgetPos : 73 ≤ hintFinalBudget G Nj maxR := by dsimp only [hintFinalBodyTime] at hZeroBudget; omega
  obtain ⟨hScanAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintFinalScanStmt.compile base) at hScanAt
  change At P (base + 763) ((Stmt.seq (.code hintFinalCheckCode)
    (.ite (.neqz 1) hintFinalReplayStmt (.code hintReplayStop))).compile (base + 763)) at hRestAt
  obtain ⟨hCheckAt, hBranchAt⟩ := At.seqStmt hRestAt
  change At P (base + 763) hintFinalCheckCode at hCheckAt
  change At P (base + 771) ((Stmt.ite (.neqz 1) hintFinalReplayStmt (.code hintReplayStop)).compile (base + 771)) at hBranchAt
  obtain ⟨_, kS, sS, hRunS, hPcS, hCostS, hStateS, _, hSingletonS, hSelectS⟩ :=
    hintFinalScanStmt_sem G coords beta hPrefix Nj parent outsideBase bitmapBase maxR oldCount v hPos
      P E state base hPublic hInput hHeader hContext hLimit hScanAt hPc
  have hCheck := hintFinalCheckCode_spec E sS parent total (by omega) (hStateS.context_value.trans hParent.symm)
    (min_le_left _ _) hStateS.total
  generalize hC : runBlock hintFinalCheckCode E sS = sC at hCheck
  obtain ⟨hPcC, hMemC, hFlagC, hCtxC⟩ := hCheck
  have hRunC : (step P E)^[8] sS = sC := by
    have hh := iterate_runBlock_of_at P E hintFinalCheckCode sS (by rwa [hPcS])
      (by simp [hintFinalCheckCode, hintFinalCheckPrep, hintScanParent, hintFamilyCheckTail, NoBranch, Instr.NoBranchI])
    rw [hC] at hh
    exact hh
  have hCapIff : total = 1 ↔ U.card = 1 := by
    change min 2 (hintFinalRawPrefix G coords beta Nj (maxR + 1) v hPos) = 1 ↔ U.card = 1
    rw [← hStateS.total]
    exact hSingletonS
  have hFlag : sC.regs 1 = hintTruth (U.card = 1) := hFlagC.trans (hintTruth_congr hCapIff)
  have hDataC : HintScanReadOnly G coords Nj (maxR + 1) parent outsideBase bitmapBase v sC.mem := by
    rw [hMemC]; exact hStateS.readonly
  have hHeaderC : ∃ index, HintGaussHeader G index sC.mem := by rw [hMemC]; exact hStateS.header
  let Q : ℕ → RAMState → Prop := fun k out => k ≤ hintFinalBudget G Nj maxR ∧
    (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧ (out.regs 1 = 1 ↔ U.card = 1) ∧
    (out.regs 1 = 1 → HintFinalCandidate G coords beta Nj maxR parent outsideBase bitmapBase v out.mem) ∧
    (∃ count, HintScanReadOnly G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
    (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR sC.mem out.mem
  have hBranch : Sem P E (base + 771) (base + 1435) sC Q := by
    apply Sem.ite P E (base + 771) (.neqz 1) hintFinalReplayStmt (.code hintReplayStop) sC Q
      hBranchAt hPublic.geometry.word_bound (by omega)
    · intro hGo
      change Sem P E (base + 772) (base + 1432) {sC with pc := base + 772}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1435})
      have hUnion : U.card = 1 := by
        by_contra hBad
        have hZero : sC.regs 1 = 0 := by simpa [hintTruth, hBad] using hFlag
        exact hGo hZero
      obtain ⟨r, hr, hSaved, hSOne, _⟩ := hSelectS (hSingletonS.mpr hUnion)
      obtain ⟨target, hSuccess⟩ := Finset.card_eq_one.mp hSOne
      have hNative := hintFinalReplayStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase maxR (maxR + 1) v
        P E {sC with pc := base + 772} (base + 772) hPublic hr target hSuccess hDataC hHeaderC (hCtxC.trans hParent)
        (by rw [hMemC]; exact hSaved) (at_ite hBranchAt).2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hOne, hSolution, hArray, hData, hHeader, hCtx, hFrame⟩ := hOut
      have hCandidate := hintFinalCandidate_of_replay G coords beta Nj maxR parent outsideBase bitmapBase r v hPos target out.mem
        hr hUnion hData hSolution hArray
      have hLocalBudget : hintFinalBodyTime G Nj r ≤ hintFinalBudget G Nj maxR :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      refine ⟨?_, Or.inr hOne, ⟨fun _ => hUnion, fun _ => hOne⟩, fun _ => hCandidate,
        ⟨r, hData⟩, hHeader, hCtx, hFrame⟩
      dsimp only [hintFinalBodyTime] at hLocalBudget
      omega
    · intro hStop
      change Sem P E (base + 1433) (base + 1434) {sC with pc := base + 1433}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1435})
      have hBad : ¬ U.card = 1 := by
        intro hGood
        have hOne : sC.regs 1 = 1 := by simpa [hintTruth, hGood] using hFlag
        apply hStop
        change sC.regs 1 ≠ 0
        rw [hOne]; decide
      have hNative := Sem.block P E (base + 1433) hintReplayStop {sC with pc := base + 1433}
        (at_ite hBranchAt).2.2.2.2.1 (by simp [hintReplayStop, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      dsimp only [Q]
      refine ⟨by change k = 1 at hCost; omega, Or.inl ?_, ?_, ?_, ⟨maxR + 1, hDataC⟩, hHeaderC, ?_, ?_⟩
      · simp [hintReplayStop, runBlock, execInstr]
      · simp [hintReplayStop, runBlock, execInstr, hBad]
      · intro hOne; simp [hintReplayStop, runBlock, execInstr] at hOne
      · simpa [hintReplayStop, runBlock, execInstr] using hCtxC.trans hParent
      · exact HintFinalFrame.refl G parent outsideBase bitmapBase Nj maxR sC.mem
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hBitB, hSingletonB, hCandidateB, hDataB, hHeaderB, hCtxB, hFrameB⟩ := hBranch
  have hFrameB' : HintFinalFrame G parent outsideBase bitmapBase Nj maxR sS.mem out.mem := by rw [← hMemC]; exact hFrameB
  exact ⟨hPc, kB + (8 + kS), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunS hRunC) hRunB, hPcB, by omega,
    hBitB, hSingletonB, hCandidateB, hDataB, hHeaderB, hCtxB, hStateS.frame.trans hFrameB'⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalRecoverStmt_sem
end S_HintFinalRecover20261120
section S_HintFinalGuard20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintRowInput.frame_any_count {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR count parent outsideBase bitmapBase : ℕ} {v : HintVec G.rows} {original memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj count parent outsideBase bitmapBase v original)
    (hFrame : CRMemFrame bitmapBase (bitmapBase + Nj) original memory) :
    HintRowInput G coords Nj count parent outsideBase bitmapBase v memory := by
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFrame _ (Or.inr (by omega))]; exact hInput.outside_pointer
  · rw [hFrame _ (Or.inr (by omega))]; exact hInput.bitmap_pointer
  · rw [hFrame _ (Or.inr (by omega))]; exact hInput.radix
  · rw [hFrame _ (Or.inr (by omega))]; exact hInput.outside_count
  · intro j; rw [hFrame _ (Or.inr (by omega))]; exact hInput.hints j
  · intro t; rw [hFrame _ (Or.inr (by omega))]; exact hInput.observation t

theorem HintFinalFrame.of_bitmap {G : HintGaussArea} {parent outsideBase bitmapBase Nj maxR : ℕ}
    {original memory : ℕ → ℕ} (hFrame : CRMemFrame bitmapBase (bitmapBase + Nj) original memory) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR original memory := by
  intro addr hB _ _ _ _ _ _
  exact hFrame addr hB

def hintFinalGuardCode : List Instr := hintScanParent ++ hintParentLoad 8 17 ++ hintParentLoad 9 6 ++ hintRowWaitTail
theorem hintFinalGuardCode_length : hintFinalGuardCode.length = 11 := rfl

theorem hintFinalGuardCode_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState) (parent BX index : ℕ)
    (hParent : parent + 16 = G.context) (hContext : state.regs 14 = G.context)
    (hHeader : HintGaussHeader G index state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hBX : BX < 2 ^ E.W) (hReadBX : state.mem (parent + 6) = BX) :
    let out := runBlock hintFinalGuardCode E state
    out.pc = state.pc + 11 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (G.hints ≤ BX) ∧ out.regs 14 = G.context := by
  have hSpan := hFits.span
  have hWord : 1 < 2 ^ E.W := by omega
  have hReadH : state.mem (parent + 17) = G.hints := by
    rw [show parent + 17 = G.context + 1 by omega]
    exact hHeader 1 (by decide)
  have hHintsWord : G.hints < 2 ^ E.W := hFits.values 1 (by decide)
  have hP := hintScanParent_spec E state parent (by omega) (hContext.trans hParent.symm)
  generalize hPExec : runBlock hintScanParent E state = sP at hP
  obtain ⟨hPcP, hMemP, hPointerP, hCtxP⟩ := hP
  have hH := hintParentLoad_spec E sP parent 17 8 hPointerP (by omega) (by decide) (by decide)
  generalize hHExec : runBlock (hintParentLoad 8 17) E sP = sH at hH
  obtain ⟨hPcH, hMemH, hValueH, hPointerH, hCtxH, _⟩ := hH
  have h8H : sH.regs 8 = G.hints := by rw [hValueH, hMemP, hReadH, Nat.mod_eq_of_lt hHintsWord]
  have hB := hintParentLoad_spec E sH parent 6 9 hPointerH (by omega) (by decide) (by decide)
  generalize hBExec : runBlock (hintParentLoad 9 6) E sH = sB at hB
  obtain ⟨hPcB, hMemB, hValueB, _, hCtxB, hRegsB⟩ := hB
  have h9B : sB.regs 9 = BX := by rw [hValueB, hMemH, hMemP, hReadBX, Nat.mod_eq_of_lt hBX]
  have h8B : sB.regs 8 = G.hints := (hRegsB 8 (by decide) (by decide)).trans h8H
  have hTail := hintRowWaitTail_spec E sB BX G.hints hWord h8B h9B
  generalize hTExec : runBlock hintRowWaitTail E sB = out at hTail
  obtain ⟨hPcT, hMemT, hFlagT, hCtxT⟩ := hTail
  have hRun : runBlock hintFinalGuardCode E state = out := by
    rw [hintFinalGuardCode, runBlock_append, runBlock_append, runBlock_append, hPExec, hHExec, hBExec, hTExec]
  rw [hRun]
  exact ⟨by omega, hMemT.trans (hMemB.trans (hMemH.trans hMemP)), hFlagT,
    hCtxT.trans (hCtxB.trans (hCtxH.trans (hCtxP.trans hParent)))⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalGuardCode_spec
end S_HintFinalGuard20261120


