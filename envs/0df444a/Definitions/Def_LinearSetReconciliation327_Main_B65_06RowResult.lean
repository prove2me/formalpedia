-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_06RowResult
-- name    : LinearSetReconciliation327_Main_B65_06RowResult
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T04:36:01.394515+00:00
-- url     : https://prove2.me/theorems/5c05f5ae-fdc0-5261-9cd5-cb10f10b14a5
-- title:
--   Theorem 6.5 supporting machine proof B65_06RowResult
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_06RowTranscript
import Definitions.Def_LinearSetReconciliation327_Main_B65_06RowReplay
import Definitions.Def_LinearSetReconciliation327_Main_B65_06Bitmap
set_option autoImplicit false

section S_HintFinalAux20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintEmptyBitmapStmt : Stmt := .seq hintBitmapClearStmt (.code hintReplayStop)
theorem hintEmptyBitmapStmt_len : hintEmptyBitmapStmt.len = 20 := rfl

theorem hintEmptyBitmapStmt_sem (parent bitmapBase Nj : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hBitmap : bitmapBase < 2 ^ E.W) (hNj : Nj < 2 ^ E.W) (hSpan : bitmapBase + Nj ≤ 2 ^ E.W)
    (hReadBitmap : state.mem (parent + 1) = bitmapBase) (hReadNj : state.mem (parent + 2) = Nj)
    (hAt : At P base (hintEmptyBitmapStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 20) state (fun k out => k ≤ 7 * Nj + 15 ∧ out.regs 1 = 0 ∧
      (∀ q < Nj, out.mem (bitmapBase + q) = 0) ∧
      CRMemFrame bitmapBase (bitmapBase + Nj) state.mem out.mem ∧ out.regs 14 = parent + 16) := by
  obtain ⟨hClearAt, hStopAt⟩ := At.seqStmt hAt
  change At P base (hintBitmapClearStmt.compile base) at hClearAt
  change At P (base + 19) hintReplayStop at hStopAt
  obtain ⟨_, kC, sC, hRunC, hPcC, hCostC, hZeroC, hFrameC, hCtxC⟩ :=
    hintBitmapClearStmt_sem parent bitmapBase Nj P E state base hEnd hContext hBitmap hNj hSpan hReadBitmap hReadNj hClearAt hPc
  have hStop : let out := runBlock hintReplayStop E sC
      out.pc = sC.pc + 1 ∧ out.mem = sC.mem ∧ out.regs 1 = 0 ∧ out.regs 14 = sC.regs 14 := by
    refine ⟨?_, rfl, ?_, ?_⟩ <;> simp [hintReplayStop, runBlock, execInstr]
  generalize hS : runBlock hintReplayStop E sC = out at hStop
  obtain ⟨hPcS, hMemS, hFlagS, hCtxS⟩ := hStop
  have hRunS : (step P E)^[1] sC = out := by
    have hh := iterate_runBlock_of_at P E hintReplayStop sC (by rwa [hPcC])
      (by simp [hintReplayStop, NoBranch, Instr.NoBranchI])
    rw [hS] at hh
    exact hh
  refine ⟨hPc, 1 + kC, out, hintIterate_then (step P E) hRunC hRunS, by omega, by omega, hFlagS, ?_, ?_, hCtxS.trans hCtxC⟩
  · rw [hMemS]; exact hZeroC
  · rw [hMemS]; exact hFrameC

theorem hintWorkerFinal_eq (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (N m Nj maxR BX BY : ℕ) (j : Fin m) (v : HintVec G.rows)
    (hNj : rowLen N m j.val = Nj) (hMax : maxR = min BY (Nj - G.hints)) :
    workerFinal N m G.steps G.buckets BX BY j beta (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v) =
      if BX < G.hints then ∅ else if (hintFinalUnion G coords beta Nj maxR v).card = 1 then
        ((hintFinalUnion G coords beta Nj maxR v).toList.head?).getD ∅ else ∅ := by
  classical
  unfold workerFinal
  dsimp only
  rw [hintCoords_card coords hInj, hNj, ← hMax]
  rfl

theorem hintFinalUnion_eq_singleton (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj maxR : ℕ) (v : HintVec G.rows) (C : Finset ℕ)
    (hC : C ∈ hintFinalUnion G coords beta Nj maxR v)
    (hUnique : ∀ D ∈ hintFinalUnion G coords beta Nj maxR v, D = C) :
    hintFinalUnion G coords beta Nj maxR v = {C} := by
  classical
  ext D
  simp only [Finset.mem_singleton]
  exact ⟨fun hD => hUnique D hD, fun heq => heq ▸ hC⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEmptyBitmapStmt_sem
#print axioms LinearSetReconciliation327.Main.hintWorkerFinal_eq
end S_HintFinalAux20261120
section S_HintFinalResult20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintFinalChosenSet (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj maxR : ℕ) (v : HintVec G.rows) : Finset ℕ := by
  classical
  let U := hintFinalUnion G coords beta Nj maxR v
  exact if U.card = 1 then U.toList.head?.getD ∅ else ∅

def hintFinalResultStmt : Stmt := .seq hintFinalRecoverStmt
  (.ite (.neqz 1) hintCandidateBitmapStmt hintEmptyBitmapStmt)
theorem hintFinalResultStmt_len : hintFinalResultStmt.len = 1524 := rfl

theorem hintFinalResultStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj parent outsideBase bitmapBase maxR oldCount : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hLimit : state.mem (parent + 4) = maxR)
    (hAt : At P base (hintFinalResultStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1524) state (fun k out =>
      k ≤ (hintFinalBudget G Nj maxR + 2) * (maxR + 1) + hintFinalBudget G Nj maxR + 14 * Nj + 18 * G.hints + 8 * maxR + 95 ∧
      (∀ q < Nj, out.mem (bitmapBase + q) = hintTruth (q ∈ hintFinalChosenSet G coords beta Nj maxR v)) ∧
      (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem) := by
  classical
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutsideSpan := hPublic.outside_span
  have hBitmapSpan := hPublic.bitmap_span
  have hSpan := hPublic.fits.span
  have hNjWord : Nj < 2 ^ E.W := hPublic.bucket_bound.trans_lt (hPublic.fits.values 12 (by decide))
  obtain ⟨hRecoverAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base (hintFinalRecoverStmt.compile base) at hRecoverAt
  change At P (base + 1435) ((Stmt.ite (.neqz 1) hintCandidateBitmapStmt hintEmptyBitmapStmt).compile (base + 1435)) at hBranchAt
  obtain ⟨_, kR, sR, hRunR, hPcR, hCostR, hFlagR, hUniqueR, hCandidateR, hDataR, hHeaderR, hCtxR, hFrameR⟩ :=
    hintFinalRecoverStmt_sem G coords beta hPrefix Nj parent outsideBase bitmapBase maxR oldCount v hPos
      P E state base hPublic hInput hHeader hContext hLimit hRecoverAt hPc
  let Q : ℕ → RAMState → Prop := fun k out => k ≤ 7 * Nj + 10 * G.hints + 8 * maxR + 49 ∧
    (∀ q < Nj, out.mem (bitmapBase + q) = hintTruth (q ∈ hintFinalChosenSet G coords beta Nj maxR v)) ∧
    (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
    (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR sR.mem out.mem
  have hBranch : Sem P E (base + 1435) (base + 1524) sR Q := by
    apply Sem.ite P E (base + 1435) (.neqz 1) hintCandidateBitmapStmt hintEmptyBitmapStmt sR Q
      hBranchAt hPublic.geometry.word_bound hPcR
    · intro hGo
      change Sem P E (base + 1436) (base + 1502) {sR with pc := base + 1436}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1524})
      have hOne : sR.regs 1 = 1 := hFlagR.resolve_left hGo
      obtain ⟨r, hr, outside, z, hData, hZ, hOutside, hMember, hUnique⟩ := hCandidateR hOne
      have hWeak : HintRowInput G coords Nj r parent outsideBase bitmapBase v sR.mem :=
        ⟨hData.outside_pointer, hData.bitmap_pointer, hData.radix, hData.outside_count, hData.hints, hData.observation⟩
      let C := hintBitsSet (fun t => (coords t).val) z ∪ hintTupleSet outside
      have hUEq := hintFinalUnion_eq_singleton G coords beta Nj maxR v C hMember hUnique
      have hChosen : hintFinalChosenSet G coords beta Nj maxR v = C := by simp [hintFinalChosenSet, hUEq]
      have hNative := hintCandidateBitmapStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase maxR v outside z
        P E {sR with pc := base + 1436} (base + 1436) hPublic hr hWeak hHeaderR hCtxR hZ hOutside
        (at_ite hBranchAt).2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, _, hBitmap, hInputOut, hHeaderOut, hCtxOut, hFrameOut⟩ := hOut
      refine ⟨by omega, ?_, ⟨r, hInputOut⟩, hHeaderOut, hCtxOut, HintFinalFrame.of_bitmap hFrameOut⟩
      intro q hq
      rw [hChosen]
      exact hBitmap q hq
    · intro hStop
      change Sem P E (base + 1503) (base + 1523) {sR with pc := base + 1503}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1524})
      have hBad : ¬ (hintFinalUnion G coords beta Nj maxR v).card = 1 := by
        intro hGood
        have hOne := hUniqueR.mpr hGood
        apply hStop
        change sR.regs 1 ≠ 0
        rw [hOne]; decide
      have hChosen : hintFinalChosenSet G coords beta Nj maxR v = ∅ := by simp [hintFinalChosenSet, hBad]
      obtain ⟨count, hData⟩ := hDataR
      have hWeak : HintRowInput G coords Nj count parent outsideBase bitmapBase v sR.mem :=
        ⟨hData.outside_pointer, hData.bitmap_pointer, hData.radix, hData.outside_count, hData.hints, hData.observation⟩
      have hNative := hintEmptyBitmapStmt_sem parent bitmapBase Nj P E {sR with pc := base + 1503} (base + 1503)
        (by omega) (hCtxR.trans hParent.symm) (by omega) hNjWord (by omega) hData.bitmap_pointer hData.radix
        (at_ite hBranchAt).2.2.2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, _, hBitmap, hFrameOut, hCtxOut⟩ := hOut
      have hInputOut := HintRowInput.frame_any_count hPublic hWeak hFrameOut
      have hHeaderOut : ∃ index, HintGaussHeader G index out.mem := by
        obtain ⟨index, hHeader⟩ := hHeaderR
        refine ⟨index, ?_⟩
        intro i hi; rw [hFrameOut _ (Or.inr (by omega))]; exact hHeader i hi
      refine ⟨by omega, ?_, ⟨count, hInputOut⟩, hHeaderOut, hCtxOut.trans hParent, HintFinalFrame.of_bitmap hFrameOut⟩
      intro q hq
      rw [hBitmap q hq, hChosen]
      simp [hintTruth]
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hBitmapB, hInputB, hHeaderB, hCtxB, hFrameB⟩ := hBranch
  exact ⟨hPc, kB + kR, out, hintIterate_then (step P E) hRunR hRunB, hPcB, by omega,
    hBitmapB, hInputB, hHeaderB, hCtxB, hFrameR.trans hFrameB⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalResultStmt_sem
end S_HintFinalResult20261120
section S_HintRowFinal20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintRowFinalStmt : Stmt := .seq (.code hintFinalGuardCode)
  (.ite (.neqz 1) hintFinalResultStmt hintEmptyBitmapStmt)

theorem hintRowFinalStmt_len : hintRowFinalStmt.len = 1558 := rfl

theorem hintRowFinalStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (N m Nj parent outsideBase bitmapBase maxR BX BY oldCount : ℕ) (j : Fin m) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hNj : rowLen N m j.val = Nj) (hMax : maxR = min BY (Nj - G.hints))
    (hBX : BX < 2 ^ E.W) (hReadBX : state.mem (parent + 6) = BX)
    (hLimit : state.mem (parent + 4) = maxR)
    (hAt : At P base (hintRowFinalStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1558) state (fun k out =>
      k ≤ (hintFinalBudget G Nj maxR + 2) * (maxR + 1) + hintFinalBudget G Nj maxR +
        14 * Nj + 18 * G.hints + 8 * maxR + 108 ∧
      (∀ q < Nj, out.mem (bitmapBase + q) = hintTruth (q ∈
        workerFinal N m G.steps G.buckets BX BY j beta
          (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v))) ∧
      (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem) := by
  classical
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutsideSpan := hPublic.outside_span
  have hBitmapSpan := hPublic.bitmap_span
  have hSpan := hPublic.fits.span
  have hNjWord : Nj < 2 ^ E.W := hPublic.bucket_bound.trans_lt (hPublic.fits.values 12 (by decide))
  let answer := workerFinal N m G.steps G.buckets BX BY j beta
    (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v)
  have hAnswer : answer = if BX < G.hints then ∅ else hintFinalChosenSet G coords beta Nj maxR v :=
    hintWorkerFinal_eq G coords hPublic.injective beta N m Nj maxR BX BY j v hNj hMax
  obtain ⟨hGuardAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base hintFinalGuardCode at hGuardAt
  change At P (base + 11) ((Stmt.ite (.neqz 1) hintFinalResultStmt hintEmptyBitmapStmt).compile (base + 11)) at hBranchAt
  obtain ⟨index, hHead⟩ := hHeader
  have hGuard := hintFinalGuardCode_spec E G state parent BX index hParent hContext hHead hPublic.fits hBX hReadBX
  generalize hG : runBlock hintFinalGuardCode E state = sG at hGuard
  obtain ⟨hPcG, hMemG, hFlagG, hCtxG⟩ := hGuard
  have hRunG : (step P E)^[11] state = sG := by
    have hh := iterate_runBlock_of_at P E hintFinalGuardCode state (by rwa [hPc])
      (by simp [hintFinalGuardCode, hintScanParent, hintParentLoad, hintRowWaitTail, NoBranch, Instr.NoBranchI])
    simpa only [hintFinalGuardCode_length, hG] using hh
  have hInputG : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v sG.mem := by rw [hMemG]; exact hInput
  have hHeaderG : ∃ index, HintGaussHeader G index sG.mem := by rw [hMemG]; exact ⟨index, hHead⟩
  let Q : ℕ → RAMState → Prop := fun k out =>
    k ≤ (hintFinalBudget G Nj maxR + 2) * (maxR + 1) + hintFinalBudget G Nj maxR +
      14 * Nj + 18 * G.hints + 8 * maxR + 97 ∧
    (∀ q < Nj, out.mem (bitmapBase + q) = hintTruth (q ∈ answer)) ∧
    (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
    (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR sG.mem out.mem
  have hBranch : Sem P E (base + 11) (base + 1558) sG Q := by
    apply Sem.ite P E (base + 11) (.neqz 1) hintFinalResultStmt hintEmptyBitmapStmt sG Q
      hBranchAt hPublic.geometry.word_bound (by omega)
    · intro hGo
      change Sem P E (base + 12) (base + 1536) {sG with pc := base + 12}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1558})
      have hSize : G.hints ≤ BX := by
        by_contra hBad
        exact hGo (by simpa [hintTruth, hBad] using hFlagG)
      have hNative := hintFinalResultStmt_sem G coords beta hPrefix Nj parent outsideBase bitmapBase maxR oldCount v
        hPublic.positive P E {sG with pc := base + 12} (base + 12) hPublic hInputG hHeaderG hCtxG
        (by rw [hMemG]; exact hLimit) (at_ite hBranchAt).2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hBitmap, hInputOut, hHeaderOut, hCtxOut, hFrameOut⟩ := hOut
      refine ⟨by omega, ?_, hInputOut, hHeaderOut, hCtxOut, hFrameOut⟩
      intro q hq
      rw [hAnswer, if_neg (by omega : ¬ BX < G.hints)]
      exact hBitmap q hq
    · intro hStop
      change Sem P E (base + 1537) (base + 1557) {sG with pc := base + 1537}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1558})
      have hSize : BX < G.hints := by
        by_contra hBad
        have hGood : G.hints ≤ BX := by omega
        have hOne : sG.regs 1 = 1 := by simpa [hintTruth, hGood] using hFlagG
        apply hStop
        change sG.regs 1 ≠ 0
        rw [hOne]
        decide
      have hNative := hintEmptyBitmapStmt_sem parent bitmapBase Nj P E {sG with pc := base + 1537} (base + 1537)
        (by omega) (hCtxG.trans hParent.symm) (by omega) hNjWord (by omega)
        hInputG.bitmap_pointer hInputG.radix (at_ite hBranchAt).2.2.2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, _, hBitmap, hFrameOut, hCtxOut⟩ := hOut
      have hInputOut := HintRowInput.frame_any_count hPublic hInputG hFrameOut
      have hHeaderOut : ∃ index, HintGaussHeader G index out.mem := by
        obtain ⟨i, hh⟩ := hHeaderG
        refine ⟨i, ?_⟩
        intro t ht
        rw [hFrameOut _ (Or.inr (by omega))]
        exact hh t ht
      refine ⟨by omega, ?_, ⟨oldCount, hInputOut⟩, hHeaderOut, hCtxOut.trans hParent, HintFinalFrame.of_bitmap hFrameOut⟩
      intro q hq
      rw [hBitmap q hq, hAnswer, if_pos hSize]
      simp [hintTruth]
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hBitmapB, hInputB, hHeaderB, hCtxB, hFrameB⟩ := hBranch
  refine ⟨hPc, kB + 11, out, hintIterate_then (step P E) hRunG hRunB, hPcB, by omega,
    hBitmapB, hInputB, hHeaderB, hCtxB, ?_⟩
  rw [← hMemG]
  exact hFrameB

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowFinalStmt_sem
end S_HintRowFinal20261120


