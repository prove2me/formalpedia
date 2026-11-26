-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_09Part1
-- name    : LinearSetReconciliation327_Main_B65_09Part1
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T07:55:29.97919+00:00
-- url     : https://prove2.me/theorems/e74cc3dd-a303-5f9a-8a29-eb322df6fef8
-- title:
--   Theorem 6.5 supporting machine proof B65_09Part1
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_HintChildUpdateAction20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintSubtreeDet20261120
import Definitions.Def_LinearSetReconciliation327_Main_B65_01
import Definitions.Def_LinearSetReconciliation327_Main_B65_07
import Definitions.Def_LinearSetReconciliation327_Main_B65_08
set_option autoImplicit false

section S_HintRunPredict20261120
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
end S_HintRunPredict20261120
section S_HintRunFinal20261120
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
end S_HintRunFinal20261120
section S_HintColumnAdd20261120
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
end S_HintColumnAdd20261120
section S_HintNativeRoot20261120
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
end S_HintNativeRoot20261120
section S_HintTreeEvents20261120
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
end S_HintTreeEvents20261120
section S_HintTreeRanges20261120
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
end S_HintTreeRanges20261120
section S_HintDetBlocks20261120
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
end S_HintDetBlocks20261120
section S_HintDetABI20261120
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
end S_HintDetABI20261120
section S_HintCRLayout20261120
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
end S_HintCRLayout20261120
section S_HintNodeArena20261120
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
end S_HintNodeArena20261120
section S_HintNodeInfo20261120
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
end S_HintNodeInfo20261120
section S_HintRowWorkspace20261120
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
end S_HintRowWorkspace20261120
section S_HintRowWorkspaceCall20261120
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
end S_HintRowWorkspaceCall20261120


