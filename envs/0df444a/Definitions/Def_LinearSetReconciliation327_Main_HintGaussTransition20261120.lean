-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintGaussTransition20261120
-- name    : LinearSetReconciliation327_Main_HintGaussTransition20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T10:30:14.308923+00:00
-- url     : https://prove2.me/theorems/a661c416-c382-4963-a141-fbcef135af49
-- title:
--   LinearSetReconciliation327 — HintGaussTransition (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintGaussTransition20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintGaussNative20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintGaussPrepareStmt : Stmt := .seq hintGaussResidualStmt
  (.seq hintGaussLiftStmt (.seq hintGaussUnitStmt hintGaussPivotStmt))
theorem hintGaussPrepareStmt_len : hintGaussPrepareStmt.len = 107 := rfl

/-- From a real stored Gaussian state and its current input column, this fixed
    program computes both update vectors and selects a pivot, or certifies that
    the residual column is zero. The matrices and private header are retained. -/
theorem hintGaussPrepareStmt_sem (G : HintGaussArea)
    (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows) (B : HintElimState G.rows G.hints)
    (j : Fin G.hints) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G)
    (hStored : HintElimStored B G.residual G.lift state.mem)
    (hColumn : ∀ t : Fin G.rows, state.mem (G.column + t.val) = (A (Pi.single j 1) t).val)
    (hHeader : HintGaussHeader G j.val state.mem) (hFits : HintGaussHeaderFits E G j.val)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussPrepareStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 107) state (fun k out =>
      k ≤ (11 * G.rows + 11) * (G.rows + G.hints) + 11 * G.rows + 62 ∧
      HintElimStored B G.residual G.lift out.mem ∧ HintGaussHeader G j.val out.mem ∧
      (∀ t : Fin G.rows, out.mem (G.residualVec + t.val) = (B.residual (A (Pi.single j 1)) t).val) ∧
      (∀ t : Fin G.hints, out.mem (G.kernelVec + t.val) = (hintElimKernel A B j t).val) ∧
      out.regs 1 ≤ G.rows ∧ (out.regs 1 = 0 ↔ B.residual (A (Pi.single j 1)) = 0) ∧
      (out.regs 1 ≠ 0 → ∃ p : Fin G.rows, out.regs 1 = p.val + 1 ∧ B.residual (A (Pi.single j 1)) p = 1) ∧
      CRMemFrame G.residualVec (G.kernelVec + G.hints) state.mem out.mem ∧ out.regs 14 = G.context) := by
  have hWord := hGeometry.word_bound
  have hWidth := hGeometry.width_bound
  have hHints := hGeometry.hints_bound
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hGeometry
  obtain ⟨hRA, hRest0⟩ := At.seqStmt hAt
  obtain ⟨hLA, hRest1⟩ := At.seqStmt hRest0
  obtain ⟨hUA, hPA⟩ := At.seqStmt hRest1
  change At P base (hintGaussResidualStmt.compile base) at hRA
  change At P (base + 38) (hintGaussLiftStmt.compile (base + 38)) at hLA
  change At P (base + 76) (hintGaussUnitStmt.compile (base + 76)) at hUA
  change At P (base + 87) (hintGaussPivotStmt.compile (base + 87)) at hPA
  obtain ⟨_, kR, sR, hRunR, hPcR, hCostR, hRValues, hFrameR, hCtxR⟩ :=
    hintGaussResidualStmt_sem G j.val B.residual (A (Pi.single j 1)) P E state base
      hWord hWidth hWidth (by omega) (by omega) (by omega)
      hStored.residual_cells hColumn (Or.inl (by omega)) (Or.inl h3) hHeader hFits hContext hRA hPc
  have hHeaderR := hintGaussHeader_of_frame G j.val G.residualVec (G.residualVec + G.rows)
    state.mem sR.mem hHeader hFrameR (Or.inl (by omega))
  have hStoredR := hStored.of_frame hFrameR (Or.inl (by omega)) (Or.inl (by omega))
  have hColumnR : ∀ t : Fin G.rows, sR.mem (G.column + t.val) = (A (Pi.single j 1) t).val := by
    intro t
    rw [hFrameR _ (Or.inl (by have := t.isLt; omega))]
    exact hColumn t
  have hPcR' : sR.pc = base + 38 := hPcR
  obtain ⟨_, kL, sL, hRunL, hPcL, hCostL, hLValues, hFrameL, hCtxL⟩ :=
    hintGaussLiftStmt_sem G j.val B.lift (A (Pi.single j 1)) P E sR (base + 38)
      hWord hWidth hHints (by omega) (by omega) (by omega)
      hStoredR.lift_cells hColumnR (Or.inl (by omega)) (Or.inl (by omega)) hHeaderR hFits hCtxR hLA hPcR'
  have hHeaderL := hintGaussHeader_of_frame G j.val G.kernelVec (G.kernelVec + G.hints)
    sR.mem sL.mem hHeaderR hFrameL (Or.inl (by omega))
  have hStoredL := hStoredR.of_frame hFrameL (Or.inl (by omega)) (Or.inl (by omega))
  have hRValuesL : ∀ t : Fin G.rows,
      sL.mem (G.residualVec + t.val) = (B.residual (A (Pi.single j 1)) t).val := by
    intro t
    rw [hFrameL _ (Or.inl (by have := t.isLt; omega))]
    exact hRValues t
  have hPcL' : sL.pc = base + 76 := by simpa only [Nat.add_assoc] using hPcL
  obtain ⟨_, kU, sU, hRunU, hPcU, hCostU, hUValues, hFrameU, hCtxU⟩ :=
    hintGaussUnitStmt_sem G j (B.lift (A (Pi.single j 1))) P E sL (base + 76)
      hWord (by omega) hLValues hHeaderL hFits hCtxL hUA hPcL'
  have hFrameU' : CRMemFrame G.kernelVec (G.kernelVec + G.hints) sL.mem sU.mem := by
    intro addr hOutside
    apply hFrameU addr
    have := j.isLt
    rcases hOutside with hBefore | hAfter <;> omega
  have hHeaderU := hintGaussHeader_of_frame G j.val G.kernelVec (G.kernelVec + G.hints)
    sL.mem sU.mem hHeaderL hFrameU' (Or.inl (by omega))
  have hStoredU := hStoredL.of_frame hFrameU' (Or.inl (by omega)) (Or.inl (by omega))
  have hKernelEq : B.lift (A (Pi.single j 1)) + (Pi.single j 1 : HintVec G.hints) = hintElimKernel A B j := by
    rw [hintElimKernel, add_comm]
  rw [hKernelEq] at hUValues
  have hRValuesU : ∀ t : Fin G.rows,
      sU.mem (G.residualVec + t.val) = (B.residual (A (Pi.single j 1)) t).val := by
    intro t
    rw [hFrameU' _ (Or.inl (by have := t.isLt; omega))]
    exact hRValuesL t
  have hPcU' : sU.pc = base + 87 := by simpa only [Nat.add_assoc] using hPcU
  obtain ⟨_, kP, out, hRunP, hPcP, hCostP, hMemP, hBoundP, hZeroP, hGoodP, hCtxP⟩ :=
    hintGaussPivotStmt_sem G j.val (B.residual (A (Pi.single j 1))) P E sU (base + 87)
      hWord hWidth (by omega) hRValuesU hHeaderU hFits hCtxU hPA hPcU'
  have hAllRun := hintIterate_then (step P E)
    (hintIterate_then (step P E) (hintIterate_then (step P E) hRunR hRunL) hRunU) hRunP
  refine ⟨hPc, kP + (kU + (kL + kR)), out, hAllRun, ?_, ?_, ?_, ?_, ?_, ?_, hBoundP, hZeroP, hGoodP, ?_, hCtxP⟩
  · simpa only [Nat.add_assoc] using hPcP
  · have hExpand : (11 * G.rows + 11) * (G.rows + G.hints) =
        (11 * G.rows + 11) * G.rows + (11 * G.rows + 11) * G.hints := by ring
    omega
  · rw [hMemP]
    exact hStoredU
  · rw [hMemP]
    exact hHeaderU
  · intro t
    rw [hMemP]
    exact hRValuesU t
  · intro t
    rw [hMemP]
    exact hUValues t
  · intro addr hOutside
    have hOutsideR : addr < G.residualVec ∨ G.residualVec + G.rows ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    have hOutsideQ : addr < G.kernelVec ∨ G.kernelVec + G.hints ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    rw [hMemP, hFrameU' addr hOutsideQ, hFrameL addr hOutsideQ, hFrameR addr hOutsideR]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussPrepareStmt_sem

namespace LinearSetReconciliation327.Main

def hintGaussInsertStmt : Stmt := .seq hintGaussCacheStmt (.seq hintGaussRankResidualStmt hintGaussRankLiftStmt)
theorem hintGaussInsertStmt_len : hintGaussInsertStmt.len = 98 := rfl

theorem hintGaussInsertStmt_sem (G : HintGaussArea)
    (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows) (B : HintElimState G.rows G.hints)
    (j : Fin G.hints) (pivot : Fin G.rows) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hStored : HintElimStored B G.residual G.lift state.mem)
    (hRVector : ∀ t : Fin G.rows, state.mem (G.residualVec + t.val) = (B.residual (A (Pi.single j 1)) t).val)
    (hQVector : ∀ t : Fin G.hints, state.mem (G.kernelVec + t.val) = (hintElimKernel A B j t).val)
    (hHeader : HintGaussHeader G j.val state.mem) (hFits : HintGaussHeaderFits E G j.val)
    (hContext : state.regs 14 = G.context) (hPivot : state.regs 1 = pivot.val + 1)
    (hAt : At P base (hintGaussInsertStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 98) state (fun k out =>
      k ≤ (11 * G.rows + 11) * (G.rows + G.hints) + 9 * G.rows + 55 ∧
      HintElimStored (hintElimInsert A B j pivot) G.residual G.lift out.mem ∧
      HintGaussHeader G j.val out.mem ∧
      CRMemFrame G.residual (G.pivotRow + G.rows) state.mem out.mem ∧ out.regs 14 = G.context) := by
  have hWord := hGeometry.word_bound
  have hWidth := hGeometry.width_bound
  have hHints := hGeometry.hints_bound
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hGeometry
  obtain ⟨hCA, hRest⟩ := At.seqStmt hAt
  obtain ⟨hRA, hLA⟩ := At.seqStmt hRest
  change At P base (hintGaussCacheStmt.compile base) at hCA
  change At P (base + 24) (hintGaussRankResidualStmt.compile (base + 24)) at hRA
  change At P (base + 61) (hintGaussRankLiftStmt.compile (base + 61)) at hLA
  obtain ⟨_, kC, sC, hRunC, hPcC, hCostC, hCacheC, hFrameC, hCtxC⟩ :=
    hintGaussCacheStmt_sem G j.val B pivot P E state base hWord hWidth (by omega) h6
      (hStored.residual_cells pivot) (Or.inl (by omega)) hHeader hFits hContext hPivot hCA hPc
  have hHeaderC := hintGaussHeader_of_frame G j.val G.pivotRow (G.pivotRow + G.rows)
    state.mem sC.mem hHeader hFrameC (Or.inl (by omega))
  have hStoredC := hStored.of_frame hFrameC (Or.inl (by omega)) (Or.inl (by omega))
  have hRVectorC : ∀ t : Fin G.rows, sC.mem (G.residualVec + t.val) = (B.residual (A (Pi.single j 1)) t).val := by
    intro t
    rw [hFrameC _ (Or.inl (by have := t.isLt; omega))]
    exact hRVector t
  have hQVectorC : ∀ t : Fin G.hints, sC.mem (G.kernelVec + t.val) = (hintElimKernel A B j t).val := by
    intro t
    rw [hFrameC _ (Or.inl (by have := t.isLt; omega))]
    exact hQVector t
  obtain ⟨_, kR, sR, hRunR, hPcR, hCostR, hRCells, hFrameR, hCtxR⟩ :=
    hintGaussRankResidualStmt_sem G j.val A B j pivot P E sC (base + 24)
      hWord hWidth hWidth (by omega) h6 (by omega) hStoredC.residual_cells hCacheC hRVectorC
      (Or.inl (by omega)) (Or.inl (by omega)) hHeaderC hFits hCtxC hRA hPcC
  have hHeaderR := hintGaussHeader_of_frame G j.val G.residual (G.residual + G.rows * G.rows)
    sC.mem sR.mem hHeaderC hFrameR (Or.inl h0)
  have hLMatrixR : ∀ r : Fin G.hints, ∀ t : Fin G.rows,
      sR.mem (G.lift + r.val * G.rows + t.val) = (B.lift (Pi.single t 1) r).val := by
    intro r t
    rw [hFrameR _ (Or.inr (by omega))]
    exact hStoredC.lift_cells r t
  have hCacheR : ∀ t : Fin G.rows, sR.mem (G.pivotRow + t.val) = (B.residual (Pi.single t 1) pivot).val := by
    intro t
    rw [hFrameR _ (Or.inr (by omega))]
    exact hCacheC t
  have hQVectorR : ∀ t : Fin G.hints, sR.mem (G.kernelVec + t.val) = (hintElimKernel A B j t).val := by
    intro t
    rw [hFrameR _ (Or.inr (by omega))]
    exact hQVectorC t
  have hPcR' : sR.pc = base + 61 := by simpa only [Nat.add_assoc] using hPcR
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hLCells, hFrameL, hCtxL⟩ :=
    hintGaussRankLiftStmt_sem G j.val A B j pivot P E sR (base + 61)
      hWord hWidth hHints (by omega) h6 (by omega) hLMatrixR hCacheR hQVectorR
      (Or.inl (by omega)) (Or.inl (by omega)) hHeaderR hFits hCtxR hLA hPcR'
  have hHeaderL := hintGaussHeader_of_frame G j.val G.lift (G.lift + G.hints * G.rows)
    sR.mem out.mem hHeaderR hFrameL (Or.inl (by omega))
  have hAllRun := hintIterate_then (step P E) (hintIterate_then (step P E) hRunC hRunR) hRunL
  refine ⟨hPc, kL + (kR + kC), out, hAllRun, ?_, ?_, ⟨?_, hLCells⟩, hHeaderL, ?_, hCtxL⟩
  · simpa only [Nat.add_assoc] using hPcL
  · have hExpand : (11 * G.rows + 11) * (G.rows + G.hints) =
        (11 * G.rows + 11) * G.rows + (11 * G.rows + 11) * G.hints := by ring
    omega
  · intro s t
    have hCell := hintMatrix_cell_lt G.residual G.rows G.rows s.val t.val s.isLt t.isLt
    rw [hFrameL _ (Or.inl (by omega))]
    exact hRCells s t
  · intro addr hOutside
    have hOutsideL : addr < G.lift ∨ G.lift + G.hints * G.rows ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    have hOutsideR : addr < G.residual ∨ G.residual + G.rows * G.rows ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    have hOutsideC : addr < G.pivotRow ∨ G.pivotRow + G.rows ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    rw [hFrameL addr hOutsideL, hFrameR addr hOutsideR, hFrameC addr hOutsideC]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussInsertStmt_sem


