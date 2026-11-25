-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_01
-- name    : LinearSetReconciliation327_Main_B65_01
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-25T00:56:45.885846+00:00
-- url     : https://prove2.me/theorems/ba32feeb-30da-4fe0-b93a-4aa127bca524
-- title:
--   Theorem 6.5 dependency bundle 01
-- statement:
--   Theorem 6.5 dependency bundle 01
-- source:
--   arXiv:2611.11409, Theorem 6.5 dependency closure (bundled for publication).

import Definitions.Def_LinearSetReconciliation327_Main_HintGaussNative20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintGaussTransition20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintRowCoeff20261120
set_option autoImplicit false

section S_HintGaussColumn20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintGaussColumnResult (G : HintGaussArea)
    (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows) (done : Finset (Fin G.hints))
    (B : HintElimState G.rows G.hints) (j : Fin G.hints) (out : RAMState) : Prop :=
  (out.regs 1 = 0 ∧ HintElimStored B G.residual G.lift out.mem ∧
    ∃ q : HintVec G.hints, A q = 0 ∧ q ≠ 0 ∧
      ∀ t : Fin G.hints, out.mem (G.kernelVec + t.val) = (q t).val) ∨
  (out.regs 1 = 1 ∧ ∃ B' : HintElimState G.rows G.hints,
    HintElimStored B' G.residual G.lift out.mem ∧ HintElimInvariant A (insert j done) B')

def hintGaussInsertSuccessStmt : Stmt := .seq hintGaussInsertStmt (.code [.imm 1 1])
def hintGaussColumnStmt : Stmt := .seq hintGaussPrepareStmt
  (.ite (.neqz 1) hintGaussInsertSuccessStmt (.code [.imm 1 0]))
theorem hintGaussColumnStmt_len : hintGaussColumnStmt.len = 210 := rfl

theorem hintSetStatus_sem (P : Program) (E : RAMEnv) (state : RAMState) (base value : ℕ)
    (hValue : value < 2 ^ E.W) (hAt : At P base [.imm 1 value]) (hPc : state.pc = base) :
    Sem P E base (base + 1) state (fun k out => k = 1 ∧ out.regs 1 = value ∧
      out.mem = state.mem ∧ out.regs 14 = state.regs 14) := by
  have hNative := Sem.block P E base [.imm 1 value] state hAt
    (by simp [NoBranch, Instr.NoBranchI]) hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hK, rfl⟩ := hOut
  refine ⟨hK, ?_, rfl, ?_⟩ <;> simp [runBlock, execInstr, Nat.mod_eq_of_lt hValue]

/-- A complete native Gaussian column step. Failure returns a physically stored
    nonzero kernel certificate; success stores a state satisfying the enlarged
    elimination invariant. The branch is decided by the actual pivot scan. -/
theorem hintGaussColumnStmt_sem (G : HintGaussArea)
    (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows) (done : Finset (Fin G.hints))
    (B : HintElimState G.rows G.hints) (j : Fin G.hints)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hInv : HintElimInvariant A done B) (hj : j ∉ done)
    (hStored : HintElimStored B G.residual G.lift state.mem)
    (hColumn : ∀ t : Fin G.rows, state.mem (G.column + t.val) = (A (Pi.single j 1) t).val)
    (hHeader : HintGaussHeader G j.val state.mem) (hFits : HintGaussHeaderFits E G j.val)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussColumnStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 210) state (fun k out =>
      k ≤ 2 * ((11 * G.rows + 11) * (G.rows + G.hints)) + 20 * G.rows + 120 ∧
      HintGaussHeader G j.val out.mem ∧
      CRMemFrame G.residual (G.pivotRow + G.rows) state.mem out.mem ∧
      out.regs 14 = G.context ∧ HintGaussColumnResult G A done B j out) := by
  have hWord := hGeometry.word_bound
  obtain ⟨hPrepAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base (hintGaussPrepareStmt.compile base) at hPrepAt
  change At P (base + 107)
    ((Stmt.ite (.neqz 1) hintGaussInsertSuccessStmt (.code [.imm 1 0])).compile (base + 107)) at hBranchAt
  obtain ⟨_, kP, sP, hRunP, hPcP, hCostP, hStoredP, hHeaderP, hRValues, hQValues,
      hBoundP, hZeroP, hGoodP, hFrameP, hCtxP⟩ :=
    hintGaussPrepareStmt_sem G A B j P E state base hGeometry hStored hColumn hHeader hFits hContext hPrepAt hPc
  let Q : ℕ → RAMState → Prop := fun k out =>
    k ≤ (11 * G.rows + 11) * (G.rows + G.hints) + 9 * G.rows + 58 ∧
      HintGaussHeader G j.val out.mem ∧
      CRMemFrame G.residual (G.pivotRow + G.rows) sP.mem out.mem ∧
      out.regs 14 = G.context ∧ HintGaussColumnResult G A done B j out
  have hBranch : Sem P E (base + 107) (base + 210) sP Q := by
    apply Sem.ite P E (base + 107) (.neqz 1) hintGaussInsertSuccessStmt (.code [.imm 1 0])
      sP Q hBranchAt hWord hPcP
    · intro hGo
      change Sem P E (base + 108) (base + 207) {sP with pc := base + 108}
        (fun k out => Q (1 + k + 1) {out with pc := base + 210})
      have hNonzero : sP.regs 1 ≠ 0 := hGo
      obtain ⟨pivot, hPivot, hPivotBit⟩ := hGoodP hNonzero
      have hTrueAt := (at_ite hBranchAt).2.2.1
      obtain ⟨hInsertAt, hFinishAt⟩ := At.seqStmt hTrueAt
      change At P (base + 108) (hintGaussInsertStmt.compile (base + 108)) at hInsertAt
      change At P (base + 206) [.imm 1 1] at hFinishAt
      obtain ⟨_, kI, sI, hRunI, hPcI, hCostI, hStoredI, hHeaderI, hFrameI, hCtxI⟩ :=
        hintGaussInsertStmt_sem G A B j pivot P E {sP with pc := base + 108} (base + 108)
          hGeometry hStoredP hRValues hQValues hHeaderP hFits hCtxP hPivot hInsertAt rfl
      obtain ⟨_, kF, out, hRunF, hPcF, hCostF, hStatusF, hMemF, hCtxF⟩ :=
        hintSetStatus_sem P E sI (base + 206) 1 hWord hFinishAt hPcI
      refine ⟨rfl, kF + kI, out, hintIterate_then (step P E) hRunI hRunF, hPcF, ?_⟩
      change Q (1 + (kF + kI) + 1) {out with pc := base + 210}
      dsimp only [Q]
      refine ⟨by omega, ?_, ?_, hCtxF.trans hCtxI, Or.inr ⟨hStatusF, hintElimInsert A B j pivot, ?_, ?_⟩⟩
      · rw [hMemF]
        exact hHeaderI
      · rw [hMemF]
        exact hFrameI
      · rw [hMemF]
        exact hStoredI
      · exact hintElimInsert_invariant A done B j pivot hInv hPivotBit
    · intro hStop
      change Sem P E (base + 208) (base + 209) {sP with pc := base + 208}
        (fun k out => Q (1 + k + 1) {out with pc := base + 210})
      have hZeroReg : sP.regs 1 = 0 := by
        change ¬ sP.regs 1 ≠ 0 at hStop
        exact not_not.mp hStop
      have hResidualZero := hZeroP.mp hZeroReg
      have hFalseAt := (at_ite hBranchAt).2.2.2.2.1
      change At P (base + 208) [.imm 1 0] at hFalseAt
      have hNative := hintSetStatus_sem P E {sP with pc := base + 208} (base + 208) 0
        (by omega) hFalseAt rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hStatus, hMem, hCtx⟩ := hOut
      change Q (1 + k + 1) {out with pc := base + 210}
      dsimp only [Q]
      refine ⟨by omega, ?_, ?_, hCtx.trans hCtxP, Or.inl ⟨hStatus, ?_, hintElimKernel A B j, ?_, ?_, ?_⟩⟩
      · rw [hMem]
        exact hHeaderP
      · intro addr _
        exact congrFun hMem addr
      · rw [hMem]
        exact hStoredP
      · exact (hintElimKernel_image A done B j hInv).trans hResidualZero
      · exact hintElimKernel_nonzero A done B j hInv hj
      · intro t
        rw [hMem]
        exact hQValues t
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hHeaderB, hFrameB, hCtxB, hResult⟩ := hBranch
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  refine ⟨hPc, kB + kP, out, hintIterate_then (step P E) hRunP hRunB, hPcB, by omega, hHeaderB, ?_, hCtxB, hResult⟩
  intro addr hOutside
  have hOutsideP : addr < G.residualVec ∨ G.kernelVec + G.hints ≤ addr := by
    rcases hOutside with hBefore | hAfter <;> omega
  rw [hFrameB addr hOutside, hFrameP addr hOutsideP]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussColumnStmt_sem

namespace LinearSetReconciliation327.Main

def hintGaussQueryFields : List (Fin 16 × ℕ) :=
  [(4, 4), (6, 0), (7, 12), (10, 10), (11, 11), (12, 13), (13, 9), (0, 8)]
def hintGaussQueryTail : List Instr :=
  [.add 3 13 0, .load 9 3, .mul 5 11 12, .mul 5 5 7, .add 5 5 9, .imm 15 1]
def hintGaussQuerySetup : List Instr := hintLoadFields hintGaussQueryFields ++ hintGaussQueryTail
theorem hintGaussQuerySetup_length : hintGaussQuerySetup.length = 30 := rfl

theorem hintGaussQueryTail_spec (E : RAMEnv) (state : RAMState)
    (dest count buckets key row steps hints index context : ℕ) (v : Fin buckets)
    (hWord : 1 < 2 ^ E.W) (hBuckets : buckets < 2 ^ E.W)
    (hHintAddr : hints + index < 2 ^ E.W) (hOffset : row * steps * buckets + v.val < 2 ^ E.W)
    (h4 : state.regs 4 = dest) (h6 : state.regs 6 = count) (h7 : state.regs 7 = buckets)
    (h10 : state.regs 10 = key) (h11 : state.regs 11 = row) (h12 : state.regs 12 = steps)
    (h13 : state.regs 13 = hints) (h0 : state.regs 0 = index) (h14 : state.regs 14 = context)
    (hHint : state.mem (hints + index) = v.val) :
    let out := runBlock hintGaussQueryTail E state
    HintCoeffCopyParams dest (row * steps * buckets + v.val) buckets count key out ∧
      out.mem = state.mem ∧ out.regs 14 = context := by
  have hPositive : 0 < buckets := by have := v.isLt; omega
  have hMulLe : row * steps ≤ row * steps * buckets := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (row * steps) (Nat.succ_le_of_lt hPositive)
  have hFirst : row * steps < 2 ^ E.W := by omega
  have hSecond : row * steps * buckets < 2 ^ E.W := by omega
  have hV : v.val < 2 ^ E.W := v.isLt.trans hBuckets
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [hintGaussQueryTail, runBlock, execInstr, h4, h6, h7, h10, h11, h12, h13, h0, h14,
      hHint, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hHintAddr, Nat.mod_eq_of_lt hFirst,
      Nat.mod_eq_of_lt hSecond, Nat.mod_eq_of_lt hV, Nat.mod_eq_of_lt hOffset]

theorem hintGaussQuerySetup_spec (E : RAMEnv) (G : HintGaussArea) (j : Fin G.hints)
    (v : Fin G.buckets) (state : RAMState)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G j.val state.mem)
    (hFits : HintGaussHeaderFits E G j.val) (hWord : 1 < 2 ^ E.W)
    (hHintSpan : G.hintList + G.hints < 2 ^ E.W)
    (hHint : state.mem (G.hintList + j.val) = v.val)
    (hOffset : G.row * G.steps * G.buckets + v.val < 2 ^ E.W) :
    let out := runBlock hintGaussQuerySetup E state
    HintCoeffCopyParams G.column (G.row * G.steps * G.buckets + v.val) G.buckets G.rows G.node out ∧
      out.mem = state.mem ∧ out.regs 14 = G.context := by
  have hValid : ∀ pair ∈ hintGaussQueryFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintGaussQueryFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintGaussQueryFields state hContext hValid
  have hValues := hintGaussHeader_mod E G j.val state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintGaussQueryFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G j.val 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G j.val 4 := by
    have hh := hLoad.2.2.2 4 (by decide)
    simpa [hintGaussQueryFields, hintLoadedValue, hZero,
      hValues 4 (by decide), hValues 8 (by decide), hValues 9 (by decide), hValues 10 (by decide), hValues 11 (by decide), hValues 12 (by decide), hValues 13 (by decide)] using hh
  have hR6 : mid.regs 6 = hintGaussHeaderValue G j.val 0 := by
    have hh := hLoad.2.2.2 6 (by decide)
    simpa [hintGaussQueryFields, hintLoadedValue, hZero,
      hValues 4 (by decide), hValues 8 (by decide), hValues 9 (by decide), hValues 10 (by decide), hValues 11 (by decide), hValues 12 (by decide), hValues 13 (by decide)] using hh
  have hR7 : mid.regs 7 = hintGaussHeaderValue G j.val 12 := by
    have hh := hLoad.2.2.2 7 (by decide)
    simpa [hintGaussQueryFields, hintLoadedValue, hZero,
      hValues 4 (by decide), hValues 8 (by decide), hValues 9 (by decide), hValues 10 (by decide), hValues 11 (by decide), hValues 12 (by decide), hValues 13 (by decide)] using hh
  have hR10 : mid.regs 10 = hintGaussHeaderValue G j.val 10 := by
    have hh := hLoad.2.2.2 10 (by decide)
    simpa [hintGaussQueryFields, hintLoadedValue, hZero,
      hValues 4 (by decide), hValues 8 (by decide), hValues 9 (by decide), hValues 10 (by decide), hValues 11 (by decide), hValues 12 (by decide), hValues 13 (by decide)] using hh
  have hR11 : mid.regs 11 = hintGaussHeaderValue G j.val 11 := by
    have hh := hLoad.2.2.2 11 (by decide)
    simpa [hintGaussQueryFields, hintLoadedValue, hZero,
      hValues 4 (by decide), hValues 8 (by decide), hValues 9 (by decide), hValues 10 (by decide), hValues 11 (by decide), hValues 12 (by decide), hValues 13 (by decide)] using hh
  have hR12 : mid.regs 12 = hintGaussHeaderValue G j.val 13 := by
    have hh := hLoad.2.2.2 12 (by decide)
    simpa [hintGaussQueryFields, hintLoadedValue, hZero,
      hValues 4 (by decide), hValues 8 (by decide), hValues 9 (by decide), hValues 10 (by decide), hValues 11 (by decide), hValues 12 (by decide), hValues 13 (by decide)] using hh
  have hR13 : mid.regs 13 = hintGaussHeaderValue G j.val 9 := by
    have hh := hLoad.2.2.2 13 (by decide)
    simpa [hintGaussQueryFields, hintLoadedValue, hZero,
      hValues 4 (by decide), hValues 8 (by decide), hValues 9 (by decide), hValues 10 (by decide), hValues 11 (by decide), hValues 12 (by decide), hValues 13 (by decide)] using hh
  have hR0 : mid.regs 0 = hintGaussHeaderValue G j.val 8 := by
    have hh := hLoad.2.2.2 0 (by decide)
    simpa [hintGaussQueryFields, hintLoadedValue, hZero,
      hValues 4 (by decide), hValues 8 (by decide), hValues 9 (by decide), hValues 10 (by decide), hValues 11 (by decide), hValues 12 (by decide), hValues 13 (by decide)] using hh
  have hHint' : mid.mem (G.hintList + j.val) = v.val := by rw [hLoad.2.1]; exact hHint
  have hTail := hintGaussQueryTail_spec E mid G.column G.rows G.buckets G.node G.row G.steps G.hintList j.val G.context v
    hWord (hFits.values 12 (by decide)) (by have := j.isLt; omega) hOffset
    hR4 hR6 hR7 hR10 hR11 hR12 hR13 hR0 hLoad.2.2.1 hHint'
  dsimp only
  rw [hintGaussQuerySetup, runBlock_append, hMid]
  exact ⟨hTail.1, hTail.2.1.trans hLoad.2.1, hTail.2.2⟩

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintColumnsLinearMap {a h : ℕ} (cols : Fin h → HintVec a) : HintVec h →ₗ[ZMod 2] HintVec a where
  toFun z := ∑ t : Fin h, z t • cols t
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply]

theorem hintColumnsLinearMap_basis {a h : ℕ} (cols : Fin h → HintVec a) (j : Fin h) :
    hintColumnsLinearMap cols (Pi.single j 1) = cols j := by
  classical
  simp [hintColumnsLinearMap, Pi.single_apply]

def hintGaussMap (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) :
    HintVec G.hints →ₗ[ZMod 2] HintVec G.rows :=
  hintColumnsLinearMap (fun j s => beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (coords j))

theorem hintGaussMap_basis (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (j : Fin G.hints) (s : Fin G.rows) :
    hintGaussMap G coords beta hPrefix (Pi.single j 1) s = beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (coords j) := by
  exact congrFun (hintColumnsLinearMap_basis _ j) s

def hintGaussQueryStmt : Stmt := .seq (.code hintGaussQuerySetup) hintCoeffCopyStmt
theorem hintGaussQueryStmt_len : hintGaussQueryStmt.len = 40 := rfl

/-- Actual hint-list reads and public coefficient queries produce the current
    column of the logical row matrix used by the Gaussian invariant. -/
theorem hintGaussQueryStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (j : Fin G.hints)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G)
    (hHintSpan : G.hintList + G.hints < 2 ^ E.W)
    (hHint : state.mem (G.hintList + j.val) = (coords j).val)
    (hOffset : G.row * G.steps * G.buckets + (coords j).val < 2 ^ E.W)
    (hQuerySpan : ∀ s < G.rows, G.row * G.steps * G.buckets + (coords j).val + s * G.buckets < 2 ^ E.W)
    (hCoeff : ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (coords j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (coords j)).val)
    (hHeader : HintGaussHeader G j.val state.mem) (hFits : HintGaussHeaderFits E G j.val)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussQueryStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 40) state (fun k out => k = 9 * G.rows + 33 ∧
      (∀ s : Fin G.rows, out.mem (G.column + s.val) = (hintGaussMap G coords beta hPrefix (Pi.single j 1) s).val) ∧
      CRMemFrame G.column (G.column + G.rows) state.mem out.mem ∧ HintGaussHeader G j.val out.mem ∧
      out.regs 14 = G.context) := by
  have hWord := hGeometry.word_bound
  have hWidth := hGeometry.width_bound
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintGaussQuerySetup at hSetupAt
  change At P (base + 30) (hintCoeffCopyStmt.compile (base + 30)) at hBodyAt
  have hNo : NoBranch hintGaussQuerySetup := by
    rw [hintGaussQuerySetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintGaussQueryTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintGaussQuerySetup_spec E G j (coords j) state hContext hHeader hFits hWord hHintSpan hHint hOffset
  generalize hMid : runBlock hintGaussQuerySetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h14⟩ := hSetup
  have hRunSetup : (step P E)^[30] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGaussQuerySetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 30 := by
    have hh := runBlock_pc hintGaussQuerySetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  let vec : HintVec G.rows := fun s => beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (coords j)
  have hCoeff' : ∀ s < G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (coords j).val + s * G.buckets) = (hintDenseVec vec s).val := by
    intro s hs
    simpa only [hintDenseVec, dif_pos hs] using hCoeff ⟨s, hs⟩
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, _, hOutMem, _, hFrame, hRegs⟩ :=
    hintCoeffCopyStmt_sem P E mid G.column (G.row * G.steps * G.buckets + (coords j).val) G.buckets G.rows G.node
      (base + 30) (hintDenseVec vec) hWord hWidth (by intro s hs; omega) hQuerySpan hCoeff' hBodyAt hMidPc hArgs
  have hFrame' : CRMemFrame G.column (G.column + G.rows) state.mem out.mem := by
    intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)
  refine ⟨hPc, kBody + 30, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega, ?_, hFrame', ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro s
    rw [hOutMem, hintGaussMap_basis]
    have hRange : G.column ≤ G.column + s.val ∧ G.column + s.val < G.column + G.rows := by have := s.isLt; omega
    simp only [hintCopyMem, hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, zero_mul, add_zero,
      hintDenseVec, dif_pos s.isLt]
    rfl
  · exact hintGaussHeader_of_frame G j.val G.column (G.column + G.rows) state.mem out.mem hHeader hFrame' (Or.inl (by omega))
  · exact (hRegs 14 (by decide) (by decide) (by decide) (by decide)).trans h14

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintColumnsLinearMap_basis
#print axioms LinearSetReconciliation327.Main.hintGaussQueryStmt_sem
end S_HintGaussColumn20261120
section S_HintGaussControl20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintGauss_publicCoeff (params : HintParams) (E : RAMEnv) (key N X Y : ℕ)
    (coins : NodeCoins params N X Y) (hAlign : CoefAl params E key N X Y coins)
    (row : Fin (params.rows X Y)) (s : Fin (params.ell N X Y)) (v : Fin (params.Nmax N X Y)) :
    E.coeff key (row.val * params.ell N X Y * params.Nmax N X Y + v.val + s.val * params.Nmax N X Y) =
      (coins row s v).val := by
  have hIndex : row.val * params.ell N X Y * params.Nmax N X Y + v.val + s.val * params.Nmax N X Y =
      (row.val * params.ell N X Y + s.val) * params.Nmax N X Y + v.val := by ring
  rw [hIndex]
  exact hAlign row s v

theorem hintGauss_query_index_lt (row steps buckets s v : ℕ) (hs : s < steps) (hv : v < buckets) :
    row * steps * buckets + v + s * buckets < (row + 1) * steps * buckets := by
  have hNext : row * steps + s + 1 ≤ row * steps + steps := by omega
  have hMul := Nat.mul_le_mul_right buckets hNext
  calc
    row * steps * buckets + v + s * buckets = (row * steps + s) * buckets + v := by ring
    _ < (row * steps + s) * buckets + buckets := Nat.add_lt_add_left hv _
    _ ≤ (row + 1) * steps * buckets := by nlinarith only [hMul]

def hintGaussReadColumnStmt : Stmt := .seq hintGaussQueryStmt hintGaussColumnStmt
theorem hintGaussReadColumnStmt_len : hintGaussReadColumnStmt.len = 250 := rfl

/-- End-to-end native column work: fetch the current hint coordinate, query its
    public matrix column, then either extend the elimination invariant or return
    a nonzero kernel certificate stored in RAM. -/
theorem hintGaussReadColumnStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (done : Finset (Fin G.hints)) (B : HintElimState G.rows G.hints) (j : Fin G.hints)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G)
    (hInv : HintElimInvariant (hintGaussMap G coords beta hPrefix) done B) (hj : j ∉ done)
    (hStored : HintElimStored B G.residual G.lift state.mem)
    (hHintSpan : G.hintList + G.hints < 2 ^ E.W)
    (hHint : state.mem (G.hintList + j.val) = (coords j).val)
    (hOffset : G.row * G.steps * G.buckets + (coords j).val < 2 ^ E.W)
    (hQuerySpan : ∀ s < G.rows, G.row * G.steps * G.buckets + (coords j).val + s * G.buckets < 2 ^ E.W)
    (hCoeff : ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (coords j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (coords j)).val)
    (hHeader : HintGaussHeader G j.val state.mem) (hFits : HintGaussHeaderFits E G j.val)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussReadColumnStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 250) state (fun k out =>
      k ≤ 2 * ((11 * G.rows + 11) * (G.rows + G.hints)) + 29 * G.rows + 153 ∧
      HintGaussHeader G j.val out.mem ∧
      CRMemFrame G.residual (G.pivotRow + G.rows) state.mem out.mem ∧ out.regs 14 = G.context ∧
      HintGaussColumnResult G (hintGaussMap G coords beta hPrefix) done B j out) := by
  obtain ⟨hQueryAt, hColumnAt⟩ := At.seqStmt hAt
  change At P base (hintGaussQueryStmt.compile base) at hQueryAt
  change At P (base + 40) (hintGaussColumnStmt.compile (base + 40)) at hColumnAt
  obtain ⟨_, kQ, sQ, hRunQ, hPcQ, hCostQ, hColumnQ, hFrameQ, hHeaderQ, hCtxQ⟩ :=
    hintGaussQueryStmt_sem G coords beta hPrefix j P E state base hGeometry hHintSpan hHint hOffset
      hQuerySpan hCoeff hHeader hFits hContext hQueryAt hPc
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have hStoredQ := hStored.of_frame hFrameQ (Or.inl (by omega)) (Or.inl h2)
  obtain ⟨_, kC, out, hRunC, hPcC, hCostC, hHeaderC, hFrameC, hCtxC, hResultC⟩ :=
    hintGaussColumnStmt_sem G (hintGaussMap G coords beta hPrefix) done B j P E sQ (base + 40)
      hGeometry hInv hj hStoredQ hColumnQ hHeaderQ hFits hCtxQ hColumnAt hPcQ
  refine ⟨hPc, kC + kQ, out, hintIterate_then (step P E) hRunQ hRunC, ?_, by omega, hHeaderC, ?_, hCtxC, hResultC⟩
  · simpa only [Nat.add_assoc] using hPcC
  · intro addr hOutside
    have hOutsideQ : addr < G.column ∨ G.column + G.rows ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    rw [hFrameC addr hOutside, hFrameQ addr hOutsideQ]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussReadColumnStmt_sem

namespace LinearSetReconciliation327.Main

theorem hintGaussHeaderValue_index (G : HintGaussArea) (old new i : ℕ) (hi : i < 14) :
    hintGaussHeaderValue G new i = if i = 8 then new else hintGaussHeaderValue G old i := by
  interval_cases i <;> simp [hintGaussHeaderValue]

theorem hintGaussHeader_set_index (G : HintGaussArea) (old new : ℕ) (memory : ℕ → ℕ)
    (hHeader : HintGaussHeader G old memory) :
    HintGaussHeader G new (Function.update memory (G.context + 8) new) := by
  intro i hi
  by_cases hEq : i = 8
  · subst i
    simp [hintGaussHeaderValue]
  · have hAddr : G.context + i ≠ G.context + 8 := by omega
    rw [Function.update_of_ne hAddr, hHeader i hi, hintGaussHeaderValue_index G old new i hi, if_neg hEq]

theorem HintGaussHeaderFits.change_index {E : RAMEnv} {G : HintGaussArea} {old new : ℕ}
    (h : HintGaussHeaderFits E G old) (hNew : new < 2 ^ E.W) : HintGaussHeaderFits E G new := by
  refine ⟨h.span, ?_⟩
  intro i hi
  rw [hintGaussHeaderValue_index G old new i hi]
  split_ifs
  · exact hNew
  · exact h.values i hi

def hintGaussAdvanceCode : List Instr :=
  [.imm 3 8, .add 3 14 3, .load 0 3, .imm 15 1, .add 0 0 15, .store 3 0,
    .imm 3 1, .add 3 14 3, .load 6 3]

theorem hintGaussAdvance_spec (E : RAMEnv) (G : HintGaussArea) (j : ℕ) (state : RAMState)
    (hHeader : HintGaussHeader G j state.mem) (hFits : HintGaussHeaderFits E G j)
    (hContext : state.regs 14 = G.context) (hNext : j + 1 < 2 ^ E.W) :
    let out := runBlock hintGaussAdvanceCode E state
    out.pc = state.pc + 9 ∧ out.regs 0 = j + 1 ∧ out.regs 6 = G.hints ∧ out.regs 14 = G.context ∧
      out.mem = Function.update state.mem (G.context + 8) (j + 1) ∧ HintGaussHeader G (j + 1) out.mem ∧
      (∀ addr, addr ≠ G.context + 8 → out.mem addr = state.mem addr) ∧
      (∀ r, r ≠ 0 → r ≠ 3 → r ≠ 6 → r ≠ 15 → out.regs r = state.regs r) := by
  have hSpan := hFits.span
  have hAddr8 : G.context + 8 < 2 ^ E.W := by omega
  have hAddr1 : G.context + 1 < 2 ^ E.W := by omega
  have hEight : 8 < 2 ^ E.W := by omega
  have hOne : 1 < 2 ^ E.W := by omega
  have hJ : j < 2 ^ E.W := by omega
  have hH : G.hints < 2 ^ E.W := hFits.values 1 (by decide)
  have hRead8 : state.mem (G.context + 8) = j := hHeader 8 (by decide)
  have hRead1 : state.mem (G.context + 1) = G.hints := hHeader 1 (by decide)
  have hNe : G.context + 1 ≠ G.context + 8 := by omega
  have hMemory : (runBlock hintGaussAdvanceCode E state).mem = Function.update state.mem (G.context + 8) (j + 1) := by
    simp [hintGaussAdvanceCode, runBlock, execInstr, hContext, hRead8, hRead1,
      Nat.mod_eq_of_lt hAddr8, Nat.mod_eq_of_lt hEight, Nat.mod_eq_of_lt hOne,
      Nat.mod_eq_of_lt hJ, Nat.mod_eq_of_lt hNext]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, hMemory, ?_, ?_, ?_⟩
  · simp [hintGaussAdvanceCode, runBlock, execInstr, Nat.add_assoc]
  · simp [hintGaussAdvanceCode, runBlock, execInstr, hContext, hRead8, Nat.mod_eq_of_lt hAddr8,
      Nat.mod_eq_of_lt hEight, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hJ, Nat.mod_eq_of_lt hNext]
  · simp [hintGaussAdvanceCode, runBlock, execInstr, hContext, hRead8, hRead1, hNe,
      Nat.mod_eq_of_lt hAddr8, Nat.mod_eq_of_lt hAddr1, Nat.mod_eq_of_lt hEight,
      Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hJ, Nat.mod_eq_of_lt hNext, Nat.mod_eq_of_lt hH]
  · simp [hintGaussAdvanceCode, runBlock, execInstr, hContext]
  · rw [hMemory]
    exact hintGaussHeader_set_index G j (j + 1) state.mem hHeader
  · intro addr hOutside
    rw [hMemory]
    exact Function.update_of_ne hOutside _ _
  · intro r h0 h3 h6 h15
    simp [hintGaussAdvanceCode, runBlock, execInstr, Function.update_of_ne h0,
      Function.update_of_ne h3, Function.update_of_ne h6, Function.update_of_ne h15]

def hintGaussStoreStatusCode : List Instr := [.imm 3 14, .add 3 14 3, .store 3 1]

theorem hintGaussStoreStatus_spec (E : RAMEnv) (G : HintGaussArea) (j value : ℕ) (state : RAMState)
    (hHeader : HintGaussHeader G j state.mem) (hFits : HintGaussHeaderFits E G j)
    (hContext : state.regs 14 = G.context) (hStatus : state.regs 1 = value) (hValue : value < 2 ^ E.W) :
    let out := runBlock hintGaussStoreStatusCode E state
    out.mem = Function.update state.mem (G.context + 14) value ∧ HintGaussHeader G j out.mem ∧
      out.regs 14 = G.context ∧ out.pc = state.pc + 3 ∧
      (∀ addr, addr ≠ G.context + 14 → out.mem addr = state.mem addr) := by
  have hSpan := hFits.span
  have hFourteen : 14 < 2 ^ E.W := by omega
  have hMemory : (runBlock hintGaussStoreStatusCode E state).mem = Function.update state.mem (G.context + 14) value := by
    simp [hintGaussStoreStatusCode, runBlock, execInstr, hContext, hStatus,
      Nat.mod_eq_of_lt hFourteen, Nat.mod_eq_of_lt hSpan, Nat.mod_eq_of_lt hValue]
  dsimp only
  refine ⟨hMemory, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hNe : G.context + i ≠ G.context + 14 := by omega
    rw [hMemory, Function.update_of_ne hNe]
    exact hHeader i hi
  · simp [hintGaussStoreStatusCode, runBlock, execInstr, hContext]
  · simp [hintGaussStoreStatusCode, runBlock, execInstr, Nat.add_assoc]
  · intro addr hNe
    rw [hMemory]
    exact Function.update_of_ne hNe _ _

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussAdvance_spec
#print axioms LinearSetReconciliation327.Main.hintGaussStoreStatus_spec
end S_HintGaussControl20261120
section S_HintGaussLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintGaussDone (h j : ℕ) : Finset (Fin h) := Finset.univ.filter (fun t => t.val < j)

theorem hintGaussDone_fresh {h : ℕ} (j : Fin h) : j ∉ hintGaussDone h j.val := by
  simp [hintGaussDone]

theorem hintGaussDone_succ {h : ℕ} (j : Fin h) :
    insert j (hintGaussDone h j.val) = hintGaussDone h (j.val + 1) := by
  ext t
  simp only [Finset.mem_insert, hintGaussDone, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hEq | hLess)
    · subst t
      exact Nat.lt_succ_self _
    · omega
  · intro hLess
    by_cases hEq : t.val = j.val
    · exact Or.inl (Fin.ext hEq)
    · exact Or.inr (by omega)

theorem hintGaussDone_full (h : ℕ) : hintGaussDone h h = Finset.univ := by
  ext t
  simp [hintGaussDone, t.isLt]

def HintGaussScanCore (G : HintGaussArea) (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows)
    (j : ℕ) (memory : ℕ → ℕ) : Prop :=
  (memory (G.context + 14) = 1 ∧ ∃ B : HintElimState G.rows G.hints,
    HintElimStored B G.residual G.lift memory ∧ HintElimInvariant A (hintGaussDone G.hints j) B) ∨
  (memory (G.context + 14) = 0 ∧ ∃ q : HintVec G.hints, A q = 0 ∧ q ≠ 0 ∧
    ∀ t : Fin G.hints, memory (G.kernelVec + t.val) = (q t).val)

structure HintGaussScanInv (G : HintGaussArea) (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows)
    (j : ℕ) (state : RAMState) : Prop where
  header : HintGaussHeader G j state.mem
  core : HintGaussScanCore G A j state.mem
  counter : state.regs 0 = j
  count_value : state.regs 6 = G.hints
  context_value : state.regs 14 = G.context

theorem hintGauss_header_update_frame (memory : ℕ → ℕ) (context index value : ℕ) (hIndex : index < 16) :
    CRMemFrame context (context + 16) memory (Function.update memory (context + index) value) := by
  intro addr hOutside
  have hNe : addr ≠ context + index := by
    rcases hOutside with hBefore | hAfter <;> omega
  exact Function.update_of_ne hNe _ _

theorem HintGaussScanCore.of_header_frame {E : RAMEnv} {G : HintGaussArea}
    {A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows} {j : ℕ} {original memory : ℕ → ℕ}
    (hCore : HintGaussScanCore G A j original) (hGeometry : HintGaussGeometry E G)
    (hReserve : G.context + 16 ≤ G.residual)
    (hFrame : CRMemFrame G.context (G.context + 16) original memory)
    (hFlag : memory (G.context + 14) = original (G.context + 14)) : HintGaussScanCore G A j memory := by
  have hR := hGeometry.residual_before
  have hL := hGeometry.lift_before
  have hCol := hGeometry.column_before
  have hVec := hGeometry.residualVec_before
  rcases hCore with ⟨hActive, B, hStored, hInv⟩ | ⟨hFailed, q, hAq, hNe, hQ⟩
  · exact Or.inl ⟨hFlag.trans hActive, B, hStored.of_frame hFrame (Or.inr hReserve) (Or.inr (by omega)), hInv⟩
  · refine Or.inr ⟨hFlag.trans hFailed, q, hAq, hNe, ?_⟩
    intro t
    rw [hFrame _ (Or.inr (by omega))]
    exact hQ t

theorem hintGaussCore_set_index {E : RAMEnv} {G : HintGaussArea}
    {A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows} {j new : ℕ} {memory : ℕ → ℕ}
    (hCore : HintGaussScanCore G A j memory) (hGeometry : HintGaussGeometry E G)
    (hReserve : G.context + 16 ≤ G.residual) :
    HintGaussScanCore G A j (Function.update memory (G.context + 8) new) := by
  apply hCore.of_header_frame hGeometry hReserve (hintGauss_header_update_frame memory G.context 8 new (by decide))
  exact Function.update_of_ne (by omega : G.context + 14 ≠ G.context + 8) _ _

theorem hintGaussColumnResult_store_status (G : HintGaussArea)
    (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows) (B : HintElimState G.rows G.hints)
    (j : Fin G.hints) (E : RAMEnv) (state : RAMState)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hResult : HintGaussColumnResult G A (hintGaussDone G.hints j.val) B j state) :
    HintGaussScanCore G A (j.val + 1) (Function.update state.mem (G.context + 14) (state.regs 1)) := by
  have hFrame := hintGauss_header_update_frame state.mem G.context 14 (state.regs 1) (by decide)
  have hR := hGeometry.residual_before
  have hL := hGeometry.lift_before
  have hCol := hGeometry.column_before
  have hVec := hGeometry.residualVec_before
  rcases hResult with ⟨hFailed, _, q, hAq, hNe, hQ⟩ | ⟨hActive, B', hStored, hInv⟩
  · refine Or.inr ⟨?_, q, hAq, hNe, ?_⟩
    · rw [Function.update_self]
      exact hFailed
    · intro t
      rw [hFrame _ (Or.inr (by omega))]
      exact hQ t
  · refine Or.inl ⟨?_, B', hStored.of_frame hFrame (Or.inr hReserve) (Or.inr (by omega)), ?_⟩
    · rw [Function.update_self]
      exact hActive
    · rw [hintGaussDone_succ] at hInv
      exact hInv

theorem hintGaussFailed_next (G : HintGaussArea) (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows)
    (old new : ℕ) (memory : ℕ → ℕ) (hCore : HintGaussScanCore G A old memory)
    (hFailed : memory (G.context + 14) = 0) : HintGaussScanCore G A new memory := by
  rcases hCore with ⟨hActive, _⟩ | hFailure
  · omega
  · exact Or.inr hFailure

theorem HintGaussScanInv.pc {G : HintGaussArea} {A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows}
    {j pc : ℕ} {state : RAMState} (h : HintGaussScanInv G A j state) :
    HintGaussScanInv G A j {state with pc := pc} :=
  ⟨h.header, h.core, h.counter, h.count_value, h.context_value⟩

theorem HintGaussScanInv.test {G : HintGaussArea} {A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows}
    {j : ℕ} {state : RAMState} (E : RAMEnv) (h : HintGaussScanInv G A j state) :
    HintGaussScanInv G A j (runBlock (Cond.lt 2 0 6).code E state) := by
  refine ⟨h.header, h.core, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.counter
  · simpa [Cond.code, runBlock, execInstr] using h.count_value
  · simpa [Cond.code, runBlock, execInstr] using h.context_value

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintGaussActiveStmt : Stmt := .seq hintGaussReadColumnStmt (.code hintGaussStoreStatusCode)
def hintGaussScanBranch : Stmt := .ite (.neqz 1) hintGaussActiveStmt (.code [])
def hintGaussScanBody : Stmt := .seq (.code (hintLoadField 1 14))
  (.seq hintGaussScanBranch (.code hintGaussAdvanceCode))
theorem hintGaussScanBody_len : hintGaussScanBody.len = 268 := rfl

theorem hintGaussScanBody_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (j : Fin G.hints)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hInv : HintGaussScanInv G (hintGaussMap G coords beta hPrefix) j.val state)
    (hHintSpan : G.hintList + G.hints < 2 ^ E.W)
    (hHint : state.mem (G.hintList + j.val) = (coords j).val)
    (hOffset : G.row * G.steps * G.buckets + (coords j).val < 2 ^ E.W)
    (hQuerySpan : ∀ s < G.rows, G.row * G.steps * G.buckets + (coords j).val + s * G.buckets < 2 ^ E.W)
    (hCoeff : ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (coords j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (coords j)).val)
    (hFits : HintGaussHeaderFits E G j.val)
    (hAt : At P base (hintGaussScanBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 268) state (fun k out =>
      k ≤ 2 * ((11 * G.rows + 11) * (G.rows + G.hints)) + 29 * G.rows + 170 ∧
      HintGaussScanInv G (hintGaussMap G coords beta hPrefix) (j.val + 1) out ∧
      CRMemFrame G.context (G.pivotRow + G.rows) state.mem out.mem) := by
  let A := hintGaussMap G coords beta hPrefix
  have hWord := hGeometry.word_bound
  have hHints := hGeometry.hints_bound
  have hNext : j.val + 1 < 2 ^ E.W := by have := j.isLt; omega
  have hR := hGeometry.residual_before
  have hL := hGeometry.lift_before
  have hCol := hGeometry.column_before
  have hVec := hGeometry.residualVec_before
  have hQ := hGeometry.kernelVec_before
  obtain ⟨hFlagAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hBranchAt, hAdvanceAt⟩ := At.seqStmt hRestAt
  change At P base (hintLoadField 1 14) at hFlagAt
  change At P (base + 3) (hintGaussScanBranch.compile (base + 3)) at hBranchAt
  change At P (base + 259) hintGaussAdvanceCode at hAdvanceAt
  have hFlagSpec := hintLoadField_spec E state 1 14 G.context hInv.context_value hFits.span
  generalize hSF : runBlock (hintLoadField 1 14) E state = sF at hFlagSpec
  obtain ⟨hFPc, hFMem, hFValue, hFRegs⟩ := hFlagSpec
  have hFlagBound : state.mem (G.context + 14) < 2 ^ E.W := by
    rcases hInv.core with ⟨hActive, _⟩ | ⟨hFailed, _⟩ <;> omega
  rw [Nat.mod_eq_of_lt hFlagBound] at hFValue
  have hFContext : sF.regs 14 = G.context := (hFRegs 14 (by decide) (by decide)).trans hInv.context_value
  have hFHeader : HintGaussHeader G j.val sF.mem := by rw [hFMem]; exact hInv.header
  have hRunF : (step P E)^[3] state = sF := by
    have hh := iterate_runBlock_of_at P E (hintLoadField 1 14) state (by rwa [hPc])
      (by simp [hintLoadField, NoBranch, Instr.NoBranchI])
    rw [hSF] at hh
    exact hh
  have hPcF : sF.pc = base + 3 := by rw [hFPc, hPc]
  let Q : ℕ → RAMState → Prop := fun k out =>
    k ≤ 2 * ((11 * G.rows + 11) * (G.rows + G.hints)) + 29 * G.rows + 158 ∧
      HintGaussHeader G j.val out.mem ∧ HintGaussScanCore G A (j.val + 1) out.mem ∧
      CRMemFrame G.context (G.pivotRow + G.rows) state.mem out.mem ∧ out.regs 14 = G.context
  have hBranch : Sem P E (base + 3) (base + 259) sF Q := by
    apply Sem.ite P E (base + 3) (.neqz 1) hintGaussActiveStmt (.code []) sF Q hBranchAt hWord hPcF
    · intro hGo
      change Sem P E (base + 4) (base + 257) {sF with pc := base + 4}
        (fun k out => Q (1 + k + 1) {out with pc := base + 259})
      have hActiveData : ∃ B : HintElimState G.rows G.hints,
          HintElimStored B G.residual G.lift state.mem ∧ HintElimInvariant A (hintGaussDone G.hints j.val) B := by
        rcases hInv.core with ⟨_, hB⟩ | ⟨hFailed, _⟩
        · exact hB
        · exact False.elim (hGo (hFValue.trans hFailed))
      obtain ⟨B, hStoredB, hInvB⟩ := hActiveData
      have hStoredF : HintElimStored B G.residual G.lift sF.mem := by rw [hFMem]; exact hStoredB
      have hHintF : sF.mem (G.hintList + j.val) = (coords j).val := by rw [hFMem]; exact hHint
      have hActiveAt := (at_ite hBranchAt).2.2.1
      obtain ⟨hReadAt, hStoreAt⟩ := At.seqStmt hActiveAt
      change At P (base + 4) (hintGaussReadColumnStmt.compile (base + 4)) at hReadAt
      change At P (base + 254) hintGaussStoreStatusCode at hStoreAt
      obtain ⟨_, kR, sR, hRunR, hPcR, hCostR, hHeaderR, hFrameR, hCtxR, hResultR⟩ :=
        hintGaussReadColumnStmt_sem G coords beta hPrefix (hintGaussDone G.hints j.val) B j
          P E {sF with pc := base + 4} (base + 4) hGeometry hInvB (hintGaussDone_fresh j)
          hStoredF hHintSpan hHintF hOffset hQuerySpan hCoeff hFHeader hFits hFContext hReadAt rfl
      have hStatusBound : sR.regs 1 < 2 ^ E.W := by
        rcases hResultR with ⟨hFailed, _⟩ | ⟨hActive, _⟩ <;> omega
      have hStoreSpec := hintGaussStoreStatus_spec E G j.val (sR.regs 1) sR hHeaderR hFits hCtxR rfl hStatusBound
      generalize hSO : runBlock hintGaussStoreStatusCode E sR = out at hStoreSpec
      obtain ⟨hMemS, hHeaderS, hCtxS, hPcS, hFrameS⟩ := hStoreSpec
      have hRunS : (step P E)^[3] sR = out := by
        have hh := iterate_runBlock_of_at P E hintGaussStoreStatusCode sR (by rwa [hPcR])
          (by simp [hintGaussStoreStatusCode, NoBranch, Instr.NoBranchI])
        rw [hSO] at hh
        exact hh
      have hCoreS : HintGaussScanCore G A (j.val + 1) out.mem := by
        rw [hMemS]
        exact hintGaussColumnResult_store_status G A B j E sR hGeometry hReserve hResultR
      refine ⟨rfl, 3 + kR, out, hintIterate_then (step P E) hRunR hRunS, ?_, ?_⟩
      · rw [hPcS, hPcR]
      · dsimp only [Q]
        refine ⟨by omega, hHeaderS, hCoreS, ?_, hCtxS⟩
        intro addr hOutside
        have hNe : addr ≠ G.context + 14 := by
          rcases hOutside with hBefore | hAfter <;> omega
        have hOutsideR : addr < G.residual ∨ G.pivotRow + G.rows ≤ addr := by
          rcases hOutside with hBefore | hAfter <;> omega
        rw [hFrameS addr hNe, hFrameR addr hOutsideR]
        exact congrFun hFMem addr
    · intro hStop
      change Sem P E (base + 258) (base + 258) {sF with pc := base + 258}
        (fun k out => Q (1 + k + 1) {out with pc := base + 259})
      have hZero : sF.regs 1 = 0 := by
        change ¬ sF.regs 1 ≠ 0 at hStop
        exact not_not.mp hStop
      have hFailed : state.mem (G.context + 14) = 0 := hFValue.symm.trans hZero
      have hCoreFailed := hintGaussFailed_next G A j.val (j.val + 1) state.mem hInv.core hFailed
      have hNative := Sem.block P E (base + 258) [] {sF with pc := base + 258}
        (by intro i hi; simp at hi)
        (by trivial) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      dsimp only [Q]
      refine ⟨by simp_all only [List.length_nil]; omega, hFHeader, ?_, ?_, hFContext⟩
      · change HintGaussScanCore G A (j.val + 1) sF.mem
        rw [hFMem]
        exact hCoreFailed
      · intro addr _
        exact congrFun hFMem addr
  obtain ⟨_, kB, sB, hRunB, hPcB, hCostB, hHeaderB, hCoreB, hFrameB, hCtxB⟩ := hBranch
  have hAdvance := hintGaussAdvance_spec E G j.val sB hHeaderB hFits hCtxB hNext
  generalize hSA : runBlock hintGaussAdvanceCode E sB = out at hAdvance
  obtain ⟨hPcA, hCounterA, hCountA, hCtxA, hMemA, hHeaderA, hFrameA, _⟩ := hAdvance
  have hRunA : (step P E)^[9] sB = out := by
    have hh := iterate_runBlock_of_at P E hintGaussAdvanceCode sB (by rwa [hPcB])
      (by simp [hintGaussAdvanceCode, NoBranch, Instr.NoBranchI])
    rw [hSA] at hh
    exact hh
  have hCoreA : HintGaussScanCore G A (j.val + 1) out.mem := by
    rw [hMemA]
    exact hintGaussCore_set_index hCoreB hGeometry hReserve
  refine ⟨hPc, 9 + (kB + 3), out, hintIterate_then (step P E) (hintIterate_then (step P E) hRunF hRunB) hRunA,
    ?_, by omega, ⟨hHeaderA, hCoreA, hCounterA, hCountA, hCtxA⟩, ?_⟩
  · rw [hPcA, hPcB]
  · intro addr hOutside
    have hNe : addr ≠ G.context + 8 := by rcases hOutside with hBefore | hAfter <;> omega
    rw [hFrameA addr hNe, hFrameB addr hOutside]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintGaussScanLoop : Stmt := .loop (.lt 2 0 6) hintGaussScanBody
theorem hintGaussScanLoop_len : hintGaussScanLoop.len = 271 := rfl

/-- The actual native loop visits every hint column. Once a kernel certificate
    is found, later iterations skip elimination and retain that certificate. -/
theorem hintGaussScanLoop_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hInv : HintGaussScanInv G (hintGaussMap G coords beta hPrefix) 0 state)
    (hHintBefore : G.hintList + G.hints ≤ G.context)
    (hHint : ∀ j : Fin G.hints, state.mem (G.hintList + j.val) = (coords j).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ j : Fin G.hints, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (coords j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (coords j)).val)
    (hFits : HintGaussHeaderFits E G 0)
    (hAt : At P base (hintGaussScanLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 271) state (fun k out =>
      k ≤ (2 * ((11 * G.rows + 11) * (G.rows + G.hints)) + 29 * G.rows + 173) * G.hints + 2 ∧
      HintGaussScanInv G (hintGaussMap G coords beta hPrefix) G.hints out ∧
      CRMemFrame G.context (G.pivotRow + G.rows) state.mem out.mem) := by
  let A := hintGaussMap G coords beta hPrefix
  let B := 2 * ((11 * G.rows + 11) * (G.rows + G.hints)) + 29 * G.rows + 170
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = G.hints ∧
    HintGaussScanInv G A j st ∧ CRMemFrame G.context (G.pivotRow + G.rows) state.mem st.mem
  have hWord := hGeometry.word_bound
  have hHints := hGeometry.hints_bound
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  have hBodyAt : At P (base + 2) (hintGaussScanBody.compile (base + 2)) := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hScan, hFrame⟩ := hI
    exact ⟨j, hJ, hScan.pc, hFrame⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 0 6).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, hScan, hFrame⟩ := hI
    exact ⟨j, hJ, hScan.test E, hFrame⟩
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 0 6).eval st := by
    intro left st hI
    obtain ⟨j, hJ, hScan, _⟩ := hI
    change st.regs 0 < st.regs 6
    rw [hScan.counter, hScan.count_value]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 6).eval st := by
    intro st hI
    obtain ⟨j, hJ, hScan, _⟩ := hI
    change ¬ st.regs 0 < st.regs 6
    rw [hScan.counter, hScan.count_value]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + hintGaussScanBody.len) st
        (fun k out => k ≤ B ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hScan, hFrame⟩ := hI
    have hj : j < G.hints := by omega
    let t : Fin G.hints := ⟨j, hj⟩
    have hHintNow : st.mem (G.hintList + t.val) = (coords t).val := by
      rw [hFrame _ (Or.inl (by have := t.isLt; omega))]
      exact hHint t
    have hOffset : G.row * G.steps * G.buckets + (coords t).val < 2 ^ E.W := by
      have hh := (hintGauss_query_index_lt G.row G.steps G.buckets 0 (coords t).val hSteps (coords t).isLt).trans_le hCoeffSpan
      simpa only [Nat.zero_mul, Nat.add_zero] using hh
    have hQueries : ∀ s < G.rows, G.row * G.steps * G.buckets + (coords t).val + s * G.buckets < 2 ^ E.W := by
      intro s hs
      exact (hintGauss_query_index_lt G.row G.steps G.buckets s (coords t).val (hs.trans_le hPrefix) (coords t).isLt).trans_le hCoeffSpan
    have hFitsNow : HintGaussHeaderFits E G t.val := hFits.change_index (hj.trans hHints)
    have hNative := hintGaussScanBody_sem G coords beta hPrefix t P E st (base + 2) hGeometry hReserve hScan
      (by omega) hHintNow hOffset hQueries (hCoeff t) hFitsNow hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hNext, hNextFrame⟩ := hOut
    refine ⟨hCost, j + 1, by omega, hNext, ?_⟩
    intro addr hOutside
    exact (hNextFrame addr hOutside).trans (hFrame addr hOutside)
  have hInitial : I G.hints state := ⟨0, by omega, hInv, by intro addr _; rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) hintGaussScanBody hAt hWord I B
    hIpc hItest hGo hStop hBody G.hints state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, hFinal, hFrame⟩ := hOut
  have hj : j = G.hints := by omega
  rw [hj] at hFinal
  refine ⟨?_, hFinal, hFrame⟩
  have hFactor : 1 + B + 2 = 2 * ((11 * G.rows + 11) * (G.rows + G.hints)) + 29 * G.rows + 173 := by
    dsimp only [B]
    omega
  change k ≤ (1 + B + 2) * G.hints + 2 at hCost
  simpa only [hFactor] using hCost

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussScanLoop_sem
end S_HintGaussLoop20261120
section S_HintGaussFactor20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintGaussInitFields : List (Fin 16 × ℕ) := [(4, 2), (11, 1), (12, 3), (13, 0)]
def hintGaussInitTail : List Instr := [.imm 1 1, .imm 3 14, .add 3 14 3, .store 3 1]
def hintGaussInitPre : List Instr := hintLoadFields hintGaussInitFields ++ hintGaussInitTail
theorem hintGaussInitPre_length : hintGaussInitPre.length = 16 := rfl

theorem hintGaussInitPre_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) :
    let out := runBlock hintGaussInitPre E state
    HintInitRegs G.lift G.rows G.hints G.context out ∧ out.regs 4 = G.residual ∧
      out.mem = Function.update state.mem (G.context + 14) 1 ∧ HintGaussHeader G 0 out.mem ∧
      out.mem (G.context + 14) = 1 := by
  have hSpan := hFits.span
  have hWord : 1 < 2 ^ E.W := by omega
  have hFourteen : 14 < 2 ^ E.W := by omega
  have hValid : ∀ pair ∈ hintGaussInitFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintGaussInitFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by omega⟩
  have hLoad := hintLoadFields_spec E G.context hintGaussInitFields state hContext hValid
  have hValues := hintGaussHeader_mod E G 0 state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintGaussInitFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G 0 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G 0 2 := by
    simpa [hintGaussInitFields, hintLoadedValue, hZero,
      hValues 1 (by decide), hValues 2 (by decide), hValues 3 (by decide)] using hLoad.2.2.2 4 (by decide)
  have hR11 : mid.regs 11 = hintGaussHeaderValue G 0 1 := by
    simpa [hintGaussInitFields, hintLoadedValue, hZero,
      hValues 1 (by decide), hValues 2 (by decide), hValues 3 (by decide)] using hLoad.2.2.2 11 (by decide)
  have hR12 : mid.regs 12 = hintGaussHeaderValue G 0 3 := by
    simpa [hintGaussInitFields, hintLoadedValue, hZero,
      hValues 1 (by decide), hValues 2 (by decide), hValues 3 (by decide)] using hLoad.2.2.2 12 (by decide)
  have hR13 : mid.regs 13 = hintGaussHeaderValue G 0 0 := by
    simpa [hintGaussInitFields, hintLoadedValue, hZero,
      hValues 1 (by decide), hValues 2 (by decide), hValues 3 (by decide)] using hLoad.2.2.2 13 (by decide)
  have h14 : mid.regs 14 = G.context := hLoad.2.2.1
  have hMemory : (runBlock hintGaussInitTail E mid).mem = Function.update state.mem (G.context + 14) 1 := by
    simp [hintGaussInitTail, runBlock, execInstr, h14, Nat.mod_eq_of_lt hWord,
      Nat.mod_eq_of_lt hFourteen, Nat.mod_eq_of_lt hSpan, hLoad.2.1]
  dsimp only
  rw [hintGaussInitPre, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, hMemory, ?_, ?_⟩
  · simp [hintGaussInitTail, runBlock, execInstr, hR4, hR11, hR12, hR13, h14, hintGaussHeaderValue]
  · simp [hintGaussInitTail, runBlock, execInstr, hR4, hR11, hR12, hR13, h14, hintGaussHeaderValue]
  · simp [hintGaussInitTail, runBlock, execInstr, hR4, hR11, hR12, hR13, h14, hintGaussHeaderValue]
  · simp [hintGaussInitTail, runBlock, execInstr, hR4, hR11, hR12, hR13, h14, hintGaussHeaderValue]
  · simp [hintGaussInitTail, runBlock, execInstr, hR4, hR11, hR12, hR13, h14, hintGaussHeaderValue]
  · intro i hi
    have hNe : G.context + i ≠ G.context + 14 := by omega
    rw [hMemory, Function.update_of_ne hNe]
    exact hHeader i hi
  · rw [hMemory, Function.update_self]

def hintGaussInitEnd : List Instr := hintLoadField 6 1 ++ [.imm 0 0]
theorem hintGaussInitEnd_length : hintGaussInitEnd.length = 4 := rfl

theorem hintGaussInitEnd_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) :
    let out := runBlock hintGaussInitEnd E state
    out.pc = state.pc + 4 ∧ out.mem = state.mem ∧ out.regs 0 = 0 ∧
      out.regs 6 = G.hints ∧ out.regs 14 = G.context := by
  have hSpan := hFits.span
  have hRead := hintLoadField_spec E state 6 1 G.context hContext (by omega)
  generalize hMid : runBlock (hintLoadField 6 1) E state = mid at hRead
  have hCount : mid.regs 6 = G.hints := by
    rw [hRead.2.2.1, hHeader 1 (by decide), Nat.mod_eq_of_lt (hFits.values 1 (by decide))]
    rfl
  have h14 : mid.regs 14 = G.context := (hRead.2.2.2 14 (by decide) (by decide)).trans hContext
  dsimp only
  rw [hintGaussInitEnd, runBlock_append, hMid]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [runBlock, execInstr, hCount, h14, hRead.1, hRead.2.1, Nat.add_assoc]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintGaussInitializeStmt : Stmt := .seq (.code hintGaussInitPre)
  (.seq hintElimInitStmt (.code hintGaussInitEnd))
theorem hintGaussInitializeStmt_len : hintGaussInitializeStmt.len = 57 := rfl

theorem hintGaussInitializeStmt_sem (G : HintGaussArea) (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussInitializeStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 57) state (fun k out =>
      k = 7 * (G.rows * G.rows + G.rows + G.hints * G.rows) + 42 ∧
      HintGaussScanInv G A 0 out ∧ CRMemFrame G.context (G.pivotRow + G.rows) state.mem out.mem) := by
  have hWord := hGeometry.word_bound
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hGeometry
  have hSelf : G.rows ≤ G.rows * G.rows := by
    rcases Nat.eq_zero_or_pos G.rows with hZero | hPositive
    · simp [hZero]
    · simpa only [Nat.mul_one] using Nat.mul_le_mul_left G.rows (Nat.succ_le_of_lt hPositive)
  obtain ⟨hPreAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hInitAt, hEndAt⟩ := At.seqStmt hRestAt
  change At P base hintGaussInitPre at hPreAt
  change At P (base + 16) (hintElimInitStmt.compile (base + 16)) at hInitAt
  change At P (base + 53) hintGaussInitEnd at hEndAt
  have hPreNo : NoBranch hintGaussInitPre := by
    rw [hintGaussInitPre, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintGaussInitTail, NoBranch, Instr.NoBranchI]⟩
  have hPre := hintGaussInitPre_spec E G state hHeader hFits hContext
  generalize hSP : runBlock hintGaussInitPre E state = sP at hPre
  obtain ⟨hArgsP, hDestP, hMemP, hHeaderP, hFlagP⟩ := hPre
  have hRunP : (step P E)^[16] state = sP := by
    have hh := iterate_runBlock_of_at P E hintGaussInitPre state (by rwa [hPc]) hPreNo
    rw [hSP] at hh
    exact hh
  have hPcP : sP.pc = base + 16 := by
    have hh := runBlock_pc hintGaussInitPre E state hPreNo
    rw [hSP, hPc] at hh
    exact hh
  obtain ⟨_, kI, sI, hRunI, hPcI, hCostI, hStoredI, hFrameI, hArgsI, _⟩ :=
    hintElimInitStmt_stored_sem P E sP G.residual G.lift G.rows G.hints G.context (base + 16)
      hWord (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl h1) hInitAt hPcP hArgsP hDestP
  have hHeaderI : HintGaussHeader G 0 sI.mem := by
    intro i hi
    rw [hFrameI _ (Or.inl (by omega)) (Or.inl (by omega))]
    exact hHeaderP i hi
  have hFlagI : sI.mem (G.context + 14) = 1 := by
    rw [hFrameI _ (Or.inl (by omega)) (Or.inl (by omega))]
    exact hFlagP
  have hEnd := hintGaussInitEnd_spec E G sI hHeaderI hFits hArgsI.context_value
  generalize hSE : runBlock hintGaussInitEnd E sI = out at hEnd
  obtain ⟨hPcE, hMemE, hCounterE, hCountE, hCtxE⟩ := hEnd
  have hRunE : (step P E)^[4] sI = out := by
    have hh := iterate_runBlock_of_at P E hintGaussInitEnd sI (by rwa [hPcI])
      (by simp [hintGaussInitEnd, hintLoadField, upNoBranch_append, NoBranch, Instr.NoBranchI])
    rw [hSE] at hh
    exact hh
  have hCore : HintGaussScanCore G A 0 out.mem := by
    refine Or.inl ⟨?_, hintElimInit G.rows G.hints, ?_, ?_⟩
    · rw [hMemE]
      exact hFlagI
    · rw [hMemE]
      exact hStoredI
    · simpa [hintGaussDone] using hintElimInit_invariant A
  have hHeaderE : HintGaussHeader G 0 out.mem := by rw [hMemE]; exact hHeaderI
  refine ⟨hPc, 4 + (kI + 16), out, hintIterate_then (step P E) (hintIterate_then (step P E) hRunP hRunI) hRunE,
    ?_, by omega, ⟨hHeaderE, hCore, hCounterE, hCountE, hCtxE⟩, ?_⟩
  · rw [hPcE, hPcI]
  · intro addr hOutside
    have hOutsideR : addr < G.residual ∨ G.residual + G.rows * G.rows ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    have hOutsideL : addr < G.lift ∨ G.lift + G.hints * G.rows ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    have hNe : addr ≠ G.context + 14 := by rcases hOutside with hBefore | hAfter <;> omega
    rw [hMemE, hFrameI addr hOutsideR hOutsideL, hMemP, Function.update_of_ne hNe]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintGaussFactorStmt : Stmt := .seq hintGaussInitializeStmt hintGaussScanLoop
theorem hintGaussFactorStmt_len : hintGaussFactorStmt.len = 328 := rfl

/-- From arbitrary old workspace memory, initialize and factor the actual public
    hint-column matrix. All loops, branches and their cost are native RAM steps. -/
theorem hintGaussFactorStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hHintBefore : G.hintList + G.hints ≤ G.context)
    (hHint : ∀ j : Fin G.hints, state.mem (G.hintList + j.val) = (coords j).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ j : Fin G.hints, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (coords j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (coords j)).val)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussFactorStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 328) state (fun k out =>
      k ≤ 7 * (G.rows * G.rows + G.rows + G.hints * G.rows) +
        (2 * ((11 * G.rows + 11) * (G.rows + G.hints)) + 29 * G.rows + 173) * G.hints + 44 ∧
      HintGaussScanInv G (hintGaussMap G coords beta hPrefix) G.hints out ∧
      CRMemFrame G.context (G.pivotRow + G.rows) state.mem out.mem) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base (hintGaussInitializeStmt.compile base) at hInitAt
  change At P (base + 57) (hintGaussScanLoop.compile (base + 57)) at hLoopAt
  obtain ⟨_, kI, sI, hRunI, hPcI, hCostI, hInvI, hFrameI⟩ :=
    hintGaussInitializeStmt_sem G (hintGaussMap G coords beta hPrefix) P E state base
      hGeometry hReserve hHeader hFits hContext hInitAt hPc
  have hHintI : ∀ j : Fin G.hints, sI.mem (G.hintList + j.val) = (coords j).val := by
    intro j
    rw [hFrameI _ (Or.inl (by have := j.isLt; omega))]
    exact hHint j
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hInvL, hFrameL⟩ :=
    hintGaussScanLoop_sem G coords beta hPrefix P E sI (base + 57) hGeometry hReserve hInvI
      hHintBefore hHintI hSteps hCoeffSpan hCoeff hFits hLoopAt hPcI
  refine ⟨hPc, kL + kI, out, hintIterate_then (step P E) hRunI hRunL, ?_, by omega, hInvL, ?_⟩
  · simpa only [Nat.add_assoc] using hPcL
  · intro addr hOutside
    exact (hFrameL addr hOutside).trans (hFrameI addr hOutside)

theorem hintGaussScanCore_complete (G : HintGaussArea) (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows)
    (memory : ℕ → ℕ) (hCore : HintGaussScanCore G A G.hints memory) :
    (memory (G.context + 14) = 1 ∧ ∃ B : HintElimState G.rows G.hints,
      HintElimStored B G.residual G.lift memory ∧ HintElimInvariant A Finset.univ B ∧
      ∀ x : HintVec G.hints, B.lift (A x) = x) ∨
    (memory (G.context + 14) = 0 ∧ ∃ q : HintVec G.hints, A q = 0 ∧ q ≠ 0 ∧
      ∀ t : Fin G.hints, memory (G.kernelVec + t.val) = (q t).val) := by
  rcases hCore with ⟨hActive, B, hStored, hInv⟩ | hFailed
  · rw [hintGaussDone_full] at hInv
    exact Or.inl ⟨hActive, B, hStored, hInv, hintElim_left_inverse A B hInv⟩
  · exact Or.inr hFailed

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussFactorStmt_sem
#print axioms LinearSetReconciliation327.Main.hintGaussScanCore_complete
end S_HintGaussFactor20261120
section S_HintGaussCandidate20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintGaussRhsFields : List (Fin 16 × ℕ) := [(4, 4), (5, 9), (6, 0), (13, 1)]
def hintGaussRhsTail : List Instr := [.add 5 5 13, .imm 7 1, .imm 15 1]
def hintGaussRhsSetup : List Instr := hintLoadFields hintGaussRhsFields ++ hintGaussRhsTail
theorem hintGaussRhsSetup_length : hintGaussRhsSetup.length = 15 := rfl

theorem hintGaussRhsSetup_spec (E : RAMEnv) (G : HintGaussArea) (phase : ℕ) (state : RAMState)
    (hHeader : HintGaussHeader G phase state.mem) (hFits : HintGaussHeaderFits E G phase)
    (hContext : state.regs 14 = G.context) (hWord : 1 < 2 ^ E.W)
    (hSource : G.hintList + G.hints < 2 ^ E.W) :
    let out := runBlock hintGaussRhsSetup E state
    HintCopyParams G.column (G.hintList + G.hints) 1 G.rows out ∧ out.mem = state.mem ∧ out.regs 14 = G.context := by
  have hValid : ∀ pair ∈ hintGaussRhsFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintGaussRhsFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintGaussRhsFields state hContext hValid
  have hValues := hintGaussHeader_mod E G phase state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintGaussRhsFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G phase 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G phase 4 := by
    simpa [hintGaussRhsFields, hintLoadedValue, hZero,
      hValues 1 (by decide), hValues 4 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 4 (by decide)
  have hR5 : mid.regs 5 = hintGaussHeaderValue G phase 9 := by
    simpa [hintGaussRhsFields, hintLoadedValue, hZero,
      hValues 1 (by decide), hValues 4 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 5 (by decide)
  have hR6 : mid.regs 6 = hintGaussHeaderValue G phase 0 := by
    simpa [hintGaussRhsFields, hintLoadedValue, hZero,
      hValues 1 (by decide), hValues 4 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 6 (by decide)
  have hR13 : mid.regs 13 = hintGaussHeaderValue G phase 1 := by
    simpa [hintGaussRhsFields, hintLoadedValue, hZero,
      hValues 1 (by decide), hValues 4 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 13 (by decide)
  dsimp only
  rw [hintGaussRhsSetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [hintGaussRhsTail, runBlock, execInstr, hR4, hR5, hR6, hR13, hintGaussHeaderValue,
      Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hSource, hLoad.2.1, hLoad.2.2.1]

def hintGaussRhsCopyStmt : Stmt := .seq (.code hintGaussRhsSetup) hintCopyStmt
theorem hintGaussRhsCopyStmt_len : hintGaussRhsCopyStmt.len = 25 := rfl

theorem hintGaussRhsCopyStmt_sem (G : HintGaussArea) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base phase : ℕ)
    (hGeometry : HintGaussGeometry E G) (hSource : G.hintList + G.hints + G.rows ≤ G.context)
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + s.val) = (v s).val)
    (hHeader : HintGaussHeader G phase state.mem) (hFits : HintGaussHeaderFits E G phase)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussRhsCopyStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 25) state (fun k out => k = 9 * G.rows + 18 ∧
      (∀ s : Fin G.rows, out.mem (G.column + s.val) = (v s).val) ∧
      CRMemFrame G.column (G.column + G.rows) state.mem out.mem ∧ HintGaussHeader G phase out.mem ∧
      out.regs 14 = G.context) := by
  have hWord := hGeometry.word_bound
  have hWidth := hGeometry.width_bound
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hGeometry
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintGaussRhsSetup at hSetupAt
  change At P (base + 15) (hintCopyStmt.compile (base + 15)) at hBodyAt
  have hNo : NoBranch hintGaussRhsSetup := by
    rw [hintGaussRhsSetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintGaussRhsTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintGaussRhsSetup_spec E G phase state hHeader hFits hContext hWord (by omega)
  generalize hMid : runBlock hintGaussRhsSetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h14⟩ := hSetup
  have hRunSetup : (step P E)^[15] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGaussRhsSetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 15 := by
    have hh := runBlock_pc hintGaussRhsSetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hVector' : ∀ s < G.rows, mid.mem (G.hintList + G.hints + s * 1) = (hintDenseVec v s).val := by
    intro s hs
    rw [hMem]
    simpa only [hintDenseVec, dif_pos hs, Nat.mul_one] using hVector ⟨s, hs⟩
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, _, hOutMem, _, hFrame, hRegs⟩ :=
    hintCopyStmt_sem P E mid G.column (G.hintList + G.hints) 1 G.rows (base + 15) (hintDenseVec v)
      hWord hWidth (by intro s hs; omega) (by intro s hs; simp only [Nat.mul_one]; omega)
      (by intro s hs; simp only [Nat.mul_one]; exact Or.inl (by omega)) hVector' hBodyAt hMidPc hArgs
  have hFrame' : CRMemFrame G.column (G.column + G.rows) state.mem out.mem := by
    intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)
  refine ⟨hPc, kBody + 15, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega, ?_, hFrame', ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro s
    rw [hOutMem]
    have hRange : G.column ≤ G.column + s.val ∧ G.column + s.val < G.column + G.rows := by have := s.isLt; omega
    simp only [hintCopyMem, hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, zero_mul, add_zero,
      hintDenseVec, dif_pos s.isLt]
  · exact hintGaussHeader_of_frame G phase G.column (G.column + G.rows) state.mem out.mem hHeader hFrame' (Or.inl (by omega))
  · exact (hRegs 14 (by decide) (by decide) (by decide) (by decide)).trans h14

end LinearSetReconciliation327.Main

namespace LinearSetReconciliation327.Main

def hintGaussSolveVecStmt : Stmt := .seq hintGaussResidualStmt (.seq hintGaussLiftStmt hintGaussPivotStmt)
theorem hintGaussSolveVecStmt_len : hintGaussSolveVecStmt.len = 96 := rfl

/-- Apply the computed elimination state to an actual right-hand side in RAM.
    A zero pivot result is equivalent to a unique solution, and its coordinates
    are stored in the kernel/output buffer. -/
theorem hintGaussSolveVecStmt_sem (G : HintGaussArea)
    (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows) (B : HintElimState G.rows G.hints) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base phase : ℕ)
    (hGeometry : HintGaussGeometry E G) (hInv : HintElimInvariant A Finset.univ B)
    (hStored : HintElimStored B G.residual G.lift state.mem)
    (hColumn : ∀ t : Fin G.rows, state.mem (G.column + t.val) = (v t).val)
    (hHeader : HintGaussHeader G phase state.mem) (hFits : HintGaussHeaderFits E G phase)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussSolveVecStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 96) state (fun k out =>
      k ≤ (11 * G.rows + 11) * (G.rows + G.hints) + 11 * G.rows + 51 ∧
      HintElimStored B G.residual G.lift out.mem ∧ HintGaussHeader G phase out.mem ∧
      (∀ t : Fin G.hints, out.mem (G.kernelVec + t.val) = (B.lift v t).val) ∧
      (out.regs 1 = 0 ↔ B.residual v = 0) ∧ (out.regs 1 = 0 ↔ ∃! x, A x = v) ∧
      (out.regs 1 = 0 → A (B.lift v) = v ∧ ∀ x, A x = v → x = B.lift v) ∧
      CRMemFrame G.residualVec (G.kernelVec + G.hints) state.mem out.mem ∧ out.regs 14 = G.context) := by
  have hWord := hGeometry.word_bound
  have hWidth := hGeometry.width_bound
  have hHints := hGeometry.hints_bound
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hGeometry
  obtain ⟨hRA, hRest⟩ := At.seqStmt hAt
  obtain ⟨hLA, hPA⟩ := At.seqStmt hRest
  change At P base (hintGaussResidualStmt.compile base) at hRA
  change At P (base + 38) (hintGaussLiftStmt.compile (base + 38)) at hLA
  change At P (base + 76) (hintGaussPivotStmt.compile (base + 76)) at hPA
  obtain ⟨_, kR, sR, hRunR, hPcR, hCostR, hRValues, hFrameR, hCtxR⟩ :=
    hintGaussResidualStmt_sem G phase B.residual v P E state base hWord hWidth hWidth
      (by omega) (by omega) (by omega) hStored.residual_cells hColumn
      (Or.inl (by omega)) (Or.inl h3) hHeader hFits hContext hRA hPc
  have hHeaderR := hintGaussHeader_of_frame G phase G.residualVec (G.residualVec + G.rows)
    state.mem sR.mem hHeader hFrameR (Or.inl (by omega))
  have hStoredR := hStored.of_frame hFrameR (Or.inl (by omega)) (Or.inl (by omega))
  have hColumnR : ∀ t : Fin G.rows, sR.mem (G.column + t.val) = (v t).val := by
    intro t
    rw [hFrameR _ (Or.inl (by have := t.isLt; omega))]
    exact hColumn t
  obtain ⟨_, kL, sL, hRunL, hPcL, hCostL, hLValues, hFrameL, hCtxL⟩ :=
    hintGaussLiftStmt_sem G phase B.lift v P E sR (base + 38) hWord hWidth hHints
      (by omega) (by omega) (by omega) hStoredR.lift_cells hColumnR
      (Or.inl (by omega)) (Or.inl (by omega)) hHeaderR hFits hCtxR hLA hPcR
  have hHeaderL := hintGaussHeader_of_frame G phase G.kernelVec (G.kernelVec + G.hints)
    sR.mem sL.mem hHeaderR hFrameL (Or.inl (by omega))
  have hStoredL := hStoredR.of_frame hFrameL (Or.inl (by omega)) (Or.inl (by omega))
  have hRValuesL : ∀ t : Fin G.rows, sL.mem (G.residualVec + t.val) = (B.residual v t).val := by
    intro t
    rw [hFrameL _ (Or.inl (by have := t.isLt; omega))]
    exact hRValues t
  have hPcL' : sL.pc = base + 76 := by simpa only [Nat.add_assoc] using hPcL
  obtain ⟨_, kP, out, hRunP, hPcP, hCostP, hMemP, _, hZeroP, _, hCtxP⟩ :=
    hintGaussPivotStmt_sem G phase (B.residual v) P E sL (base + 76) hWord hWidth (by omega)
      hRValuesL hHeaderL hFits hCtxL hPA hPcL'
  refine ⟨hPc, kP + (kL + kR), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunR hRunL) hRunP, ?_, ?_, ?_, ?_, ?_, hZeroP, ?_, ?_, ?_, hCtxP⟩
  · simpa only [Nat.add_assoc] using hPcP
  · have hExpand : (11 * G.rows + 11) * (G.rows + G.hints) =
        (11 * G.rows + 11) * G.rows + (11 * G.rows + 11) * G.hints := by ring
    omega
  · rw [hMemP]
    exact hStoredL
  · rw [hMemP]
    exact hHeaderL
  · intro t
    rw [hMemP]
    exact hLValues t
  · constructor
    · intro hz
      exact hintElim_solution_unique A B hInv v (hZeroP.mp hz)
    · rintro ⟨x, hx, _⟩
      exact hZeroP.mpr ((hintElim_solution_iff A B hInv v).mp ⟨x, hx⟩)
  · intro hz
    refine ⟨?_, ?_⟩
    · simpa only [hZeroP.mp hz, add_zero] using hInv.decompose v
    · intro x hx
      rw [← hintElim_left_inverse A B hInv x, hx]
  · intro addr hOutside
    have hOutsideR : addr < G.residualVec ∨ G.residualVec + G.rows ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    have hOutsideL : addr < G.kernelVec ∨ G.kernelVec + G.hints ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    rw [hMemP, hFrameL addr hOutsideL, hFrameR addr hOutsideR]

end LinearSetReconciliation327.Main

namespace LinearSetReconciliation327.Main

def hintGaussSolveStatusCode : List Instr := [.imm 3 1, .lt 1 1 3]

theorem hintGaussSolveStatus_spec (E : RAMEnv) (state : RAMState) (hWord : 1 < 2 ^ E.W) :
    let out := runBlock hintGaussSolveStatusCode E state
    out.regs 1 = (if state.regs 1 = 0 then 1 else 0) ∧ out.mem = state.mem ∧
      out.regs 14 = state.regs 14 ∧ out.pc = state.pc + 2 := by
  dsimp only
  by_cases hz : state.regs 1 = 0 <;>
    simp [hintGaussSolveStatusCode, runBlock, execInstr, Nat.mod_eq_of_lt hWord, Nat.lt_one_iff, hz, Nat.add_assoc]

def hintGaussCandidateStmt : Stmt := .seq hintGaussRhsCopyStmt
  (.seq hintGaussSolveVecStmt (.code hintGaussSolveStatusCode))
theorem hintGaussCandidateStmt_len : hintGaussCandidateStmt.len = 123 := rfl

/-- After successful factorization, copy the actual preserved right-hand side
    and return status1 exactly when its affine fiber has a unique member. -/
theorem hintGaussCandidateStmt_sem (G : HintGaussArea)
    (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows) (B : HintElimState G.rows G.hints) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base phase : ℕ)
    (hGeometry : HintGaussGeometry E G) (hInv : HintElimInvariant A Finset.univ B)
    (hStored : HintElimStored B G.residual G.lift state.mem)
    (hSource : G.hintList + G.hints + G.rows ≤ G.context)
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + s.val) = (v s).val)
    (hHeader : HintGaussHeader G phase state.mem) (hFits : HintGaussHeaderFits E G phase)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussCandidateStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 123) state (fun k out =>
      k ≤ (11 * G.rows + 11) * (G.rows + G.hints) + 20 * G.rows + 71 ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧ (out.regs 1 = 1 ↔ ∃! x, A x = v) ∧
      (out.regs 1 = 1 → ∃ z : HintVec G.hints, A z = v ∧ (∀ x, A x = v → x = z) ∧
        ∀ t : Fin G.hints, out.mem (G.kernelVec + t.val) = (z t).val) ∧
      HintGaussHeader G phase out.mem ∧
      CRMemFrame G.column (G.kernelVec + G.hints) state.mem out.mem ∧ out.regs 14 = G.context) := by
  have hWord := hGeometry.word_bound
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  obtain ⟨hCopyAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hSolveAt, hFlipAt⟩ := At.seqStmt hRestAt
  change At P base (hintGaussRhsCopyStmt.compile base) at hCopyAt
  change At P (base + 25) (hintGaussSolveVecStmt.compile (base + 25)) at hSolveAt
  change At P (base + 121) hintGaussSolveStatusCode at hFlipAt
  obtain ⟨_, kC, sC, hRunC, hPcC, hCostC, hColumnC, hFrameC, hHeaderC, hCtxC⟩ :=
    hintGaussRhsCopyStmt_sem G v P E state base phase hGeometry hSource hVector hHeader hFits hContext hCopyAt hPc
  have hStoredC := hStored.of_frame hFrameC (Or.inl (by omega)) (Or.inl h2)
  obtain ⟨_, kS, sS, hRunS, hPcS, hCostS, _, hHeaderS, hQCells, _, hUniqueS, hWitnessS, hFrameS, hCtxS⟩ :=
    hintGaussSolveVecStmt_sem G A B v P E sC (base + 25) phase hGeometry hInv hStoredC hColumnC
      hHeaderC hFits hCtxC hSolveAt hPcC
  have hFlip := hintGaussSolveStatus_spec E sS hWord
  generalize hSF : runBlock hintGaussSolveStatusCode E sS = out at hFlip
  obtain ⟨hStatus, hMemF, hCtxF, hPcF⟩ := hFlip
  have hRunF : (step P E)^[2] sS = out := by
    have hh := iterate_runBlock_of_at P E hintGaussSolveStatusCode sS (by rwa [hPcS])
      (by simp [hintGaussSolveStatusCode, NoBranch, Instr.NoBranchI])
    rw [hSF] at hh
    exact hh
  have hFlagIff : out.regs 1 = 1 ↔ sS.regs 1 = 0 := by
    rw [hStatus]
    by_cases hz : sS.regs 1 = 0 <;> simp [hz]
  refine ⟨hPc, 2 + (kS + kC), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunC hRunS) hRunF,
    ?_, by omega, ?_, hFlagIff.trans hUniqueS, ?_, ?_, ?_, hCtxF.trans hCtxS⟩
  · rw [hPcF, hPcS]
  · rw [hStatus]
    split_ifs <;> simp
  · intro hSuccess
    obtain ⟨hSolution, hUnique⟩ := hWitnessS (hFlagIff.mp hSuccess)
    refine ⟨B.lift v, hSolution, hUnique, ?_⟩
    intro t
    rw [hMemF]
    exact hQCells t
  · rw [hMemF]
    exact hHeaderS
  · intro addr hOutside
    have hOutsideS : addr < G.residualVec ∨ G.kernelVec + G.hints ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    have hOutsideC : addr < G.column ∨ G.column + G.rows ≤ addr := by
      rcases hOutside with hBefore | hAfter <;> omega
    rw [hMemF, hFrameS addr hOutsideS, hFrameC addr hOutsideC]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussCandidateStmt_sem
end S_HintGaussCandidate20261120
section S_HintGaussSolver20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintGaussAffineResult (G : HintGaussArea) (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows)
    (v : HintVec G.rows) (out : RAMState) : Prop :=
  (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧ (out.regs 1 = 1 ↔ ∃! x, A x = v) ∧
    (out.regs 1 = 1 → ∃ z : HintVec G.hints, A z = v ∧ (∀ x, A x = v → x = z) ∧
      ∀ t : Fin G.hints, out.mem (G.kernelVec + t.val) = (z t).val)

def hintGaussSolverStmt : Stmt := .seq hintGaussFactorStmt
  (.seq (.code (hintLoadField 1 14)) (.ite (.neqz 1) hintGaussCandidateStmt (.code [.imm 1 0])))
theorem hintGaussSolverStmt_len : hintGaussSolverStmt.len = 458 := rfl

/-- The fixed native affine solver. Its only successful output is exactly the
    unique member of the original public row-matrix fiber. -/
theorem hintGaussSolverStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hSource : G.hintList + G.hints + G.rows ≤ G.context)
    (hHint : ∀ j : Fin G.hints, state.mem (G.hintList + j.val) = (coords j).val)
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + s.val) = (v s).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ j : Fin G.hints, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (coords j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (coords j)).val)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussSolverStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 458) state (fun k out =>
      k ≤ 7 * (G.rows * G.rows + G.rows + G.hints * G.rows) +
        (2 * ((11 * G.rows + 11) * (G.rows + G.hints)) + 29 * G.rows + 173) * G.hints +
        (11 * G.rows + 11) * (G.rows + G.hints) + 20 * G.rows + 120 ∧
      HintGaussAffineResult G (hintGaussMap G coords beta hPrefix) v out ∧
      HintGaussHeader G G.hints out.mem ∧
      CRMemFrame G.context (G.pivotRow + G.rows) state.mem out.mem ∧ out.regs 14 = G.context) := by
  let A := hintGaussMap G coords beta hPrefix
  have hWord := hGeometry.word_bound
  have hFitsEnd : HintGaussHeaderFits E G G.hints := hFits.change_index hGeometry.hints_bound
  have hR := hGeometry.residual_before
  have hL := hGeometry.lift_before
  have hCol := hGeometry.column_before
  have hVec := hGeometry.residualVec_before
  have hQ := hGeometry.kernelVec_before
  obtain ⟨hFactorAt, hRestAt⟩ := At.seqStmt hAt
  obtain ⟨hFlagAt, hBranchAt⟩ := At.seqStmt hRestAt
  change At P base (hintGaussFactorStmt.compile base) at hFactorAt
  change At P (base + 328) (hintLoadField 1 14) at hFlagAt
  change At P (base + 331)
    ((Stmt.ite (.neqz 1) hintGaussCandidateStmt (.code [.imm 1 0])).compile (base + 331)) at hBranchAt
  obtain ⟨_, kF, sF, hRunF, hPcF, hCostF, hInvF, hFrameF⟩ :=
    hintGaussFactorStmt_sem G coords beta hPrefix P E state base hGeometry hReserve (by omega)
      hHint hSteps hCoeffSpan hCoeff hHeader hFits hContext hFactorAt hPc
  have hComplete := hintGaussScanCore_complete G A sF.mem hInvF.core
  have hFlagBound : sF.mem (G.context + 14) < 2 ^ E.W := by
    rcases hComplete with ⟨hActive, _⟩ | ⟨hFailed, _⟩ <;> omega
  have hVectorF : ∀ s : Fin G.rows, sF.mem (G.hintList + G.hints + s.val) = (v s).val := by
    intro s
    rw [hFrameF _ (Or.inl (by have := s.isLt; omega))]
    exact hVector s
  have hFlag := hintLoadField_spec E sF 1 14 G.context hInvF.context_value hFitsEnd.span
  generalize hSL : runBlock (hintLoadField 1 14) E sF = sL at hFlag
  obtain ⟨hPcL, hMemL, hStatusL, hRegsL⟩ := hFlag
  rw [Nat.mod_eq_of_lt hFlagBound] at hStatusL
  have hCtxL : sL.regs 14 = G.context := (hRegsL 14 (by decide) (by decide)).trans hInvF.context_value
  have hHeaderL : HintGaussHeader G G.hints sL.mem := by rw [hMemL]; exact hInvF.header
  have hVectorL : ∀ s : Fin G.rows, sL.mem (G.hintList + G.hints + s.val) = (v s).val := by
    rw [hMemL]
    exact hVectorF
  have hRunL : (step P E)^[3] sF = sL := by
    have hh := iterate_runBlock_of_at P E (hintLoadField 1 14) sF (by rwa [hPcF])
      (by simp [hintLoadField, NoBranch, Instr.NoBranchI])
    rw [hSL] at hh
    exact hh
  have hStartL : sL.pc = base + 331 := by rw [hPcL, hPcF]
  let Q : ℕ → RAMState → Prop := fun k out =>
    k ≤ (11 * G.rows + 11) * (G.rows + G.hints) + 20 * G.rows + 73 ∧
      HintGaussAffineResult G A v out ∧ HintGaussHeader G G.hints out.mem ∧
      CRMemFrame G.context (G.pivotRow + G.rows) sF.mem out.mem ∧ out.regs 14 = G.context
  have hBranch : Sem P E (base + 331) (base + 458) sL Q := by
    apply Sem.ite P E (base + 331) (.neqz 1) hintGaussCandidateStmt (.code [.imm 1 0])
      sL Q hBranchAt hWord hStartL
    · intro hGo
      change Sem P E (base + 332) (base + 455) {sL with pc := base + 332}
        (fun k out => Q (1 + k + 1) {out with pc := base + 458})
      have hData : ∃ B : HintElimState G.rows G.hints,
          HintElimStored B G.residual G.lift sL.mem ∧ HintElimInvariant A Finset.univ B := by
        rcases hComplete with ⟨_, B, hStoredB, hInvB, _⟩ | ⟨hFailed, _⟩
        · refine ⟨B, ?_, hInvB⟩
          rw [hMemL]
          exact hStoredB
        · exact False.elim (hGo (hStatusL.trans hFailed))
      obtain ⟨B, hStoredB, hInvB⟩ := hData
      have hTrueAt := (at_ite hBranchAt).2.2.1
      change At P (base + 332) (hintGaussCandidateStmt.compile (base + 332)) at hTrueAt
      have hNative := hintGaussCandidateStmt_sem G A B v P E {sL with pc := base + 332} (base + 332) G.hints
        hGeometry hInvB hStoredB hSource hVectorL hHeaderL hFitsEnd hCtxL hTrueAt rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hBit, hUnique, hWitness, hHeaderOut, hFrameOut, hCtxOut⟩ := hOut
      dsimp only [Q]
      refine ⟨by omega, ⟨hBit, hUnique, hWitness⟩, hHeaderOut, ?_, hCtxOut⟩
      intro addr hOutside
      have hOutsideC : addr < G.column ∨ G.kernelVec + G.hints ≤ addr := by
        rcases hOutside with hBefore | hAfter <;> omega
      rw [hFrameOut addr hOutsideC]
      exact congrFun hMemL addr
    · intro hStop
      change Sem P E (base + 456) (base + 457) {sL with pc := base + 456}
        (fun k out => Q (1 + k + 1) {out with pc := base + 458})
      have hZeroReg : sL.regs 1 = 0 := by
        change ¬ sL.regs 1 ≠ 0 at hStop
        exact not_not.mp hStop
      have hFailed : sF.mem (G.context + 14) = 0 := hStatusL.symm.trans hZeroReg
      have hKernel : ∃ q : HintVec G.hints, A q = 0 ∧ q ≠ 0 := by
        rcases hComplete with ⟨hActive, _⟩ | ⟨_, q, hAq, hNonzero, _⟩
        · omega
        · exact ⟨q, hAq, hNonzero⟩
      obtain ⟨q, hAq, hNonzero⟩ := hKernel
      have hNoUnique := hintKernel_no_unique A q hNonzero hAq v
      have hFalseAt := (at_ite hBranchAt).2.2.2.2.1
      change At P (base + 456) [.imm 1 0] at hFalseAt
      have hNative := hintSetStatus_sem P E {sL with pc := base + 456} (base + 456) 0 (by omega) hFalseAt rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hStatus, hMem, hCtx⟩ := hOut
      dsimp only [Q]
      refine ⟨by omega, ⟨Or.inl hStatus, ?_, ?_⟩, ?_, ?_, hCtx.trans hCtxL⟩
      · simp [hStatus, hNoUnique]
      · intro hSuccess
        exact False.elim (Nat.zero_ne_one (hStatus.symm.trans hSuccess))
      · rw [hMem]
        exact hHeaderL
      · intro addr _
        exact (congrFun hMem addr).trans (congrFun hMemL addr)
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hResultB, hHeaderB, hFrameB, hCtxB⟩ := hBranch
  refine ⟨hPc, kB + (3 + kF), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunF hRunL) hRunB,
    hPcB, by omega, hResultB, hHeaderB, ?_, hCtxB⟩
  intro addr hOutside
  exact (hFrameB addr hOutside).trans (hFrameF addr hOutside)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussSolverStmt_sem
end S_HintGaussSolver20261120
section S_HintGaussBounds20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintGaussTime (a h : ℕ) : ℕ :=
  7 * (a * a + a + h * a) + (2 * ((11 * a + 11) * (a + h)) + 29 * a + 173) * h +
    (11 * a + 11) * (a + h) + 20 * a + 120

theorem hintGaussTime_expand (a h : ℕ) :
    hintGaussTime a h = 22 * a * a * h + 22 * a * h * h + 18 * a * a + 22 * h * h +
      69 * a * h + 38 * a + 184 * h + 120 := by
  unfold hintGaussTime
  ring

theorem hintGaussTime_le (a h : ℕ) : hintGaussTime a h ≤ 512 * (a + h + 1) ^ 3 := by
  rw [hintGaussTime_expand]
  nlinarith only [Nat.zero_le (a * a * a), Nat.zero_le (h * h * h), Nat.zero_le (a * a * h),
    Nat.zero_le (a * h * h), Nat.zero_le (a * a), Nat.zero_le (h * h), Nat.zero_le (a * h), Nat.zero_le a, Nat.zero_le h]

/-- A concrete consecutive allocator for the private matrices and buffers. -/
def hintGaussDenseArea (context a h hintList node row buckets steps : ℕ) : HintGaussArea where
  context := context
  rows := a
  hints := h
  residual := context + 16
  lift := context + 16 + a * a
  column := context + 16 + a * a + h * a
  residualVec := context + 16 + a * a + h * a + a
  kernelVec := context + 16 + a * a + h * a + a + a
  pivotRow := context + 16 + a * a + h * a + a + a + h
  hintList := hintList
  node := node
  row := row
  buckets := buckets
  steps := steps

theorem hintGaussDenseArea_geometry (E : RAMEnv) (context a h hintList node row buckets steps : ℕ)
    (hSpan : context + 16 + a * a + h * a + 3 * a + h < 2 ^ E.W) :
    HintGaussGeometry E (hintGaussDenseArea context a h hintList node row buckets steps) := by
  constructor <;> dsimp only [hintGaussDenseArea] <;> omega

theorem hintGaussDenseArea_reserve (context a h hintList node row buckets steps : ℕ) :
    (hintGaussDenseArea context a h hintList node row buckets steps).context + 16 ≤
      (hintGaussDenseArea context a h hintList node row buckets steps).residual := le_rfl

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussTime_le
#print axioms LinearSetReconciliation327.Main.hintGaussDenseArea_geometry
end S_HintGaussBounds20261120
section S_HintFamilyLinear20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintBitsSet {h : ℕ} (iota : Fin h → ℕ) (z : HintVec h) : Finset ℕ :=
  (Finset.univ.filter (fun j => z j = 1)).image iota

def hintSetBits {h : ℕ} (iota : Fin h → ℕ) (C : Finset ℕ) : HintVec h :=
  fun j => if iota j ∈ C then 1 else 0

theorem hintBitsSet_mem {h : ℕ} (iota : Fin h → ℕ) (hInj : Function.Injective iota)
    (z : HintVec h) (j : Fin h) : iota j ∈ hintBitsSet iota z ↔ z j = 1 := by
  constructor
  · intro hMem
    obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp hMem
    have htj : t = j := hInj hEq
    subst t
    exact (Finset.mem_filter.mp ht).2
  · intro hz
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩

theorem hintSetBits_mem {h : ℕ} (iota : Fin h → ℕ) (C : Finset ℕ) (j : Fin h) :
    hintSetBits iota C j = 1 ↔ iota j ∈ C := by
  by_cases hMem : iota j ∈ C <;> simp [hintSetBits, hMem]

theorem hintBitsSet_subset {h : ℕ} (iota : Fin h → ℕ) (z : HintVec h) :
    hintBitsSet iota z ⊆ Finset.univ.image iota := by
  intro v hv
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

theorem hintSetBits_bitsSet {h : ℕ} (iota : Fin h → ℕ) (hInj : Function.Injective iota) (z : HintVec h) :
    hintSetBits iota (hintBitsSet iota z) = z := by
  funext j
  have hTwo : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  by_cases hz : z j = 1
  · simp [hintSetBits, (hintBitsSet_mem iota hInj z j).mpr hz, hz]
  · have hZero : z j = 0 := (hTwo (z j)).resolve_right hz
    have hNot : iota j ∉ hintBitsSet iota z := fun hm => hz ((hintBitsSet_mem iota hInj z j).mp hm)
    simp [hintSetBits, hNot, hZero]

theorem hintBitsSet_setBits {h : ℕ} (iota : Fin h → ℕ) (C : Finset ℕ)
    (hSub : C ⊆ Finset.univ.image iota) : hintBitsSet iota (hintSetBits iota C) = C := by
  ext v
  constructor
  · intro hMem
    obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hMem
    have hjBit := (Finset.mem_filter.mp hj).2
    have hIn := (hintSetBits_mem iota C j).mp hjBit
    rwa [hEq] at hIn
  · intro hMem
    obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp (hSub hMem)
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hEq⟩
    apply (hintSetBits_mem iota C j).mpr
    rwa [hEq]

def hintSubsetCodec {h : ℕ} (iota : Fin h → ℕ) (hInj : Function.Injective iota) :
    HintVec h ≃ {C : Finset ℕ // C ⊆ Finset.univ.image iota} where
  toFun z := ⟨hintBitsSet iota z, hintBitsSet_subset iota z⟩
  invFun C := hintSetBits iota C.val
  left_inv z := hintSetBits_bitsSet iota hInj z
  right_inv C := Subtype.ext (hintBitsSet_setBits iota C.val C.property)

theorem hintBitsSet_injective {h : ℕ} (iota : Fin h → ℕ) (hInj : Function.Injective iota) :
    Function.Injective (hintBitsSet iota) := by
  intro z z' hEq
  have hh := congrArg (hintSetBits iota) hEq
  simpa only [hintSetBits_bitsSet iota hInj] using hh

/-- Exact agreement with the paper's protected rowBit definition. -/
theorem hintBitsSet_rowBit {h ell K : ℕ} (iota : Fin h → ℕ) (hInj : Function.Injective iota)
    (hRange : ∀ j, iota j < K) (beta : Fin ell → Fin K → ZMod 2) (z : HintVec h) (s : Fin ell) :
    rowBit beta (hintBitsSet iota z) s = ∑ j : Fin h, z j * beta s ⟨iota j, hRange j⟩ := by
  classical
  rw [rowBit, hintBitsSet, Finset.sum_image]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    rw [dif_pos (hRange j)]
    by_cases hz : z j = 1
    · simp [hz]
    · have hTwo : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
      have hZero := (hTwo (z j)).resolve_right hz
      simp [hz, hZero]
  · intro j _ k _ hEq
    exact hInj hEq

theorem hintBitsSet_gaussMap (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (z : HintVec G.hints) (s : Fin G.rows) :
    rowBit beta (hintBitsSet (fun j => (coords j).val) z) ⟨s.val, s.isLt.trans_le hPrefix⟩ =
      hintGaussMap G coords beta hPrefix z s := by
  have hNatInj : Function.Injective (fun j => (coords j).val) := by
    intro j k hEq
    exact hInj (Fin.ext hEq)
  rw [hintBitsSet_rowBit _ hNatInj (fun j => (coords j).isLt)]
  change _ = (∑ j : Fin G.hints, z j • (fun t : Fin G.rows => beta ⟨t.val, t.isLt.trans_le hPrefix⟩ (coords j))) s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open HintParams

theorem hintBitsSet_inter {h : ℕ} (iota : Fin h → ℕ) (C : Finset ℕ) :
    hintBitsSet iota (hintSetBits iota C) = C ∩ Finset.univ.image iota := by
  ext v
  constructor
  · intro hMem
    obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hMem
    have hIn := (hintSetBits_mem iota C j).mp (Finset.mem_filter.mp hj).2
    exact Finset.mem_inter.mpr ⟨by rwa [hEq] at hIn, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hEq⟩⟩
  · intro hMem
    obtain ⟨hC, hJ⟩ := Finset.mem_inter.mp hMem
    obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp hJ
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hintSetBits_mem iota C j).mpr (by rwa [hEq])⟩, hEq⟩

theorem hintBitsUnion_sdiff {h : ℕ} (iota : Fin h → ℕ) (A : Finset ℕ)
    (hSeparate : Disjoint A (Finset.univ.image iota)) (z : HintVec h) :
    (hintBitsSet iota z ∪ A) \ Finset.univ.image iota = A := by
  ext v
  by_cases hJ : v ∈ Finset.univ.image iota
  · have hA : v ∉ A := fun hv => Finset.disjoint_left.mp hSeparate hv hJ
    simp [hJ, hA]
  · have hZ : v ∉ hintBitsSet iota z := fun hv => hJ (hintBitsSet_subset iota z hv)
    simp [hJ, hZ]

theorem hintBitsUnion_encode {h : ℕ} (iota : Fin h → ℕ) (hInj : Function.Injective iota)
    (A : Finset ℕ) (hSeparate : Disjoint A (Finset.univ.image iota)) (z : HintVec h) :
    hintSetBits iota (hintBitsSet iota z ∪ A) = z := by
  have hEq : hintSetBits iota (hintBitsSet iota z ∪ A) = hintSetBits iota (hintBitsSet iota z) := by
    funext j
    have hNot : iota j ∉ A := fun hA => Finset.disjoint_left.mp hSeparate hA
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    simp only [hintSetBits, Finset.mem_union, hNot, or_false]
  exact hEq.trans (hintSetBits_bitsSet iota hInj z)

theorem hintBitsUnion_decode {h : ℕ} (iota : Fin h → ℕ) (A C : Finset ℕ)
    (hOutside : C \ Finset.univ.image iota = A) :
    hintBitsSet iota (hintSetBits iota C) ∪ A = C := by
  rw [hintBitsSet_inter, ← hOutside]
  ext v
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

def hintOutsideCodec {h : ℕ} (iota : Fin h → ℕ) (hInj : Function.Injective iota)
    (A : Finset ℕ) (hSeparate : Disjoint A (Finset.univ.image iota)) :
    HintVec h ≃ {C : Finset ℕ // C \ Finset.univ.image iota = A} where
  toFun z := ⟨hintBitsSet iota z ∪ A, hintBitsUnion_sdiff iota A hSeparate z⟩
  invFun C := hintSetBits iota C.val
  left_inv z := hintBitsUnion_encode iota hInj A hSeparate z
  right_inv C := Subtype.ext (hintBitsUnion_decode iota A C.val C.property)

theorem hintBitsUnion_rowBit {h ell K : ℕ} (iota : Fin h → ℕ) (A : Finset ℕ)
    (hSeparate : Disjoint A (Finset.univ.image iota))
    (beta : Fin ell → Fin K → ZMod 2) (z : HintVec h) (s : Fin ell) :
    rowBit beta (hintBitsSet iota z ∪ A) s = rowBit beta (hintBitsSet iota z) s + rowBit beta A s := by
  have hDisjoint : Disjoint (hintBitsSet iota z) A := by
    apply Finset.disjoint_left.mpr
    intro v hvZ hvA
    exact Finset.disjoint_left.mp hSeparate hvA (hintBitsSet_subset iota z hvZ)
  exact Finset.sum_union hDisjoint

theorem hintPrefix_eq_ofFn {ell a : ℕ} (hPrefix : a ≤ ell) (f : Fin ell → ZMod 2) (v : HintVec a) :
    ((List.finRange ell).take a).map f = List.ofFn v ↔
      ∀ s : Fin a, f ⟨s.val, s.isLt.trans_le hPrefix⟩ = v s := by
  have hLen : (((List.finRange ell).take a).map f).length = a := by simp [Nat.min_eq_left hPrefix]
  constructor
  · intro hEq s
    have hL : s.val < (((List.finRange ell).take a).map f).length := by rw [hLen]; exact s.isLt
    have hR : s.val < (List.ofFn v).length := by simpa using s.isLt
    have hh := (List.ext_getElem_iff.mp hEq).2 s.val hL hR
    simpa [List.getElem_map, List.getElem_take, List.getElem_finRange, List.getElem_ofFn] using hh
  · intro hh
    apply List.ext_getElem (by simp [Nat.min_eq_left hPrefix])
    intro i hL hR
    have hi : i < a := by simpa using hR
    simpa [List.getElem_map, List.getElem_take, List.getElem_finRange, List.getElem_ofFn] using hh ⟨i, hi⟩

theorem hintFamily_mem {ell K a : ℕ} (hPrefix : a ≤ ell) (Nj : ℕ)
    (beta : Fin ell → Fin K → ZMod 2) (J C : Finset ℕ) (r : ℕ) (v : HintVec a) :
    C ∈ family Nj beta J r (List.ofFn v) ↔ C ⊆ Finset.range Nj ∧ (C \ J).card = r ∧
      ∀ s : Fin a, rowBit beta C ⟨s.val, s.isLt.trans_le hPrefix⟩ = v s := by
  simp only [family, Finset.mem_filter, Finset.mem_powerset, List.length_ofFn,
    hintPrefix_eq_ofFn hPrefix]

theorem hintFamily_fixedOutside {ell K a : ℕ} (hPrefix : a ≤ ell) (Nj : ℕ)
    (beta : Fin ell → Fin K → ZMod 2) (J A C : Finset ℕ) (r : ℕ) (v : HintVec a)
    (hJ : J ⊆ Finset.range Nj) (hA : A ⊆ Finset.range Nj) (hCard : A.card = r) :
    (C ∈ family Nj beta J r (List.ofFn v) ∧ C \ J = A) ↔
      C \ J = A ∧ ∀ s : Fin a, rowBit beta C ⟨s.val, s.isLt.trans_le hPrefix⟩ = v s := by
  constructor
  · rintro ⟨hMem, hDiff⟩
    exact ⟨hDiff, ((hintFamily_mem hPrefix Nj beta J C r v).mp hMem).2.2⟩
  · rintro ⟨hDiff, hRows⟩
    refine ⟨(hintFamily_mem hPrefix Nj beta J C r v).mpr ⟨?_, ?_, hRows⟩, hDiff⟩
    · intro w hw
      by_cases hwJ : w ∈ J
      · exact hJ hwJ
      · have hwA : w ∈ A := by rw [← hDiff]; exact Finset.mem_sdiff.mpr ⟨hw, hwJ⟩
        exact hA hwA
    · rw [hDiff, hCard]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main
open HintParams

noncomputable def hintOutsideRhs (G : HintGaussArea) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (A : Finset ℕ) (v : HintVec G.rows) : HintVec G.rows :=
  fun s => v s + rowBit beta A ⟨s.val, s.isLt.trans_le hPrefix⟩

theorem hintF2_move_right (a b c : ZMod 2) : a + b = c ↔ a = c + b := by
  constructor
  · intro h
    calc
      a = a + (b + b) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = (a + b) + b := by abel
      _ = c + b := by rw [h]
  · intro h
    rw [h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem hintBitsUnion_affine (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (A : Finset ℕ) (v : HintVec G.rows) (z : HintVec G.hints)
    (hSeparate : Disjoint A (Finset.univ.image (fun j => (coords j).val))) :
    (∀ s : Fin G.rows, rowBit beta (hintBitsSet (fun j => (coords j).val) z ∪ A)
      ⟨s.val, s.isLt.trans_le hPrefix⟩ = v s) ↔
    hintGaussMap G coords beta hPrefix z = hintOutsideRhs G beta hPrefix A v := by
  constructor
  · intro hRows
    funext s
    have hs := hRows s
    rw [hintBitsUnion_rowBit _ A hSeparate, hintBitsSet_gaussMap G coords hInj beta hPrefix] at hs
    exact (hintF2_move_right _ _ _).mp hs
  · intro hEq s
    rw [hintBitsUnion_rowBit _ A hSeparate, hintBitsSet_gaussMap G coords hInj beta hPrefix]
    exact (hintF2_move_right _ _ _).mpr (congrFun hEq s)

theorem hintUnique_congr {α : Type*} (P Q : α → Prop) (h : ∀ x, P x ↔ Q x) :
    (∃! x, P x) ↔ ∃! x, Q x := by
  constructor
  · rintro ⟨x, hx, hUnique⟩
    exact ⟨x, (h x).mp hx, fun y hy => hUnique y ((h y).mpr hy)⟩
  · rintro ⟨x, hx, hUnique⟩
    exact ⟨x, (h x).mpr hx, fun y hy => hUnique y ((h y).mp hy)⟩

theorem hintEquiv_unique {α β : Type*} (e : α ≃ β) (P : β → Prop) :
    (∃! x : α, P (e x)) ↔ ∃! y : β, P y := by
  constructor
  · rintro ⟨x, hx, hUnique⟩
    refine ⟨e x, hx, ?_⟩
    intro y hy
    have hxy : e.symm y = x := hUnique (e.symm y) (by simpa using hy)
    calc
      y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = e x := congrArg e hxy
  · rintro ⟨y, hy, hUnique⟩
    refine ⟨e.symm y, by simpa using hy, ?_⟩
    intro x hx
    apply e.injective
    simpa using hUnique (e x) hx

theorem hintSubtype_unique {α : Type*} (P Q : α → Prop) :
    (∃! x : {x // P x}, Q x.val) ↔ ∃! x : α, P x ∧ Q x := by
  constructor
  · rintro ⟨x, hx, hUnique⟩
    refine ⟨x.val, ⟨x.property, hx⟩, ?_⟩
    intro y hy
    exact congrArg Subtype.val (hUnique ⟨y, hy.1⟩ hy.2)
  · rintro ⟨x, ⟨hP, hQ⟩, hUnique⟩
    refine ⟨⟨x, hP⟩, hQ, ?_⟩
    intro y hy
    exact Subtype.ext (hUnique y.val ⟨y.property, hy⟩)

theorem hintOutside_affine_unique (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (A : Finset ℕ) (v : HintVec G.rows)
    (hSeparate : Disjoint A (Finset.univ.image (fun j => (coords j).val))) :
    (∃! z, hintGaussMap G coords beta hPrefix z = hintOutsideRhs G beta hPrefix A v) ↔
      ∃! C : Finset ℕ, C \ Finset.univ.image (fun j => (coords j).val) = A ∧
        ∀ s : Fin G.rows, rowBit beta C ⟨s.val, s.isLt.trans_le hPrefix⟩ = v s := by
  let iota := fun j => (coords j).val
  have hNatInj : Function.Injective iota := by
    intro j k hEq
    exact hInj (Fin.ext hEq)
  let e := hintOutsideCodec iota hNatInj A hSeparate
  let Q : Finset ℕ → Prop := fun C => ∀ s : Fin G.rows, rowBit beta C ⟨s.val, s.isLt.trans_le hPrefix⟩ = v s
  calc
    (∃! z, hintGaussMap G coords beta hPrefix z = hintOutsideRhs G beta hPrefix A v) ↔
        ∃! z, Q (e z).val := hintUnique_congr _ _ (fun z => (hintBitsUnion_affine G coords hInj beta hPrefix A v z hSeparate).symm)
    _ ↔ ∃! C : {C : Finset ℕ // C \ Finset.univ.image iota = A}, Q C.val :=
      hintEquiv_unique e (fun C => Q C.val)
    _ ↔ _ := hintSubtype_unique _ Q

/-- Exactly the protected paper family, restricted to one outside subset.
    No change is made to family, its transcript format, or its coin matrix. -/
theorem hintFamily_affine_unique (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj r : ℕ) (A : Finset ℕ) (v : HintVec G.rows)
    (hHintValid : ∀ j, (coords j).val < Nj) (hOutsideValid : A ⊆ Finset.range Nj) (hCard : A.card = r)
    (hSeparate : Disjoint A (Finset.univ.image (fun j => (coords j).val))) :
    (∃! z, hintGaussMap G coords beta hPrefix z = hintOutsideRhs G beta hPrefix A v) ↔
      ∃! C : Finset ℕ,
        C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v) ∧
          C \ Finset.univ.image (fun j => (coords j).val) = A := by
  have hJ : Finset.univ.image (fun j => (coords j).val) ⊆ Finset.range Nj := by
    intro w hw
    obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp hw
    rw [← hEq]
    exact Finset.mem_range.mpr (hHintValid j)
  apply (hintOutside_affine_unique G coords hInj beta hPrefix A v hSeparate).trans
  exact hintUnique_congr _ _ (fun C =>
    (hintFamily_fixedOutside hPrefix Nj beta _ A C r v hJ hOutsideValid hCard).symm)

theorem hintFamily_affine_solution (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj r : ℕ) (A : Finset ℕ) (v : HintVec G.rows) (z : HintVec G.hints)
    (hHintValid : ∀ j, (coords j).val < Nj) (hOutsideValid : A ⊆ Finset.range Nj) (hCard : A.card = r)
    (hSeparate : Disjoint A (Finset.univ.image (fun j => (coords j).val))) :
    hintGaussMap G coords beta hPrefix z = hintOutsideRhs G beta hPrefix A v ↔
      (hintBitsSet (fun j => (coords j).val) z ∪ A) ∈
          family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v) ∧
        (hintBitsSet (fun j => (coords j).val) z ∪ A) \ Finset.univ.image (fun j => (coords j).val) = A := by
  have hJ : Finset.univ.image (fun j => (coords j).val) ⊆ Finset.range Nj := by
    intro w hw
    obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp hw
    rw [← hEq]
    exact Finset.mem_range.mpr (hHintValid j)
  rw [hintFamily_fixedOutside hPrefix Nj beta _ A _ r v hJ hOutsideValid hCard]
  have hDiff := hintBitsUnion_sdiff (fun j => (coords j).val) A hSeparate z
  simp only [hDiff, true_and]
  exact (hintBitsUnion_affine G coords hInj beta hPrefix A v z hSeparate).symm

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFamily_affine_unique
#print axioms LinearSetReconciliation327.Main.hintFamily_affine_solution
end S_HintFamilyLinear20261120
section S_HintFamilyCall20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintFamilyClass (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj r : ℕ) (outside : Finset ℕ)
    (v : HintVec G.rows) (C : Finset ℕ) : Prop :=
  C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v) ∧
    C \ Finset.univ.image (fun j => (coords j).val) = outside

/-- A real native call for one outside subset. Its successful physical output
    encodes exactly the unique candidate in the paper's original family class. -/
theorem hintFamilyCandidateCall_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r : ℕ) (outside : Finset ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hSource : G.hintList + G.hints + G.rows ≤ G.context)
    (hInj : Function.Injective coords) (hHintValid : ∀ j, (coords j).val < Nj)
    (hOutsideValid : outside ⊆ Finset.range Nj) (hCard : outside.card = r)
    (hSeparate : Disjoint outside (Finset.univ.image (fun j => (coords j).val)))
    (hHint : ∀ j : Fin G.hints, state.mem (G.hintList + j.val) = (coords j).val)
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + s.val) =
      (hintOutsideRhs G beta hPrefix outside v s).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ j : Fin G.hints, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (coords j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (coords j)).val)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussSolverStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 458) state (fun k out => k ≤ 512 * (G.rows + G.hints + 1) ^ 3 ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
      (out.regs 1 = 1 ↔ ∃! C : Finset ℕ, hintFamilyClass G coords beta Nj r outside v C) ∧
      (out.regs 1 = 1 → ∃ z : HintVec G.hints,
        (∀ t : Fin G.hints, out.mem (G.kernelVec + t.val) = (z t).val) ∧
        hintFamilyClass G coords beta Nj r outside v (hintBitsSet (fun j => (coords j).val) z ∪ outside) ∧
        ∀ C : Finset ℕ, hintFamilyClass G coords beta Nj r outside v C →
          C = hintBitsSet (fun j => (coords j).val) z ∪ outside) ∧
      HintGaussHeader G G.hints out.mem ∧
      CRMemFrame G.context (G.pivotRow + G.rows) state.mem out.mem ∧ out.regs 14 = G.context) := by
  have hNative := hintGaussSolverStmt_sem G coords beta hPrefix (hintOutsideRhs G beta hPrefix outside v)
    P E state base hGeometry hReserve hSource hHint hVector hSteps hCoeffSpan hCoeff hHeader hFits hContext hAt hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, hAffine, hHeaderOut, hFrame, hCtx⟩ := hOut
  obtain ⟨hBit, hUnique, hWitness⟩ := hAffine
  have hCost' : k ≤ hintGaussTime G.rows G.hints := hCost
  have hUniqueClass : out.regs 1 = 1 ↔ ∃! C : Finset ℕ, hintFamilyClass G coords beta Nj r outside v C :=
    hUnique.trans (hintFamily_affine_unique G coords hInj beta hPrefix Nj r outside v
      hHintValid hOutsideValid hCard hSeparate)
  refine ⟨hCost'.trans (hintGaussTime_le G.rows G.hints), hBit, hUniqueClass, ?_, hHeaderOut, hFrame, hCtx⟩
  intro hSuccess
  obtain ⟨z, hz, _, hCells⟩ := hWitness hSuccess
  have hCorrect : hintFamilyClass G coords beta Nj r outside v (hintBitsSet (fun j => (coords j).val) z ∪ outside) :=
    (hintFamily_affine_solution G coords hInj beta hPrefix Nj r outside v z hHintValid hOutsideValid hCard hSeparate).mp hz
  obtain ⟨C0, _, hUniqueC⟩ := hUniqueClass.mp hSuccess
  refine ⟨z, hCells, hCorrect, ?_⟩
  intro C hC
  exact (hUniqueC C hC).trans (hUniqueC _ hCorrect).symm

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFamilyCandidateCall_sem
end S_HintFamilyCall20261120


