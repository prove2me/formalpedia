-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_01
-- name    : LinearSetReconciliation327_Main_Bundle51_01
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T10:42:45.491774+00:00
-- url     : https://prove2.me/theorems/93dd123c-d4d7-435e-a81f-00fb39782b82
-- title:
--   LinearSetReconciliation327 — Bundle51_01
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_01` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintGaussInit20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintGaussSetup20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintGaussUpdate20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintRowCoeff20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintRowPivot20261120

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_01
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintGaussNative20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintGaussTransition20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintGaussColumn20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintGaussControl20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintGaussLoop20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintGaussFactor20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintGaussNative20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintGaussResidualStmt : Stmt := .seq (.code hintGaussResidualSetup) hintMatVecStmt
theorem hintGaussResidualStmt_len : hintGaussResidualStmt.len = 38 := rfl

theorem hintGaussResidualStmt_sem (G : HintGaussArea) (phase : ℕ)
    (F : HintVec G.rows →ₗ[ZMod 2] HintVec G.rows) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hWidth : G.rows < 2 ^ E.W) (hRows : G.rows < 2 ^ E.W)
    (hMatrixSpan : G.residual + G.rows * G.rows < 2 ^ E.W)
    (hVecSpan : G.column + G.rows < 2 ^ E.W) (hOutSpan : G.residualVec + G.rows < 2 ^ E.W)
    (hMatrix : ∀ r : Fin G.rows, ∀ t : Fin G.rows,
      state.mem (G.residual + r.val * G.rows + t.val) = (F (Pi.single t 1) r).val)
    (hVector : ∀ t : Fin G.rows, state.mem (G.column + t.val) = (v t).val)
    (hMatrixSeparate : G.residual + G.rows * G.rows ≤ G.residualVec ∨ G.residualVec + G.rows ≤ G.residual)
    (hVecSeparate : G.column + G.rows ≤ G.residualVec ∨ G.residualVec + G.rows ≤ G.column)
    (hHeader : HintGaussHeader G phase state.mem) (hFits : HintGaussHeaderFits E G phase)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussResidualStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 38) state (fun k out => k ≤ (11 * G.rows + 11) * G.rows + 20 ∧
      (∀ r : Fin G.rows, out.mem (G.residualVec + r.val) = (F v r).val) ∧
      (∀ addr, (addr < G.residualVec ∨ G.residualVec + G.rows ≤ addr) → out.mem addr = state.mem addr) ∧
      out.regs 14 = G.context) := by
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintGaussResidualSetup at hSetupAt
  change At P (base + 17) (hintMatVecStmt.compile (base + 17)) at hBodyAt
  have hNo : NoBranch hintGaussResidualSetup := by
    rw [hintGaussResidualSetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintGaussSetupTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintGaussResidualSetup_spec E G phase state hContext hHeader hFits hWord
  generalize hMid : runBlock hintGaussResidualSetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h14⟩ := hSetup
  have hRunSetup : (step P E)^[17] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGaussResidualSetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 17 := by
    have hh := runBlock_pc hintGaussResidualSetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hMatrix' : ∀ r : Fin G.rows, ∀ t : Fin G.rows,
      mid.mem (G.residual + r.val * G.rows + t.val) = (F (Pi.single t 1) r).val := by
    simpa only [hMem] using hMatrix
  have hVector' : ∀ t : Fin G.rows, mid.mem (G.column + t.val) = (v t).val := by
    simpa only [hMem] using hVector
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, hCells, hFrame, _, hOut14⟩ :=
    hintMatVecStmt_map_sem F v P E mid G.residual G.column G.residualVec (base + 17)
      hWord hWidth hRows hMatrixSpan hVecSpan hOutSpan hMatrix' hVector'
      hMatrixSeparate hVecSeparate hBodyAt hMidPc hArgs
  refine ⟨hPc, kBody + 17, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega, hCells, ?_, hOut14.trans h14⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)

def hintGaussLiftStmt : Stmt := .seq (.code hintGaussLiftSetup) hintMatVecStmt
theorem hintGaussLiftStmt_len : hintGaussLiftStmt.len = 38 := rfl

theorem hintGaussLiftStmt_sem (G : HintGaussArea) (phase : ℕ)
    (F : HintVec G.rows →ₗ[ZMod 2] HintVec G.hints) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hWidth : G.rows < 2 ^ E.W) (hRows : G.hints < 2 ^ E.W)
    (hMatrixSpan : G.lift + G.hints * G.rows < 2 ^ E.W)
    (hVecSpan : G.column + G.rows < 2 ^ E.W) (hOutSpan : G.kernelVec + G.hints < 2 ^ E.W)
    (hMatrix : ∀ r : Fin G.hints, ∀ t : Fin G.rows,
      state.mem (G.lift + r.val * G.rows + t.val) = (F (Pi.single t 1) r).val)
    (hVector : ∀ t : Fin G.rows, state.mem (G.column + t.val) = (v t).val)
    (hMatrixSeparate : G.lift + G.hints * G.rows ≤ G.kernelVec ∨ G.kernelVec + G.hints ≤ G.lift)
    (hVecSeparate : G.column + G.rows ≤ G.kernelVec ∨ G.kernelVec + G.hints ≤ G.column)
    (hHeader : HintGaussHeader G phase state.mem) (hFits : HintGaussHeaderFits E G phase)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussLiftStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 38) state (fun k out => k ≤ (11 * G.rows + 11) * G.hints + 20 ∧
      (∀ r : Fin G.hints, out.mem (G.kernelVec + r.val) = (F v r).val) ∧
      (∀ addr, (addr < G.kernelVec ∨ G.kernelVec + G.hints ≤ addr) → out.mem addr = state.mem addr) ∧
      out.regs 14 = G.context) := by
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintGaussLiftSetup at hSetupAt
  change At P (base + 17) (hintMatVecStmt.compile (base + 17)) at hBodyAt
  have hNo : NoBranch hintGaussLiftSetup := by
    rw [hintGaussLiftSetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintGaussSetupTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintGaussLiftSetup_spec E G phase state hContext hHeader hFits hWord
  generalize hMid : runBlock hintGaussLiftSetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h14⟩ := hSetup
  have hRunSetup : (step P E)^[17] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGaussLiftSetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 17 := by
    have hh := runBlock_pc hintGaussLiftSetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hMatrix' : ∀ r : Fin G.hints, ∀ t : Fin G.rows,
      mid.mem (G.lift + r.val * G.rows + t.val) = (F (Pi.single t 1) r).val := by
    simpa only [hMem] using hMatrix
  have hVector' : ∀ t : Fin G.rows, mid.mem (G.column + t.val) = (v t).val := by
    simpa only [hMem] using hVector
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, hCells, hFrame, _, hOut14⟩ :=
    hintMatVecStmt_map_sem F v P E mid G.lift G.column G.kernelVec (base + 17)
      hWord hWidth hRows hMatrixSpan hVecSpan hOutSpan hMatrix' hVector'
      hMatrixSeparate hVecSeparate hBodyAt hMidPc hArgs
  refine ⟨hPc, kBody + 17, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega, hCells, ?_, hOut14.trans h14⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)

def hintGaussRankResidualStmt : Stmt := .seq (.code hintGaussRankResidualSetup) hintRankOneStmt
theorem hintGaussRankResidualStmt_len : hintGaussRankResidualStmt.len = 37 := rfl

theorem hintGaussRankResidualStmt_sem (G : HintGaussArea) (phase : ℕ)
    (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows) (B : HintElimState G.rows G.hints)
    (j : Fin G.hints) (pivot : Fin G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hWidth : G.rows < 2 ^ E.W) (hRows : G.rows < 2 ^ E.W)
    (hMatrixSpan : G.residual + G.rows * G.rows < 2 ^ E.W)
    (hCacheSpan : G.pivotRow + G.rows < 2 ^ E.W) (hScaleSpan : G.residualVec + G.rows < 2 ^ E.W)
    (hMatrix : ∀ r : Fin G.rows, ∀ t : Fin G.rows,
      state.mem (G.residual + r.val * G.rows + t.val) = (B.residual (Pi.single t 1) r).val)
    (hCache : ∀ t : Fin G.rows, state.mem (G.pivotRow + t.val) = (B.residual (Pi.single t 1) pivot).val)
    (hScale : ∀ r : Fin G.rows, state.mem (G.residualVec + r.val) = (B.residual (A (Pi.single j 1)) r).val)
    (hSeparate : G.residual + G.rows * G.rows ≤ G.pivotRow ∨ G.pivotRow + G.rows ≤ G.residual)
    (hScaleSeparate : G.residual + G.rows * G.rows ≤ G.residualVec ∨ G.residualVec + G.rows ≤ G.residual)
    (hHeader : HintGaussHeader G phase state.mem) (hFits : HintGaussHeaderFits E G phase)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussRankResidualStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 37) state (fun k out => k ≤ (11 * G.rows + 11) * G.rows + 19 ∧
      (∀ r : Fin G.rows, ∀ t : Fin G.rows,
        out.mem (G.residual + r.val * G.rows + t.val) = ((hintElimInsert A B j pivot).residual (Pi.single t 1) r).val) ∧
      CRMemFrame G.residual (G.residual + G.rows * G.rows) state.mem out.mem ∧
      out.regs 14 = G.context) := by
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintGaussRankResidualSetup at hSetupAt
  change At P (base + 16) (hintRankOneStmt.compile (base + 16)) at hBodyAt
  have hNo : NoBranch hintGaussRankResidualSetup := by
    rw [hintGaussRankResidualSetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintGaussRankResidualSetup_spec E G phase state hContext hHeader hFits hWord
  generalize hMid : runBlock hintGaussRankResidualSetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h14⟩ := hSetup
  have hRunSetup : (step P E)^[16] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGaussRankResidualSetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 16 := by
    have hh := runBlock_pc hintGaussRankResidualSetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hMatrix' : ∀ r : Fin G.rows, ∀ t : Fin G.rows,
      mid.mem (G.residual + r.val * G.rows + t.val) = (B.residual (Pi.single t 1) r).val := by
    simpa only [hMem] using hMatrix
  have hCache' : ∀ t : Fin G.rows, mid.mem (G.pivotRow + t.val) = (B.residual (Pi.single t 1) pivot).val := by
    simpa only [hMem] using hCache
  have hScale' : ∀ r : Fin G.rows, mid.mem (G.residualVec + r.val) = (B.residual (A (Pi.single j 1)) r).val := by
    simpa only [hMem] using hScale
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, hCells, hFrame, _, hOut14⟩ :=
    hintRankOneStmt_residual_sem A B j pivot P E mid G.residual G.pivotRow G.residualVec (base + 16)
      hWord hWidth hRows hMatrixSpan hCacheSpan hScaleSpan hMatrix' hCache' hScale'
      hSeparate hScaleSeparate hBodyAt hMidPc hArgs
  refine ⟨hPc, kBody + 16, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega, hCells, ?_, hOut14.trans h14⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)

def hintGaussRankLiftStmt : Stmt := .seq (.code hintGaussRankLiftSetup) hintRankOneStmt
theorem hintGaussRankLiftStmt_len : hintGaussRankLiftStmt.len = 37 := rfl

theorem hintGaussRankLiftStmt_sem (G : HintGaussArea) (phase : ℕ)
    (A : HintVec G.hints →ₗ[ZMod 2] HintVec G.rows) (B : HintElimState G.rows G.hints)
    (j : Fin G.hints) (pivot : Fin G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hWidth : G.rows < 2 ^ E.W) (hRows : G.hints < 2 ^ E.W)
    (hMatrixSpan : G.lift + G.hints * G.rows < 2 ^ E.W)
    (hCacheSpan : G.pivotRow + G.rows < 2 ^ E.W) (hScaleSpan : G.kernelVec + G.hints < 2 ^ E.W)
    (hMatrix : ∀ r : Fin G.hints, ∀ t : Fin G.rows,
      state.mem (G.lift + r.val * G.rows + t.val) = (B.lift (Pi.single t 1) r).val)
    (hCache : ∀ t : Fin G.rows, state.mem (G.pivotRow + t.val) = (B.residual (Pi.single t 1) pivot).val)
    (hScale : ∀ r : Fin G.hints, state.mem (G.kernelVec + r.val) = (hintElimKernel A B j r).val)
    (hSeparate : G.lift + G.hints * G.rows ≤ G.pivotRow ∨ G.pivotRow + G.rows ≤ G.lift)
    (hScaleSeparate : G.lift + G.hints * G.rows ≤ G.kernelVec ∨ G.kernelVec + G.hints ≤ G.lift)
    (hHeader : HintGaussHeader G phase state.mem) (hFits : HintGaussHeaderFits E G phase)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussRankLiftStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 37) state (fun k out => k ≤ (11 * G.rows + 11) * G.hints + 19 ∧
      (∀ r : Fin G.hints, ∀ t : Fin G.rows,
        out.mem (G.lift + r.val * G.rows + t.val) = ((hintElimInsert A B j pivot).lift (Pi.single t 1) r).val) ∧
      CRMemFrame G.lift (G.lift + G.hints * G.rows) state.mem out.mem ∧
      out.regs 14 = G.context) := by
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintGaussRankLiftSetup at hSetupAt
  change At P (base + 16) (hintRankOneStmt.compile (base + 16)) at hBodyAt
  have hNo : NoBranch hintGaussRankLiftSetup := by
    rw [hintGaussRankLiftSetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintGaussRankLiftSetup_spec E G phase state hContext hHeader hFits hWord
  generalize hMid : runBlock hintGaussRankLiftSetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h14⟩ := hSetup
  have hRunSetup : (step P E)^[16] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGaussRankLiftSetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 16 := by
    have hh := runBlock_pc hintGaussRankLiftSetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hMatrix' : ∀ r : Fin G.hints, ∀ t : Fin G.rows,
      mid.mem (G.lift + r.val * G.rows + t.val) = (B.lift (Pi.single t 1) r).val := by
    simpa only [hMem] using hMatrix
  have hCache' : ∀ t : Fin G.rows, mid.mem (G.pivotRow + t.val) = (B.residual (Pi.single t 1) pivot).val := by
    simpa only [hMem] using hCache
  have hScale' : ∀ r : Fin G.hints, mid.mem (G.kernelVec + r.val) = (hintElimKernel A B j r).val := by
    simpa only [hMem] using hScale
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, hCells, hFrame, _, hOut14⟩ :=
    hintRankOneStmt_lift_sem A B j pivot P E mid G.lift G.pivotRow G.kernelVec (base + 16)
      hWord hWidth hRows hMatrixSpan hCacheSpan hScaleSpan hMatrix' hCache' hScale'
      hSeparate hScaleSeparate hBodyAt hMidPc hArgs
  refine ⟨hPc, kBody + 16, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega, hCells, ?_, hOut14.trans h14⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussResidualStmt_sem
#print axioms LinearSetReconciliation327.Main.hintGaussLiftStmt_sem
#print axioms LinearSetReconciliation327.Main.hintGaussRankResidualStmt_sem
#print axioms LinearSetReconciliation327.Main.hintGaussRankLiftStmt_sem

namespace LinearSetReconciliation327.Main

structure HintUnitParams (dest index : ℕ) (state : RAMState) : Prop where
  dest_value : state.regs 4 = dest
  index_value : state.regs 0 = index
  one_value : state.regs 15 = 1

def hintGaussUnitFields : List (Fin 16 × ℕ) := [(4, 6), (0, 8)]
def hintGaussUnitSetup : List Instr := hintLoadFields hintGaussUnitFields ++ [.imm 15 1]
theorem hintGaussUnitSetup_length : hintGaussUnitSetup.length = 7 := rfl

theorem hintGaussUnitSetup_spec (E : RAMEnv) (G : HintGaussArea) (j : ℕ) (state : RAMState)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G j state.mem)
    (hFits : HintGaussHeaderFits E G j) (hWord : 1 < 2 ^ E.W) :
    let out := runBlock hintGaussUnitSetup E state
    HintUnitParams G.kernelVec j out ∧ out.mem = state.mem ∧ out.regs 14 = G.context := by
  have hValid : ∀ pair ∈ hintGaussUnitFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintGaussUnitFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintGaussUnitFields state hContext hValid
  have hValues := hintGaussHeader_mod E G j state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintGaussUnitFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G j 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G j 6 := by
    have hh := hLoad.2.2.2 4 (by decide)
    simpa [hintGaussUnitFields, hintLoadedValue, hZero, hValues 6 (by decide), hValues 8 (by decide)] using hh
  have hR0 : mid.regs 0 = hintGaussHeaderValue G j 8 := by
    have hh := hLoad.2.2.2 0 (by decide)
    simpa [hintGaussUnitFields, hintLoadedValue, hZero, hValues 6 (by decide), hValues 8 (by decide)] using hh
  dsimp only
  rw [hintGaussUnitSetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [runBlock, execInstr, hR4, hR0, hintGaussHeaderValue,
      Nat.mod_eq_of_lt hWord, hLoad.2.1, hLoad.2.2.1]

def hintGaussPivotFields : List (Fin 16 × ℕ) := [(4, 5), (6, 0)]
def hintGaussPivotSetup : List Instr := hintLoadFields hintGaussPivotFields ++ [.imm 15 1]
theorem hintGaussPivotSetup_length : hintGaussPivotSetup.length = 7 := rfl

theorem hintGaussPivotSetup_spec (E : RAMEnv) (G : HintGaussArea) (j : ℕ) (state : RAMState)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G j state.mem)
    (hFits : HintGaussHeaderFits E G j) (hWord : 1 < 2 ^ E.W) :
    let out := runBlock hintGaussPivotSetup E state
    HintPivotParams G.residualVec G.rows out ∧ out.mem = state.mem ∧ out.regs 14 = G.context := by
  have hValid : ∀ pair ∈ hintGaussPivotFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintGaussPivotFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintGaussPivotFields state hContext hValid
  have hValues := hintGaussHeader_mod E G j state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintGaussPivotFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G j 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G j 5 := by
    have hh := hLoad.2.2.2 4 (by decide)
    simpa [hintGaussPivotFields, hintLoadedValue, hZero, hValues 5 (by decide)] using hh
  have hR6 : mid.regs 6 = hintGaussHeaderValue G j 0 := by
    have hh := hLoad.2.2.2 6 (by decide)
    simpa [hintGaussPivotFields, hintLoadedValue, hZero, hValues 5 (by decide)] using hh
  dsimp only
  rw [hintGaussPivotSetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [runBlock, execInstr, hR4, hR6, hintGaussHeaderValue,
      Nat.mod_eq_of_lt hWord, hLoad.2.1, hLoad.2.2.1]

def hintGaussUnitStmt : Stmt := .seq (.code hintGaussUnitSetup) hintUnitStmt
theorem hintGaussUnitStmt_len : hintGaussUnitStmt.len = 11 := rfl

theorem hintGaussUnitStmt_sem (G : HintGaussArea) (j : Fin G.hints) (v : HintVec G.hints)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hOutSpan : G.kernelVec + G.hints < 2 ^ E.W)
    (hVector : ∀ t : Fin G.hints, state.mem (G.kernelVec + t.val) = (v t).val)
    (hHeader : HintGaussHeader G j.val state.mem) (hFits : HintGaussHeaderFits E G j.val)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussUnitStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 11) state (fun k out => k = 11 ∧
      (∀ t : Fin G.hints, out.mem (G.kernelVec + t.val) = ((v + (Pi.single j 1 : HintVec G.hints)) t).val) ∧
      (∀ addr, addr ≠ G.kernelVec + j.val → out.mem addr = state.mem addr) ∧ out.regs 14 = G.context) := by
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintGaussUnitSetup at hSetupAt
  change At P (base + 7) (hintUnitStmt.compile (base + 7)) at hBodyAt
  have hNo : NoBranch hintGaussUnitSetup := by
    rw [hintGaussUnitSetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintGaussUnitSetup_spec E G j.val state hContext hHeader hFits hWord
  generalize hMid : runBlock hintGaussUnitSetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h14⟩ := hSetup
  have hRunSetup : (step P E)^[7] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGaussUnitSetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 7 := by
    have hh := runBlock_pc hintGaussUnitSetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hVector' : ∀ t : Fin G.hints, mid.mem (G.kernelVec + t.val) = (v t).val := by
    simpa only [hMem] using hVector
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, hCells, hFrame, hRegs⟩ :=
    hintUnitStmt_sem v j P E mid G.kernelVec (base + 7) hWord (by have := j.isLt; omega)
      hArgs.dest_value hArgs.index_value hArgs.one_value hVector' hBodyAt hMidPc
  refine ⟨hPc, kBody + 7, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega, hCells, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)
  · exact (hRegs 14 (by decide) (by decide)).trans h14

def hintGaussPivotStmt : Stmt := .seq (.code hintGaussPivotSetup) hintPivotStmt
theorem hintGaussPivotStmt_len : hintGaussPivotStmt.len = 20 := rfl

theorem hintGaussPivotStmt_sem (G : HintGaussArea) (phase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hRows : G.rows < 2 ^ E.W) (hVecSpan : G.residualVec + G.rows < 2 ^ E.W)
    (hVector : ∀ t : Fin G.rows, state.mem (G.residualVec + t.val) = (v t).val)
    (hHeader : HintGaussHeader G phase state.mem) (hFits : HintGaussHeaderFits E G phase)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintGaussPivotStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 20) state (fun k out => k = 11 * G.rows + 11 ∧ out.mem = state.mem ∧
      out.regs 1 ≤ G.rows ∧ (out.regs 1 = 0 ↔ v = 0) ∧
      (out.regs 1 ≠ 0 → ∃ p : Fin G.rows, out.regs 1 = p.val + 1 ∧ v p = 1) ∧ out.regs 14 = G.context) := by
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintGaussPivotSetup at hSetupAt
  change At P (base + 7) (hintPivotStmt.compile (base + 7)) at hBodyAt
  have hNo : NoBranch hintGaussPivotSetup := by
    rw [hintGaussPivotSetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintGaussPivotSetup_spec E G phase state hContext hHeader hFits hWord
  generalize hMid : runBlock hintGaussPivotSetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h14⟩ := hSetup
  have hRunSetup : (step P E)^[7] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGaussPivotSetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 7 := by
    have hh := runBlock_pc hintGaussPivotSetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hVector' : ∀ t < G.rows, mid.mem (G.residualVec + t) = (hintDenseVec v t).val := by
    intro t ht
    rw [hMem]
    simpa only [hintDenseVec, dif_pos ht] using hVector ⟨t, ht⟩
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, hOutMem, hBound, hZero, hGood, hRegs⟩ :=
    hintPivotStmt_find_sem P E mid G.residualVec G.rows (base + 7) (hintDenseVec v) hWord hRows
      (by intro t ht; omega) hVector' hBodyAt hMidPc hArgs
  have hZeroVec : (∀ t < G.rows, hintDenseVec v t = 0) ↔ v = 0 := by
    constructor
    · intro hh
      funext t
      change v t = 0
      simpa only [hintDenseVec, dif_pos t.isLt] using hh t.val t.isLt
    · intro hh t ht
      simp [hintDenseVec, hh]
  refine ⟨hPc, kBody + 7, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega,
    hOutMem.trans hMem, hBound, hZero.trans hZeroVec, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro hNonzero
    obtain ⟨hP, hBit⟩ := hGood hNonzero
    refine ⟨⟨out.regs 1 - 1, hP⟩, by simp only; omega, ?_⟩
    simpa only [hintDenseVec, dif_pos hP] using hBit
  · exact (hRegs 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussUnitStmt_sem
#print axioms LinearSetReconciliation327.Main.hintGaussPivotStmt_sem

namespace LinearSetReconciliation327.Main

def hintGaussCacheFields : List (Fin 16 × ℕ) := [(4, 7), (5, 2), (6, 0)]
def hintGaussCacheTail : List Instr := [.imm 15 1, .imm 7 1, .sub 1 1 15, .mul 3 1 6, .add 5 5 3]
def hintGaussCacheSetup : List Instr := hintLoadFields hintGaussCacheFields ++ hintGaussCacheTail
theorem hintGaussCacheSetup_length : hintGaussCacheSetup.length = 14 := rfl

theorem hintGaussCacheTail_spec (E : RAMEnv) (state : RAMState) (dest matrix width p : ℕ)
    (hWord : 1 < 2 ^ E.W) (hPivot : p < 2 ^ E.W) (hAddr : matrix + p * width < 2 ^ E.W)
    (h4 : state.regs 4 = dest) (h5 : state.regs 5 = matrix) (h6 : state.regs 6 = width)
    (h1 : state.regs 1 = p + 1) :
    let out := runBlock hintGaussCacheTail E state
    HintCopyParams dest (matrix + p * width) 1 width out ∧ out.mem = state.mem ∧ out.regs 14 = state.regs 14 := by
  have hSub : (p + 1 + 2 ^ E.W - 1) % 2 ^ E.W = p := by
    have hEq : p + 1 + 2 ^ E.W - 1 = p + 2 ^ E.W := by omega
    rw [hEq, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hPivot]
  have hMul : p * width < 2 ^ E.W := by omega
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [hintGaussCacheTail, runBlock, execInstr, h4, h5, h6, h1, Nat.mod_eq_of_lt hWord,
      hSub, Nat.mod_eq_of_lt hMul, Nat.mod_eq_of_lt hAddr]

theorem hintGaussCacheSetup_spec (E : RAMEnv) (G : HintGaussArea) (phase : ℕ) (p : Fin G.rows) (state : RAMState)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G phase state.mem)
    (hFits : HintGaussHeaderFits E G phase) (hWord : 1 < 2 ^ E.W)
    (hMatrixSpan : G.residual + G.rows * G.rows < 2 ^ E.W) (hPivot : state.regs 1 = p.val + 1) :
    let out := runBlock hintGaussCacheSetup E state
    HintCopyParams G.pivotRow (G.residual + p.val * G.rows) 1 G.rows out ∧
      out.mem = state.mem ∧ out.regs 14 = G.context := by
  have hValid : ∀ pair ∈ hintGaussCacheFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintGaussCacheFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintGaussCacheFields state hContext hValid
  have hValues := hintGaussHeader_mod E G phase state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintGaussCacheFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = G.rows := by
    simpa only [Nat.add_zero, hintGaussHeaderValue] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = G.pivotRow := by
    simpa [hintGaussCacheFields, hintLoadedValue, hintGaussHeaderValue, hValues 7 (by decide)] using hLoad.2.2.2 4 (by decide)
  have hR5 : mid.regs 5 = G.residual := by
    simpa [hintGaussCacheFields, hintLoadedValue, hintGaussHeaderValue, hValues 2 (by decide)] using hLoad.2.2.2 5 (by decide)
  have hR6 : mid.regs 6 = G.rows := by
    simpa [hintGaussCacheFields, hintLoadedValue, hZero] using hLoad.2.2.2 6 (by decide)
  have hR1 : mid.regs 1 = p.val + 1 := by
    simpa [hintGaussCacheFields, hintLoadedValue, hPivot] using hLoad.2.2.2 1 (by decide)
  have hWidth : G.rows < 2 ^ E.W := hFits.values 0 (by decide)
  have hOffset := Nat.mul_le_mul_right G.rows p.isLt.le
  have hTail := hintGaussCacheTail_spec E mid G.pivotRow G.residual G.rows p.val hWord (p.isLt.trans hWidth)
    (by omega) hR4 hR5 hR6 hR1
  dsimp only
  rw [hintGaussCacheSetup, runBlock_append, hMid]
  exact ⟨hTail.1, hTail.2.1.trans hLoad.2.1, hTail.2.2.trans hLoad.2.2.1⟩

def hintGaussCacheStmt : Stmt := .seq (.code hintGaussCacheSetup) hintCopyStmt
theorem hintGaussCacheStmt_len : hintGaussCacheStmt.len = 24 := rfl

theorem hintGaussCacheStmt_sem (G : HintGaussArea) (phase : ℕ) (B : HintElimState G.rows G.hints) (p : Fin G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hWidth : G.rows < 2 ^ E.W)
    (hMatrixSpan : G.residual + G.rows * G.rows < 2 ^ E.W) (hCacheSpan : G.pivotRow + G.rows < 2 ^ E.W)
    (hMatrix : ∀ t : Fin G.rows,
      state.mem (G.residual + p.val * G.rows + t.val) = (B.residual (Pi.single t 1) p).val)
    (hSeparate : G.residual + G.rows * G.rows ≤ G.pivotRow ∨ G.pivotRow + G.rows ≤ G.residual)
    (hHeader : HintGaussHeader G phase state.mem) (hFits : HintGaussHeaderFits E G phase)
    (hContext : state.regs 14 = G.context) (hPivot : state.regs 1 = p.val + 1)
    (hAt : At P base (hintGaussCacheStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 24) state (fun k out => k = 9 * G.rows + 17 ∧
      (∀ t : Fin G.rows, out.mem (G.pivotRow + t.val) = (B.residual (Pi.single t 1) p).val) ∧
      (∀ addr, (addr < G.pivotRow ∨ G.pivotRow + G.rows ≤ addr) → out.mem addr = state.mem addr) ∧
      out.regs 14 = G.context) := by
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintGaussCacheSetup at hSetupAt
  change At P (base + 14) (hintCopyStmt.compile (base + 14)) at hBodyAt
  have hNo : NoBranch hintGaussCacheSetup := by
    rw [hintGaussCacheSetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintGaussCacheTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintGaussCacheSetup_spec E G phase p state hContext hHeader hFits hWord hMatrixSpan hPivot
  generalize hMid : runBlock hintGaussCacheSetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h14⟩ := hSetup
  have hRunSetup : (step P E)^[14] state = mid := by
    have hh := iterate_runBlock_of_at P E hintGaussCacheSetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 14 := by
    have hh := runBlock_pc hintGaussCacheSetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hRowEnd : G.residual + p.val * G.rows + G.rows ≤ G.residual + G.rows * G.rows := by
    have hMul := Nat.mul_le_mul_right G.rows (Nat.succ_le_of_lt p.isLt)
    simpa only [Nat.succ_mul, Nat.add_assoc] using Nat.add_le_add_left hMul G.residual
  have hSource : ∀ t < G.rows, G.residual + p.val * G.rows + t * 1 < G.pivotRow ∨
      G.pivotRow + G.rows ≤ G.residual + p.val * G.rows + t * 1 := by
    intro t ht
    simp only [Nat.mul_one]
    rcases hSeparate with hBefore | hAfter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hVector' : ∀ t < G.rows, mid.mem (G.residual + p.val * G.rows + t * 1) = (hintDenseRow B.residual p t).val := by
    intro t ht
    rw [hMem]
    simpa only [hintDenseRow, dif_pos ht, Nat.mul_one] using hMatrix ⟨t, ht⟩
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, _, hOutMem, _, hFrame, hRegs⟩ :=
    hintCopyStmt_sem P E mid G.pivotRow (G.residual + p.val * G.rows) 1 G.rows (base + 14)
      (hintDenseRow B.residual p) hWord hWidth (by intro t ht; omega)
      (by intro t ht; simp only [Nat.mul_one]; omega) hSource hVector' hBodyAt hMidPc hArgs
  refine ⟨hPc, kBody + 14, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro t
    rw [hOutMem]
    have hRange : G.pivotRow ≤ G.pivotRow + t.val ∧ G.pivotRow + t.val < G.pivotRow + G.rows := by
      have := t.isLt
      omega
    simp only [hintCopyMem, hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, zero_mul, add_zero,
      hintDenseRow, dif_pos t.isLt]
  · intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)
  · exact (hRegs 14 (by decide) (by decide) (by decide) (by decide)).trans h14

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussCacheStmt_sem

namespace LinearSetReconciliation327.Main

/-- Ordered private regions. The original hint list is read-only and separate;
    none of these fields changes the paper's public det encoding. -/
structure HintGaussGeometry (E : RAMEnv) (G : HintGaussArea) : Prop where
  header_before : G.context + 14 ≤ G.residual
  residual_before : G.residual + G.rows * G.rows ≤ G.lift
  lift_before : G.lift + G.hints * G.rows ≤ G.column
  column_before : G.column + G.rows ≤ G.residualVec
  residualVec_before : G.residualVec + G.rows ≤ G.kernelVec
  kernelVec_before : G.kernelVec + G.hints ≤ G.pivotRow
  span : G.pivotRow + G.rows < 2 ^ E.W

theorem hintMatrix_cell_lt (matrix rows width r t : ℕ) (hr : r < rows) (ht : t < width) :
    matrix + r * width + t < matrix + rows * width := by
  have hMul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at hMul
  omega

theorem hintGaussHeader_of_frame (G : HintGaussArea) (j lo hi : ℕ) (original memory : ℕ → ℕ)
    (hHeader : HintGaussHeader G j original) (hFrame : CRMemFrame lo hi original memory)
    (hSeparate : G.context + 14 ≤ lo ∨ hi ≤ G.context) : HintGaussHeader G j memory := by
  intro i hi'
  have hOutside : G.context + i < lo ∨ hi ≤ G.context + i := by
    rcases hSeparate with hBefore | hAfter <;> omega
  rw [hFrame _ hOutside]
  exact hHeader i hi'

theorem HintElimStored.of_frame {a h : ℕ} {B : HintElimState a h} {residual lift lo hi : ℕ}
    {original memory : ℕ → ℕ} (hStored : HintElimStored B residual lift original)
    (hFrame : CRMemFrame lo hi original memory)
    (hR : residual + a * a ≤ lo ∨ hi ≤ residual)
    (hL : lift + h * a ≤ lo ∨ hi ≤ lift) : HintElimStored B residual lift memory := by
  constructor
  · intro s t
    have hCell := hintMatrix_cell_lt residual a a s.val t.val s.isLt t.isLt
    have hOutside : residual + s.val * a + t.val < lo ∨ hi ≤ residual + s.val * a + t.val := by
      rcases hR with hBefore | hAfter <;> omega
    rw [hFrame _ hOutside]
    exact hStored.residual_cells s t
  · intro s t
    have hCell := hintMatrix_cell_lt lift h a s.val t.val s.isLt t.isLt
    have hOutside : lift + s.val * a + t.val < lo ∨ hi ≤ lift + s.val * a + t.val := by
      rcases hL with hBefore | hAfter <;> omega
    rw [hFrame _ hOutside]
    exact hStored.lift_cells s t

theorem HintGaussGeometry.width_bound {E : RAMEnv} {G : HintGaussArea} (h : HintGaussGeometry E G) :
    G.rows < 2 ^ E.W := by
  have := h.span
  omega

theorem HintGaussGeometry.hints_bound {E : RAMEnv} {G : HintGaussArea} (h : HintGaussGeometry E G) :
    G.hints < 2 ^ E.W := by
  obtain ⟨_, _, _, _, _, h6, h7⟩ := h
  omega

theorem HintGaussGeometry.word_bound {E : RAMEnv} {G : HintGaussArea} (h : HintGaussGeometry E G) :
    1 < 2 ^ E.W := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussHeader_of_frame
#print axioms LinearSetReconciliation327.Main.HintElimStored.of_frame
end -- Def_LinearSetReconciliation327_Main_HintGaussNative20261120

section -- Def_LinearSetReconciliation327_Main_HintGaussTransition20261120
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
end -- Def_LinearSetReconciliation327_Main_HintGaussTransition20261120

section -- Def_LinearSetReconciliation327_Main_HintGaussColumn20261120
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
end -- Def_LinearSetReconciliation327_Main_HintGaussColumn20261120

section -- Def_LinearSetReconciliation327_Main_HintGaussControl20261120
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
end -- Def_LinearSetReconciliation327_Main_HintGaussControl20261120

section -- Def_LinearSetReconciliation327_Main_HintGaussLoop20261120
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
end -- Def_LinearSetReconciliation327_Main_HintGaussLoop20261120

section -- Def_LinearSetReconciliation327_Main_HintGaussFactor20261120
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
end -- Def_LinearSetReconciliation327_Main_HintGaussFactor20261120


