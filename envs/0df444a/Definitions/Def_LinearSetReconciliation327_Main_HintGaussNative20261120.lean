-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintGaussNative20261120
-- name    : LinearSetReconciliation327_Main_HintGaussNative20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T10:28:12.225811+00:00
-- url     : https://prove2.me/theorems/9c8e796d-8ec9-45d3-b182-479902753da5
-- title:
--   LinearSetReconciliation327 — HintGaussNative (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintGaussNative20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintGaussSetup20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintGaussUpdate20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintGaussInit20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintRowPivot20261120
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


