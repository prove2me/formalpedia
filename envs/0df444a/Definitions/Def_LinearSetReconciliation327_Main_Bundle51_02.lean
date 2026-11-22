-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_02
-- name    : LinearSetReconciliation327_Main_Bundle51_02
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T10:47:47.577542+00:00
-- url     : https://prove2.me/theorems/1a535aba-de0d-46bf-8095-0bc5b02fb835
-- title:
--   LinearSetReconciliation327 — Bundle51_02
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_02` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_01

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_02
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintGaussCandidate20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintGaussSolver20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintGaussBounds20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFamilyLinear20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFamilyCall20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRhsQuery20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRhsPrimitives20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRhsLoop20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFamilyInput20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintTupleFilterInner20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintGaussCandidate20261120
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
end -- Def_LinearSetReconciliation327_Main_HintGaussCandidate20261120

section -- Def_LinearSetReconciliation327_Main_HintGaussSolver20261120
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
end -- Def_LinearSetReconciliation327_Main_HintGaussSolver20261120

section -- Def_LinearSetReconciliation327_Main_HintGaussBounds20261120
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
end -- Def_LinearSetReconciliation327_Main_HintGaussBounds20261120

section -- Def_LinearSetReconciliation327_Main_HintFamilyLinear20261120
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
end -- Def_LinearSetReconciliation327_Main_HintFamilyLinear20261120

section -- Def_LinearSetReconciliation327_Main_HintFamilyCall20261120
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
end -- Def_LinearSetReconciliation327_Main_HintFamilyCall20261120

section -- Def_LinearSetReconciliation327_Main_HintRhsQuery20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRhsQueryFields : List (Fin 16 × ℕ) :=
  [(4, 4), (6, 0), (10, 10), (5, 11), (8, 13), (7, 12), (11, 15)]
def hintRhsQueryTail : List Instr :=
  [.mul 5 5 8, .mul 5 5 7, .imm 15 1, .add 3 11 12, .add 3 3 15, .load 9 3, .add 5 5 9]
def hintRhsQuerySetup : List Instr := hintLoadFields hintRhsQueryFields ++ hintRhsQueryTail
theorem hintRhsQuerySetup_length : hintRhsQuerySetup.length = 28 := rfl

theorem hintRhsQueryTail_spec (E : RAMEnv) (state : RAMState)
    (dest count buckets key row steps outsideBase index outsideCount context : ℕ) (v : Fin buckets)
    (hWord : 1 < 2 ^ E.W) (hBuckets : buckets < 2 ^ E.W)
    (hOutsideAddr : outsideBase + 1 + index < 2 ^ E.W)
    (hOffset : row * steps * buckets + v.val < 2 ^ E.W)
    (h4 : state.regs 4 = dest) (h6 : state.regs 6 = count) (h7 : state.regs 7 = buckets)
    (h10 : state.regs 10 = key) (h5 : state.regs 5 = row) (h8 : state.regs 8 = steps)
    (h11 : state.regs 11 = outsideBase) (h12 : state.regs 12 = index)
    (h13 : state.regs 13 = outsideCount) (h14 : state.regs 14 = context)
    (hOutside : state.mem (outsideBase + 1 + index) = v.val) :
    let out := runBlock hintRhsQueryTail E state
    HintCoeffCopyParams dest (row * steps * buckets + v.val) buckets count key out ∧
      out.mem = state.mem ∧ out.regs 12 = index ∧ out.regs 13 = outsideCount ∧ out.regs 14 = context := by
  have hPositive : 0 < buckets := by have := v.isLt; omega
  have hMulLe : row * steps ≤ row * steps * buckets := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (row * steps) (Nat.succ_le_of_lt hPositive)
  have hFirst : row * steps < 2 ^ E.W := by omega
  have hSecond : row * steps * buckets < 2 ^ E.W := by omega
  have hV : v.val < 2 ^ E.W := v.isLt.trans hBuckets
  have hAdd : outsideBase + index < 2 ^ E.W := by omega
  have hAddr : outsideBase + index + 1 < 2 ^ E.W := by omega
  have hRead : state.mem (outsideBase + index + 1) = v.val := by
    rw [show outsideBase + index + 1 = outsideBase + 1 + index from by omega]
    exact hOutside
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintRhsQueryTail, runBlock, execInstr, h4, h6, h7, h10, h5, h8, h11, h12, h13, h14,
      hRead, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hAdd, Nat.mod_eq_of_lt hAddr,
      Nat.mod_eq_of_lt hFirst, Nat.mod_eq_of_lt hSecond, Nat.mod_eq_of_lt hV, Nat.mod_eq_of_lt hOffset]

theorem hintRhsQuerySetup_spec (E : RAMEnv) (G : HintGaussArea) (r : ℕ) (j : Fin r)
    (outsideBase : ℕ) (v : Fin G.buckets) (state : RAMState)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hCounter : state.regs 12 = j.val) (hCount : state.regs 13 = r)
    (hPointer : state.mem (G.context + 15) = outsideBase)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : state.mem (outsideBase + 1 + j.val) = v.val)
    (hOffset : G.row * G.steps * G.buckets + v.val < 2 ^ E.W) :
    let out := runBlock hintRhsQuerySetup E state
    HintCoeffCopyParams G.column (G.row * G.steps * G.buckets + v.val) G.buckets G.rows G.node out ∧
      out.mem = state.mem ∧ out.regs 12 = j.val ∧ out.regs 13 = r ∧ out.regs 14 = G.context := by
  have hWord := hGeometry.word_bound
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have h3 := hGeometry.residualVec_before
  have h4 := hGeometry.kernelVec_before
  have h5 := hGeometry.span
  have hHintList : G.hintList < 2 ^ E.W := hFits.values 9 (by decide)
  have hBase : outsideBase < 2 ^ E.W := by omega
  have hValid : ∀ pair ∈ hintRhsQueryFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintRhsQueryFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by omega⟩
  have hLoad := hintLoadFields_spec E G.context hintRhsQueryFields state hContext hValid
  have hValues := hintGaussHeader_mod E G 0 state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintRhsQueryFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G 0 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hFifteen : state.mem (G.context + 15) % 2 ^ E.W = outsideBase := by
    rw [hPointer, Nat.mod_eq_of_lt hBase]
  have hR4 : mid.regs 4 = hintGaussHeaderValue G 0 4 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 4 (by decide)
  have hR6 : mid.regs 6 = hintGaussHeaderValue G 0 0 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 6 (by decide)
  have hR10 : mid.regs 10 = hintGaussHeaderValue G 0 10 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 10 (by decide)
  have hR5 : mid.regs 5 = hintGaussHeaderValue G 0 11 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 5 (by decide)
  have hR8 : mid.regs 8 = hintGaussHeaderValue G 0 13 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 8 (by decide)
  have hR7 : mid.regs 7 = hintGaussHeaderValue G 0 12 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 7 (by decide)
  have hR11 : mid.regs 11 = outsideBase := by
    simpa [hintRhsQueryFields, hintLoadedValue, hFifteen] using hLoad.2.2.2 11 (by decide)
  have hR12 : mid.regs 12 = j.val := by
    simpa [hintRhsQueryFields, hintLoadedValue, hCounter] using hLoad.2.2.2 12 (by decide)
  have hR13 : mid.regs 13 = r := by
    simpa [hintRhsQueryFields, hintLoadedValue, hCount] using hLoad.2.2.2 13 (by decide)
  have hOutside' : mid.mem (outsideBase + 1 + j.val) = v.val := by rw [hLoad.2.1]; exact hOutside
  have hTail := hintRhsQueryTail_spec E mid G.column G.rows G.buckets G.node G.row G.steps outsideBase j.val r G.context v
    hWord (hFits.values 12 (by decide)) (by have := j.isLt; omega) hOffset
    hR4 hR6 hR7 hR10 hR5 hR8 hR11 hR12 hR13 hLoad.2.2.1 hOutside'
  dsimp only
  rw [hintRhsQuerySetup, runBlock_append, hMid]
  exact ⟨hTail.1, hTail.2.1.trans hLoad.2.1, hTail.2.2.1, hTail.2.2.2.1, hTail.2.2.2.2⟩

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintRhsQueryStmt : Stmt := .seq (.code hintRhsQuerySetup) hintCoeffCopyStmt
theorem hintRhsQueryStmt_len : hintRhsQueryStmt.len = 38 := rfl

theorem hintRhsQueryStmt_sem (G : HintGaussArea) (r : ℕ) (j : Fin r) (outsideBase : ℕ)
    (v : Fin G.buckets) (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hCounter : state.regs 12 = j.val) (hCount : state.regs 13 = r)
    (hPointer : state.mem (G.context + 15) = outsideBase)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : state.mem (outsideBase + 1 + j.val) = v.val)
    (hOffset : G.row * G.steps * G.buckets + v.val < 2 ^ E.W)
    (hQuerySpan : ∀ s < G.rows, G.row * G.steps * G.buckets + v.val + s * G.buckets < 2 ^ E.W)
    (hCoeff : ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + v.val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ v).val)
    (hAt : At P base (hintRhsQueryStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 38) state (fun k out => k = 9 * G.rows + 31 ∧
      (∀ s : Fin G.rows, out.mem (G.column + s.val) = (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ v).val) ∧
      CRMemFrame G.column (G.column + G.rows) state.mem out.mem ∧ HintGaussHeader G 0 out.mem ∧
      out.mem (G.context + 15) = outsideBase ∧ out.regs 12 = j.val ∧ out.regs 13 = r ∧
      out.regs 14 = G.context ∧
      HintCoeffCopyParams G.column (G.row * G.steps * G.buckets + v.val) G.buckets G.rows G.node out) := by
  have hWord := hGeometry.word_bound
  have hWidth := hGeometry.width_bound
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have h3 := hGeometry.residualVec_before
  have h4 := hGeometry.kernelVec_before
  have h5 := hGeometry.span
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintRhsQuerySetup at hSetupAt
  change At P (base + 28) (hintCoeffCopyStmt.compile (base + 28)) at hBodyAt
  have hNo : NoBranch hintRhsQuerySetup := by
    rw [hintRhsQuerySetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintRhsQueryTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintRhsQuerySetup_spec E G r j outsideBase v state hGeometry hReserve hHeader hFits hContext
    hCounter hCount hPointer hOutsideSpan hOutside hOffset
  generalize hMid : runBlock hintRhsQuerySetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h12, h13, h14⟩ := hSetup
  have hRunSetup : (step P E)^[28] state = mid := by
    have hh := iterate_runBlock_of_at P E hintRhsQuerySetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 28 := by
    have hh := runBlock_pc hintRhsQuerySetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  let vec : HintVec G.rows := fun s => beta ⟨s.val, s.isLt.trans_le hPrefix⟩ v
  have hCoeff' : ∀ s < G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + v.val + s * G.buckets) = (hintDenseVec vec s).val := by
    intro s hs
    simpa only [hintDenseVec, dif_pos hs] using hCoeff ⟨s, hs⟩
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, _, hOutMem, hOutArgs, hFrame, hRegs⟩ :=
    hintCoeffCopyStmt_sem P E mid G.column (G.row * G.steps * G.buckets + v.val) G.buckets G.rows G.node
      (base + 28) (hintDenseVec vec) hWord hWidth (by intro s hs; omega) hQuerySpan hCoeff' hBodyAt hMidPc hArgs
  have hFrame' : CRMemFrame G.column (G.column + G.rows) state.mem out.mem := by
    intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)
  refine ⟨hPc, kBody + 28, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega,
    ?_, hFrame', ?_, ?_, ?_, ?_, ?_, hOutArgs⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro s
    rw [hOutMem]
    have hRange : G.column ≤ G.column + s.val ∧ G.column + s.val < G.column + G.rows := by have := s.isLt; omega
    simp only [hintCopyMem, hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, zero_mul, add_zero,
      hintDenseVec, dif_pos s.isLt]
    rfl
  · exact hintGaussHeader_of_frame G 0 G.column (G.column + G.rows) state.mem out.mem hHeader hFrame' (Or.inl (by omega))
  · rw [hFrame' _ (Or.inl (by omega))]
    exact hPointer
  · exact (hRegs 12 (by decide) (by decide) (by decide) (by decide)).trans h12
  · exact (hRegs 13 (by decide) (by decide) (by decide) (by decide)).trans h13
  · exact (hRegs 14 (by decide) (by decide) (by decide) (by decide)).trans h14

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRhsQueryStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintRhsQuery20261120

section -- Def_LinearSetReconciliation327_Main_HintRhsPrimitives20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRhsEntry : List Instr := hintLoadField 11 15 ++ [.load 13 11, .imm 12 0]
theorem hintRhsEntry_length : hintRhsEntry.length = 5 := rfl

theorem hintRhsEntry_spec (E : RAMEnv) (G : HintGaussArea) (r outsideBase : ℕ) (state : RAMState)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hFits : HintGaussHeaderFits E G 0) (hContext : state.regs 14 = G.context)
    (hPointer : state.mem (G.context + 15) = outsideBase) (hCount : state.mem outsideBase = r)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList) :
    let out := runBlock hintRhsEntry E state
    out.pc = state.pc + 5 ∧ out.mem = state.mem ∧ out.regs 12 = 0 ∧ out.regs 13 = r ∧ out.regs 14 = G.context := by
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have h3 := hGeometry.residualVec_before
  have h4 := hGeometry.kernelVec_before
  have h5 := hGeometry.span
  have hHintList : G.hintList < 2 ^ E.W := hFits.values 9 (by decide)
  have hBase : outsideBase < 2 ^ E.W := by omega
  have hR : r < 2 ^ E.W := by omega
  have hRead := hintLoadField_spec E state 11 15 G.context hContext (by omega)
  generalize hMid : runBlock (hintLoadField 11 15) E state = mid at hRead
  have h11 : mid.regs 11 = outsideBase := by rw [hRead.2.2.1, hPointer, Nat.mod_eq_of_lt hBase]
  have hCountMid : mid.mem outsideBase = r := by rw [hRead.2.1]; exact hCount
  have h14 : mid.regs 14 = G.context := (hRead.2.2.2 14 (by decide) (by decide)).trans hContext
  dsimp only
  rw [hintRhsEntry, runBlock_append, hMid]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [runBlock, execInstr, h11, h14, hCountMid, hRead.1, hRead.2.1, Nat.mod_eq_of_lt hBase, Nat.mod_eq_of_lt hR, Nat.add_assoc]

def hintRhsCloneFields : List (Fin 16 × ℕ) := [(4, 9), (5, 1), (6, 0)]
def hintRhsCloneTail : List Instr := [.add 4 4 5, .add 5 4 6, .imm 7 1, .imm 15 1]
def hintRhsCloneSetup : List Instr := hintLoadFields hintRhsCloneFields ++ hintRhsCloneTail
theorem hintRhsCloneSetup_length : hintRhsCloneSetup.length = 13 := rfl

theorem hintRhsCloneSetup_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState)
    (hGeometry : HintGaussGeometry E G) (hHeader : HintGaussHeader G 0 state.mem)
    (hFits : HintGaussHeaderFits E G 0) (hContext : state.regs 14 = G.context)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context) :
    let out := runBlock hintRhsCloneSetup E state
    HintCopyParams (G.hintList + G.hints) (G.hintList + G.hints + G.rows) 1 G.rows out ∧
      out.mem = state.mem ∧ out.regs 12 = state.regs 12 ∧ out.regs 13 = state.regs 13 ∧ out.regs 14 = G.context := by
  have hWord := hGeometry.word_bound
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  have hDest : G.hintList + G.hints < 2 ^ E.W := by omega
  have hBackup : G.hintList + G.hints + G.rows < 2 ^ E.W := by omega
  have hValid : ∀ pair ∈ hintRhsCloneFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintRhsCloneFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintRhsCloneFields state hContext hValid
  have hValues := hintGaussHeader_mod E G 0 state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintRhsCloneFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G 0 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G 0 9 := by
    simpa [hintRhsCloneFields, hintLoadedValue, hZero, hValues 1 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 4 (by decide)
  have hR5 : mid.regs 5 = hintGaussHeaderValue G 0 1 := by
    simpa [hintRhsCloneFields, hintLoadedValue, hZero, hValues 1 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 5 (by decide)
  have hR6 : mid.regs 6 = hintGaussHeaderValue G 0 0 := by
    simpa [hintRhsCloneFields, hintLoadedValue, hZero, hValues 1 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 6 (by decide)
  have hR12 : mid.regs 12 = state.regs 12 := by
    simpa [hintRhsCloneFields, hintLoadedValue] using hLoad.2.2.2 12 (by decide)
  have hR13 : mid.regs 13 = state.regs 13 := by
    simpa [hintRhsCloneFields, hintLoadedValue] using hLoad.2.2.2 13 (by decide)
  dsimp only
  rw [hintRhsCloneSetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintRhsCloneTail, runBlock, execInstr, hR4, hR5, hR6, hR12, hR13, hintGaussHeaderValue,
      Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hBackup, Nat.mod_eq_of_lt hWord, hLoad.2.1, hLoad.2.2.1]

def hintRhsAxpyFields : List (Fin 16 × ℕ) := [(4, 9), (8, 1), (5, 4)]
def hintRhsAxpyTail : List Instr := [.add 4 4 8, .imm 8 1]
def hintRhsAxpySetup : List Instr := hintLoadFields hintRhsAxpyFields ++ hintRhsAxpyTail
theorem hintRhsAxpySetup_length : hintRhsAxpySetup.length = 11 := rfl

theorem hintRhsAxpySetup_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState)
    (hGeometry : HintGaussGeometry E G) (hHeader : HintGaussHeader G 0 state.mem)
    (hFits : HintGaussHeaderFits E G 0) (hContext : state.regs 14 = G.context)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hCount : state.regs 6 = G.rows) (hOne : state.regs 15 = 1) :
    let out := runBlock hintRhsAxpySetup E state
    HintAxpyParams (G.hintList + G.hints) G.column G.rows 1 out ∧ out.mem = state.mem ∧
      out.regs 12 = state.regs 12 ∧ out.regs 13 = state.regs 13 ∧ out.regs 14 = G.context := by
  have hWord := hGeometry.word_bound
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  have hDest : G.hintList + G.hints < 2 ^ E.W := by omega
  have hValid : ∀ pair ∈ hintRhsAxpyFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintRhsAxpyFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintRhsAxpyFields state hContext hValid
  have hValues := hintGaussHeader_mod E G 0 state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintRhsAxpyFields) E state = mid at hLoad
  have hR4 : mid.regs 4 = hintGaussHeaderValue G 0 9 := by
    simpa [hintRhsAxpyFields, hintLoadedValue, hValues 1 (by decide), hValues 4 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 4 (by decide)
  have hR8 : mid.regs 8 = hintGaussHeaderValue G 0 1 := by
    simpa [hintRhsAxpyFields, hintLoadedValue, hValues 1 (by decide), hValues 4 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 8 (by decide)
  have hR5 : mid.regs 5 = hintGaussHeaderValue G 0 4 := by
    simpa [hintRhsAxpyFields, hintLoadedValue, hValues 1 (by decide), hValues 4 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 5 (by decide)
  have hR6 : mid.regs 6 = G.rows := by
    simpa [hintRhsAxpyFields, hintLoadedValue, hCount] using hLoad.2.2.2 6 (by decide)
  have hR15 : mid.regs 15 = 1 := by
    simpa [hintRhsAxpyFields, hintLoadedValue, hOne] using hLoad.2.2.2 15 (by decide)
  have hR12 : mid.regs 12 = state.regs 12 := by
    simpa [hintRhsAxpyFields, hintLoadedValue] using hLoad.2.2.2 12 (by decide)
  have hR13 : mid.regs 13 = state.regs 13 := by
    simpa [hintRhsAxpyFields, hintLoadedValue] using hLoad.2.2.2 13 (by decide)
  dsimp only
  rw [hintRhsAxpySetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintRhsAxpyTail, runBlock, execInstr, hR4, hR8, hR5, hR6, hR12, hR13, hR15, hintGaussHeaderValue,
      Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hWord, hLoad.2.1, hLoad.2.2.1,
      show (1 : ZMod 2).val = 1 from rfl]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintRhsCloneStmt : Stmt := .seq (.code hintRhsCloneSetup) hintCopyStmt
theorem hintRhsCloneStmt_len : hintRhsCloneStmt.len = 23 := rfl

theorem hintRhsCloneStmt_sem (G : HintGaussArea) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + G.rows + s.val) = (v s).val)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintRhsCloneStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 23) state (fun k out => k = 9 * G.rows + 16 ∧
      (∀ s : Fin G.rows, out.mem (G.hintList + G.hints + s.val) = (v s).val) ∧
      CRMemFrame (G.hintList + G.hints) (G.hintList + G.hints + G.rows) state.mem out.mem ∧
      HintGaussHeader G 0 out.mem ∧ out.regs 12 = state.regs 12 ∧ out.regs 13 = state.regs 13 ∧ out.regs 14 = G.context) := by
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
  change At P base hintRhsCloneSetup at hSetupAt
  change At P (base + 13) (hintCopyStmt.compile (base + 13)) at hBodyAt
  have hNo : NoBranch hintRhsCloneSetup := by
    rw [hintRhsCloneSetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintRhsCloneTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintRhsCloneSetup_spec E G state hGeometry hHeader hFits hContext hSource
  generalize hMid : runBlock hintRhsCloneSetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h12, h13, h14⟩ := hSetup
  have hRunSetup : (step P E)^[13] state = mid := by
    have hh := iterate_runBlock_of_at P E hintRhsCloneSetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 13 := by
    have hh := runBlock_pc hintRhsCloneSetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hVector' : ∀ s < G.rows,
      mid.mem (G.hintList + G.hints + G.rows + s * 1) = (hintDenseVec v s).val := by
    intro s hs
    rw [hMem]
    simpa only [hintDenseVec, dif_pos hs, Nat.mul_one] using hVector ⟨s, hs⟩
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, _, hOutMem, _, hFrame, hRegs⟩ :=
    hintCopyStmt_sem P E mid (G.hintList + G.hints) (G.hintList + G.hints + G.rows) 1 G.rows (base + 13) (hintDenseVec v)
      hWord hWidth (by intro s hs; omega) (by intro s hs; simp only [Nat.mul_one]; omega)
      (by intro s hs; simp only [Nat.mul_one]; exact Or.inr (by omega)) hVector' hBodyAt hMidPc hArgs
  have hFrame' : CRMemFrame (G.hintList + G.hints) (G.hintList + G.hints + G.rows) state.mem out.mem := by
    intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)
  refine ⟨hPc, kBody + 13, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega,
    ?_, hFrame', ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro s
    rw [hOutMem]
    have hRange : G.hintList + G.hints ≤ G.hintList + G.hints + s.val ∧
        G.hintList + G.hints + s.val < G.hintList + G.hints + G.rows := by have := s.isLt; omega
    simp only [hintCopyMem, hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, zero_mul, add_zero,
      hintDenseVec, dif_pos s.isLt]
  · intro i hi
    rw [hFrame' _ (Or.inr (by omega))]
    exact hHeader i hi
  · exact (hRegs 12 (by decide) (by decide) (by decide) (by decide)).trans h12
  · exact (hRegs 13 (by decide) (by decide) (by decide) (by decide)).trans h13
  · exact (hRegs 14 (by decide) (by decide) (by decide) (by decide)).trans h14

def hintRhsAxpyStmt : Stmt := .seq (.code hintRhsAxpySetup) hintAxpyStmt
theorem hintRhsAxpyStmt_len : hintRhsAxpyStmt.len = 24 := rfl

theorem hintRhsAxpyStmt_sem (G : HintGaussArea) (f g : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hF : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + s.val) = (f s).val)
    (hG : ∀ s : Fin G.rows, state.mem (G.column + s.val) = (g s).val)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hCount : state.regs 6 = G.rows) (hOne : state.regs 15 = 1)
    (hAt : At P base (hintRhsAxpyStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 24) state (fun k out => k = 11 * G.rows + 15 ∧
      (∀ s : Fin G.rows, out.mem (G.hintList + G.hints + s.val) = (f s + g s).val) ∧
      CRMemFrame (G.hintList + G.hints) (G.hintList + G.hints + G.rows) state.mem out.mem ∧
      HintGaussHeader G 0 out.mem ∧ out.regs 12 = state.regs 12 ∧ out.regs 13 = state.regs 13 ∧
      out.regs 14 = G.context ∧ out.regs 15 = 1) := by
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
  change At P base hintRhsAxpySetup at hSetupAt
  change At P (base + 11) (hintAxpyStmt.compile (base + 11)) at hBodyAt
  have hNo : NoBranch hintRhsAxpySetup := by
    rw [hintRhsAxpySetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintRhsAxpyTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintRhsAxpySetup_spec E G state hGeometry hHeader hFits hContext hSource hCount hOne
  generalize hMid : runBlock hintRhsAxpySetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h12, h13, h14⟩ := hSetup
  have hRunSetup : (step P E)^[11] state = mid := by
    have hh := iterate_runBlock_of_at P E hintRhsAxpySetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 11 := by
    have hh := runBlock_pc hintRhsAxpySetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hF' : ∀ s < G.rows, mid.mem (G.hintList + G.hints + s) = (hintDenseVec f s).val := by
    intro s hs
    rw [hMem]
    simpa only [hintDenseVec, dif_pos hs] using hF ⟨s, hs⟩
  have hG' : ∀ s < G.rows, mid.mem (G.column + s) = (hintDenseVec g s).val := by
    intro s hs
    rw [hMem]
    simpa only [hintDenseVec, dif_pos hs] using hG ⟨s, hs⟩
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, _, hOutMem, hOutArgs, hFrame, hRegs⟩ :=
    hintAxpyStmt_sem P E mid (G.hintList + G.hints) G.column G.rows (base + 11) 1 (hintDenseVec f) (hintDenseVec g)
      hWord hWidth (by intro s hs; omega) (by intro s hs; omega) hF' hG'
      (Or.inl (by omega)) hBodyAt hMidPc hArgs
  have hFrame' : CRMemFrame (G.hintList + G.hints) (G.hintList + G.hints + G.rows) state.mem out.mem := by
    intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)
  refine ⟨hPc, kBody + 11, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega,
    ?_, hFrame', ?_, ?_, ?_, ?_, hOutArgs.one_value⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro s
    rw [hOutMem]
    have hRange : G.hintList + G.hints ≤ G.hintList + G.hints + s.val ∧
        G.hintList + G.hints + s.val < G.hintList + G.hints + G.rows := by have := s.isLt; omega
    simp only [hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, hintDenseVec, dif_pos s.isLt, one_mul]
  · intro i hi
    rw [hFrame' _ (Or.inr (by omega))]
    exact hHeader i hi
  · exact (hRegs 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12
  · exact (hRegs 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13
  · exact (hRegs 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRhsCloneStmt_sem
#print axioms LinearSetReconciliation327.Main.hintRhsAxpyStmt_sem

namespace LinearSetReconciliation327.Main
open HintParams

noncomputable def hintRhsValue (G : HintGaussArea) {r : ℕ} (outside : Fin r → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (v : HintVec G.rows) (j : ℕ) : HintVec G.rows :=
  fun s => v s + ∑ i ∈ hintGaussDone r j, beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside i)

theorem hintRhsValue_zero (G : HintGaussArea) {r : ℕ} (outside : Fin r → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows) :
    hintRhsValue G outside beta hPrefix v 0 = v := by
  funext s
  simp [hintRhsValue, hintGaussDone]

theorem hintRhsValue_step (G : HintGaussArea) {r : ℕ} (outside : Fin r → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (v : HintVec G.rows) (j : Fin r) :
    hintRhsValue G outside beta hPrefix v (j.val + 1) =
      hintRhsValue G outside beta hPrefix v j.val +
        (fun s : Fin G.rows => beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside j)) := by
  funext s
  unfold hintRhsValue
  rw [← hintGaussDone_succ j, Finset.sum_insert (hintGaussDone_fresh j)]
  simp only [Pi.add_apply]
  abel

theorem hintRowBit_image {r ell K : ℕ} (outside : Fin r → Fin K) (hInj : Function.Injective outside)
    (beta : Fin ell → Fin K → ZMod 2) (s : Fin ell) :
    rowBit beta (Finset.univ.image (fun i => (outside i).val)) s = ∑ i : Fin r, beta s (outside i) := by
  have hNatInj : Function.Injective (fun i => (outside i).val) := by
    intro i j hEq
    exact hInj (Fin.ext hEq)
  have hh := hintBitsSet_rowBit (fun i => (outside i).val) hNatInj (fun i => (outside i).isLt)
    beta (fun _ => 1) s
  simpa [hintBitsSet] using hh

theorem hintRhsValue_full (G : HintGaussArea) {r : ℕ} (outside : Fin r → Fin G.buckets)
    (hInj : Function.Injective outside) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows) :
    hintRhsValue G outside beta hPrefix v r =
      hintOutsideRhs G beta hPrefix (Finset.univ.image (fun i => (outside i).val)) v := by
  funext s
  simp only [hintRhsValue, hintGaussDone_full, hintOutsideRhs]
  rw [hintRowBit_image outside hInj]

def HintRhsFrame (G : HintGaussArea) (original memory : ℕ → ℕ) : Prop :=
  ∀ addr, (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
    (addr < G.column ∨ G.column + G.rows ≤ addr) → memory addr = original addr

theorem HintRhsFrame.refl (G : HintGaussArea) (memory : ℕ → ℕ) : HintRhsFrame G memory memory := by
  intro addr _ _
  rfl

theorem HintRhsFrame.trans {G : HintGaussArea} {first middle last : ℕ → ℕ}
    (hFirst : HintRhsFrame G first middle) (hLast : HintRhsFrame G middle last) : HintRhsFrame G first last := by
  intro addr hRhs hColumn
  exact (hLast addr hRhs hColumn).trans (hFirst addr hRhs hColumn)

theorem HintRhsFrame.of_rhs {G : HintGaussArea} {original memory : ℕ → ℕ}
    (h : CRMemFrame (G.hintList + G.hints) (G.hintList + G.hints + G.rows) original memory) :
    HintRhsFrame G original memory := by
  intro addr hRhs _
  exact h addr hRhs

theorem HintRhsFrame.of_column {G : HintGaussArea} {original memory : ℕ → ℕ}
    (h : CRMemFrame G.column (G.column + G.rows) original memory) : HintRhsFrame G original memory := by
  intro addr _ hColumn
  exact h addr hColumn

theorem HintRhsFrame.header {E : RAMEnv} {G : HintGaussArea} {original memory : ℕ → ℕ}
    (hFrame : HintRhsFrame G original memory) (hGeometry : HintGaussGeometry E G)
    (hSource : G.hintList + G.hints + G.rows ≤ G.context) (hHeader : HintGaussHeader G 0 original) :
    HintGaussHeader G 0 memory := by
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  intro i hi
  rw [hFrame _ (Or.inr (by omega)) (Or.inl (by omega))]
  exact hHeader i hi

theorem HintRhsFrame.pointer {E : RAMEnv} {G : HintGaussArea} {original memory : ℕ → ℕ}
    (hFrame : HintRhsFrame G original memory) (hGeometry : HintGaussGeometry E G)
    (hReserve : G.context + 16 ≤ G.residual) (hSource : G.hintList + G.hints + G.rows ≤ G.context) :
    memory (G.context + 15) = original (G.context + 15) := by
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  exact hFrame _ (Or.inr (by omega)) (Or.inl (by omega))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRhsValue_full
#print axioms LinearSetReconciliation327.Main.HintRhsFrame.header
end -- Def_LinearSetReconciliation327_Main_HintRhsPrimitives20261120

section -- Def_LinearSetReconciliation327_Main_HintRhsLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRhsAdvanceCode : List Instr := [.add 12 12 15]

theorem hintRhsAdvance_spec (E : RAMEnv) (state : RAMState) (j r context : ℕ)
    (hNext : j + 1 < 2 ^ E.W) (hCounter : state.regs 12 = j)
    (hCount : state.regs 13 = r) (hContext : state.regs 14 = context) (hOne : state.regs 15 = 1) :
    let out := runBlock hintRhsAdvanceCode E state
    out.pc = state.pc + 1 ∧ out.mem = state.mem ∧ out.regs 12 = j + 1 ∧
      out.regs 13 = r ∧ out.regs 14 = context := by
  simp [hintRhsAdvanceCode, runBlock, execInstr, hCounter, hCount, hContext, hOne, Nat.mod_eq_of_lt hNext]

def hintRhsBody : Stmt := .seq hintRhsQueryStmt (.seq hintRhsAxpyStmt (.code hintRhsAdvanceCode))
theorem hintRhsBody_len : hintRhsBody.len = 63 := rfl

theorem hintRhsBody_sem (G : HintGaussArea) (r : ℕ) (j : Fin r) (outsideBase : ℕ)
    (outside : Fin r → Fin G.buckets) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hCounter : state.regs 12 = j.val) (hCount : state.regs 13 = r)
    (hPointer : state.mem (G.context + 15) = outsideBase)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : state.mem (outsideBase + 1 + j.val) = (outside j).val)
    (hRhs : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + s.val) =
      (hintRhsValue G outside beta hPrefix v j.val s).val)
    (hOffset : G.row * G.steps * G.buckets + (outside j).val < 2 ^ E.W)
    (hQuerySpan : ∀ s < G.rows, G.row * G.steps * G.buckets + (outside j).val + s * G.buckets < 2 ^ E.W)
    (hCoeff : ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (outside j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside j)).val)
    (hAt : At P base (hintRhsBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 63) state (fun k out => k = 20 * G.rows + 47 ∧
      (∀ s : Fin G.rows, out.mem (G.hintList + G.hints + s.val) =
        (hintRhsValue G outside beta hPrefix v (j.val + 1) s).val) ∧
      HintRhsFrame G state.mem out.mem ∧ HintGaussHeader G 0 out.mem ∧
      out.mem (G.context + 15) = outsideBase ∧ out.regs 12 = j.val + 1 ∧
      out.regs 13 = r ∧ out.regs 14 = G.context) := by
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have h3 := hGeometry.residualVec_before
  have h4 := hGeometry.kernelVec_before
  have h5 := hGeometry.span
  obtain ⟨hQueryAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintRhsQueryStmt.compile base) at hQueryAt
  change At P (base + 38) ((Stmt.seq hintRhsAxpyStmt (.code hintRhsAdvanceCode)).compile (base + 38)) at hRestAt
  obtain ⟨hAxpyAt, hAdvanceAt⟩ := At.seqStmt hRestAt
  change At P (base + 38) (hintRhsAxpyStmt.compile (base + 38)) at hAxpyAt
  change At P (base + 62) hintRhsAdvanceCode at hAdvanceAt
  obtain ⟨_, kQ, sQ, hRunQ, hPcQ, hCostQ, hColumnQ, hFrameQ, hHeaderQ, hPointerQ, hCounterQ, hCountQ, hContextQ, hArgsQ⟩ :=
    hintRhsQueryStmt_sem G r j outsideBase (outside j) beta hPrefix P E state base hGeometry hReserve
      hHeader hFits hContext hCounter hCount hPointer hOutsideSpan hOutside hOffset hQuerySpan hCoeff hQueryAt hPc
  have hRhsQ : ∀ s : Fin G.rows, sQ.mem (G.hintList + G.hints + s.val) =
      (hintRhsValue G outside beta hPrefix v j.val s).val := by
    intro s
    rw [hFrameQ _ (Or.inl (by have := s.isLt; omega))]
    exact hRhs s
  obtain ⟨_, kA, sA, hRunA, hPcA, hCostA, hRhsA, hFrameA, hHeaderA, hCounterA, hCountA, hContextA, hOneA⟩ :=
    hintRhsAxpyStmt_sem G (hintRhsValue G outside beta hPrefix v j.val)
      (fun s => beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside j)) P E sQ (base + 38)
      hGeometry hSource hRhsQ hColumnQ hHeaderQ hFits hContextQ hArgsQ.count_value hArgsQ.one_value hAxpyAt hPcQ
  have hCounterA' : sA.regs 12 = j.val := hCounterA.trans hCounterQ
  have hCountA' : sA.regs 13 = r := hCountA.trans hCountQ
  have hNext : j.val + 1 < 2 ^ E.W := by
    have := j.isLt
    have := hFits.values 9 (by decide)
    change G.hintList < 2 ^ E.W at this
    omega
  have hAdvance := hintRhsAdvance_spec E sA j.val r G.context hNext hCounterA' hCountA' hContextA hOneA
  generalize hOut : runBlock hintRhsAdvanceCode E sA = out at hAdvance
  obtain ⟨hPcOut, hMemOut, hCounterOut, hCountOut, hContextOut⟩ := hAdvance
  have hRunAdvance : (step P E)^[1] sA = out := by
    have hh := iterate_runBlock_of_at P E hintRhsAdvanceCode sA (by rwa [hPcA])
      (by simp [hintRhsAdvanceCode, NoBranch, Instr.NoBranchI])
    rw [hOut] at hh
    exact hh
  have hFrameQA : HintRhsFrame G state.mem sA.mem :=
    (HintRhsFrame.of_column hFrameQ).trans (HintRhsFrame.of_rhs hFrameA)
  have hFrameOut : HintRhsFrame G state.mem out.mem := by rw [hMemOut]; exact hFrameQA
  refine ⟨hPc, 1 + (kA + kQ), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunQ hRunA) hRunAdvance,
    ?_, by omega, ?_, hFrameOut, ?_, ?_, hCounterOut, hCountOut, hContextOut⟩
  · rw [hPcOut, hPcA]
  · intro s
    rw [hMemOut, hRhsA, hintRhsValue_step]
    rfl
  · rw [hMemOut]
    exact hHeaderA
  · exact (hFrameOut.pointer hGeometry hReserve (by omega)).trans hPointer

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

structure HintRhsInv (G : HintGaussArea) {r : ℕ} (outside : Fin r → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (v : HintVec G.rows) (outsideBase j : ℕ) (state : RAMState) : Prop where
  rhs : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + s.val) =
    (hintRhsValue G outside beta hPrefix v j s).val
  header : HintGaussHeader G 0 state.mem
  pointer : state.mem (G.context + 15) = outsideBase
  counter : state.regs 12 = j
  count_value : state.regs 13 = r
  context_value : state.regs 14 = G.context

theorem HintRhsInv.pc {G : HintGaussArea} {r : ℕ} {outside : Fin r → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {v : HintVec G.rows} {outsideBase j : ℕ} {state : RAMState}
    (h : HintRhsInv G outside beta hPrefix v outsideBase j state) (pc : ℕ) :
    HintRhsInv G outside beta hPrefix v outsideBase j {state with pc := pc} :=
  ⟨h.rhs, h.header, h.pointer, h.counter, h.count_value, h.context_value⟩

theorem HintRhsInv.test {G : HintGaussArea} {r : ℕ} {outside : Fin r → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {v : HintVec G.rows} {outsideBase j : ℕ} {state : RAMState}
    (h : HintRhsInv G outside beta hPrefix v outsideBase j state) (E : RAMEnv) :
    HintRhsInv G outside beta hPrefix v outsideBase j (runBlock (Cond.lt 2 12 13).code E state) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.rhs
  · simpa [Cond.code, runBlock, execInstr] using h.header
  · simpa [Cond.code, runBlock, execInstr] using h.pointer
  · simpa [Cond.code, runBlock, execInstr] using h.counter
  · simpa [Cond.code, runBlock, execInstr] using h.count_value
  · simpa [Cond.code, runBlock, execInstr] using h.context_value

def hintRhsLoop : Stmt := .loop (.lt 2 12 13) hintRhsBody
theorem hintRhsLoop_len : hintRhsLoop.len = 66 := rfl

theorem hintRhsLoop_sem (G : HintGaussArea) (r : ℕ) (outsideBase : ℕ)
    (outside : Fin r → Fin G.buckets) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hInv : HintRhsInv G outside beta hPrefix v outsideBase 0 state)
    (hFits : HintGaussHeaderFits E G 0)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : ∀ j : Fin r, state.mem (outsideBase + 1 + j.val) = (outside j).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ j : Fin r, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (outside j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside j)).val)
    (hAt : At P base (hintRhsLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 66) state (fun k out => k ≤ (20 * G.rows + 50) * r + 2 ∧
      HintRhsInv G outside beta hPrefix v outsideBase r out ∧ HintRhsFrame G state.mem out.mem) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = r ∧
    HintRhsInv G outside beta hPrefix v outsideBase j st ∧ HintRhsFrame G state.mem st.mem
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have hBodyAt : At P (base + 2) (hintRhsBody.compile (base + 2)) := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hRhs, hFrame⟩ := hI
    exact ⟨j, hJ, hRhs.pc pc, hFrame⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 12 13).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, hRhs, hFrame⟩ := hI
    exact ⟨j, hJ, hRhs.test E, hFrame⟩
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 12 13).eval st := by
    intro left st hI
    obtain ⟨j, hJ, hRhs, _⟩ := hI
    change st.regs 12 < st.regs 13
    rw [hRhs.counter, hRhs.count_value]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 12 13).eval st := by
    intro st hI
    obtain ⟨j, hJ, hRhs, _⟩ := hI
    change ¬ st.regs 12 < st.regs 13
    rw [hRhs.counter, hRhs.count_value]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 12 13).code.length + 1 →
      Sem P E (base + (Cond.lt 2 12 13).code.length + 1)
        (base + (Cond.lt 2 12 13).code.length + 1 + hintRhsBody.len) st
        (fun k out => k ≤ 20 * G.rows + 47 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hRhs, hFrame⟩ := hI
    have hj : j < r := by omega
    let t : Fin r := ⟨j, hj⟩
    have hOutsideNow : st.mem (outsideBase + 1 + t.val) = (outside t).val := by
      rw [hFrame _ (Or.inl (by have := t.isLt; omega)) (Or.inl (by have := t.isLt; omega))]
      exact hOutside t
    have hOffset : G.row * G.steps * G.buckets + (outside t).val < 2 ^ E.W := by
      have hh := (hintGauss_query_index_lt G.row G.steps G.buckets 0 (outside t).val hSteps (outside t).isLt).trans_le hCoeffSpan
      simpa only [Nat.zero_mul, Nat.add_zero] using hh
    have hQueries : ∀ s < G.rows, G.row * G.steps * G.buckets + (outside t).val + s * G.buckets < 2 ^ E.W := by
      intro s hs
      exact (hintGauss_query_index_lt G.row G.steps G.buckets s (outside t).val (hs.trans_le hPrefix) (outside t).isLt).trans_le hCoeffSpan
    have hNative := hintRhsBody_sem G r t outsideBase outside beta hPrefix v P E st (base + 2)
      hGeometry hReserve hSource hRhs.header hFits hRhs.context_value hRhs.counter hRhs.count_value
      hRhs.pointer hOutsideSpan hOutsideNow hRhs.rhs hOffset hQueries (hCoeff t) hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hValue, hFrameOut, hHeader, hPointer, hCounter, hCount, hContext⟩ := hOut
    exact ⟨hCost.le, j + 1, by omega, ⟨hValue, hHeader, hPointer, hCounter, hCount, hContext⟩, hFrame.trans hFrameOut⟩
  have hInitial : I r state := ⟨0, by omega, hInv, HintRhsFrame.refl G state.mem⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 12 13) hintRhsBody hAt hGeometry.word_bound I (20 * G.rows + 47)
    hIpc hItest hGo hStop hBody r state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, hFinal, hFrame⟩ := hOut
  have hj : j = r := by omega
  rw [hj] at hFinal
  change k ≤ (1 + (20 * G.rows + 47) + 2) * r + 2 at hCost
  exact ⟨by simpa only [show 1 + (20 * G.rows + 47) + 2 = 20 * G.rows + 50 from by omega] using hCost,
    hFinal, hFrame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRhsLoop_sem
end -- Def_LinearSetReconciliation327_Main_HintRhsLoop20261120

section -- Def_LinearSetReconciliation327_Main_HintFamilyInput20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRhsBuilder : Stmt := .seq (.code hintRhsEntry) (.seq hintRhsCloneStmt hintRhsLoop)
theorem hintRhsBuilder_len : hintRhsBuilder.len = 94 := rfl

/-- Build the affine right-hand side from the actual observation backup and the
    actual outside-coordinate array. Nothing supplies the resulting vector. -/
theorem hintRhsBuilder_sem (G : HintGaussArea) (r outsideBase : ℕ)
    (outside : Fin r → Fin G.buckets) (hOutsideInj : Function.Injective outside)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hPointer : state.mem (G.context + 15) = outsideBase)
    (hCount : state.mem outsideBase = r) (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : ∀ j : Fin r, state.mem (outsideBase + 1 + j.val) = (outside j).val)
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + G.rows + s.val) = (v s).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ j : Fin r, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (outside j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside j)).val)
    (hAt : At P base (hintRhsBuilder.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 94) state (fun k out => k ≤ 9 * G.rows + 23 + (20 * G.rows + 50) * r ∧
      (∀ s : Fin G.rows, out.mem (G.hintList + G.hints + s.val) =
        (hintOutsideRhs G beta hPrefix (Finset.univ.image (fun j => (outside j).val)) v s).val) ∧
      HintRhsFrame G state.mem out.mem ∧ HintGaussHeader G 0 out.mem ∧
      out.mem (G.context + 15) = outsideBase ∧ out.regs 12 = r ∧ out.regs 13 = r ∧ out.regs 14 = G.context) := by
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  obtain ⟨hEntryAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintRhsEntry at hEntryAt
  change At P (base + 5) ((Stmt.seq hintRhsCloneStmt hintRhsLoop).compile (base + 5)) at hRestAt
  obtain ⟨hCloneAt, hLoopAt⟩ := At.seqStmt hRestAt
  change At P (base + 5) (hintRhsCloneStmt.compile (base + 5)) at hCloneAt
  change At P (base + 28) (hintRhsLoop.compile (base + 28)) at hLoopAt
  have hNo : NoBranch hintRhsEntry := by simp [hintRhsEntry, hintLoadField, NoBranch, Instr.NoBranchI]
  have hEntry := hintRhsEntry_spec E G r outsideBase state hGeometry hReserve hFits hContext hPointer hCount hOutsideSpan
  generalize hMid : runBlock hintRhsEntry E state = mid at hEntry
  obtain ⟨hPcMid, hMemMid, hCounterMid, hCountMid, hContextMid⟩ := hEntry
  have hRunMid : (step P E)^[5] state = mid := by
    have hh := iterate_runBlock_of_at P E hintRhsEntry state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hVectorMid : ∀ s : Fin G.rows, mid.mem (G.hintList + G.hints + G.rows + s.val) = (v s).val := by
    rw [hMemMid]
    exact hVector
  have hHeaderMid : HintGaussHeader G 0 mid.mem := by rw [hMemMid]; exact hHeader
  obtain ⟨_, kC, sC, hRunC, hPcC, hCostC, hVectorC, hFrameC, hHeaderC, hCounterC, hCountC, hContextC⟩ :=
    hintRhsCloneStmt_sem G v P E mid (base + 5) hGeometry hSource hVectorMid hHeaderMid hFits hContextMid hCloneAt
      (by rw [hPcMid, hPc])
  have hFrameC' : HintRhsFrame G state.mem sC.mem := by
    have hh := HintRhsFrame.of_rhs hFrameC
    rw [hMemMid] at hh
    exact hh
  have hInvC : HintRhsInv G outside beta hPrefix v outsideBase 0 sC := by
    refine ⟨?_, hHeaderC, ?_, hCounterC.trans hCounterMid, hCountC.trans hCountMid, hContextC⟩
    · simpa only [hintRhsValue_zero] using hVectorC
    · exact (hFrameC'.pointer hGeometry hReserve (by omega)).trans hPointer
  have hOutsideC : ∀ j : Fin r, sC.mem (outsideBase + 1 + j.val) = (outside j).val := by
    intro j
    rw [hFrameC' _ (Or.inl (by have := j.isLt; omega)) (Or.inl (by have := j.isLt; omega))]
    exact hOutside j
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hInvL, hFrameL⟩ :=
    hintRhsLoop_sem G r outsideBase outside beta hPrefix v P E sC (base + 28) hGeometry hReserve
      hSource hInvC hFits hOutsideSpan hOutsideC hSteps hCoeffSpan hCoeff hLoopAt (by simpa only [Nat.add_assoc] using hPcC)
  refine ⟨hPc, kL + (kC + 5), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunMid hRunC) hRunL,
    ?_, by omega, ?_, hFrameC'.trans hFrameL, hInvL.header, hInvL.pointer, hInvL.counter, hInvL.count_value, hInvL.context_value⟩
  · simpa only [Nat.add_assoc] using hPcL
  · simpa only [hintRhsValue_full G outside hOutsideInj beta hPrefix v] using hInvL.rhs

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintFamilyInputCallStmt : Stmt := .seq hintRhsBuilder hintGaussSolverStmt
theorem hintFamilyInputCallStmt_len : hintFamilyInputCallStmt.len = 552 := rfl

/-- Unlike the lower-level affine call, this call takes only the original
    transcript backup and actual coordinate arrays as its data inputs. -/
theorem hintFamilyInputCall_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (r outsideBase : ℕ) (outside : Fin r → Fin G.buckets) (hOutsideInj : Function.Injective outside)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows) (Nj : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hInj : Function.Injective coords) (hHintValid : ∀ j, (coords j).val < Nj)
    (hOutsideValid : ∀ j, (outside j).val < Nj)
    (hSeparate : Disjoint (Finset.univ.image (fun j => (outside j).val))
      (Finset.univ.image (fun j => (coords j).val)))
    (hHint : ∀ j : Fin G.hints, state.mem (G.hintList + j.val) = (coords j).val)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hPointer : state.mem (G.context + 15) = outsideBase)
    (hCount : state.mem outsideBase = r) (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : ∀ j : Fin r, state.mem (outsideBase + 1 + j.val) = (outside j).val)
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + G.rows + s.val) = (v s).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ c : Fin G.buckets, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + c.val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ c).val)
    (hAt : At P base (hintFamilyInputCallStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 552) state (fun k out =>
      k ≤ 9 * G.rows + 23 + (20 * G.rows + 50) * r + 512 * (G.rows + G.hints + 1) ^ 3 ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
      (out.regs 1 = 1 ↔ ∃! C : Finset ℕ, hintFamilyClass G coords beta Nj r
        (Finset.univ.image (fun j => (outside j).val)) v C) ∧
      (out.regs 1 = 1 → ∃ z : HintVec G.hints,
        (∀ t : Fin G.hints, out.mem (G.kernelVec + t.val) = (z t).val) ∧
        hintFamilyClass G coords beta Nj r (Finset.univ.image (fun j => (outside j).val)) v
          (hintBitsSet (fun j => (coords j).val) z ∪ Finset.univ.image (fun j => (outside j).val)) ∧
        ∀ C : Finset ℕ, hintFamilyClass G coords beta Nj r (Finset.univ.image (fun j => (outside j).val)) v C →
          C = hintBitsSet (fun j => (coords j).val) z ∪ Finset.univ.image (fun j => (outside j).val)) ∧
      HintGaussHeader G G.hints out.mem ∧
      (∀ addr, (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
        (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → out.mem addr = state.mem addr) ∧ out.regs 14 = G.context) := by
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  obtain ⟨hBuilderAt, hSolverAt⟩ := At.seqStmt hAt
  change At P base (hintRhsBuilder.compile base) at hBuilderAt
  change At P (base + 94) (hintGaussSolverStmt.compile (base + 94)) at hSolverAt
  obtain ⟨_, kB, sB, hRunB, hPcB, hCostB, hRhsB, hFrameB, hHeaderB, _, _, _, hContextB⟩ :=
    hintRhsBuilder_sem G r outsideBase outside hOutsideInj beta hPrefix v P E state base hGeometry hReserve hSource
      hHeader hFits hContext hPointer hCount hOutsideSpan hOutside hVector hSteps hCoeffSpan (fun j => hCoeff (outside j)) hBuilderAt hPc
  have hHintB : ∀ j : Fin G.hints, sB.mem (G.hintList + j.val) = (coords j).val := by
    intro j
    rw [hFrameB _ (Or.inl (by have := j.isLt; omega)) (Or.inl (by have := j.isLt; omega))]
    exact hHint j
  have hOutsideSet : Finset.univ.image (fun j => (outside j).val) ⊆ Finset.range Nj := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hOutsideValid j)
  have hNatInj : Function.Injective (fun j => (outside j).val) := by
    intro i j hEq
    exact hOutsideInj (Fin.ext hEq)
  have hCard : (Finset.univ.image (fun j => (outside j).val)).card = r := by
    rw [Finset.card_image_of_injective _ hNatInj, Finset.card_univ, Fintype.card_fin]
  obtain ⟨_, kS, out, hRunS, hPcS, hCostS, hBit, hUnique, hWitness, hHeaderOut, hFrameS, hContextOut⟩ :=
    hintFamilyCandidateCall_sem G coords beta hPrefix Nj r (Finset.univ.image (fun j => (outside j).val)) v
      P E sB (base + 94) hGeometry hReserve (by omega) hInj hHintValid hOutsideSet hCard hSeparate hHintB hRhsB
      hSteps hCoeffSpan (fun j => hCoeff (coords j)) hHeaderB hFits hContextB hSolverAt hPcB
  refine ⟨hPc, kS + kB, out, hintIterate_then (step P E) hRunB hRunS, ?_, by omega,
    hBit, hUnique, hWitness, hHeaderOut, ?_, hContextOut⟩
  · simpa only [Nat.add_assoc] using hPcS
  · intro addr hRhs hOutsideGauss
    rw [hFrameS addr hOutsideGauss]
    apply hFrameB addr hRhs
    rcases hOutsideGauss with hBefore | hAfter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFamilyInputCall_sem
end -- Def_LinearSetReconciliation327_Main_HintFamilyInput20261120

section -- Def_LinearSetReconciliation327_Main_HintTupleFilterInner20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintTruth (P : Prop) : ℕ := by classical exact if P then 1 else 0

theorem hintTruth_congr {P Q : Prop} (h : P ↔ Q) : hintTruth P = hintTruth Q := congrArg hintTruth (propext h)

def HintTuplePrefix (g : ℕ → ℕ) (i j : ℕ) : Prop := ∀ t < j, i < t → g i < g t

theorem hintTuplePrefix_succ (g : ℕ → ℕ) (i j : ℕ) :
    HintTuplePrefix g i (j + 1) ↔ HintTuplePrefix g i j ∧ (i < j → g i < g j) := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (by omega), h j (by omega)⟩
  · rintro ⟨h, hLast⟩ t ht hit
    by_cases hEq : t = j
    · subst t; exact hLast hit
    · exact h t (by omega) hit

structure HintTupleScanArgs (arrayBase count firstIndex firstValue : ℕ) (state : RAMState) : Prop where
  array : state.regs 4 = arrayBase
  count_value : state.regs 13 = count
  first_index : state.regs 12 = firstIndex
  first_value : state.regs 11 = firstValue
  one_value : state.regs 15 = 1

def hintTupleScanBody : List Instr :=
  [.add 3 4 0, .load 8 3, .lt 9 12 0, .lt 10 11 8, .lt 9 9 15,
    .bor 9 9 10, .mul 1 1 9, .add 0 0 15]

theorem hintTupleScanBody_spec (E : RAMEnv) (state : RAMState) (arrayBase count i j value first : ℕ)
    (accepted : Prop) (hWord : 1 < 2 ^ E.W) (hValue : value < 2 ^ E.W)
    (hAddr : arrayBase + j < 2 ^ E.W) (hNext : j + 1 < 2 ^ E.W)
    (hArgs : HintTupleScanArgs arrayBase count i first state)
    (hCounter : state.regs 0 = j) (hAccept : state.regs 1 = hintTruth accepted)
    (hRead : state.mem (arrayBase + j) = value) :
    let out := runBlock hintTupleScanBody E state
    out.pc = state.pc + 8 ∧ out.mem = state.mem ∧ out.regs 0 = j + 1 ∧
      out.regs 1 = hintTruth (accepted ∧ (i < j → first < value)) ∧
      HintTupleScanArgs arrayBase count i first out ∧
      out.regs 7 = state.regs 7 ∧ out.regs 14 = state.regs 14 := by
  classical
  obtain ⟨h4, h13, h12, h11, h15⟩ := hArgs
  dsimp only
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hintTupleScanBody, runBlock, execInstr]
  · simp [hintTupleScanBody, runBlock, execInstr, hCounter, h15, Nat.mod_eq_of_lt hNext]
  · by_cases hA : accepted <;> by_cases hIJ : i < j <;> by_cases hLT : first < value <;>
      simp [hintTupleScanBody, runBlock, execInstr, hintTruth, h4, h12, h11, h15,
        hCounter, hAccept, hRead, hA, hIJ, hLT, Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hValue, Nat.mod_eq_of_lt hWord]
  · exact ⟨by simpa [hintTupleScanBody, runBlock, execInstr] using h4,
      by simpa [hintTupleScanBody, runBlock, execInstr] using h13,
      by simpa [hintTupleScanBody, runBlock, execInstr] using h12,
      by simpa [hintTupleScanBody, runBlock, execInstr] using h11,
      by simpa [hintTupleScanBody, runBlock, execInstr] using h15⟩
  · simp [hintTupleScanBody, runBlock, execInstr]
  · simp [hintTupleScanBody, runBlock, execInstr]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem HintTupleScanArgs.pc {arrayBase count firstIndex firstValue : ℕ} {state : RAMState}
    (h : HintTupleScanArgs arrayBase count firstIndex firstValue state) (pc : ℕ) :
    HintTupleScanArgs arrayBase count firstIndex firstValue {state with pc := pc} :=
  ⟨h.array, h.count_value, h.first_index, h.first_value, h.one_value⟩

theorem HintTupleScanArgs.test {arrayBase count firstIndex firstValue : ℕ} {state : RAMState}
    (h : HintTupleScanArgs arrayBase count firstIndex firstValue state) (E : RAMEnv) :
    HintTupleScanArgs arrayBase count firstIndex firstValue (runBlock (Cond.lt 2 0 13).code E state) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.array
  · simpa [Cond.code, runBlock, execInstr] using h.count_value
  · simpa [Cond.code, runBlock, execInstr] using h.first_index
  · simpa [Cond.code, runBlock, execInstr] using h.first_value
  · simpa [Cond.code, runBlock, execInstr] using h.one_value

def HintTupleScanInv (arrayBase count firstIndex : ℕ) (g original : ℕ → ℕ) (accepted : Prop)
    (j : ℕ) (state : RAMState) : Prop :=
  HintTupleScanArgs arrayBase count firstIndex (g firstIndex) state ∧
    state.regs 0 = j ∧ state.regs 1 = hintTruth (accepted ∧ HintTuplePrefix g firstIndex j) ∧ state.mem = original

def hintTupleScanLoop : Stmt := .loop (.lt 2 0 13) (.code hintTupleScanBody)
theorem hintTupleScanLoop_len : hintTupleScanLoop.len = 11 := rfl

theorem hintTupleScanLoop_sem (arrayBase count i : ℕ) (g : ℕ → ℕ) (accepted : Prop)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hSpan : arrayBase + count < 2 ^ E.W)
    (hBound : ∀ j < count, g j < 2 ^ E.W)
    (hArgs : HintTupleScanArgs arrayBase count i (g i) state)
    (hCounter : state.regs 0 = 0) (hAccept : state.regs 1 = hintTruth accepted)
    (hDigits : ∀ j < count, state.mem (arrayBase + j) = g j)
    (hAt : At P base (hintTupleScanLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 11) state (fun k out => k ≤ 11 * count + 2 ∧
      HintTupleScanArgs arrayBase count i (g i) out ∧ out.regs 0 = count ∧
      out.regs 1 = hintTruth (accepted ∧ HintTuplePrefix g i count) ∧ out.mem = state.mem ∧
      out.regs 7 = state.regs 7 ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = count ∧
    HintTupleScanInv arrayBase count i g state.mem accepted j st ∧
    st.regs 7 = state.regs 7 ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintTupleScanBody := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, ⟨hA, h0, h1, hMem⟩, h7, h14⟩ := hI
    exact ⟨j, hJ, ⟨hA.pc pc, h0, h1, hMem⟩, h7, h14⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 0 13).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, ⟨hA, h0, h1, hMem⟩, h7, h14⟩ := hI
    refine ⟨j, hJ, ⟨hA.test E, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa [Cond.code, runBlock, execInstr] using h0
    · simpa [Cond.code, runBlock, execInstr] using h1
    · simpa [Cond.code, runBlock, execInstr] using hMem
    · simpa [Cond.code, runBlock, execInstr] using h7
    · simpa [Cond.code, runBlock, execInstr] using h14
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 0 13).eval st := by
    intro left st hI
    obtain ⟨j, hJ, ⟨hA, h0, _, _⟩, _, _⟩ := hI
    change st.regs 0 < st.regs 13
    rw [h0, hA.count_value]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 13).eval st := by
    intro st hI
    obtain ⟨j, hJ, ⟨hA, h0, _, _⟩, _, _⟩ := hI
    change ¬ st.regs 0 < st.regs 13
    rw [h0, hA.count_value]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 13).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 13).code.length + 1)
        (base + (Cond.lt 2 0 13).code.length + 1 + (Stmt.code hintTupleScanBody).len) st
        (fun k out => k ≤ 8 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, ⟨hA, h0, h1, hMem⟩, h7, h14⟩ := hI
    have hj : j < count := by omega
    have hRead : st.mem (arrayBase + j) = g j := by rw [hMem]; exact hDigits j hj
    have hSpec := hintTupleScanBody_spec E st arrayBase count i j (g j) (g i)
      (accepted ∧ HintTuplePrefix g i j) hWord (hBound j hj) (by omega) (by omega) hA h0 h1 hRead
    generalize hMid : runBlock hintTupleScanBody E st = mid at hSpec
    obtain ⟨_, hMemMid, h0Mid, h1Mid, hArgsMid, h7Mid, h14Mid⟩ := hSpec
    have hFlag : mid.regs 1 = hintTruth (accepted ∧ HintTuplePrefix g i (j + 1)) :=
      h1Mid.trans (hintTruth_congr (by rw [hintTuplePrefix_succ]; tauto))
    have hNative := Sem.block P E (base + 2) hintTupleScanBody st hBodyAt
      (by simp [hintTupleScanBody, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hK, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨by simpa [hintTupleScanBody] using hK.le, j + 1, by omega,
      ⟨hArgsMid, h0Mid, hFlag, hMemMid.trans hMem⟩, h7Mid.trans h7, h14Mid.trans h14⟩
  have hFlag0 : state.regs 1 = hintTruth (accepted ∧ HintTuplePrefix g i 0) := by
    rw [hAccept]
    apply hintTruth_congr
    simp [HintTuplePrefix]
  have hInitial : I count state := ⟨0, by omega, ⟨hArgs, hCounter, hFlag0, rfl⟩, rfl, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 13) (.code hintTupleScanBody) hAt hWord I 8
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, ⟨hA, h0, h1, hMem⟩, h7, h14⟩ := hOut
  have hj : j = count := by omega
  rw [hj] at h0 h1
  exact ⟨hCost, hA, h0, h1, hMem, h7, h14⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTupleScanLoop_sem
end -- Def_LinearSetReconciliation327_Main_HintTupleFilterInner20261120


