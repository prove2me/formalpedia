-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_06
-- name    : LinearSetReconciliation327_Main_Bundle51_06
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T13:36:05.356166+00:00
-- url     : https://prove2.me/theorems/a3e39329-2d02-4d9e-9477-913b8c8e55c9
-- title:
--   LinearSetReconciliation327 — Bundle51_06
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_06` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_05

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_06
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalBody20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalLoop20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalInit20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalScan20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalReplayPrep20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalReplay20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintWeightedBitmapLoop20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBitmapUnionLoop20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintOutputSetup20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBitmapClear20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintCandidateBitmap20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalCandidate20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalRecover20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalAux20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalGuard20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalResult20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowFinal20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintTranscript20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintGatherBody20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintFinalBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalBody : Stmt := .seq hintScanFirstPassStmt (.seq hintFinalAccumulateStmt (.code hintRowAdvanceCode))
theorem hintFinalBody_len : hintFinalBody.len = 713 := rfl

def hintFinalBodyTime (G : HintGaussArea) (Nj r : ℕ) : ℕ :=
  7 * r + 73 + (hintScanBodyTime G r + 2) * Nj ^ r

theorem hintFinalBody_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj parent outsideBase bitmapBase maxR j : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) (original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase) (hj : j ≤ maxR)
    (hState : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original state)
    (hAt : At P base (hintFinalBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 713) state (fun k out => k ≤ hintFinalBodyTime G Nj j ∧
      HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR (j + 1) v hPos original out ∧
      out.regs 13 = hintTruth (j + 1 ≤ maxR)) := by
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hSpan := hPublic.fits.span
  obtain ⟨hFirstAt, hTailAt⟩ := At.seqStmt hAt
  change At P base (hintScanFirstPassStmt.compile base) at hFirstAt
  change At P (base + 661) ((Stmt.seq hintFinalAccumulateStmt (.code hintRowAdvanceCode)).compile (base + 661)) at hTailAt
  obtain ⟨hAccAt, hAdvanceAt⟩ := At.seqStmt hTailAt
  change At P (base + 661) (hintFinalAccumulateStmt.compile (base + 661)) at hAccAt
  change At P (base + 701) hintRowAdvanceCode at hAdvanceAt
  obtain ⟨_, kF, sF, hRunF, hPcF, hCostF, hCountF, _, hDataF, hHeaderF, hCtxF, hScanFrameF⟩ :=
    hintScanFirstPassStmt_sem G coords beta hPrefix Nj j parent outsideBase bitmapBase v P E state base
      (hPublic.at_count j hj) hState.readonly hState.header hState.context_value hFirstAt hPc
  have hMutationF : HintRowMutationFrame G parent outsideBase bitmapBase Nj j state.mem sF.mem := by
    intro addr _ hO h3 hR hG
    exact hScanFrameF addr hO h3 hR hG
  have hMetaF : ∀ i, 4 ≤ i → i < 16 → sF.mem (parent + i) = state.mem (parent + i) := by
    intro i hi hi'
    exact hMutationF.parent (hPublic.at_count j hj) i hi hi'
  have hStateF : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original sF := by
    refine ⟨hDataF, hHeaderF, hCtxF, (hMetaF 4 (by decide) (by decide)).trans hState.limit,
      (hMetaF 7 (by decide) (by decide)).trans hState.total, ?_,
      hState.frame.trans (HintFinalFrame.of_scan hj hScanFrameF)⟩
    rw [hMetaF 8 (by decide) (by decide)]
    exact hState.saved
  obtain ⟨_, kA, sA, hRunA, hPcA, hCostA, hMemA, _, hCtxA⟩ :=
    hintFinalAccumulateStmt_sem parent outsideBase j
      (min 2 (hintFinalRawPrefix G coords beta Nj j v hPos))
      (min 2 (hintFamilySuccesses G coords beta Nj j v hPos).card)
      P E sF (base + 661) (by omega) (hCtxF.trans hParent.symm) (by omega) (by omega)
      (min_le_left _ _) (min_le_left _ _) hDataF.outside_pointer hDataF.outside_count hStateF.total hCountF hAccAt hPcF
  have hTallied : HintFinalTallied G coords beta Nj parent outsideBase bitmapBase maxR j (j + 1) v hPos original sA :=
    HintFinalState.after_accumulate hPublic hStateF hMemA (hCtxA.trans hParent)
  have hAdvance := hintRowAdvanceCode_spec E sA parent outsideBase j maxR (by omega) hCtxA
    (by omega) (by omega) (by omega) hTallied.readonly.outside_pointer hTallied.readonly.outside_count hTallied.limit
  generalize hD : runBlock hintRowAdvanceCode E sA = out at hAdvance
  obtain ⟨hPcD, hMemD, hGoD, _, _, hCtxD⟩ := hAdvance
  have hStateD := HintFinalTallied.after_count hPublic hTallied hMemD (hCtxD.trans hParent)
  have hRunD : (step P E)^[12] sA = out := by
    have hh := iterate_runBlock_of_at P E hintRowAdvanceCode sA (by rwa [hPcA])
      (by simp [hintRowAdvanceCode, hintScanParent, hintRowAdvanceFetch, hintParentLoad, hintRowAdvanceTail, NoBranch, Instr.NoBranchI])
    simpa only [hintRowAdvanceCode_length, hD] using hh
  refine ⟨hPc, 12 + (kA + kF), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunF hRunA) hRunD,
    by omega, ?_, hStateD, hGoD⟩
  dsimp only [hintFinalBodyTime]
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalBody_sem
end -- Def_LinearSetReconciliation327_Main_HintFinalBody20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalLoop : Stmt := .loop (.neqz 13) hintFinalBody
theorem hintFinalLoop_len : hintFinalLoop.len = 715 := rfl

def hintFinalBudget (G : HintGaussArea) (Nj maxR : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (maxR + 1), hintFinalBodyTime G Nj r

theorem hintFinalLoop_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj parent outsideBase bitmapBase maxR : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) (original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hState : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR 0 v hPos original state)
    (hGoInitial : state.regs 13 = 1)
    (hAt : At P base (hintFinalLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 715) state (fun k out => k ≤ (hintFinalBudget G Nj maxR + 2) * (maxR + 1) + 1 ∧
      HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR (maxR + 1) v hPos original out ∧
      out.regs 13 = 0) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = maxR + 1 ∧
    HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original st ∧
      st.regs 13 = hintTruth (j ≤ maxR)
  have hBodyAt : At P (base + 1) (hintFinalBody.compile (base + 1)) := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hState, hGo⟩ := hI
    exact ⟨j, hJ, hState.pc pc, hGo⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.neqz 13).code E st) := by
    intro left st hI
    exact hI
  have hGo : ∀ left st, I (left + 1) st → (Cond.neqz 13).eval st := by
    intro left st hI
    obtain ⟨j, hJ, _, hGo⟩ := hI
    have hj : j ≤ maxR := by omega
    have hOne : st.regs 13 = 1 := by simpa [hintTruth, hj] using hGo
    change st.regs 13 ≠ 0
    rw [hOne]; decide
  have hStop : ∀ st, I 0 st → ¬ (Cond.neqz 13).eval st := by
    intro st hI
    obtain ⟨j, hJ, _, hGo⟩ := hI
    have hj : j = maxR + 1 := by omega
    have hZero : st.regs 13 = 0 := by simpa [hintTruth, hj] using hGo
    change ¬ st.regs 13 ≠ 0
    rw [hZero]; simp
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.neqz 13).code.length + 1 →
      Sem P E (base + (Cond.neqz 13).code.length + 1)
        (base + (Cond.neqz 13).code.length + 1 + hintFinalBody.len) st
        (fun k out => k ≤ hintFinalBudget G Nj maxR ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hState, _⟩ := hI
    have hj : j ≤ maxR := by omega
    have hNative := hintFinalBody_sem G coords beta hPrefix Nj parent outsideBase bitmapBase maxR j v hPos original
      P E st (base + 1) hPublic hj hState hBodyAt hStart
    have hBudget : hintFinalBodyTime G Nj j ≤ hintFinalBudget G Nj maxR :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hFinal, hGo⟩ := hOut
    exact ⟨hCost.trans hBudget, j + 1, by omega, hFinal, hGo⟩
  have hInitial : I (maxR + 1) state :=
    ⟨0, by omega, hState, by simpa [hintTruth] using hGoInitial⟩
  have hNative := hintLoopFuel_sem P E base (.neqz 13) hintFinalBody hAt hPublic.geometry.word_bound I
    (hintFinalBudget G Nj maxR) hIpc hItest hGo hStop hBody (maxR + 1) state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, hFinal, hGo⟩ := hOut
  simp only [Cond.code, List.length_nil, Nat.zero_add] at hCost
  have hj : j = maxR + 1 := by omega
  rw [hj] at hFinal hGo
  exact ⟨hCost, hFinal, by simpa [hintTruth] using hGo⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalLoop_sem
end -- Def_LinearSetReconciliation327_Main_HintFinalLoop20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalInit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalResetTail : List Instr := [.imm 3 7, .add 3 11 3, .imm 0 0, .store 3 0, .imm 13 1]
def hintFinalResetCode : List Instr := hintScanParent ++ hintFinalResetTail

theorem hintFinalResetCode_spec (E : RAMEnv) (state : RAMState) (parent : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16) :
    let out := runBlock hintFinalResetCode E state
    out.pc = state.pc + 7 ∧ out.mem = Function.update state.mem (parent + 7) 0 ∧
      out.regs 13 = 1 ∧ out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have h7 : 7 < 2 ^ E.W := by omega
  have hAddr : parent + 7 < 2 ^ E.W := by omega
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hTail : let out := runBlock hintFinalResetTail E sP
      out.pc = sP.pc + 5 ∧ out.mem = Function.update sP.mem (parent + 7) 0 ∧
        out.regs 13 = 1 ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [hintFinalResetTail, runBlock, execInstr, hParentP, hContextP,
        Nat.mod_eq_of_lt h7, Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hWord]
  generalize hT : runBlock hintFinalResetTail E sP = out at hTail
  obtain ⟨hPcT, hMemT, hGo, hCtx⟩ := hTail
  have hRun : runBlock hintFinalResetCode E state = out := by rw [hintFinalResetCode, runBlock_append, hP, hT]
  rw [hRun]
  exact ⟨by omega, by rw [hMemT, hMemP], hGo, hCtx⟩

def hintFinalInitStmt : Stmt := .seq (.code hintRowOuterInitCode) (.seq hintRowBitmapStmt (.code hintFinalResetCode))
theorem hintFinalInitStmt_len : hintFinalInitStmt.len = 48 := rfl

theorem hintFinalInitStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj parent outsideBase bitmapBase maxR oldCount : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hLimit : state.mem (parent + 4) = maxR)
    (hAt : At P base (hintFinalInitStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 48) state (fun k out => k ≤ 7 * Nj + 8 * G.hints + 37 ∧
      HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR 0 v hPos state.mem out ∧ out.regs 13 = 1) := by
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hSpan := hPublic.fits.span
  obtain ⟨hInitAt, hTailAt⟩ := At.seqStmt hAt
  change At P base hintRowOuterInitCode at hInitAt
  change At P (base + 7) ((Stmt.seq hintRowBitmapStmt (.code hintFinalResetCode)).compile (base + 7)) at hTailAt
  obtain ⟨hBitmapAt, hResetAt⟩ := At.seqStmt hTailAt
  change At P (base + 7) (hintRowBitmapStmt.compile (base + 7)) at hBitmapAt
  change At P (base + 41) hintFinalResetCode at hResetAt
  have hInit := hintRowOuterInitCode_spec E state parent outsideBase (by omega) (hContext.trans hParent.symm)
    (by omega) hInput.outside_pointer
  generalize hI : runBlock hintRowOuterInitCode E state = sI at hInit
  obtain ⟨hPcI, hMemI, _, _, hCtxI⟩ := hInit
  have hRunI : (step P E)^[7] state = sI := by
    have hh := iterate_runBlock_of_at P E hintRowOuterInitCode state (by rwa [hPc])
      (by simp [hintRowOuterInitCode, hintScanParent, hintRowOuterInitTail, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  have hInputI : HintRowInput G coords Nj 0 parent outsideBase bitmapBase v sI.mem := by
    rw [hMemI]; exact HintRowInput.set_count hPublic hInput 0
  have hHeaderI : ∃ index, HintGaussHeader G index sI.mem := by
    obtain ⟨index, hHeader⟩ := hHeader
    refine ⟨index, ?_⟩
    intro i hi
    rw [hMemI, Function.update_of_ne (by omega : G.context + i ≠ outsideBase)]
    exact hHeader i hi
  have hFrameI : HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem sI.mem := by
    rw [hMemI]
    exact HintFinalFrame.of_controller (HintRowControllerFrame.set_count G parent outsideBase bitmapBase Nj maxR state.mem 0)
  obtain ⟨_, kB, sB, hRunB, hPcB, hCostB, hDataB, hHeaderB, hCtxB, hBitmapFrame⟩ :=
    hintRowBitmapStmt_sem G coords beta hPrefix Nj 0 parent outsideBase bitmapBase v P E sI (base + 7)
      (hPublic.at_count 0 (by omega)) hInputI hHeaderI (hCtxI.trans hParent) hBitmapAt (by omega)
  have hFrameB : HintFinalFrame G parent outsideBase bitmapBase Nj maxR sI.mem sB.mem := by
    intro addr hB _ _ _ _ _ _
    exact hBitmapFrame addr hB
  have hReset := hintFinalResetCode_spec E sB parent (by omega) (hCtxB.trans hParent.symm)
  generalize hR : runBlock hintFinalResetCode E sB = out at hReset
  obtain ⟨hPcR, hMemR, hGoR, hCtxR⟩ := hReset
  have hRunR : (step P E)^[7] sB = out := by
    have hh := iterate_runBlock_of_at P E hintFinalResetCode sB (by rwa [hPcB])
      (by simp [hintFinalResetCode, hintScanParent, hintFinalResetTail, NoBranch, Instr.NoBranchI])
    rw [hR] at hh
    exact hh
  have hFrameR : HintFinalFrame G parent outsideBase bitmapBase Nj maxR sB.mem out.mem := by
    rw [hMemR]
    exact HintFinalFrame.set_meta G parent outsideBase bitmapBase Nj maxR sB.mem 7 0 (Or.inl rfl)
  have hAllFrame := hFrameI.trans (hFrameB.trans hFrameR)
  have hFinal : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR 0 v hPos state.mem out := by
    refine ⟨?_, ?_, hCtxR.trans hParent,
      (hAllFrame.parent hPublic 4 (by decide) (by decide) (by decide) (by decide)).trans hLimit,
      ?_, HintSavedUnique.zero _ _, hAllFrame⟩
    · rw [hMemR]
      exact HintScanReadOnly.set_meta hPublic hDataB 7 0 (by decide)
    · obtain ⟨index, hHeader⟩ := hHeaderB
      rw [hMemR]
      exact ⟨index, hintGaussHeader_set_meta hParent hHeader 7 0 (by decide)⟩
    · simp [hMemR, hintFinalRawPrefix_zero]
  exact ⟨hPc, 7 + (kB + 7), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunI hRunB) hRunR,
    by omega, by omega, hFinal, hGoR⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalInitStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintFinalInit20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalScan20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalScanStmt : Stmt := .seq hintFinalInitStmt hintFinalLoop
theorem hintFinalScanStmt_len : hintFinalScanStmt.len = 763 := rfl

/-- Native all-count final scan from actual row inputs. It constructs the hint
    bitmap, initializes all needed counters, and records a real replay count. -/
theorem hintFinalScanStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj parent outsideBase bitmapBase maxR oldCount : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hLimit : state.mem (parent + 4) = maxR)
    (hAt : At P base (hintFinalScanStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 763) state (fun k out =>
      k ≤ (hintFinalBudget G Nj maxR + 2) * (maxR + 1) + 7 * Nj + 8 * G.hints + 38 ∧
      HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR (maxR + 1) v hPos state.mem out ∧
      out.regs 13 = 0 ∧
      (out.mem (parent + 7) = 1 ↔ (hintFinalUnion G coords beta Nj maxR v).card = 1) ∧
      (out.mem (parent + 7) = 1 → ∃ r ≤ maxR, out.mem (parent + 8) = r ∧
        (hintFamilySuccesses G coords beta Nj r v hPos).card = 1 ∧
        ∀ s ≤ maxR, s ≠ r → (hintFamilySuccesses G coords beta Nj s v hPos).card = 0)) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base (hintFinalInitStmt.compile base) at hInitAt
  change At P (base + 48) (hintFinalLoop.compile (base + 48)) at hLoopAt
  obtain ⟨_, kI, sI, hRunI, hPcI, hCostI, hStateI, hGoI⟩ :=
    hintFinalInitStmt_sem G coords beta hPrefix Nj parent outsideBase bitmapBase maxR oldCount v hPos P E state base
      hPublic hInput hHeader hContext hLimit hInitAt hPc
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hFinal, hGo⟩ :=
    hintFinalLoop_sem G coords beta hPrefix Nj parent outsideBase bitmapBase maxR v hPos state.mem P E sI (base + 48)
      hPublic hStateI hGoI hLoopAt hPcI
  refine ⟨hPc, kL + kI, out, hintIterate_then (step P E) hRunI hRunL,
    by omega, by omega, hFinal, hGo, ?_, ?_⟩
  · rw [hFinal.total]
    exact hintFinal_cap_one G coords hPublic.injective beta hPrefix Nj maxR v hPos hPublic.hint_valid
  · intro hOne
    have hCapOne : min 2 (hintFinalRawPrefix G coords beta Nj (maxR + 1) v hPos) = 1 := hFinal.total.symm.trans hOne
    have hRawOne := (hintCap2_one _).mp hCapOne
    obtain ⟨hBound, hSavedOne, hOthers⟩ := hFinal.saved hRawOne
    exact ⟨out.mem (parent + 8), by omega, rfl, hSavedOne, fun s hs hNe => hOthers s (by omega) hNe⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalScanStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintFinalScan20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalReplayPrep20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalRestoreTail : List Instr := [.load 4 11, .imm 3 8, .add 3 11 3, .load 0 3, .store 4 0]
def hintFinalRestoreCode : List Instr := hintScanParent ++ hintFinalRestoreTail

theorem hintFinalRestoreCode_spec (E : RAMEnv) (state : RAMState) (parent outsideBase r : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase < 2 ^ E.W) (hR : r < 2 ^ E.W)
    (hPointer : state.mem parent = outsideBase) (hSaved : state.mem (parent + 8) = r) :
    let out := runBlock hintFinalRestoreCode E state
    out.pc = state.pc + 7 ∧ out.mem = Function.update state.mem outsideBase r ∧ out.regs 14 = parent + 16 := by
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hPointerP : sP.mem parent = outsideBase := by rw [hMemP]; exact hPointer
  have hSavedP : sP.mem (parent + 8) = r := by rw [hMemP]; exact hSaved
  have h8 : 8 < 2 ^ E.W := by omega
  have hAddr : parent + 8 < 2 ^ E.W := by omega
  have hTail : let out := runBlock hintFinalRestoreTail E sP
      out.pc = sP.pc + 5 ∧ out.mem = Function.update sP.mem outsideBase r ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [hintFinalRestoreTail, runBlock, execInstr, hParentP, hContextP, hPointerP, hSavedP,
        Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt hAddr]
  generalize hT : runBlock hintFinalRestoreTail E sP = out at hTail
  obtain ⟨hPcT, hMemT, hContextT⟩ := hTail
  have hRun : runBlock hintFinalRestoreCode E state = out := by rw [hintFinalRestoreCode, runBlock_append, hP, hT]
  rw [hRun]
  exact ⟨by omega, by rw [hMemT, hMemP], hContextT⟩

def hintFinalCheckPrep : List Instr := hintScanParent ++ [.imm 4 7, .add 4 11 4]
def hintFinalCheckCode : List Instr := hintFinalCheckPrep ++ hintFamilyCheckTail

theorem hintFinalOneTail_spec (E : RAMEnv) (state : RAMState) (pointer count : ℕ)
    (hWord : 3 < 2 ^ E.W) (hCount : count ≤ 2)
    (h4 : state.regs 4 = pointer) (hRead : state.mem pointer = count) :
    let out := runBlock hintFamilyCheckTail E state
    out.pc = state.pc + 4 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (count = 1) ∧ out.regs 14 = state.regs 14 := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hTwo : 2 < 2 ^ E.W := by omega
  interval_cases count <;> refine ⟨?_, rfl, ?_, ?_⟩ <;>
    simp [hintFamilyCheckTail, runBlock, execInstr, h4, hRead, hintTruth,
      Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hTwo]

theorem hintFinalCheckCode_spec (E : RAMEnv) (state : RAMState) (parent count : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hCount : count ≤ 2) (hRead : state.mem (parent + 7) = count) :
    let out := runBlock hintFinalCheckCode E state
    out.pc = state.pc + 8 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (count = 1) ∧ out.regs 14 = parent + 16 := by
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have h7 : 7 < 2 ^ E.W := by omega
  have hAddr : parent + 7 < 2 ^ E.W := by omega
  have hPrep : let out := runBlock [.imm 4 7, .add 4 11 4] E sP
      out.pc = sP.pc + 2 ∧ out.mem = sP.mem ∧ out.regs 4 = parent + 7 ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, rfl, ?_, ?_⟩ <;> simp [runBlock, execInstr, hParentP, hContextP, Nat.mod_eq_of_lt h7, Nat.mod_eq_of_lt hAddr]
  generalize hQ : runBlock [.imm 4 7, .add 4 11 4] E sP = sQ at hPrep
  obtain ⟨hPcQ, hMemQ, h4, hContextQ⟩ := hPrep
  have hTail := hintFinalOneTail_spec E sQ (parent + 7) count (by omega) hCount h4 (by rw [hMemQ, hMemP]; exact hRead)
  generalize hT : runBlock hintFamilyCheckTail E sQ = out at hTail
  obtain ⟨hPcT, hMemT, hFlagT, hContextT⟩ := hTail
  have hRun : runBlock hintFinalCheckCode E state = out := by
    rw [hintFinalCheckCode, hintFinalCheckPrep, runBlock_append, runBlock_append, hP, hQ, hT]
  rw [hRun]
  exact ⟨by omega, hMemT.trans (hMemQ.trans hMemP), hFlagT, hContextT.trans hContextQ⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalRestoreCode_spec
#print axioms LinearSetReconciliation327.Main.hintFinalCheckCode_spec
end -- Def_LinearSetReconciliation327_Main_HintFinalReplayPrep20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalReplay20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalReplayStmt : Stmt := .seq (.code hintFinalRestoreCode) hintReplayStmt
theorem hintFinalReplayStmt_len : hintFinalReplayStmt.len = 660 := rfl

theorem hintFinalReplayStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase maxR oldCount : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase) (hr : r ≤ maxR)
    (target : Fin (Nj ^ r)) (hS : hintFamilySuccesses G coords beta Nj r v hPublic.positive = {target})
    (hData : HintScanReadOnly G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hSaved : state.mem (parent + 8) = r)
    (hAt : At P base (hintFinalReplayStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 660) state (fun k out => k ≤ 7 * r + 30 + (hintScanBodyTime G r + 2) * Nj ^ r ∧
      out.regs 1 = 1 ∧
      HintScanSolution G coords beta Nj r (hintTupleSet (hintOdometerEnumeration Nj r hPublic.positive target)) v out.mem ∧
      (∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i) ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem) := by
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hSpan := hPublic.fits.span
  obtain ⟨hRestoreAt, hReplayAt⟩ := At.seqStmt hAt
  change At P base hintFinalRestoreCode at hRestoreAt
  change At P (base + 7) (hintReplayStmt.compile (base + 7)) at hReplayAt
  have hRestore := hintFinalRestoreCode_spec E state parent outsideBase r (by omega)
    (hContext.trans hParent.symm) (by omega) (by omega) hData.outside_pointer hSaved
  generalize hR : runBlock hintFinalRestoreCode E state = sR at hRestore
  obtain ⟨hPcR, hMemR, hCtxR⟩ := hRestore
  have hRunR : (step P E)^[7] state = sR := by
    have hh := iterate_runBlock_of_at P E hintFinalRestoreCode state (by rwa [hPc])
      (by simp [hintFinalRestoreCode, hintScanParent, hintFinalRestoreTail, NoBranch, Instr.NoBranchI])
    rw [hR] at hh
    exact hh
  have hDataR : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v sR.mem := by
    rw [hMemR]; exact HintScanReadOnly.set_count hPublic hData r
  have hHeaderR : ∃ index, HintGaussHeader G index sR.mem := by
    obtain ⟨index, hHeader⟩ := hHeader
    refine ⟨index, ?_⟩
    intro i hi
    rw [hMemR, Function.update_of_ne (by omega : G.context + i ≠ outsideBase)]
    exact hHeader i hi
  have hFrameR : HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem sR.mem := by
    rw [hMemR]
    exact HintFinalFrame.of_controller (HintRowControllerFrame.set_count G parent outsideBase bitmapBase Nj maxR state.mem r)
  obtain ⟨_, kP, out, hRunP, hPcP, hCostP, hOne, hSolution, hArray, hCommon⟩ :=
    hintReplayStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E sR (base + 7)
      (hPublic.at_count r hr) target hS hDataR hHeaderR (hCtxR.trans hParent) hReplayAt (by omega)
  exact ⟨hPc, kP + 7, out, hintIterate_then (step P E) hRunR hRunP, by omega, by omega,
    hOne, hSolution, hArray, hCommon.readonly, hCommon.header, hCommon.context_value,
    hFrameR.trans (HintFinalFrame.of_scan hr hCommon.frame)⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalReplayStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintFinalReplay20261120

section -- Def_LinearSetReconciliation327_Main_HintWeightedBitmapLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintWeightedBitmapValue {h K : ℕ} (coords : Fin h → Fin K) (z : HintVec h) (j q : ℕ) : ℕ :=
  hintTruth (q ∈ ((hintGaussDone h j).filter (fun i => z i = 1)).image (fun i => (coords i).val))

theorem hintWeightedBitmapValue_zero {h K : ℕ} (coords : Fin h → Fin K) (z : HintVec h) (q : ℕ) :
    hintWeightedBitmapValue coords z 0 q = 0 := by simp [hintWeightedBitmapValue, hintGaussDone, hintTruth]

theorem hintWeightedBitmapValue_full {h K : ℕ} (coords : Fin h → Fin K) (z : HintVec h) (q : ℕ) :
    hintWeightedBitmapValue coords z h q = hintTruth (q ∈ hintBitsSet (fun i => (coords i).val) z) := by
  simp [hintWeightedBitmapValue, hintGaussDone_full, hintBitsSet]

theorem hintWeightedBitmapValue_current {h K : ℕ} (coords : Fin h → Fin K) (hInj : Function.Injective coords)
    (z : HintVec h) (j : Fin h) : hintWeightedBitmapValue coords z j.val (coords j).val = 0 := by
  classical
  have hNot : (coords j).val ∉ ((hintGaussDone h j.val).filter (fun i => z i = 1)).image (fun i => (coords i).val) := by
    intro hMem
    obtain ⟨i, hi, hEq⟩ := Finset.mem_image.mp hMem
    have hij : i = j := hInj (Fin.ext hEq)
    subst i
    have hDone := (Finset.mem_filter.mp hi).1
    simpa [hintGaussDone] using hDone
  simp [hintWeightedBitmapValue, hintTruth, hNot]

theorem hintWeightedBitmapValue_step {h K : ℕ} (coords : Fin h → Fin K) (hInj : Function.Injective coords)
    (z : HintVec h) (j : Fin h) (q : ℕ) :
    hintWeightedBitmapValue coords z (j.val + 1) q =
      if q = (coords j).val then (z j).val else hintWeightedBitmapValue coords z j.val q := by
  classical
  by_cases hz : z j = 1
  · have hSet : ((hintGaussDone h (j.val + 1)).filter (fun i => z i = 1)).image (fun i => (coords i).val) =
        insert (coords j).val (((hintGaussDone h j.val).filter (fun i => z i = 1)).image (fun i => (coords i).val)) := by
      rw [← hintGaussDone_succ j, Finset.filter_insert, if_pos hz, Finset.image_insert]
    unfold hintWeightedBitmapValue
    rw [hSet]
    by_cases hq : q = (coords j).val <;> simp [hintTruth, hq, hz] <;> rfl
  · have hz0 : z j = 0 := ((by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (z j)).resolve_right hz
    have hSet : ((hintGaussDone h (j.val + 1)).filter (fun i => z i = 1)).image (fun i => (coords i).val) =
        ((hintGaussDone h j.val).filter (fun i => z i = 1)).image (fun i => (coords i).val) := by
      rw [← hintGaussDone_succ j, Finset.filter_insert, if_neg hz]
    change hintTruth (q ∈ _) = _
    rw [hSet]
    change hintWeightedBitmapValue coords z j.val q = _
    by_cases hq : q = (coords j).val
    · subst q
      rw [if_pos rfl, hintWeightedBitmapValue_current coords hInj z j, hz0]
      rfl
    · rw [if_neg hq]

structure HintWeightedBitmapArgs (dest src weights count : ℕ) (state : RAMState) : Prop where
  dest_value : state.regs 4 = dest
  src_value : state.regs 5 = src
  weights_value : state.regs 7 = weights
  count_value : state.regs 6 = count
  one_value : state.regs 15 = 1

def hintWeightedBitmapBody : List Instr :=
  [.add 3 5 0, .load 8 3, .add 3 7 0, .load 9 3, .add 3 4 8, .store 3 9, .add 0 0 15]

theorem hintWeightedBitmapBody_spec (E : RAMEnv) (state : RAMState) (dest src weights count j coordinate : ℕ)
    (weight : ZMod 2) (hWord : 1 < 2 ^ E.W) (hSource : src + j < 2 ^ E.W)
    (hWeights : weights + j < 2 ^ E.W) (hDest : dest + coordinate < 2 ^ E.W)
    (hCoord : coordinate < 2 ^ E.W) (hNext : j + 1 < 2 ^ E.W)
    (hArgs : HintWeightedBitmapArgs dest src weights count state) (hCounter : state.regs 0 = j)
    (hRead : state.mem (src + j) = coordinate) (hWeight : state.mem (weights + j) = weight.val) :
    let out := runBlock hintWeightedBitmapBody E state
    out.pc = state.pc + 7 ∧ out.mem = Function.update state.mem (dest + coordinate) weight.val ∧
      out.regs 0 = j + 1 ∧ HintWeightedBitmapArgs dest src weights count out ∧ out.regs 14 = state.regs 14 := by
  obtain ⟨h4, h5, h7, h6, h15⟩ := hArgs
  have hWeightWord : weight.val < 2 ^ E.W := (ZMod.val_lt _).trans_le hWord
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintWeightedBitmapBody, runBlock, execInstr, h4, h5, h7, h6, h15, hCounter, hRead, hWeight,
      Nat.mod_eq_of_lt hSource, Nat.mod_eq_of_lt hWeights, Nat.mod_eq_of_lt hDest,
      Nat.mod_eq_of_lt hCoord, Nat.mod_eq_of_lt hNext, Nat.mod_eq_of_lt hWeightWord]


structure HintWeightedBitmapInv {h K : ℕ} (coords : Fin h → Fin K) (z : HintVec h)
    (dest src weights Nj j : ℕ) (original : ℕ → ℕ) (state : RAMState) : Prop where
  args : HintWeightedBitmapArgs dest src weights h state
  counter : state.regs 0 = j
  bitmap : ∀ q < Nj, state.mem (dest + q) = hintWeightedBitmapValue coords z j q
  frame : CRMemFrame dest (dest + Nj) original state.mem

theorem hintWeightedBitmapInv_step {h K : ℕ} (coords : Fin h → Fin K) (hInj : Function.Injective coords)
    (z : HintVec h) (j : Fin h) (E : RAMEnv) (state : RAMState) (dest src weights Nj : ℕ) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hSourceSpan : src + h < 2 ^ E.W) (hWeightsSpan : weights + h < 2 ^ E.W)
    (hDestSpan : dest + Nj ≤ 2 ^ E.W) (hSeparate : dest + Nj ≤ src) (hSeparateWeights : dest + Nj ≤ weights)
    (hValid : ∀ i, (coords i).val < Nj) (hHints : ∀ i : Fin h, original (src + i.val) = (coords i).val)
    (hWeights : ∀ i : Fin h, original (weights + i.val) = (z i).val)
    (hInv : HintWeightedBitmapInv coords z dest src weights Nj j.val original state) :
    let out := runBlock hintWeightedBitmapBody E state
    HintWeightedBitmapInv coords z dest src weights Nj (j.val + 1) original out := by
  have hRead : state.mem (src + j.val) = (coords j).val := by
    rw [hInv.frame _ (Or.inr (by omega))]; exact hHints j
  have hReadWeight : state.mem (weights + j.val) = (z j).val := by
    rw [hInv.frame _ (Or.inr (by omega))]; exact hWeights j
  have hSpec := hintWeightedBitmapBody_spec E state dest src weights h j.val (coords j).val (z j)
    hWord (by have := j.isLt; omega) (by have := j.isLt; omega)
    ((Nat.add_lt_add_left (hValid j) dest).trans_le hDestSpan) (by have := hValid j; omega)
    (by have := j.isLt; omega) hInv.args hInv.counter hRead hReadWeight
  generalize hMid : runBlock hintWeightedBitmapBody E state = out at hSpec
  obtain ⟨_, hMem, hCounter, hArgs, _⟩ := hSpec
  refine ⟨hArgs, hCounter, ?_, ?_⟩
  · intro q hq
    rw [hMem, hintWeightedBitmapValue_step coords hInj z j]
    by_cases hEq : q = (coords j).val
    · subst q; simp
    · rw [Function.update_of_ne (by omega : dest + q ≠ dest + (coords j).val), hInv.bitmap q hq, if_neg hEq]
  · intro addr hAway
    have hNe : addr ≠ dest + (coords j).val := by have := hValid j; rcases hAway with hBefore | hAfter <;> omega
    rw [hMem, Function.update_of_ne hNe, hInv.frame addr hAway]

theorem HintWeightedBitmapInv.pc {h K : ℕ} {coords : Fin h → Fin K} {z : HintVec h} {dest src weights Nj j : ℕ}
    {original : ℕ → ℕ} {state : RAMState} (hI : HintWeightedBitmapInv coords z dest src weights Nj j original state) (pc : ℕ) :
    HintWeightedBitmapInv coords z dest src weights Nj j original {state with pc := pc} :=
  ⟨⟨hI.args.dest_value, hI.args.src_value, hI.args.weights_value, hI.args.count_value, hI.args.one_value⟩,
    hI.counter, hI.bitmap, hI.frame⟩

theorem HintWeightedBitmapInv.test {h K : ℕ} {coords : Fin h → Fin K} {z : HintVec h} {dest src weights Nj j : ℕ}
    {original : ℕ → ℕ} {state : RAMState} (hI : HintWeightedBitmapInv coords z dest src weights Nj j original state) (E : RAMEnv) :
    HintWeightedBitmapInv coords z dest src weights Nj j original (runBlock (Cond.lt 2 0 6).code E state) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using hI.args.dest_value
  · simpa [Cond.code, runBlock, execInstr] using hI.args.src_value
  · simpa [Cond.code, runBlock, execInstr] using hI.args.weights_value
  · simpa [Cond.code, runBlock, execInstr] using hI.args.count_value
  · simpa [Cond.code, runBlock, execInstr] using hI.args.one_value
  · simpa [Cond.code, runBlock, execInstr] using hI.counter
  · simpa [Cond.code, runBlock, execInstr] using hI.bitmap
  · simpa [Cond.code, runBlock, execInstr] using hI.frame

def hintWeightedBitmapLoop : Stmt := .loop (.lt 2 0 6) (.code hintWeightedBitmapBody)
theorem hintWeightedBitmapLoop_len : hintWeightedBitmapLoop.len = 10 := rfl

theorem hintWeightedBitmapLoop_sem {h K : ℕ} (coords : Fin h → Fin K) (hInj : Function.Injective coords) (z : HintVec h)
    (dest src weights Nj : ℕ) (original : ℕ → ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hSourceSpan : src + h < 2 ^ E.W) (hWeightsSpan : weights + h < 2 ^ E.W)
    (hDestSpan : dest + Nj ≤ 2 ^ E.W) (hSeparate : dest + Nj ≤ src) (hSeparateWeights : dest + Nj ≤ weights)
    (hValid : ∀ i, (coords i).val < Nj) (hHints : ∀ i : Fin h, original (src + i.val) = (coords i).val)
    (hWeights : ∀ i : Fin h, original (weights + i.val) = (z i).val)
    (hInv : HintWeightedBitmapInv coords z dest src weights Nj 0 original state)
    (hAt : At P base (hintWeightedBitmapLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 10) state (fun k out => k ≤ 10 * h + 2 ∧
      (∀ q < Nj, out.mem (dest + q) = hintTruth (q ∈ hintBitsSet (fun i => (coords i).val) z)) ∧
      HintWeightedBitmapArgs dest src weights h out ∧ CRMemFrame dest (dest + Nj) original out.mem ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = h ∧
    HintWeightedBitmapInv coords z dest src weights Nj j original st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintWeightedBitmapBody := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hBitmap, hCtx⟩ := hI
    exact ⟨j, hJ, hBitmap.pc pc, hCtx⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 0 6).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, hBitmap, hCtx⟩ := hI
    refine ⟨j, hJ, hBitmap.test E, ?_⟩
    simpa [Cond.code, runBlock, execInstr] using hCtx
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 0 6).eval st := by
    intro left st hI
    obtain ⟨j, hJ, hBitmap, _⟩ := hI
    change st.regs 0 < st.regs 6
    rw [hBitmap.counter, hBitmap.args.count_value]; omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 6).eval st := by
    intro st hI
    obtain ⟨j, hJ, hBitmap, _⟩ := hI
    change ¬ st.regs 0 < st.regs 6
    rw [hBitmap.counter, hBitmap.args.count_value]; omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintWeightedBitmapBody).len) st
        (fun k out => k ≤ 7 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hBitmap, hContext⟩ := hI
    have hj : j < h := by omega
    let t : Fin h := ⟨j, hj⟩
    have hStep := hintWeightedBitmapInv_step coords hInj z t E st dest src weights Nj original
      hWord hSourceSpan hWeightsSpan hDestSpan hSeparate hSeparateWeights hValid hHints hWeights hBitmap
    have hCtx : (runBlock hintWeightedBitmapBody E st).regs 14 = st.regs 14 := by simp [hintWeightedBitmapBody, runBlock, execInstr]
    generalize hMid : runBlock hintWeightedBitmapBody E st = mid at hStep hCtx
    have hNative := Sem.block P E (base + 2) hintWeightedBitmapBody st hBodyAt
      (by simp [hintWeightedBitmapBody, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨hCost.le, j + 1, by omega, hStep, hCtx.trans hContext⟩
  have hInitial : I h state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintWeightedBitmapBody) hAt hWord I 7
    hIpc hItest hGo hStop hBody h state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, hFinal, hContext⟩ := hOut
  have hEnd : j = h := by omega
  rw [hEnd] at hFinal
  exact ⟨hCost, fun q hq => (hFinal.bitmap q hq).trans (hintWeightedBitmapValue_full coords z q),
    hFinal.args, hFinal.frame, hContext⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintWeightedBitmapLoop_sem
end -- Def_LinearSetReconciliation327_Main_HintWeightedBitmapLoop20261120

section -- Def_LinearSetReconciliation327_Main_HintBitmapUnionLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintBitmapUnionValue {h K : ℕ} (coords : Fin h → Fin K) (baseSet : Finset ℕ) (j q : ℕ) : ℕ :=
  hintTruth (q ∈ baseSet ∪ (hintGaussDone h j).image (fun i => (coords i).val))

theorem hintBitmapUnionValue_zero {h K : ℕ} (coords : Fin h → Fin K) (baseSet : Finset ℕ) (q : ℕ) :
    hintBitmapUnionValue coords baseSet 0 q = hintTruth (q ∈ baseSet) := by
  simp [hintBitmapUnionValue, hintGaussDone]

theorem hintBitmapUnionValue_full {h K : ℕ} (coords : Fin h → Fin K) (baseSet : Finset ℕ) (q : ℕ) :
    hintBitmapUnionValue coords baseSet h q = hintTruth (q ∈ baseSet ∪ Finset.univ.image (fun i => (coords i).val)) := by
  rw [hintBitmapUnionValue, hintGaussDone_full]

theorem hintBitmapUnionValue_step {h K : ℕ} (coords : Fin h → Fin K) (baseSet : Finset ℕ) (j : Fin h) (q : ℕ) :
    hintBitmapUnionValue coords baseSet (j.val + 1) q = if q = (coords j).val then 1 else hintBitmapUnionValue coords baseSet j.val q := by
  classical
  unfold hintBitmapUnionValue
  rw [← hintGaussDone_succ j, Finset.image_insert]
  by_cases hEq : q = (coords j).val <;> simp [hintTruth, hEq]

structure HintBitmapUnionInv {h K : ℕ} (coords : Fin h → Fin K) (baseSet : Finset ℕ) (dest src Nj j : ℕ)
    (original : ℕ → ℕ) (state : RAMState) : Prop where
  args : HintBitmapArgs dest src h state
  counter : state.regs 0 = j
  bitmap : ∀ q < Nj, state.mem (dest + q) = hintBitmapUnionValue coords baseSet j q
  frame : CRMemFrame dest (dest + Nj) original state.mem

theorem hintBitmapUnionInv_step {h K : ℕ} (coords : Fin h → Fin K) (baseSet : Finset ℕ) (j : Fin h)
    (E : RAMEnv) (state : RAMState) (dest src Nj : ℕ) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hSourceSpan : src + h < 2 ^ E.W) (hDestSpan : dest + Nj ≤ 2 ^ E.W)
    (hSeparate : dest + Nj ≤ src) (hValid : ∀ i, (coords i).val < Nj)
    (hHints : ∀ i : Fin h, original (src + i.val) = (coords i).val)
    (hInv : HintBitmapUnionInv coords baseSet dest src Nj j.val original state) :
    let out := runBlock hintBitmapBody E state
    HintBitmapUnionInv coords baseSet dest src Nj (j.val + 1) original out := by
  have hRead : state.mem (src + j.val) = (coords j).val := by
    rw [hInv.frame _ (Or.inr (by omega))]
    exact hHints j
  have hSpec := hintBitmapBody_spec E state dest src h j.val (coords j).val hWord
    (by have := j.isLt; omega) ((Nat.add_lt_add_left (hValid j) dest).trans_le hDestSpan)
    (by have := hValid j; omega) (by have := j.isLt; omega) hInv.args hInv.counter hRead
  generalize hMid : runBlock hintBitmapBody E state = out at hSpec
  obtain ⟨_, hMem, hCounter, hArgs, _⟩ := hSpec
  refine ⟨hArgs, hCounter, ?_, ?_⟩
  · intro q hq
    rw [hMem, hintBitmapUnionValue_step]
    by_cases hEq : q = (coords j).val
    · subst q
      simp
    · rw [Function.update_of_ne (by omega : dest + q ≠ dest + (coords j).val), hInv.bitmap q hq, if_neg hEq]
  · intro addr hAway
    have hNe : addr ≠ dest + (coords j).val := by have := hValid j; rcases hAway with hBefore | hAfter <;> omega
    rw [hMem, Function.update_of_ne hNe, hInv.frame addr hAway]

theorem HintBitmapUnionInv.pc {h K : ℕ} {coords : Fin h → Fin K} {baseSet : Finset ℕ} {dest src Nj j : ℕ}
    {original : ℕ → ℕ} {state : RAMState} (hI : HintBitmapUnionInv coords baseSet dest src Nj j original state) (pc : ℕ) :
    HintBitmapUnionInv coords baseSet dest src Nj j original {state with pc := pc} :=
  ⟨⟨hI.args.dest_value, hI.args.src_value, hI.args.count_value, hI.args.one_value⟩, hI.counter, hI.bitmap, hI.frame⟩

theorem HintBitmapUnionInv.test {h K : ℕ} {coords : Fin h → Fin K} {baseSet : Finset ℕ} {dest src Nj j : ℕ}
    {original : ℕ → ℕ} {state : RAMState} (hI : HintBitmapUnionInv coords baseSet dest src Nj j original state) (E : RAMEnv) :
    HintBitmapUnionInv coords baseSet dest src Nj j original (runBlock (Cond.lt 2 0 6).code E state) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using hI.args.dest_value
  · simpa [Cond.code, runBlock, execInstr] using hI.args.src_value
  · simpa [Cond.code, runBlock, execInstr] using hI.args.count_value
  · simpa [Cond.code, runBlock, execInstr] using hI.args.one_value
  · simpa [Cond.code, runBlock, execInstr] using hI.counter
  · simpa [Cond.code, runBlock, execInstr] using hI.bitmap
  · simpa [Cond.code, runBlock, execInstr] using hI.frame



theorem hintBitmapLoop_union_sem {h K : ℕ} (coords : Fin h → Fin K) (baseSet : Finset ℕ)
    (dest src Nj : ℕ) (original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hSourceSpan : src + h < 2 ^ E.W) (hDestSpan : dest + Nj ≤ 2 ^ E.W)
    (hSeparate : dest + Nj ≤ src) (hValid : ∀ i, (coords i).val < Nj)
    (hHints : ∀ i : Fin h, original (src + i.val) = (coords i).val)
    (hInv : HintBitmapUnionInv coords baseSet dest src Nj 0 original state)
    (hAt : At P base (hintBitmapLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 8) state (fun k out => k ≤ 8 * h + 2 ∧
      (∀ q < Nj, out.mem (dest + q) = hintTruth (q ∈ baseSet ∪ Finset.univ.image (fun i => (coords i).val))) ∧
      HintBitmapArgs dest src h out ∧ CRMemFrame dest (dest + Nj) original out.mem ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = h ∧
    HintBitmapUnionInv coords baseSet dest src Nj j original st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintBitmapBody := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hBitmap, hCtx⟩ := hI
    exact ⟨j, hJ, hBitmap.pc pc, hCtx⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 0 6).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, hBitmap, hCtx⟩ := hI
    refine ⟨j, hJ, hBitmap.test E, ?_⟩
    simpa [Cond.code, runBlock, execInstr] using hCtx
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 0 6).eval st := by
    intro left st hI
    obtain ⟨j, hJ, hBitmap, _⟩ := hI
    change st.regs 0 < st.regs 6
    rw [hBitmap.counter, hBitmap.args.count_value]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 6).eval st := by
    intro st hI
    obtain ⟨j, hJ, hBitmap, _⟩ := hI
    change ¬ st.regs 0 < st.regs 6
    rw [hBitmap.counter, hBitmap.args.count_value]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintBitmapBody).len) st
        (fun k out => k ≤ 5 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hBitmap, hContext⟩ := hI
    have hj : j < h := by omega
    let t : Fin h := ⟨j, hj⟩
    have hStep := hintBitmapUnionInv_step coords baseSet t E st dest src Nj original hWord hSourceSpan hDestSpan hSeparate hValid hHints hBitmap
    have hCtx : (runBlock hintBitmapBody E st).regs 14 = st.regs 14 := by simp [hintBitmapBody, runBlock, execInstr]
    generalize hMid : runBlock hintBitmapBody E st = mid at hStep hCtx
    have hNative := Sem.block P E (base + 2) hintBitmapBody st hBodyAt
      (by simp [hintBitmapBody, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨hCost.le, j + 1, by omega, hStep, hCtx.trans hContext⟩
  have hInitial : I h state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintBitmapBody) hAt hWord I 5
    hIpc hItest hGo hStop hBody h state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, hFinal, hContext⟩ := hOut
  have hEnd : j = h := by omega
  rw [hEnd] at hFinal
  refine ⟨hCost, ?_, hFinal.args, hFinal.frame, hContext⟩
  simpa only [hintBitmapUnionValue_full] using hFinal.bitmap


end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintBitmapLoop_union_sem
end -- Def_LinearSetReconciliation327_Main_HintBitmapUnionLoop20261120

section -- Def_LinearSetReconciliation327_Main_HintOutputSetup20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintOutputFields : List (Fin 16 × ℕ) := [(5,9),(7,6),(6,1)]
def hintOutputConstants : List Instr := [.imm 15 1, .imm 0 0]
def hintWeightedOutputSetup : List Instr :=
  hintScanParent ++ hintParentLoad 4 1 ++ hintLoadFields hintOutputFields ++ hintOutputConstants

theorem hintWeightedOutputSetup_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState) (parent bitmapBase index : ℕ)
    (hParent : parent + 16 = G.context) (hContext : state.regs 14 = G.context)
    (hHeader : HintGaussHeader G index state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hBitmap : bitmapBase < 2 ^ E.W) (hReadBitmap : state.mem (parent + 1) = bitmapBase) :
    let out := runBlock hintWeightedOutputSetup E state
    out.pc = state.pc + 16 ∧ out.mem = state.mem ∧
      HintWeightedBitmapArgs bitmapBase G.hintList G.kernelVec G.hints out ∧ out.regs 0 = 0 ∧ out.regs 14 = G.context := by
  have hSpan := hFits.span
  have hWord : 1 < 2 ^ E.W := by omega
  have hP := hintScanParent_spec E state parent (by omega) (hContext.trans hParent.symm)
  generalize hPExec : runBlock hintScanParent E state = sP at hP
  obtain ⟨hPcP, hMemP, hPointerP, hCtxP⟩ := hP
  have hB := hintParentLoad_spec E sP parent 1 4 hPointerP (by omega) (by decide) (by decide)
  generalize hBExec : runBlock (hintParentLoad 4 1) E sP = sB at hB
  obtain ⟨hPcB, hMemB, hValueB, _, hCtxB, _⟩ := hB
  have h4B : sB.regs 4 = bitmapBase := by rw [hValueB, hMemP, hReadBitmap, Nat.mod_eq_of_lt hBitmap]
  have hCtxB' : sB.regs 14 = G.context := hCtxB.trans (hCtxP.trans hParent)
  have hValid : ∀ pair ∈ hintOutputFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintOutputFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by omega⟩
  have hLoad := hintLoadFields_spec E G.context hintOutputFields sB hCtxB' hValid
  generalize hLExec : runBlock (hintLoadFields hintOutputFields) E sB = sL at hLoad
  have hV9 : sB.mem (G.context + 9) % 2 ^ E.W = G.hintList := by
    rw [hMemB, hMemP, hHeader 9 (by decide)]; exact Nat.mod_eq_of_lt (hFits.values 9 (by decide))
  have hV6 : sB.mem (G.context + 6) % 2 ^ E.W = G.kernelVec := by
    rw [hMemB, hMemP, hHeader 6 (by decide)]; exact Nat.mod_eq_of_lt (hFits.values 6 (by decide))
  have hV1 : sB.mem (G.context + 1) % 2 ^ E.W = G.hints := by
    rw [hMemB, hMemP, hHeader 1 (by decide)]; exact Nat.mod_eq_of_lt (hFits.values 1 (by decide))
  have h4L : sL.regs 4 = bitmapBase := by
    have hh := hLoad.2.2.2 4 (by decide)
    simpa [hintOutputFields, hintLoadedValue, h4B] using hh
  have h5L : sL.regs 5 = G.hintList := by
    have hh := hLoad.2.2.2 5 (by decide)
    simpa [hintOutputFields, hintLoadedValue, hV9, hV6, hV1] using hh
  have h7L : sL.regs 7 = G.kernelVec := by
    have hh := hLoad.2.2.2 7 (by decide)
    simpa [hintOutputFields, hintLoadedValue, hV9, hV6, hV1] using hh
  have h6L : sL.regs 6 = G.hints := by
    have hh := hLoad.2.2.2 6 (by decide)
    simpa [hintOutputFields, hintLoadedValue, hV9, hV6, hV1] using hh
  have hTail : let out := runBlock hintOutputConstants E sL
      out.pc = sL.pc + 2 ∧ out.mem = sL.mem ∧
        HintWeightedBitmapArgs bitmapBase G.hintList G.kernelVec G.hints out ∧ out.regs 0 = 0 ∧ out.regs 14 = G.context := by
    refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp [hintOutputConstants, runBlock, execInstr, h4L, h5L, h7L, h6L, hLoad.2.2.1, Nat.mod_eq_of_lt hWord]
  generalize hCExec : runBlock hintOutputConstants E sL = out at hTail
  obtain ⟨hPcC, hMemC, hArgsC, hCounterC, hCtxC⟩ := hTail
  have hRun : runBlock hintWeightedOutputSetup E state = out := by
    rw [hintWeightedOutputSetup, runBlock_append, runBlock_append, runBlock_append, hPExec, hBExec, hLExec, hCExec]
  have hPcL : sL.pc = sB.pc + 9 := by simpa [hintOutputFields] using hLoad.1
  rw [hRun]
  exact ⟨by omega, hMemC.trans (hLoad.2.1.trans (hMemB.trans hMemP)), hArgsC, hCounterC, hCtxC⟩

def hintOutsideOutputTail : List Instr := [.load 6 5, .imm 15 1, .add 5 5 15, .imm 0 0]
def hintOutsideOutputSetup : List Instr :=
  hintScanParent ++ hintParentLoad 4 1 ++ hintParentLoad 5 0 ++ hintOutsideOutputTail

theorem hintOutsideOutputSetup_spec (E : RAMEnv) (state : RAMState) (parent bitmapBase outsideBase r : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hBitmap : bitmapBase < 2 ^ E.W) (hArray : outsideBase + 1 < 2 ^ E.W) (hR : r < 2 ^ E.W)
    (hReadBitmap : state.mem (parent + 1) = bitmapBase) (hReadPointer : state.mem parent = outsideBase)
    (hCount : state.mem outsideBase = r) :
    let out := runBlock hintOutsideOutputSetup E state
    out.pc = state.pc + 12 ∧ out.mem = state.mem ∧ HintBitmapArgs bitmapBase (outsideBase + 1) r out ∧
      out.regs 0 = 0 ∧ out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hBase : outsideBase < 2 ^ E.W := by omega
  have hP := hintScanParent_spec E state parent hEnd hContext
  generalize hPExec : runBlock hintScanParent E state = sP at hP
  obtain ⟨hPcP, hMemP, hPointerP, hCtxP⟩ := hP
  have hB := hintParentLoad_spec E sP parent 1 4 hPointerP (by omega) (by decide) (by decide)
  generalize hBExec : runBlock (hintParentLoad 4 1) E sP = sB at hB
  obtain ⟨hPcB, hMemB, hValueB, hPointerB, hCtxB, _⟩ := hB
  have h4B : sB.regs 4 = bitmapBase := by rw [hValueB, hMemP, hReadBitmap, Nat.mod_eq_of_lt hBitmap]
  have hO := hintParentLoad_spec E sB parent 0 5 hPointerB (by omega) (by decide) (by decide)
  generalize hOExec : runBlock (hintParentLoad 5 0) E sB = sO at hO
  obtain ⟨hPcO, hMemO, hValueO, _, hCtxO, hRegsO⟩ := hO
  have h5O : sO.regs 5 = outsideBase := by rw [hValueO, hMemB, hMemP, Nat.add_zero, hReadPointer, Nat.mod_eq_of_lt hBase]
  have h4O : sO.regs 4 = bitmapBase := (hRegsO 4 (by decide) (by decide)).trans h4B
  have hCountO : sO.mem outsideBase = r := by rw [hMemO, hMemB, hMemP]; exact hCount
  have h14O : sO.regs 14 = parent + 16 := hCtxO.trans (hCtxB.trans hCtxP)
  have hTail : let out := runBlock hintOutsideOutputTail E sO
      out.pc = sO.pc + 4 ∧ out.mem = sO.mem ∧ HintBitmapArgs bitmapBase (outsideBase + 1) r out ∧
        out.regs 0 = 0 ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp [hintOutsideOutputTail, runBlock, execInstr, h4O, h5O, hCountO, h14O,
        Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hArray]
  generalize hTExec : runBlock hintOutsideOutputTail E sO = out at hTail
  obtain ⟨hPcT, hMemT, hArgsT, hCounterT, hCtxT⟩ := hTail
  have hRun : runBlock hintOutsideOutputSetup E state = out := by
    rw [hintOutsideOutputSetup, runBlock_append, runBlock_append, runBlock_append, hPExec, hBExec, hOExec, hTExec]
  rw [hRun]
  exact ⟨by omega, hMemT.trans (hMemO.trans (hMemB.trans hMemP)), hArgsT, hCounterT, hCtxT⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintWeightedOutputSetup_spec
#print axioms LinearSetReconciliation327.Main.hintOutsideOutputSetup_spec
end -- Def_LinearSetReconciliation327_Main_HintOutputSetup20261120

section -- Def_LinearSetReconciliation327_Main_HintBitmapClear20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintBitmapClearStmt : Stmt := .seq (.code hintBitmapClearPrep) hintFillStmt
theorem hintBitmapClearStmt_len : hintBitmapClearStmt.len = 19 := rfl

theorem hintBitmapClearStmt_sem (parent bitmapBase Nj : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hBitmap : bitmapBase < 2 ^ E.W) (hNj : Nj < 2 ^ E.W) (hSpan : bitmapBase + Nj ≤ 2 ^ E.W)
    (hReadBitmap : state.mem (parent + 1) = bitmapBase) (hReadNj : state.mem (parent + 2) = Nj)
    (hAt : At P base (hintBitmapClearStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 19) state (fun k out => k ≤ 7 * Nj + 14 ∧
      (∀ q < Nj, out.mem (bitmapBase + q) = 0) ∧
      CRMemFrame bitmapBase (bitmapBase + Nj) state.mem out.mem ∧ out.regs 14 = parent + 16) := by
  have hWord : 1 < 2 ^ E.W := by omega
  obtain ⟨hPrepAt, hFillAt⟩ := At.seqStmt hAt
  change At P base hintBitmapClearPrep at hPrepAt
  change At P (base + 11) (hintFillStmt.compile (base + 11)) at hFillAt
  have hPrep := hintBitmapClearPrep_spec E state parent bitmapBase Nj hEnd hContext hBitmap hNj hReadBitmap hReadNj
  generalize hP : runBlock hintBitmapClearPrep E state = sP at hPrep
  obtain ⟨hPcP, hMemP, hArgsP, _, hCtxP⟩ := hPrep
  have hRunP : (step P E)^[11] state = sP := by
    have hh := iterate_runBlock_of_at P E hintBitmapClearPrep state (by rwa [hPc])
      (by simp [hintBitmapClearPrep, hintScanParent, hintParentLoad, hintBitmapConstants, NoBranch, Instr.NoBranchI])
    rw [hP] at hh
    exact hh
  obtain ⟨_, kF, out, hRunF, hPcF, hCostF, _, hMemF, _, hFrameF, hRegsF⟩ :=
    hintFillStmt_sem P E sP bitmapBase 1 Nj (base + 11) 0 hWord hNj
      (by intro q hq; simp only [Nat.mul_one]; omega) hFillAt (by rw [hPcP, hPc]) hArgsP
  have hFrame : CRMemFrame bitmapBase (bitmapBase + Nj) state.mem out.mem := by
    intro addr hAway
    have hNot : addr ∉ hintFillPositions bitmapBase 1 Nj := by
      intro hIn
      obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp hIn
      have hQ : q < Nj := Finset.mem_range.mp hq
      simp only [Nat.mul_one] at hEq
      rcases hAway with hBefore | hAfter <;> omega
    exact (hFrameF addr hNot).trans (congrFun hMemP addr)
  refine ⟨hPc, kF + 11, out, hintIterate_then (step P E) hRunP hRunF, by omega, by omega, ?_, hFrame, ?_⟩
  · intro q hq
    have hIn : bitmapBase + q ∈ hintFillPositions bitmapBase 1 Nj :=
      Finset.mem_image.mpr ⟨q, Finset.mem_range.mpr hq, by simp⟩
    rw [hMemF]
    simp [hintFillMem, hIn]
  · exact (hRegsF 14 (by decide) (by decide) (by decide)).trans hCtxP

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintBitmapClearStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintBitmapClear20261120

section -- Def_LinearSetReconciliation327_Main_HintCandidateBitmap20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintCandidateBitmapStmt : Stmt := .seq hintBitmapClearStmt (.seq (.code hintWeightedOutputSetup)
  (.seq hintWeightedBitmapLoop (.seq (.code hintOutsideOutputSetup) (.seq hintBitmapLoop (.code hintReplayFinish)))))
theorem hintCandidateBitmapStmt_len : hintCandidateBitmapStmt.len = 66 := rfl

theorem hintCandidateBitmapStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase maxR : ℕ) (v : HintVec G.rows) (outside : Fin r → Fin Nj) (z : HintVec G.hints)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase) (hr : r ≤ maxR)
    (hInput : HintRowInput G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hZ : ∀ t : Fin G.hints, state.mem (G.kernelVec + t.val) = (z t).val)
    (hOutside : ∀ i : Fin r, state.mem (outsideBase + 1 + i.val) = (outside i).val)
    (hAt : At P base (hintCandidateBitmapStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 66) state (fun k out => k ≤ 7 * Nj + 10 * G.hints + 8 * r + 47 ∧ out.regs 1 = 1 ∧
      (∀ q < Nj, out.mem (bitmapBase + q) =
        hintTruth (q ∈ hintBitsSet (fun t => (coords t).val) z ∪ hintTupleSet outside)) ∧
      HintRowInput G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      CRMemFrame bitmapBase (bitmapBase + Nj) state.mem out.mem) := by
  have hSource := hPublic.source
  have hParent := hPublic.parent_eq
  have hOutSpan := hPublic.outside_span
  have hBitmapSpan := hPublic.bitmap_span
  have hSpan := hPublic.fits.span
  have hReserve := hPublic.reserve
  have hKernel := hPublic.geometry.kernelVec_before
  have hGaussSpan := hPublic.geometry.span
  have h0 := hPublic.geometry.residual_before
  have h1 := hPublic.geometry.lift_before
  have h2 := hPublic.geometry.column_before
  have h3 := hPublic.geometry.residualVec_before
  have hWord : 1 < 2 ^ E.W := by omega
  have hNjWord : Nj < 2 ^ E.W := hPublic.bucket_bound.trans_lt (hPublic.fits.values 12 (by decide))
  obtain ⟨index, hHead⟩ := hHeader
  obtain ⟨hClearAt, hRest1⟩ := At.seqStmt hAt
  change At P base (hintBitmapClearStmt.compile base) at hClearAt
  obtain ⟨hSetupWAt, hRest2⟩ := At.seqStmt hRest1
  change At P (base + 19) hintWeightedOutputSetup at hSetupWAt
  obtain ⟨hWeightedAt, hRest3⟩ := At.seqStmt hRest2
  change At P (base + 35) (hintWeightedBitmapLoop.compile (base + 35)) at hWeightedAt
  obtain ⟨hSetupOAt, hRest4⟩ := At.seqStmt hRest3
  change At P (base + 45) hintOutsideOutputSetup at hSetupOAt
  obtain ⟨hUnionAt, hFinishAt⟩ := At.seqStmt hRest4
  change At P (base + 57) (hintBitmapLoop.compile (base + 57)) at hUnionAt
  change At P (base + 65) hintReplayFinish at hFinishAt
  obtain ⟨_, kC, sC, hRunC, hPcC, hCostC, hZeroC, hFrameC, hCtxC⟩ :=
    hintBitmapClearStmt_sem parent bitmapBase Nj P E state base (by omega) (hContext.trans hParent.symm)
      (by omega) hNjWord (by omega) hInput.bitmap_pointer hInput.radix hClearAt hPc
  have hInputC := HintRowInput.frame (hPublic.at_count r hr) hInput hFrameC
  have hHeaderC : HintGaussHeader G index sC.mem := by
    intro i hi; rw [hFrameC _ (Or.inr (by omega))]; exact hHead i hi
  have hSetupW := hintWeightedOutputSetup_spec E G sC parent bitmapBase index hParent (hCtxC.trans hParent)
    hHeaderC hPublic.fits (by omega) hInputC.bitmap_pointer
  generalize hW : runBlock hintWeightedOutputSetup E sC = sW at hSetupW
  obtain ⟨hPcW, hMemW, hArgsW, hCounterW, hCtxW⟩ := hSetupW
  have hRunW : (step P E)^[16] sC = sW := by
    have hh := iterate_runBlock_of_at P E hintWeightedOutputSetup sC (by rwa [hPcC])
      (by simp [hintWeightedOutputSetup, hintScanParent, hintParentLoad, hintLoadFields,
          hintLoadField, hintOutputFields, hintOutputConstants, NoBranch, Instr.NoBranchI])
    rw [hW] at hh
    exact hh
  have hInvW : HintWeightedBitmapInv coords z bitmapBase G.hintList G.kernelVec Nj 0 state.mem sW := by
    refine ⟨hArgsW, hCounterW, ?_, ?_⟩
    · intro q hq
      rw [hMemW, hZeroC q hq, hintWeightedBitmapValue_zero]
    · rw [hMemW]; exact hFrameC
  obtain ⟨_, kH, sH, hRunH, hPcH, hCostH, hBitmapH, _, hFrameH, hCtxH⟩ :=
    hintWeightedBitmapLoop_sem coords hPublic.injective z bitmapBase G.hintList G.kernelVec Nj state.mem
      P E sW (base + 35) hWord (by omega) (by omega) (by omega) (by omega) (by omega)
      hPublic.hint_valid hInput.hints hZ hInvW hWeightedAt (by omega)
  have hInputH := HintRowInput.frame (hPublic.at_count r hr) hInput hFrameH
  have hSetupO := hintOutsideOutputSetup_spec E sH parent bitmapBase outsideBase r (by omega)
    ((hCtxH.trans hCtxW).trans hParent.symm) (by omega) (by omega) (by omega)
    hInputH.bitmap_pointer hInputH.outside_pointer hInputH.outside_count
  generalize hO : runBlock hintOutsideOutputSetup E sH = sO at hSetupO
  obtain ⟨hPcO, hMemO, hArgsO, hCounterO, hCtxO⟩ := hSetupO
  have hRunO : (step P E)^[12] sH = sO := by
    have hh := iterate_runBlock_of_at P E hintOutsideOutputSetup sH (by rwa [hPcH])
      (by simp [hintOutsideOutputSetup, hintScanParent, hintParentLoad, hintOutsideOutputTail, NoBranch, Instr.NoBranchI])
    rw [hO] at hh
    exact hh
  have hInvO : HintBitmapUnionInv outside (hintBitsSet (fun t => (coords t).val) z)
      bitmapBase (outsideBase + 1) Nj 0 state.mem sO := by
    refine ⟨hArgsO, hCounterO, ?_, ?_⟩
    · intro q hq
      rw [hMemO, hBitmapH q hq, hintBitmapUnionValue_zero]
    · rw [hMemO]; exact hFrameH
  obtain ⟨_, kL, sL, hRunL, hPcL, hCostL, hBitmapL, _, hFrameL, hCtxL⟩ :=
    hintBitmapLoop_union_sem outside (hintBitsSet (fun t => (coords t).val) z) bitmapBase (outsideBase + 1) Nj state.mem
      P E sO (base + 57) hWord (by omega) (by omega) (by omega) (fun i => (outside i).isLt) hOutside hInvO hUnionAt (by omega)
  have hFinish : let out := runBlock hintReplayFinish E sL
      out.pc = sL.pc + 1 ∧ out.mem = sL.mem ∧ out.regs 1 = 1 ∧ out.regs 14 = sL.regs 14 := by
    refine ⟨?_, rfl, ?_, ?_⟩ <;> simp [hintReplayFinish, runBlock, execInstr, Nat.mod_eq_of_lt hWord]
  generalize hF : runBlock hintReplayFinish E sL = out at hFinish
  obtain ⟨hPcF, hMemF, hOneF, hCtxF⟩ := hFinish
  have hRunF : (step P E)^[1] sL = out := by
    have hh := iterate_runBlock_of_at P E hintReplayFinish sL (by rwa [hPcL])
      (by simp [hintReplayFinish, NoBranch, Instr.NoBranchI])
    rw [hF] at hh
    exact hh
  have hFrameOut : CRMemFrame bitmapBase (bitmapBase + Nj) state.mem out.mem := by rw [hMemF]; exact hFrameL
  have hInputOut := HintRowInput.frame (hPublic.at_count r hr) hInput hFrameOut
  have hHeaderOut : ∃ idx, HintGaussHeader G idx out.mem := by
    refine ⟨index, ?_⟩
    intro i hi; rw [hFrameOut _ (Or.inr (by omega))]; exact hHead i hi
  refine ⟨hPc, 1 + (kL + (12 + (kH + (16 + kC)))), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) (hintIterate_then (step P E)
      (hintIterate_then (step P E) (hintIterate_then (step P E) hRunC hRunW) hRunH) hRunO) hRunL) hRunF,
    by omega, by omega, hOneF, ?_, hInputOut, hHeaderOut, hCtxF.trans (hCtxL.trans (hCtxO.trans hParent)), hFrameOut⟩
  intro q hq
  rw [hMemF]
  exact hBitmapL q hq

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCandidateBitmapStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintCandidateBitmap20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalCandidate20261120
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
end -- Def_LinearSetReconciliation327_Main_HintFinalCandidate20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalRecover20261120
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
end -- Def_LinearSetReconciliation327_Main_HintFinalRecover20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalAux20261120
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
end -- Def_LinearSetReconciliation327_Main_HintFinalAux20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalGuard20261120
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
end -- Def_LinearSetReconciliation327_Main_HintFinalGuard20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalResult20261120
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
end -- Def_LinearSetReconciliation327_Main_HintFinalResult20261120

section -- Def_LinearSetReconciliation327_Main_HintRowFinal20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRowFinal20261120

section -- Def_LinearSetReconciliation327_Main_HintTranscript20261120
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
end -- Def_LinearSetReconciliation327_Main_HintTranscript20261120

section -- Def_LinearSetReconciliation327_Main_HintGatherBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintGatherArgs (dest source rows row node count : ℕ) (s : RAMState) : Prop where
  dest_value : s.regs 4 = dest
  source_value : s.regs 5 = source
  rows_value : s.regs 7 = rows
  row_value : s.regs 10 = row
  node_value : s.regs 12 = node
  count_value : s.regs 6 = count
  one_value : s.regs 15 = 1

def hintGatherHead : List Instr :=
  [.mul 8 0 7, .add 8 8 10, .qPermInv 8 12 8, .add 8 5 8, .load 9 8]
def hintGatherTail : List Instr :=
  [.add 3 4 1, .store 3 0, .add 1 1 9, .add 0 0 15]
def hintGatherBody : List Instr := hintGatherHead ++ hintGatherTail

theorem hintGatherHead_spec (E : RAMEnv) (s : RAMState)
    (dest source rows row node count q coord flag : ℕ)
    (hArgs : HintGatherArgs dest source rows row node count s) (hQ : s.regs 0 = q)
    (hPos : row + q * rows < 2 ^ E.W) (hSource : source + coord < 2 ^ E.W)
    (hFlag : flag < 2 ^ E.W) (hInv : E.permInv node (row + q * rows) = coord)
    (hRead : s.mem (source + coord) = flag) :
    let out := runBlock hintGatherHead E s
    out.pc = s.pc + 5 ∧ out.mem = s.mem ∧ out.regs 9 = flag ∧
      (∀ r : Fin 16, r ≠ 8 → r ≠ 9 → out.regs r = s.regs r) := by
  have hMul : q * rows < 2 ^ E.W := by omega
  have hAddr : q * rows + row < 2 ^ E.W := by omega
  have hCoord : coord < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [hintGatherHead, runBlock, execInstr]
  · have hLookup : E.permInv node (q * rows + row) = coord := by simpa [Nat.add_comm] using hInv
    simp [hintGatherHead, runBlock, execInstr, hQ, hArgs.rows_value, hArgs.row_value,
      hArgs.node_value, hArgs.source_value, hLookup, hRead, Nat.mod_eq_of_lt hMul,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hCoord, Nat.mod_eq_of_lt hSource,
      Nat.mod_eq_of_lt hFlag]
  · intro r h8 h9
    simp [hintGatherHead, runBlock, execInstr, h8, h9]

theorem hintGatherTail_spec (E : RAMEnv) (s : RAMState)
    (dest source rows row node count q used flag : ℕ)
    (hArgs : HintGatherArgs dest source rows row node count s)
    (hQ : s.regs 0 = q) (hUsed : s.regs 1 = used) (hFlag : s.regs 9 = flag)
    (hDest : dest + used < 2 ^ E.W) (hNext : q + 1 < 2 ^ E.W) (hUsedNext : used + flag < 2 ^ E.W) :
    let out := runBlock hintGatherTail E s
    out.pc = s.pc + 4 ∧ out.mem = Function.update s.mem (dest + used) q ∧
      out.regs 0 = q + 1 ∧ out.regs 1 = used + flag ∧
      (∀ r : Fin 16, r ≠ 0 → r ≠ 1 → r ≠ 3 → out.regs r = s.regs r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hintGatherTail, runBlock, execInstr]
  · simp [hintGatherTail, runBlock, execInstr, hArgs.dest_value, hUsed, hQ, Nat.mod_eq_of_lt hDest]
  · simp [hintGatherTail, runBlock, execInstr, hQ, hArgs.one_value, Nat.mod_eq_of_lt hNext]
  · simp [hintGatherTail, runBlock, execInstr, hUsed, hFlag, Nat.mod_eq_of_lt hUsedNext]
  · intro r h0 h1 h3
    simp [hintGatherTail, runBlock, execInstr, h0, h1, h3]

theorem hintGatherBody_spec (E : RAMEnv) (s : RAMState)
    (dest source rows row node count q used coord flag : ℕ)
    (hArgs : HintGatherArgs dest source rows row node count s)
    (hQ : s.regs 0 = q) (hUsed : s.regs 1 = used)
    (hPos : row + q * rows < 2 ^ E.W) (hSource : source + coord < 2 ^ E.W)
    (hFlag : flag < 2 ^ E.W) (hInv : E.permInv node (row + q * rows) = coord)
    (hRead : s.mem (source + coord) = flag)
    (hDest : dest + used < 2 ^ E.W) (hNext : q + 1 < 2 ^ E.W) (hUsedNext : used + flag < 2 ^ E.W) :
    let out := runBlock hintGatherBody E s
    out.pc = s.pc + 9 ∧ out.mem = Function.update s.mem (dest + used) q ∧
      out.regs 0 = q + 1 ∧ out.regs 1 = used + flag ∧
      HintGatherArgs dest source rows row node count out ∧ out.regs 14 = s.regs 14 := by
  have hHead := hintGatherHead_spec E s dest source rows row node count q coord flag
    hArgs hQ hPos hSource hFlag hInv hRead
  generalize hHeadExec : runBlock hintGatherHead E s = mid at hHead
  obtain ⟨hPcH, hMemH, hFlagH, hRegsH⟩ := hHead
  have hPreserveH (r : Fin 16) (hr : r ≠ 8) (hr' : r ≠ 9) (value : ℕ)
      (h : s.regs r = value) : mid.regs r = value := (hRegsH r hr hr').trans h
  have hArgsH : HintGatherArgs dest source rows row node count mid :=
    ⟨hPreserveH 4 (by decide) (by decide) _ hArgs.dest_value,
      hPreserveH 5 (by decide) (by decide) _ hArgs.source_value,
      hPreserveH 7 (by decide) (by decide) _ hArgs.rows_value,
      hPreserveH 10 (by decide) (by decide) _ hArgs.row_value,
      hPreserveH 12 (by decide) (by decide) _ hArgs.node_value,
      hPreserveH 6 (by decide) (by decide) _ hArgs.count_value,
      hPreserveH 15 (by decide) (by decide) _ hArgs.one_value⟩
  have hTail := hintGatherTail_spec E mid dest source rows row node count q used flag hArgsH
    (hPreserveH 0 (by decide) (by decide) _ hQ) (hPreserveH 1 (by decide) (by decide) _ hUsed)
    hFlagH hDest hNext hUsedNext
  generalize hTailExec : runBlock hintGatherTail E mid = out at hTail
  obtain ⟨hPcT, hMemT, hQOut, hUsedOut, hRegsT⟩ := hTail
  have hPreserveT (r : Fin 16) (h0 : r ≠ 0) (h1 : r ≠ 1) (h3 : r ≠ 3) (value : ℕ)
      (h : mid.regs r = value) : out.regs r = value := (hRegsT r h0 h1 h3).trans h
  have hRun : runBlock hintGatherBody E s = out := by
    rw [hintGatherBody, runBlock_append, hHeadExec, hTailExec]
  rw [hRun]
  refine ⟨by omega, by rw [hMemT, hMemH], hQOut, hUsedOut, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hPreserveT 4 (by decide) (by decide) (by decide) _ hArgsH.dest_value
  · exact hPreserveT 5 (by decide) (by decide) (by decide) _ hArgsH.source_value
  · exact hPreserveT 7 (by decide) (by decide) (by decide) _ hArgsH.rows_value
  · exact hPreserveT 10 (by decide) (by decide) (by decide) _ hArgsH.row_value
  · exact hPreserveT 12 (by decide) (by decide) (by decide) _ hArgsH.node_value
  · exact hPreserveT 6 (by decide) (by decide) (by decide) _ hArgsH.count_value
  · exact hPreserveT 15 (by decide) (by decide) (by decide) _ hArgsH.one_value
  · exact hPreserveT 14 (by decide) (by decide) (by decide) _ (hRegsH 14 (by decide) (by decide))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGatherBody_spec
end -- Def_LinearSetReconciliation327_Main_HintGatherBody20261120


