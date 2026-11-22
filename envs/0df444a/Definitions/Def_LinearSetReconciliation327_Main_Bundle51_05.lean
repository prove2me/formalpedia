-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_05
-- name    : LinearSetReconciliation327_Main_Bundle51_05
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T13:25:30.449854+00:00
-- url     : https://prove2.me/theorems/82e3495a-3b6a-4af5-8064-58292431df0f
-- title:
--   LinearSetReconciliation327 — Bundle51_05
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_05` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_04

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_05
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowPrecise20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowWait20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowEligible20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowAdvance20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowControl20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowOuterBody20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowGuard20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowOuterLoop20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowFirst20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowSearch20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowPredictAlign20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowPredict20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalClassExists20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalRaw20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalCap20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalChoose20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalAccumulate20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalSaved20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalFrame20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinalAccInvariant20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintRowPrecise20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def HintRowMutationFrame (G : HintGaussArea) (parent outsideBase bitmapBase Nj r : ℕ)
    (original memory : ℕ → ℕ) : Prop :=
  ∀ addr, (addr < bitmapBase ∨ bitmapBase + Nj ≤ addr) →
    (addr < outsideBase + 1 ∨ outsideBase + 1 + r ≤ addr) → addr ≠ parent + 3 →
    (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
    (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → memory addr = original addr

theorem HintRowMutationFrame.parent {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj r parent outsideBase bitmapBase : ℕ} {original memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (hFrame : HintRowMutationFrame G parent outsideBase bitmapBase Nj r original memory)
    (i : ℕ) (hi : 4 ≤ i) (hi' : i < 16) : memory (parent + i) = original (parent + i) := by
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  have hParent := hPublic.parent_eq
  exact hFrame _ (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))

theorem hintRowFamilyStmt_precise_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintRowFamilyStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1360) state (fun k out =>
      k ≤ 7 * Nj + 8 * G.hints + 14 * r + 78 + 2 * ((hintScanBodyTime G r + 2) * Nj ^ r) ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
      (out.regs 1 = 1 ↔
        (HintParams.family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).card = 1) ∧
      (out.regs 1 = 1 → ∃ target : Fin (Nj ^ r),
        hintFamilySuccesses G coords beta Nj r v hPublic.positive = {target} ∧
        HintScanSolution G coords beta Nj r (hintTupleSet (hintOdometerEnumeration Nj r hPublic.positive target)) v out.mem ∧
        ∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i) ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem ∧
      HintRowMutationFrame G parent outsideBase bitmapBase Nj r state.mem out.mem) := by
  obtain ⟨hBitmapAt, hSolveAt⟩ := At.seqStmt hAt
  change At P base (hintRowBitmapStmt.compile base) at hBitmapAt
  change At P (base + 34) (hintFamilySolveStmt.compile (base + 34)) at hSolveAt
  obtain ⟨_, kB, sB, hRunB, hPcB, hCostB, hDataB, hHeaderB, hContextB, hFrameB⟩ :=
    hintRowBitmapStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E state base
      hPublic hInput hHeader hContext hBitmapAt hPc
  obtain ⟨_, kS, out, hRunS, hPcS, hCostS, hBitS, hSingletonS, hSolutionS, hDataS, hHeaderS, hContextS, hFrameS⟩ :=
    hintFamilySolveStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E sB (base + 34)
      hPublic hDataB hHeaderB hContextB hSolveAt hPcB
  have hFrameS' := HintScanFrame.to_row_frame hPublic hFrameS
  have hSpan := (hintRowWork_span hPublic).2
  refine ⟨hPc, kS + kB, out, hintIterate_then (step P E) hRunB hRunS, ?_, by omega,
    hBitS, hSingletonS, hSolutionS, hDataS, hHeaderS, hContextS, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hPcS
  · intro addr hAway
    rw [hFrameS' addr hAway]
    apply hFrameB addr
    rcases hAway with hBefore | hAfter
    · exact Or.inl hBefore
    · exact Or.inr (by omega)

  · intro addr hBitmap hArray hCount hRhs hGauss
    rw [hFrameS addr hArray hCount hRhs hGauss]
    exact hFrameB addr hBitmap

theorem hintRowPredictCountStmt_precise_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hNext : G.rows < G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hNext.le Nj r parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hCoeff : ∀ c : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + c.val) = (beta ⟨G.rows, hNext⟩ c).val)
    (hAt : At P base (hintRowPredictCountStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1424) state (fun k out =>
      k ≤ 7 * Nj + 20 * G.hints + 23 * r + 123 + 2 * ((hintScanBodyTime G r + 2) * Nj ^ r) ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
      (out.regs 1 = 1 ↔ (family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).card = 1) ∧
      (out.regs 1 = 1 → ∃ C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v),
        (∀ D ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v), D = C) ∧
        out.regs 8 = (rowBit beta C ⟨G.rows, hNext⟩).val) ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem ∧
      HintRowMutationFrame G parent outsideBase bitmapBase Nj r state.mem out.mem) := by
  let Fam := family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)
  obtain ⟨hFamilyAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base (hintRowFamilyStmt.compile base) at hFamilyAt
  change At P (base + 1360) ((Stmt.ite (.neqz 1) hintNextBitStmt (.code hintReplayStop)).compile (base + 1360)) at hBranchAt
  obtain ⟨_, kR, sR, hRunR, hPcR, hCostR, hFlagR, hSingletonR, hSolvedR, hDataR, hHeaderR, hCtxR, hFrameR, hPreciseR⟩ :=
    hintRowFamilyStmt_precise_sem G coords beta hNext.le Nj r parent outsideBase bitmapBase v P E state base
      hPublic hInput hHeader hContext hFamilyAt hPc
  let Q : ℕ → RAMState → Prop := fun k out => k ≤ 12 * G.hints + 9 * r + 45 ∧
    (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧ (out.regs 1 = 1 ↔ Fam.card = 1) ∧
    (out.regs 1 = 1 → ∃ C ∈ Fam, (∀ D ∈ Fam, D = C) ∧ out.regs 8 = (rowBit beta C ⟨G.rows, hNext⟩).val) ∧
    out.mem = sR.mem ∧ out.regs 14 = G.context
  have hBranch : Sem P E (base + 1360) (base + 1424) sR Q := by
    apply Sem.ite P E (base + 1360) (.neqz 1) hintNextBitStmt (.code hintReplayStop) sR Q
      hBranchAt hPublic.geometry.word_bound hPcR
    · intro hGo
      change Sem P E (base + 1361) (base + 1421) {sR with pc := base + 1361}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1424})
      have hOne : sR.regs 1 = 1 := hFlagR.resolve_left hGo
      obtain ⟨target, hSuccess, hSolution, hArray⟩ := hSolvedR hOne
      have hNative := hintNextRecoveredStmt_sem G coords beta hNext Nj r parent outsideBase bitmapBase v
        P E {sR with pc := base + 1361} (base + 1361) hPublic target hSuccess hDataR hHeaderR hCtxR
        hArray hSolution hCoeff (at_ite hBranchAt).2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hOneOut, hPred, hMem, hCtx⟩ := hOut
      change Q (1 + k + 1) {out with pc := base + 1424}
      exact ⟨by omega, Or.inr hOneOut, ⟨fun _ => hSingletonR.mp hOne, fun _ => hOneOut⟩,
        fun _ => hPred, hMem, hCtx⟩
    · intro hStop
      change Sem P E (base + 1422) (base + 1423) {sR with pc := base + 1422}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1424})
      have hZero : sR.regs 1 = 0 := by
        by_contra hBad
        exact hStop hBad
      have hBadCard : ¬ Fam.card = 1 := by
        intro hCard
        have hOne := hSingletonR.mpr hCard
        omega
      have hNative := Sem.block P E (base + 1422) hintReplayStop {sR with pc := base + 1422}
        (at_ite hBranchAt).2.2.2.2.1 (by simp [hintReplayStop, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      change Q (1 + k + 1) {runBlock hintReplayStop E {sR with pc := base + 1422} with pc := base + 1424}
      dsimp only [Q]
      refine ⟨by change k = 1 at hCost; omega, Or.inl ?_, ?_, ?_, rfl, ?_⟩
      · simp [hintReplayStop, runBlock, execInstr]
      · simp [hintReplayStop, runBlock, execInstr, hBadCard]
      · intro hOne
        simp [hintReplayStop, runBlock, execInstr] at hOne
      · simpa [hintReplayStop, runBlock, execInstr] using hCtxR
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hFlagB, hSingletonB, hPredB, hMemB, hCtxB⟩ := hBranch
  refine ⟨hPc, kB + kR, out, hintIterate_then (step P E) hRunR hRunB, hPcB, by omega,
    hFlagB, hSingletonB, hPredB, ?_, ?_, hCtxB, ?_, ?_⟩
  · rw [hMemB]; exact hDataR
  · rw [hMemB]; exact hHeaderR
  · rw [hMemB]; exact hFrameR

  · rw [hMemB]; exact hPreciseR

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowPredictCountStmt_precise_sem
end -- Def_LinearSetReconciliation327_Main_HintRowPrecise20261120

section -- Def_LinearSetReconciliation327_Main_HintRowWait20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRowWaitFetch : List Instr :=
  [.load 4 11, .load 0 4] ++ hintParentLoad 5 5 ++ [.add 3 5 0, .qDet 8 3, .load 9 14]
def hintRowWaitTail : List Instr := [.lt 1 9 8, .imm 15 1, .bxor 1 1 15]
def hintRowWaitCode : List Instr := hintScanParent ++ hintRowWaitFetch ++ hintRowWaitTail
theorem hintRowWaitCode_length : hintRowWaitCode.length = 13 := rfl

theorem hintRowWait_clip (a ell threshold : ℕ) (ha : a < ell) :
    min ell threshold ≤ a ↔ threshold ≤ a := by omega

theorem hintRowWaitFetch_spec (E : RAMEnv) (state : RAMState)
    (parent outsideBase r table a threshold : ℕ)
    (hParent : state.regs 11 = parent) (hContext : state.regs 14 = parent + 16)
    (hEnd : parent + 16 < 2 ^ E.W) (hArray : outsideBase < 2 ^ E.W)
    (hR : r < 2 ^ E.W) (hTable : table + r < 2 ^ E.W)
    (hA : a < 2 ^ E.W) (hThreshold : threshold < 2 ^ E.W)
    (hPointer : state.mem parent = outsideBase) (hCount : state.mem outsideBase = r)
    (hTableMem : state.mem (parent + 5) = table) (hRows : state.mem (parent + 16) = a)
    (hLookup : E.det (table + r) = threshold) :
    let out := runBlock hintRowWaitFetch E state
    out.pc = state.pc + 8 ∧ out.mem = state.mem ∧ out.regs 8 = threshold ∧ out.regs 9 = a ∧
      out.regs 14 = parent + 16 := by
  have hFive : 5 < 2 ^ E.W := by omega
  have hFiveAddr : parent + 5 < 2 ^ E.W := by omega
  have hTableWord : table < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_, ?_⟩ <;>
    simp [hintRowWaitFetch, hintParentLoad, runBlock, execInstr, hParent, hContext,
      hPointer, hCount, hTableMem, hRows, hLookup,
      Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hFive,
      Nat.mod_eq_of_lt hFiveAddr, Nat.mod_eq_of_lt hTableWord, Nat.mod_eq_of_lt hTable,
      Nat.mod_eq_of_lt hThreshold, Nat.mod_eq_of_lt hA]

theorem hintRowWaitTail_spec (E : RAMEnv) (state : RAMState) (a threshold : ℕ)
    (hWord : 1 < 2 ^ E.W) (h8 : state.regs 8 = threshold) (h9 : state.regs 9 = a) :
    let out := runBlock hintRowWaitTail E state
    out.pc = state.pc + 3 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (threshold ≤ a) ∧
      out.regs 14 = state.regs 14 := by
  classical
  by_cases hLe : threshold ≤ a
  · have hNot : ¬ a < threshold := by omega
    refine ⟨?_, rfl, ?_, ?_⟩ <;>
      simp [hintRowWaitTail, runBlock, execInstr, h8, h9, hNot, hLe, hintTruth, Nat.mod_eq_of_lt hWord]
  · have hLt : a < threshold := by omega
    refine ⟨?_, rfl, ?_, ?_⟩ <;>
      simp [hintRowWaitTail, runBlock, execInstr, h8, h9, hLt, hLe, hintTruth, Nat.mod_eq_of_lt hWord]

theorem hintRowWaitCode_spec (E : RAMEnv) (state : RAMState)
    (parent outsideBase r table a ell h Nj c : ℕ)
    (hContext : state.regs 14 = parent + 16) (hEnd : parent + 16 < 2 ^ E.W)
    (hArray : outsideBase < 2 ^ E.W) (hR : r < 2 ^ E.W) (hTable : table + r < 2 ^ E.W)
    (hEll : ell < 2 ^ E.W) (hNext : a < ell)
    (hPointer : state.mem parent = outsideBase) (hCount : state.mem outsideBase = r)
    (hTableMem : state.mem (parent + 5) = table) (hRows : state.mem (parent + 16) = a)
    (hLookup : E.det (table + r) = min ell (HintParams.sigma h Nj r + c)) :
    let out := runBlock hintRowWaitCode E state
    out.pc = state.pc + 13 ∧ out.mem = state.mem ∧
      out.regs 1 = hintTruth (HintParams.sigma h Nj r + c ≤ a) ∧ out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hFetch := hintRowWaitFetch_spec E sP parent outsideBase r table a
    (min ell (HintParams.sigma h Nj r + c)) hParentP hContextP hEnd hArray hR hTable (by omega)
    ((min_le_left _ _).trans_lt hEll) (by rw [hMemP]; exact hPointer) (by rw [hMemP]; exact hCount)
    (by rw [hMemP]; exact hTableMem) (by rw [hMemP]; exact hRows) hLookup
  generalize hF : runBlock hintRowWaitFetch E sP = sF at hFetch
  obtain ⟨hPcF, hMemF, h8, h9, hContextF⟩ := hFetch
  have hTail := hintRowWaitTail_spec E sF a (min ell (HintParams.sigma h Nj r + c)) hWord h8 h9
  generalize hT : runBlock hintRowWaitTail E sF = out at hTail
  obtain ⟨hPcT, hMemT, hFlagT, hContextT⟩ := hTail
  have hRun : runBlock hintRowWaitCode E state = out := by
    rw [hintRowWaitCode, runBlock_append, runBlock_append, hP, hF, hT]
  rw [hRun]
  exact ⟨by omega, hMemT.trans (hMemF.trans hMemP),
    hFlagT.trans (hintTruth_congr (hintRowWait_clip a ell _ hNext)),
    hContextT.trans hContextF⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowWaitCode_spec
end -- Def_LinearSetReconciliation327_Main_HintRowWait20261120

section -- Def_LinearSetReconciliation327_Main_HintRowEligible20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintRowEligibleCallStmt : Stmt := .seq (.code hintRowWaitCode)
  (.ite (.neqz 1) hintRowPredictCountStmt (.code hintReplayStop))
theorem hintRowEligibleCallStmt_len : hintRowEligibleCallStmt.len = 1441 := rfl

theorem hintRowEligibleCallStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hNext : G.rows < G.steps)
    (Nj r parent outsideBase bitmapBase table c : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hNext.le Nj r parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hTable : table + r < 2 ^ E.W) (hTableMem : state.mem (parent + 5) = table)
    (hLookup : E.det (table + r) = min G.steps (sigma G.hints Nj r + c))
    (hCoeff : ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintRowEligibleCallStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1441) state (fun k out =>
      k ≤ 7 * Nj + 20 * G.hints + 23 * r + 138 + 2 * ((hintScanBodyTime G r + 2) * Nj ^ r) ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
      (out.regs 1 = 1 ↔ sigma G.hints Nj r + c ≤ G.rows ∧
        (family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).card = 1) ∧
      (out.regs 1 = 1 → ∃ C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v),
        (∀ D ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v), D = C) ∧
        out.regs 8 = (rowBit beta C ⟨G.rows, hNext⟩).val) ∧
      HintRowInput G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintRowMutationFrame G parent outsideBase bitmapBase Nj r state.mem out.mem) := by
  classical
  let Fam := family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)
  let T := 7 * Nj + 20 * G.hints + 23 * r + 125 + 2 * ((hintScanBodyTime G r + 2) * Nj ^ r)
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hSpan := hPublic.fits.span
  obtain ⟨index, hHead⟩ := hHeader
  have hRows : state.mem (parent + 16) = G.rows := by rw [hParent]; exact hHead 0 (by decide)
  obtain ⟨hWaitAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base hintRowWaitCode at hWaitAt
  change At P (base + 13) ((Stmt.ite (.neqz 1) hintRowPredictCountStmt (.code hintReplayStop)).compile (base + 13)) at hBranchAt
  have hWait := hintRowWaitCode_spec E state parent outsideBase r table G.rows G.steps G.hints Nj c
    (hContext.trans hParent.symm) (by omega) (by omega) (by omega) hTable
    (hPublic.fits.values 13 (by decide)) hNext hInput.outside_pointer hInput.outside_count hTableMem hRows hLookup
  generalize hW : runBlock hintRowWaitCode E state = sW at hWait
  obtain ⟨hPcW, hMemW, hFlagW, hCtxW⟩ := hWait
  have hRunW : (step P E)^[13] state = sW := by
    have hh := iterate_runBlock_of_at P E hintRowWaitCode state (by rwa [hPc])
      (by simp [hintRowWaitCode, hintScanParent, hintRowWaitFetch, hintParentLoad, hintRowWaitTail, NoBranch, Instr.NoBranchI])
    simpa only [hintRowWaitCode_length, hW] using hh
  have hInputW : HintRowInput G coords Nj r parent outsideBase bitmapBase v sW.mem := by rw [hMemW]; exact hInput
  have hHeaderW : ∃ index, HintGaussHeader G index sW.mem := by rw [hMemW]; exact ⟨index, hHead⟩
  let Q : ℕ → RAMState → Prop := fun k out => k ≤ T ∧
    (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
    (out.regs 1 = 1 ↔ sigma G.hints Nj r + c ≤ G.rows ∧ Fam.card = 1) ∧
    (out.regs 1 = 1 → ∃ C ∈ Fam, (∀ D ∈ Fam, D = C) ∧ out.regs 8 = (rowBit beta C ⟨G.rows, hNext⟩).val) ∧
    HintRowInput G coords Nj r parent outsideBase bitmapBase v out.mem ∧
    (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
    HintRowMutationFrame G parent outsideBase bitmapBase Nj r sW.mem out.mem
  have hBranch : Sem P E (base + 13) (base + 1441) sW Q := by
    apply Sem.ite P E (base + 13) (.neqz 1) hintRowPredictCountStmt (.code hintReplayStop) sW Q
      hBranchAt hPublic.geometry.word_bound (by omega)
    · intro hGo
      change Sem P E (base + 14) (base + 1438) {sW with pc := base + 14}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1441})
      have hEligible : sigma G.hints Nj r + c ≤ G.rows := by
        by_contra hBad
        have hZero : sW.regs 1 = 0 := by simpa [hintTruth, hBad] using hFlagW
        exact hGo hZero
      have hNative := hintRowPredictCountStmt_precise_sem G coords beta hNext Nj r parent outsideBase bitmapBase v
        P E {sW with pc := base + 14} (base + 14) hPublic hInputW hHeaderW (hCtxW.trans hParent) hCoeff
        (at_ite hBranchAt).2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hFlag, hSingleton, hPred, hData, hHeader, hCtx, _, hFrame⟩ := hOut
      have hInputOut : HintRowInput G coords Nj r parent outsideBase bitmapBase v out.mem :=
        ⟨hData.outside_pointer, hData.bitmap_pointer, hData.radix, hData.outside_count, hData.hints, hData.observation⟩
      exact ⟨by dsimp only [T]; omega, hFlag,
        ⟨fun hOne => ⟨hEligible, hSingleton.mp hOne⟩, fun hh => hSingleton.mpr hh.2⟩,
        hPred, hInputOut, hHeader, hCtx, hFrame⟩
    · intro hStop
      change Sem P E (base + 1439) (base + 1440) {sW with pc := base + 1439}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1441})
      have hBad : ¬ sigma G.hints Nj r + c ≤ G.rows := by
        intro hEligible
        have hOne : sW.regs 1 = 1 := by simpa [hintTruth, hEligible] using hFlagW
        apply hStop
        change sW.regs 1 ≠ 0
        rw [hOne]; decide
      have hNative := Sem.block P E (base + 1439) hintReplayStop {sW with pc := base + 1439}
        (at_ite hBranchAt).2.2.2.2.1 (by simp [hintReplayStop, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      dsimp only [Q]
      refine ⟨by change k = 1 at hCost; dsimp only [T]; omega, Or.inl ?_, ?_, ?_, hInputW, hHeaderW, ?_, ?_⟩
      · simp [hintReplayStop, runBlock, execInstr]
      · simp [hintReplayStop, runBlock, execInstr, hBad]
      · intro hOne
        simp [hintReplayStop, runBlock, execInstr] at hOne
      · simpa [hintReplayStop, runBlock, execInstr] using hCtxW.trans hParent
      · intro addr _ _ _ _ _; rfl
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hFlagB, hSingletonB, hPredB, hInputB, hHeaderB, hCtxB, hFrameB⟩ := hBranch
  refine ⟨hPc, kB + 13, out, hintIterate_then (step P E) hRunW hRunB, hPcB, ?_,
    hFlagB, hSingletonB, hPredB, hInputB, hHeaderB, hCtxB, ?_⟩
  · dsimp only [T] at hCostB; omega
  · rw [← hMemW]; exact hFrameB

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowEligibleCallStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintRowEligible20261120

section -- Def_LinearSetReconciliation327_Main_HintRowAdvance20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintScanPublic.at_count {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR parent outsideBase bitmapBase : ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (r : ℕ) (hr : r ≤ maxR) : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase := by
  exact { hPublic with outside_span := by have := hPublic.outside_span; omega }

theorem HintRowInput.set_count {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR oldCount parent outsideBase bitmapBase : ℕ} {v : HintVec G.rows} {memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v memory) (count : ℕ) :
    HintRowInput G coords Nj count parent outsideBase bitmapBase v (Function.update memory outsideBase count) := by
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega : parent ≠ outsideBase)]; exact hInput.outside_pointer
  · rw [Function.update_of_ne (by omega : parent + 1 ≠ outsideBase)]; exact hInput.bitmap_pointer
  · rw [Function.update_of_ne (by omega : parent + 2 ≠ outsideBase)]; exact hInput.radix
  · simp
  · intro j
    rw [Function.update_of_ne (by omega : G.hintList + j.val ≠ outsideBase)]; exact hInput.hints j
  · intro t
    rw [Function.update_of_ne (by omega : G.hintList + G.hints + G.rows + t.val ≠ outsideBase)]; exact hInput.observation t

def hintRowAdvanceFetch : List Instr := [.load 4 11, .load 0 4] ++ hintParentLoad 6 4
def hintRowAdvanceTail : List Instr := [.imm 15 1, .add 0 0 15, .store 4 0, .lt 13 6 0, .bxor 13 13 15]
def hintRowAdvanceCode : List Instr := hintScanParent ++ hintRowAdvanceFetch ++ hintRowAdvanceTail
theorem hintRowAdvanceCode_length : hintRowAdvanceCode.length = 12 := rfl

theorem hintRowAdvanceFetch_spec (E : RAMEnv) (state : RAMState) (parent outsideBase r maxR : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hParent : state.regs 11 = parent)
    (hArray : outsideBase < 2 ^ E.W) (hR : r < 2 ^ E.W) (hMaxR : maxR < 2 ^ E.W)
    (hPointer : state.mem parent = outsideBase) (hCount : state.mem outsideBase = r)
    (hLimit : state.mem (parent + 4) = maxR) :
    let out := runBlock hintRowAdvanceFetch E state
    out.pc = state.pc + 5 ∧ out.mem = state.mem ∧ out.regs 4 = outsideBase ∧ out.regs 0 = r ∧ out.regs 6 = maxR ∧
      out.regs 1 = state.regs 1 ∧ out.regs 8 = state.regs 8 ∧ out.regs 14 = state.regs 14 := by
  have hFour : 4 < 2 ^ E.W := by omega
  have hAddr : parent + 4 < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintRowAdvanceFetch, hintParentLoad, runBlock, execInstr, hParent, hPointer, hCount, hLimit,
      Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hMaxR, Nat.mod_eq_of_lt hFour, Nat.mod_eq_of_lt hAddr]

theorem hintRowAdvanceTail_spec (E : RAMEnv) (state : RAMState) (outsideBase r maxR : ℕ)
    (hWord : 1 < 2 ^ E.W) (hNext : r + 1 < 2 ^ E.W)
    (h4 : state.regs 4 = outsideBase) (h0 : state.regs 0 = r) (h6 : state.regs 6 = maxR) :
    let out := runBlock hintRowAdvanceTail E state
    out.pc = state.pc + 5 ∧ out.mem = Function.update state.mem outsideBase (r + 1) ∧
      out.regs 13 = hintTruth (r + 1 ≤ maxR) ∧ out.regs 1 = state.regs 1 ∧ out.regs 8 = state.regs 8 ∧
      out.regs 14 = state.regs 14 := by
  classical
  by_cases hLe : r + 1 ≤ maxR
  · have hNot : ¬ maxR < r + 1 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hintRowAdvanceTail, runBlock, execInstr, h4, h0, h6, hLe, hNot, hintTruth,
        Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hNext]
  · have hLt : maxR < r + 1 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hintRowAdvanceTail, runBlock, execInstr, h4, h0, h6, hLe, hLt, hintTruth,
        Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hNext]

theorem hintRowAdvanceCode_spec (E : RAMEnv) (state : RAMState) (parent outsideBase r maxR : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase < 2 ^ E.W) (hNext : r + 1 < 2 ^ E.W) (hMaxR : maxR < 2 ^ E.W)
    (hPointer : state.mem parent = outsideBase) (hCount : state.mem outsideBase = r)
    (hLimit : state.mem (parent + 4) = maxR) :
    let out := runBlock hintRowAdvanceCode E state
    out.pc = state.pc + 12 ∧ out.mem = Function.update state.mem outsideBase (r + 1) ∧
      out.regs 13 = hintTruth (r + 1 ≤ maxR) ∧ out.regs 1 = state.regs 1 ∧ out.regs 8 = state.regs 8 ∧
      out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  have hRegs : ∀ reg : Fin 16, reg ≠ 3 → reg ≠ 11 →
      (runBlock hintScanParent E state).regs reg = state.regs reg := by
    intro reg h3 h11
    simp [hintScanParent, runBlock, execInstr, h3, h11]
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec hRegs
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hFetch := hintRowAdvanceFetch_spec E sP parent outsideBase r maxR hEnd hParentP hArray (by omega) hMaxR
    (by rw [hMemP]; exact hPointer) (by rw [hMemP]; exact hCount) (by rw [hMemP]; exact hLimit)
  generalize hF : runBlock hintRowAdvanceFetch E sP = sF at hFetch
  obtain ⟨hPcF, hMemF, h4, h0, h6, h1, h8, h14⟩ := hFetch
  have hTail := hintRowAdvanceTail_spec E sF outsideBase r maxR hWord hNext h4 h0 h6
  generalize hT : runBlock hintRowAdvanceTail E sF = out at hTail
  obtain ⟨hPcT, hMemT, hGoT, h1T, h8T, hCtxT⟩ := hTail
  have hRun : runBlock hintRowAdvanceCode E state = out := by
    rw [hintRowAdvanceCode, runBlock_append, runBlock_append, hP, hF, hT]
  rw [hRun]
  refine ⟨by omega, ?_, hGoT, h1T.trans (h1.trans (hRegs 1 (by decide) (by decide))),
    h8T.trans (h8.trans (hRegs 8 (by decide) (by decide))), hCtxT.trans (h14.trans hContextP)⟩
  rw [hMemT, hMemF, hMemP]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowAdvanceCode_spec
end -- Def_LinearSetReconciliation327_Main_HintRowAdvance20261120

section -- Def_LinearSetReconciliation327_Main_HintRowControl20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintRowControllerFrame (G : HintGaussArea) (parent outsideBase bitmapBase Nj maxR : ℕ)
    (original memory : ℕ → ℕ) : Prop :=
  ∀ addr, (addr < bitmapBase ∨ bitmapBase + Nj ≤ addr) →
    (addr < outsideBase ∨ outsideBase + 1 + maxR ≤ addr) → addr ≠ parent + 3 →
    (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
    (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → memory addr = original addr

theorem HintRowControllerFrame.refl (G : HintGaussArea) (parent outsideBase bitmapBase Nj maxR : ℕ) (memory : ℕ → ℕ) :
    HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR memory memory := by intro _ _ _ _ _ _; rfl

theorem HintRowControllerFrame.trans {G : HintGaussArea} {parent outsideBase bitmapBase Nj maxR : ℕ}
    {first middle last : ℕ → ℕ}
    (h1 : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR first middle)
    (h2 : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR middle last) :
    HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR first last := by
  intro addr hB hO hC hR hG
  exact (h2 addr hB hO hC hR hG).trans (h1 addr hB hO hC hR hG)

theorem HintRowControllerFrame.of_row {G : HintGaussArea} {parent outsideBase bitmapBase Nj maxR r : ℕ}
    {original memory : ℕ → ℕ} (hr : r ≤ maxR)
    (h : HintRowMutationFrame G parent outsideBase bitmapBase Nj r original memory) :
    HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR original memory := by
  intro addr hB hO hC hR hG
  apply h addr hB _ hC hR hG
  rcases hO with hBefore | hAfter
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem HintRowControllerFrame.set_count (G : HintGaussArea) (parent outsideBase bitmapBase Nj maxR : ℕ)
    (memory : ℕ → ℕ) (count : ℕ) :
    HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR memory (Function.update memory outsideBase count) := by
  intro addr _ hO _ _ _
  apply Function.update_of_ne
  rcases hO with hBefore | hAfter <;> omega

theorem HintRowControllerFrame.parent {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR parent outsideBase bitmapBase : ℕ} {original memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hFrame : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR original memory)
    (i : ℕ) (hi : 4 ≤ i) (hi' : i < 16) : memory (parent + i) = original (parent + i) := by
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  have hParent := hPublic.parent_eq
  exact hFrame _ (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))

structure HintRowControlState (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (Nj parent outsideBase bitmapBase maxR table r : ℕ) (v : HintVec G.rows) (original : ℕ → ℕ) (state : RAMState) : Prop where
  input : HintRowInput G coords Nj r parent outsideBase bitmapBase v state.mem
  header : ∃ index, HintGaussHeader G index state.mem
  context_value : state.regs 14 = G.context
  limit : state.mem (parent + 4) = maxR
  table_pointer : state.mem (parent + 5) = table
  frame : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR original state.mem

theorem HintRowControlState.pc {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {Nj parent outsideBase bitmapBase maxR table r : ℕ} {v : HintVec G.rows} {original : ℕ → ℕ} {state : RAMState}
    (h : HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table r v original state) (pc : ℕ) :
    HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table r v original {state with pc := pc} :=
  ⟨h.input, h.header, h.context_value, h.limit, h.table_pointer, h.frame⟩

def hintRowOuterInitTail : List Instr := [.load 4 11, .imm 0 0, .store 4 0, .imm 13 1, .imm 1 0]
def hintRowOuterInitCode : List Instr := hintScanParent ++ hintRowOuterInitTail

theorem hintRowOuterInitCode_spec (E : RAMEnv) (state : RAMState) (parent outsideBase : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase < 2 ^ E.W) (hPointer : state.mem parent = outsideBase) :
    let out := runBlock hintRowOuterInitCode E state
    out.pc = state.pc + 7 ∧ out.mem = Function.update state.mem outsideBase 0 ∧
      out.regs 13 = 1 ∧ out.regs 1 = 0 ∧ out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hPointerP : sP.mem parent = outsideBase := by rw [hMemP]; exact hPointer
  have hTail : let out := runBlock hintRowOuterInitTail E sP
      out.pc = sP.pc + 5 ∧ out.mem = Function.update sP.mem outsideBase 0 ∧
        out.regs 13 = 1 ∧ out.regs 1 = 0 ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hintRowOuterInitTail, runBlock, execInstr, hParentP, hContextP, hPointerP,
        Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hWord]
  generalize hT : runBlock hintRowOuterInitTail E sP = out at hTail
  obtain ⟨hPcT, hMemT, hGo, hZero, hCtx⟩ := hTail
  have hRun : runBlock hintRowOuterInitCode E state = out := by rw [hintRowOuterInitCode, runBlock_append, hP, hT]
  rw [hRun]
  exact ⟨by omega, by rw [hMemT, hMemP], hGo, hZero, hCtx⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowOuterInitCode_spec
end -- Def_LinearSetReconciliation327_Main_HintRowControl20261120

section -- Def_LinearSetReconciliation327_Main_HintRowOuterBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintRowQualified (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj c : ℕ) (v : HintVec G.rows) (r : ℕ) : Prop :=
  sigma G.hints Nj r + c ≤ G.rows ∧ (family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).card = 1

def HintRowPredicted (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hNext : G.rows < G.steps)
    (Nj r : ℕ) (v : HintVec G.rows) (state : RAMState) : Prop :=
  ∃ C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v),
    (∀ D ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v), D = C) ∧
      state.regs 8 = (rowBit beta C ⟨G.rows, hNext⟩).val

def hintRowOuterStop : List Instr := [.imm 13 0]
def hintRowOuterBody : Stmt := .seq hintRowEligibleCallStmt
  (.ite (.neqz 1) (.code hintRowOuterStop) (.code hintRowAdvanceCode))
theorem hintRowOuterBody_len : hintRowOuterBody.len = 1457 := rfl

theorem hintRowOuterBody_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hNext : G.rows < G.steps)
    (Nj r parent outsideBase bitmapBase maxR table c : ℕ) (v : HintVec G.rows) (original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hNext.le Nj maxR parent outsideBase bitmapBase) (hr : r ≤ maxR)
    (hState : HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table r v original state)
    (hTable : table + r < 2 ^ E.W) (hLookup : E.det (table + r) = min G.steps (sigma G.hints Nj r + c))
    (hCoeff : ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintRowOuterBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1457) state (fun k out =>
      k ≤ 7 * Nj + 20 * G.hints + 23 * r + 152 + 2 * ((hintScanBodyTime G r + 2) * Nj ^ r) ∧
      ((hintRowQualified G coords beta Nj c v r ∧ out.regs 1 = 1 ∧ out.regs 13 = 0 ∧
        HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table r v original out ∧
        HintRowPredicted G coords beta hNext Nj r v out) ∨
       (¬ hintRowQualified G coords beta Nj c v r ∧ out.regs 1 = 0 ∧
        out.regs 13 = hintTruth (r + 1 ≤ maxR) ∧
        HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table (r + 1) v original out))) := by
  classical
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hSpan := hPublic.fits.span
  obtain ⟨hCallAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base (hintRowEligibleCallStmt.compile base) at hCallAt
  change At P (base + 1441) ((Stmt.ite (.neqz 1) (.code hintRowOuterStop) (.code hintRowAdvanceCode)).compile (base + 1441)) at hBranchAt
  obtain ⟨_, kE, sE, hRunE, hPcE, hCostE, hFlagE, hQualE, hPredE, hInputE, hHeaderE, hCtxE, hFrameE⟩ :=
    hintRowEligibleCallStmt_sem G coords beta hNext Nj r parent outsideBase bitmapBase table c v P E state base
      (hPublic.at_count r hr) hState.input hState.header hState.context_value hTable hState.table_pointer
      hLookup hCoeff hCallAt hPc
  have hControlFrameE := HintRowControllerFrame.of_row hr hFrameE
  have hControlE : HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table r v original sE :=
    ⟨hInputE, hHeaderE, hCtxE, (hControlFrameE.parent hPublic 4 (by decide) (by decide)).trans hState.limit,
      (hControlFrameE.parent hPublic 5 (by decide) (by decide)).trans hState.table_pointer,
      hState.frame.trans hControlFrameE⟩
  let Q : ℕ → RAMState → Prop := fun k out => k ≤ 14 ∧
    ((hintRowQualified G coords beta Nj c v r ∧ out.regs 1 = 1 ∧ out.regs 13 = 0 ∧
      HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table r v original out ∧
      HintRowPredicted G coords beta hNext Nj r v out) ∨
     (¬ hintRowQualified G coords beta Nj c v r ∧ out.regs 1 = 0 ∧
      out.regs 13 = hintTruth (r + 1 ≤ maxR) ∧
      HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table (r + 1) v original out))
  have hBranch : Sem P E (base + 1441) (base + 1457) sE Q := by
    apply Sem.ite P E (base + 1441) (.neqz 1) (.code hintRowOuterStop) (.code hintRowAdvanceCode) sE Q
      hBranchAt hPublic.geometry.word_bound hPcE
    · intro hGo
      change Sem P E (base + 1442) (base + 1443) {sE with pc := base + 1442}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1457})
      have hOne : sE.regs 1 = 1 := hFlagE.resolve_left hGo
      have hQualified : hintRowQualified G coords beta Nj c v r := hQualE.mp hOne
      have hNative := Sem.block P E (base + 1442) hintRowOuterStop {sE with pc := base + 1442}
        (at_ite hBranchAt).2.2.1 (by simp [hintRowOuterStop, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      dsimp only [Q]
      refine ⟨by change k = 1 at hCost; omega, Or.inl ⟨hQualified, ?_, ?_, ?_, ?_⟩⟩
      · simpa [hintRowOuterStop, runBlock, execInstr] using hOne
      · simp [hintRowOuterStop, runBlock, execInstr]
      · refine ⟨hControlE.input, hControlE.header, ?_, hControlE.limit, hControlE.table_pointer, hControlE.frame⟩
        simpa [hintRowOuterStop, runBlock, execInstr] using hControlE.context_value
      · simpa [HintRowPredicted, hintRowOuterStop, runBlock, execInstr] using hPredE hOne
    · intro hStop
      change Sem P E (base + 1444) (base + 1456) {sE with pc := base + 1444}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1457})
      have hZero : sE.regs 1 = 0 := by by_contra hBad; exact hStop hBad
      have hNotQualified : ¬ hintRowQualified G coords beta Nj c v r := by
        intro hQ
        have hOne := hQualE.mpr hQ
        omega
      have hAdvance := hintRowAdvanceCode_spec E {sE with pc := base + 1444} parent outsideBase r maxR
        (by omega) (hCtxE.trans hParent.symm) (by omega) (by omega) (by omega)
        hInputE.outside_pointer hInputE.outside_count hControlE.limit
      generalize hA : runBlock hintRowAdvanceCode E {sE with pc := base + 1444} = sA at hAdvance
      obtain ⟨_, hMemA, hGoA, hFlagA, _, hCtxA⟩ := hAdvance
      have hInputA : HintRowInput G coords Nj (r + 1) parent outsideBase bitmapBase v sA.mem := by
        rw [hMemA]
        exact HintRowInput.set_count hPublic hInputE (r + 1)
      have hHeaderA : ∃ index, HintGaussHeader G index sA.mem := by
        obtain ⟨index, hHeader⟩ := hHeaderE
        refine ⟨index, ?_⟩
        intro i hi
        rw [hMemA, Function.update_of_ne (by omega : G.context + i ≠ outsideBase)]
        exact hHeader i hi
      have hCountFrame : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR sE.mem sA.mem := by
        rw [hMemA]
        exact HintRowControllerFrame.set_count G parent outsideBase bitmapBase Nj maxR sE.mem (r + 1)
      have hControlA : HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table (r + 1) v original sA :=
        ⟨hInputA, hHeaderA, hCtxA.trans hParent,
          (hCountFrame.parent hPublic 4 (by decide) (by decide)).trans hControlE.limit,
          (hCountFrame.parent hPublic 5 (by decide) (by decide)).trans hControlE.table_pointer,
          hControlE.frame.trans hCountFrame⟩
      have hNative := Sem.block P E (base + 1444) hintRowAdvanceCode {sE with pc := base + 1444}
        (at_ite hBranchAt).2.2.2.2.1
        (by simp [hintRowAdvanceCode, hintScanParent, hintRowAdvanceFetch, hintParentLoad, hintRowAdvanceTail, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hOut⟩ := hOut
      rw [hA] at hOut
      subst out
      exact ⟨by change k = 12 at hCost; omega,
        Or.inr ⟨hNotQualified, hFlagA.trans hZero, hGoA, hControlA.pc (base + 1457)⟩⟩
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hResult⟩ := hBranch
  exact ⟨hPc, kB + kE, out, hintIterate_then (step P E) hRunE hRunB, hPcB, by omega, hResult⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowOuterBody_sem
end -- Def_LinearSetReconciliation327_Main_HintRowOuterBody20261120

section -- Def_LinearSetReconciliation327_Main_HintRowGuard20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRowGuardFetch : List Instr := hintParentLoad 4 6 ++ hintParentLoad 5 17 ++ hintParentLoad 6 16 ++ hintParentLoad 7 29
def hintRowGuardTail : List Instr := [.lt 1 4 5, .imm 15 1, .bxor 1 1 15, .lt 8 6 7, .mul 1 1 8]
def hintRowGuardCode : List Instr := hintScanParent ++ hintRowGuardFetch ++ hintRowGuardTail
theorem hintRowGuardCode_length : hintRowGuardCode.length = 19 := rfl

theorem hintRowGuardFetch_spec (E : RAMEnv) (state : RAMState) (parent BX h a ell : ℕ)
    (hEnd : parent + 29 < 2 ^ E.W) (hParent : state.regs 11 = parent)
    (hBX : BX < 2 ^ E.W) (hH : h < 2 ^ E.W) (hA : a < 2 ^ E.W) (hEll : ell < 2 ^ E.W)
    (hReadBX : state.mem (parent + 6) = BX) (hReadH : state.mem (parent + 17) = h)
    (hReadA : state.mem (parent + 16) = a) (hReadEll : state.mem (parent + 29) = ell) :
    let out := runBlock hintRowGuardFetch E state
    out.pc = state.pc + 12 ∧ out.mem = state.mem ∧ out.regs 4 = BX ∧ out.regs 5 = h ∧ out.regs 6 = a ∧
      out.regs 7 = ell ∧ out.regs 14 = state.regs 14 := by
  have h6 : 6 < 2 ^ E.W := by omega
  have h17 : 17 < 2 ^ E.W := by omega
  have h16 : 16 < 2 ^ E.W := by omega
  have h29 : 29 < 2 ^ E.W := by omega
  have hP6 : parent + 6 < 2 ^ E.W := by omega
  have hP17 : parent + 17 < 2 ^ E.W := by omega
  have hP16 : parent + 16 < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintRowGuardFetch, hintParentLoad, runBlock, execInstr, hParent,
      hReadBX, hReadH, hReadA, hReadEll, Nat.mod_eq_of_lt h6, Nat.mod_eq_of_lt h17,
      Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt h29, Nat.mod_eq_of_lt hP6,
      Nat.mod_eq_of_lt hP17, Nat.mod_eq_of_lt hP16, Nat.mod_eq_of_lt hEnd,
      Nat.mod_eq_of_lt hBX, Nat.mod_eq_of_lt hH, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hEll]

theorem hintRowGuardTail_spec (E : RAMEnv) (state : RAMState) (BX h a ell : ℕ)
    (hWord : 1 < 2 ^ E.W) (h4 : state.regs 4 = BX) (h5 : state.regs 5 = h)
    (h6 : state.regs 6 = a) (h7 : state.regs 7 = ell) :
    let out := runBlock hintRowGuardTail E state
    out.pc = state.pc + 5 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (h ≤ BX ∧ a < ell) ∧
      out.regs 14 = state.regs 14 := by
  classical
  by_cases hHint : h ≤ BX
  · have hNot : ¬ BX < h := by omega
    by_cases hNext : a < ell <;>
      refine ⟨?_, rfl, ?_, ?_⟩ <;>
      simp [hintRowGuardTail, runBlock, execInstr, h4, h5, h6, h7, hHint, hNot, hNext, hintTruth, Nat.mod_eq_of_lt hWord]
  · have hLt : BX < h := by omega
    by_cases hNext : a < ell <;>
      refine ⟨?_, rfl, ?_, ?_⟩ <;>
      simp [hintRowGuardTail, runBlock, execInstr, h4, h5, h6, h7, hHint, hLt, hNext, hintTruth, Nat.mod_eq_of_lt hWord]

theorem hintRowGuardCode_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState) (parent BX index : ℕ)
    (hParent : parent + 16 = G.context) (hContext : state.regs 14 = G.context)
    (hHeader : HintGaussHeader G index state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hBX : BX < 2 ^ E.W) (hReadBX : state.mem (parent + 6) = BX) :
    let out := runBlock hintRowGuardCode E state
    out.pc = state.pc + 19 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (G.hints ≤ BX ∧ G.rows < G.steps) ∧
      out.regs 14 = G.context := by
  have hSpan := hFits.span
  have hWord : 1 < 2 ^ E.W := by omega
  have hReadH : state.mem (parent + 17) = G.hints := by
    rw [show parent + 17 = G.context + 1 by omega]; exact hHeader 1 (by decide)
  have hReadA : state.mem (parent + 16) = G.rows := by rw [hParent]; exact hHeader 0 (by decide)
  have hReadEll : state.mem (parent + 29) = G.steps := by
    rw [show parent + 29 = G.context + 13 by omega]; exact hHeader 13 (by decide)
  have hParentSpec := hintScanParent_spec E state parent (by omega) (hContext.trans hParent.symm)
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hFetch := hintRowGuardFetch_spec E sP parent BX G.hints G.rows G.steps (by omega) hParentP hBX
    (hFits.values 1 (by decide)) (hFits.values 0 (by decide)) (hFits.values 13 (by decide))
    (by rw [hMemP]; exact hReadBX) (by rw [hMemP]; exact hReadH)
    (by rw [hMemP]; exact hReadA) (by rw [hMemP]; exact hReadEll)
  generalize hF : runBlock hintRowGuardFetch E sP = sF at hFetch
  obtain ⟨hPcF, hMemF, h4, h5, h6, h7, hContextF⟩ := hFetch
  have hTail := hintRowGuardTail_spec E sF BX G.hints G.rows G.steps hWord h4 h5 h6 h7
  generalize hT : runBlock hintRowGuardTail E sF = out at hTail
  obtain ⟨hPcT, hMemT, hFlagT, hContextT⟩ := hTail
  have hRun : runBlock hintRowGuardCode E state = out := by rw [hintRowGuardCode, runBlock_append, runBlock_append, hP, hF, hT]
  rw [hRun]
  exact ⟨by omega, hMemT.trans (hMemF.trans hMemP), hFlagT, hContextT.trans (hContextF.trans (hContextP.trans hParent))⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowGuardCode_spec
end -- Def_LinearSetReconciliation327_Main_HintRowGuard20261120

section -- Def_LinearSetReconciliation327_Main_HintRowOuterLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRowOuterLoop : Stmt := .loop (.neqz 13) hintRowOuterBody
theorem hintRowOuterLoop_len : hintRowOuterLoop.len = 1459 := rfl

def hintRowOuterStepTime (G : HintGaussArea) (Nj r : ℕ) : ℕ :=
  7 * Nj + 20 * G.hints + 23 * r + 152 + 2 * ((hintScanBodyTime G r + 2) * Nj ^ r)
def hintRowOuterBudget (G : HintGaussArea) (Nj maxR : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (maxR + 1), hintRowOuterStepTime G Nj r

structure HintRowOuterDone (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hNext : G.rows < G.steps)
    (Nj parent outsideBase bitmapBase maxR table target : ℕ) (v : HintVec G.rows)
    (original : ℕ → ℕ) (state : RAMState) : Prop where
  control : HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table target v original state
  stopped : state.regs 13 = 0
  answer : (target ≤ maxR ∧ state.regs 1 = 1 ∧ HintRowPredicted G coords beta hNext Nj target v state) ∨
    (target = maxR + 1 ∧ state.regs 1 = 0)

theorem HintRowOuterDone.pc {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hNext : G.rows < G.steps}
    {Nj parent outsideBase bitmapBase maxR table target : ℕ} {v : HintVec G.rows} {original : ℕ → ℕ} {state : RAMState}
    (h : HintRowOuterDone G coords beta hNext Nj parent outsideBase bitmapBase maxR table target v original state) (pc : ℕ) :
    HintRowOuterDone G coords beta hNext Nj parent outsideBase bitmapBase maxR table target v original {state with pc := pc} :=
  ⟨h.control.pc pc, h.stopped, h.answer⟩

theorem hintRowOuterLoop_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hNext : G.rows < G.steps)
    (Nj parent outsideBase bitmapBase maxR table c target : ℕ) (v : HintVec G.rows) (original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hNext.le Nj maxR parent outsideBase bitmapBase)
    (hTarget : target ≤ maxR + 1)
    (hBefore : ∀ r < target, ¬ hintRowQualified G coords beta Nj c v r)
    (hAtTarget : target ≤ maxR → hintRowQualified G coords beta Nj c v target)
    (hState : HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table 0 v original state)
    (hGoInitial : state.regs 13 = 1) (hTable : table + maxR < 2 ^ E.W)
    (hLookup : ∀ r ≤ maxR, E.det (table + r) = min G.steps (HintParams.sigma G.hints Nj r + c))
    (hCoeff : ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintRowOuterLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1459) state (fun k out =>
      k ≤ (hintRowOuterBudget G Nj maxR + 2) * min (target + 1) (maxR + 1) + 1 ∧
      HintRowOuterDone G coords beta hNext Nj parent outsideBase bitmapBase maxR table target v original out) := by
  classical
  let rounds := min (target + 1) (maxR + 1)
  have hRoundsPos : 0 < rounds := by dsimp only [rounds]; omega
  have hRoundsTarget : rounds ≤ target + 1 := min_le_left _ _
  have hRoundsMax : rounds ≤ maxR + 1 := min_le_right _ _
  let I : ℕ → RAMState → Prop := fun left st => if left = 0 then
    HintRowOuterDone G coords beta hNext Nj parent outsideBase bitmapBase maxR table target v original st else
    ∃ r, r + left = rounds ∧
      HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table r v original st ∧ st.regs 13 = 1
  have hBodyAt : At P (base + 1) (hintRowOuterBody.compile (base + 1)) := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    dsimp only [I] at hI ⊢
    by_cases hLeft : left = 0
    · rw [if_pos hLeft] at hI ⊢
      exact hI.pc pc
    · rw [if_neg hLeft] at hI ⊢
      obtain ⟨r, hR, hControl, hGo⟩ := hI
      exact ⟨r, hR, hControl.pc pc, hGo⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.neqz 13).code E st) := by
    intro left st hI
    exact hI
  have hGo : ∀ left st, I (left + 1) st → (Cond.neqz 13).eval st := by
    intro left st hI
    dsimp only [I] at hI
    rw [if_neg (by omega : left + 1 ≠ 0)] at hI
    obtain ⟨_, _, _, hGo⟩ := hI
    change st.regs 13 ≠ 0
    rw [hGo]; decide
  have hStop : ∀ st, I 0 st → ¬ (Cond.neqz 13).eval st := by
    intro st hI
    change HintRowOuterDone G coords beta hNext Nj parent outsideBase bitmapBase maxR table target v original st at hI
    change ¬ st.regs 13 ≠ 0
    rw [hI.stopped]; simp
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.neqz 13).code.length + 1 →
      Sem P E (base + (Cond.neqz 13).code.length + 1)
        (base + (Cond.neqz 13).code.length + 1 + hintRowOuterBody.len) st
        (fun k out => k ≤ hintRowOuterBudget G Nj maxR ∧ I left out) := by
    intro left st hI hStart
    dsimp only [I] at hI
    rw [if_neg (by omega : left + 1 ≠ 0)] at hI
    obtain ⟨r, hR, hControl, _⟩ := hI
    have hr : r ≤ maxR := by omega
    have hrTarget : r ≤ target := by omega
    have hNative := hintRowOuterBody_sem G coords beta hNext Nj r parent outsideBase bitmapBase maxR table c v original
      P E st (base + 1) hPublic hr hControl (by omega) (hLookup r hr) hCoeff hBodyAt hStart
    have hBudget : hintRowOuterStepTime G Nj r ≤ hintRowOuterBudget G Nj maxR :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hCases⟩ := hOut
    refine ⟨hCost.trans hBudget, ?_⟩
    dsimp only [I]
    rcases hCases with ⟨hQual, hOne, hStopped, hControlOut, hPred⟩ | ⟨hNotQual, hZero, hGoOut, hControlOut⟩
    · have hEq : r = target := by
        by_contra hNe
        exact hBefore r (by omega) hQual
      have hTargetMax : target ≤ maxR := by omega
      have hRounds : rounds = target + 1 := Nat.min_eq_left (by omega)
      have hLeft : left = 0 := by omega
      rw [if_pos hLeft]
      subst r
      exact ⟨hControlOut, hStopped, Or.inl ⟨hTargetMax, hOne, hPred⟩⟩
    · by_cases hLeft : left = 0
      · have hTargetMax : ¬ target ≤ maxR := by
          intro hSmall
          have hRounds : rounds = target + 1 := Nat.min_eq_left (by omega)
          have hEq : r = target := by omega
          exact hNotQual (hEq ▸ hAtTarget hSmall)
        have hTargetEnd : target = maxR + 1 := by omega
        have hRounds : rounds = maxR + 1 := Nat.min_eq_right (by omega)
        have hNext : r + 1 = target := by omega
        have hGoZero : out.regs 13 = 0 := by
          rw [hGoOut]
          simp [hintTruth, hNext, hTargetEnd]
        rw [if_pos hLeft]
        have hControlTarget : HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table target v original out := hNext ▸ hControlOut
        exact ⟨hControlTarget, hGoZero, Or.inr ⟨hTargetEnd, hZero⟩⟩
      · have hNextBound : r + 1 ≤ maxR := by omega
        have hGoOne : out.regs 13 = 1 := by simpa [hintTruth, hNextBound] using hGoOut
        rw [if_neg hLeft]
        exact ⟨r + 1, by omega, hControlOut, hGoOne⟩
  have hInitial : I rounds state := by
    dsimp only [I]
    rw [if_neg (by omega : rounds ≠ 0)]
    exact ⟨0, by omega, hState, hGoInitial⟩
  have hNative := hintLoopFuel_sem P E base (.neqz 13) hintRowOuterBody hAt hPublic.geometry.word_bound I
    (hintRowOuterBudget G Nj maxR) hIpc hItest hGo hStop hBody rounds state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, hDone⟩ := hOut
  simp only [Cond.code, List.length_nil, Nat.zero_add] at hCost
  exact ⟨hCost, hDone⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowOuterLoop_sem
end -- Def_LinearSetReconciliation327_Main_HintRowOuterLoop20261120

section -- Def_LinearSetReconciliation327_Main_HintRowFirst20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintFirstIndex (pred : ℕ → Prop) (maxR : ℕ) : ℕ := by
  classical
  let S := (Finset.range (maxR + 1)).filter pred
  exact if h : S.Nonempty then S.min' h else maxR + 1

theorem hintFirstIndex_spec (pred : ℕ → Prop) (maxR : ℕ) :
    let target := hintFirstIndex pred maxR
    target ≤ maxR + 1 ∧ (∀ r < target, ¬ pred r) ∧ (target ≤ maxR → pred target) := by
  classical
  let S := (Finset.range (maxR + 1)).filter pred
  have hEq : hintFirstIndex pred maxR = if h : S.Nonempty then S.min' h else maxR + 1 := rfl
  dsimp only
  rw [hEq]
  split_ifs with hS
  · have hMem : S.min' hS ∈ S := Finset.min'_mem S hS
    have hBound : S.min' hS < maxR + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hMem).1
    refine ⟨by omega, ?_, fun _ => (Finset.mem_filter.mp hMem).2⟩
    intro r hr hp
    have hRMem : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    have hLe := Finset.min'_le S r hRMem
    omega
  · refine ⟨le_rfl, ?_, ?_⟩
    · intro r hr hp
      exact hS ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hp⟩⟩
    · intro hBad; omega


theorem hintFirstIndex_exists (pred : ℕ → Prop) (maxR : ℕ) :
    hintFirstIndex pred maxR ≤ maxR ↔ ∃ r ≤ maxR, pred r := by
  have hSpec := hintFirstIndex_spec pred maxR
  constructor
  · intro hLe
    exact ⟨_, hLe, hSpec.2.2 hLe⟩
  · rintro ⟨r, hr, hp⟩
    by_contra hBad
    exact hSpec.2.1 r (by omega) hp

open Classical in
theorem hintFind_range (pred : ℕ → Prop) : ∀ (n target : ℕ),
    (∀ r < target, ¬ pred r) → (target < n → pred target) →
    (List.range n).find? (fun r => decide (pred r)) = if target < n then some target else none := by
  classical
  intro n
  induction n with
  | zero => intro target _ _; simp
  | succ n ih =>
    intro target hBefore hAt
    by_cases hLt : target < n
    · have hIH := ih target hBefore (fun ht => hAt (by omega))
      rw [List.range_succ, List.find?_append, hIH, if_pos hLt, if_pos (by omega : target < n + 1)]
      rfl
    · have hNone : (List.range n).find? (fun r => decide (pred r)) = none := by
        apply List.find?_eq_none.mpr
        intro r hr
        have hNo := hBefore r (by have := List.mem_range.mp hr; omega)
        simpa using hNo
      rw [List.range_succ, List.find?_append, hNone]
      by_cases hEq : target = n
      · subst target
        have hp : pred n := hAt (by omega)
        simp [hp]
      · have hNot : ¬ target < n + 1 := by omega
        have hNo : ¬ pred n := hBefore n (by omega)
        simp [hNot, hNo]

open Classical in
theorem hintFirstIndex_find (pred : ℕ → Prop) (maxR : ℕ) :
    (List.range (maxR + 1)).find? (fun r => decide (pred r)) =
      if hintFirstIndex pred maxR ≤ maxR then some (hintFirstIndex pred maxR) else none := by
  classical
  have hSpec := hintFirstIndex_spec pred maxR
  simpa only [Nat.lt_succ_iff] using hintFind_range pred (maxR + 1) (hintFirstIndex pred maxR)
    hSpec.2.1 (fun ht => hSpec.2.2 (by omega))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFirstIndex_find
end -- Def_LinearSetReconciliation327_Main_HintRowFirst20261120

section -- Def_LinearSetReconciliation327_Main_HintRowSearch20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRowSearchStmt : Stmt := .seq (.code hintRowOuterInitCode) hintRowOuterLoop
theorem hintRowSearchStmt_len : hintRowSearchStmt.len = 1466 := rfl

/-- Native first-eligible-singleton search. The actual count and loop flags are
    initialized by the program; the first-success index is only a proof device. -/
theorem hintRowSearchStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hNext : G.rows < G.steps)
    (Nj parent outsideBase bitmapBase maxR table c oldCount : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hNext.le Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hLimit : state.mem (parent + 4) = maxR) (hTableMem : state.mem (parent + 5) = table)
    (hTable : table + maxR < 2 ^ E.W)
    (hLookup : ∀ r ≤ maxR, E.det (table + r) = min G.steps (HintParams.sigma G.hints Nj r + c))
    (hCoeff : ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintRowSearchStmt.compile base)) (hPc : state.pc = base) :
    let target := hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR
    Sem P E base (base + 1466) state (fun k out =>
      k ≤ (hintRowOuterBudget G Nj maxR + 2) * min (target + 1) (maxR + 1) + 8 ∧
      HintRowOuterDone G coords beta hNext Nj parent outsideBase bitmapBase maxR table target v state.mem out) := by
  let target := hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR
  have hFirst := hintFirstIndex_spec (hintRowQualified G coords beta Nj c v) maxR
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hSpan := hPublic.fits.span
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintRowOuterInitCode at hInitAt
  change At P (base + 7) (hintRowOuterLoop.compile (base + 7)) at hLoopAt
  have hInit := hintRowOuterInitCode_spec E state parent outsideBase (by omega)
    (hContext.trans hParent.symm) (by omega) hInput.outside_pointer
  generalize hI : runBlock hintRowOuterInitCode E state = sI at hInit
  obtain ⟨hPcI, hMemI, hGoI, _, hCtxI⟩ := hInit
  have hRunI : (step P E)^[7] state = sI := by
    have hh := iterate_runBlock_of_at P E hintRowOuterInitCode state (by rwa [hPc])
      (by simp [hintRowOuterInitCode, hintScanParent, hintRowOuterInitTail, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  have hInputI : HintRowInput G coords Nj 0 parent outsideBase bitmapBase v sI.mem := by
    rw [hMemI]
    exact HintRowInput.set_count hPublic hInput 0
  have hHeaderI : ∃ index, HintGaussHeader G index sI.mem := by
    obtain ⟨index, hHeader⟩ := hHeader
    refine ⟨index, ?_⟩
    intro i hi
    rw [hMemI, Function.update_of_ne (by omega : G.context + i ≠ outsideBase)]
    exact hHeader i hi
  have hFrameI : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR state.mem sI.mem := by
    rw [hMemI]
    exact HintRowControllerFrame.set_count G parent outsideBase bitmapBase Nj maxR state.mem 0
  have hControlI : HintRowControlState G coords Nj parent outsideBase bitmapBase maxR table 0 v state.mem sI :=
    ⟨hInputI, hHeaderI, hCtxI.trans hParent,
      (hFrameI.parent hPublic 4 (by decide) (by decide)).trans hLimit,
      (hFrameI.parent hPublic 5 (by decide) (by decide)).trans hTableMem, hFrameI⟩
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hDone⟩ :=
    hintRowOuterLoop_sem G coords beta hNext Nj parent outsideBase bitmapBase maxR table c target v state.mem
      P E sI (base + 7) hPublic hFirst.1 hFirst.2.1 hFirst.2.2 hControlI hGoI hTable hLookup hCoeff hLoopAt (by omega)
  exact ⟨hPc, kL + 7, out, hintIterate_then (step P E) hRunI hRunL, by omega, by dsimp only [target] at hCostL; omega, hDone⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowSearchStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintRowSearch20261120

section -- Def_LinearSetReconciliation327_Main_HintRowPredictAlign20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintRowOutput (state : RAMState) : Option (ZMod 2) :=
  if state.regs 1 = 1 then some (state.regs 8 : ZMod 2) else none

theorem hintCoords_card {h K : ℕ} (coords : Fin h → Fin K) (hInj : Function.Injective coords) :
    (Finset.univ.image (fun j => (coords j).val)).card = h := by
  rw [Finset.card_image_of_injective _ (fun _ _ heq => hInj (Fin.ext heq)), Finset.card_univ, Fintype.card_fin]

theorem hintRowSearch_workerPredict (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hNext : G.rows < G.steps) (N m Nj parent outsideBase bitmapBase maxR table BX BY c : ℕ)
    (j : Fin m) (v : HintVec G.rows) (original : ℕ → ℕ) (state : RAMState)
    (hNj : rowLen N m j.val = Nj) (hBX : G.hints ≤ BX) (hMax : maxR = min BY (Nj - G.hints))
    (hDone : HintRowOuterDone G coords beta hNext Nj parent outsideBase bitmapBase maxR table
      (hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR) v original state) :
    hintRowOutput state = workerPredict N m G.steps G.buckets BX BY c j beta
      (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v) := by
  classical
  have hCard := hintCoords_card coords hInj
  have hFind := hintFirstIndex_find (hintRowQualified G coords beta Nj c v) maxR
  unfold workerPredict
  dsimp only
  rw [hCard, if_neg (by omega : ¬ BX < G.hints), hNj, ← hMax]
  simp only [List.length_ofFn]
  simp only [dif_pos hNext]
  have hPredEq : (fun r => decide (sigma G.hints Nj r + c ≤ G.rows ∧
      (family Nj beta (Finset.univ.image (fun t => (coords t).val)) r (List.ofFn v)).card = 1)) =
      (fun r => decide (hintRowQualified G coords beta Nj c v r)) := by
    funext r
    by_cases hp : sigma G.hints Nj r + c ≤ G.rows ∧
        (family Nj beta (Finset.univ.image (fun t => (coords t).val)) r (List.ofFn v)).card = 1 <;>
      simp only [hintRowQualified, hp, decide_true, decide_false]
  rw [hPredEq]
  rw [hFind]
  rcases hDone.answer with ⟨hWithin, hOne, C, hMember, hUnique, hBit⟩ | ⟨hEnd, hZero⟩
  · have hFam : family Nj beta (Finset.univ.image (fun t => (coords t).val))
        (hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR) (List.ofFn v) = {C} := by
      ext D
      simp only [Finset.mem_singleton]
      exact ⟨fun hD => hUnique D hD, fun heq => heq ▸ hMember⟩
    simp only [if_pos hWithin]
    change hintRowOutput state = Option.map (fun C => rowBit beta C ⟨G.rows, hNext⟩)
      (family Nj beta (Finset.univ.image (fun t => (coords t).val))
        (hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR) (List.ofFn v)).toList.head?
    rw [hFam]
    simp [hintRowOutput, hOne, hBit]
  · have hOutside : ¬ hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR ≤ maxR := by omega
    rw [if_neg hOutside]
    simp [hintRowOutput, hZero]

theorem hintWorkerPredict_abstain {N m ell K BX BY c : ℕ} (j : Fin m)
    (beta : Fin ell → Fin K → ZMod 2) (J : Finset ℕ) (v : List (ZMod 2))
    (hBad : BX < J.card ∨ ¬ v.length < ell) : workerPredict N m ell K BX BY c j beta J v = none := by
  classical
  unfold workerPredict
  dsimp only
  by_cases hBX : BX < J.card
  · rw [if_pos hBX]
  · rw [if_neg hBX]
    have hLength : ¬ v.length < ell := hBad.resolve_left hBX
    split <;> simp [hLength]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowSearch_workerPredict
end -- Def_LinearSetReconciliation327_Main_HintRowPredictAlign20261120

section -- Def_LinearSetReconciliation327_Main_HintRowPredict20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

def hintRowPredictStmt : Stmt := .seq (.code hintRowGuardCode)
  (.ite (.neqz 1) hintRowSearchStmt (.code hintReplayStop))
theorem hintRowPredictStmt_len : hintRowPredictStmt.len = 1489 := rfl

/-- Full native row prediction, with both abstention guards, the waiting test,
    exhaustive family recovery, first eligible singleton, and actual next bit. -/
theorem hintRowPredictStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (N m Nj parent outsideBase bitmapBase maxR table BX BY c oldCount : ℕ) (j : Fin m) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hNj : rowLen N m j.val = Nj) (hMax : maxR = min BY (Nj - G.hints))
    (hBX : BX < 2 ^ E.W) (hReadBX : state.mem (parent + 6) = BX)
    (hLimit : state.mem (parent + 4) = maxR) (hTableMem : state.mem (parent + 5) = table)
    (hTable : table + maxR < 2 ^ E.W)
    (hLookup : ∀ r ≤ maxR, E.det (table + r) = min G.steps (sigma G.hints Nj r + c))
    (hCoeff : ∀ hNext : G.rows < G.steps, ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintRowPredictStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1489) state (fun k out =>
      k ≤ (hintRowOuterBudget G Nj maxR + 2) * (maxR + 1) + 29 ∧
      hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
        (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v) ∧
      (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem) := by
  classical
  have hJCard := hintCoords_card coords hPublic.injective
  obtain ⟨hGuardAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base hintRowGuardCode at hGuardAt
  change At P (base + 19) ((Stmt.ite (.neqz 1) hintRowSearchStmt (.code hintReplayStop)).compile (base + 19)) at hBranchAt
  obtain ⟨index, hHead⟩ := hHeader
  have hGuard := hintRowGuardCode_spec E G state parent BX index hPublic.parent_eq hContext hHead hPublic.fits hBX hReadBX
  generalize hG : runBlock hintRowGuardCode E state = sG at hGuard
  obtain ⟨hPcG, hMemG, hFlagG, hCtxG⟩ := hGuard
  have hRunG : (step P E)^[19] state = sG := by
    have hh := iterate_runBlock_of_at P E hintRowGuardCode state (by rwa [hPc])
      (by simp [hintRowGuardCode, hintScanParent, hintRowGuardFetch, hintParentLoad, hintRowGuardTail, NoBranch, Instr.NoBranchI])
    simpa only [hintRowGuardCode_length, hG] using hh
  have hInputG : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v sG.mem := by rw [hMemG]; exact hInput
  have hHeaderG : ∃ index, HintGaussHeader G index sG.mem := by rw [hMemG]; exact ⟨index, hHead⟩
  let Q : ℕ → RAMState → Prop := fun k out =>
    k ≤ (hintRowOuterBudget G Nj maxR + 2) * (maxR + 1) + 10 ∧
    hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
      (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v) ∧
    (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
    (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
    HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR sG.mem out.mem
  have hBranch : Sem P E (base + 19) (base + 1489) sG Q := by
    apply Sem.ite P E (base + 19) (.neqz 1) hintRowSearchStmt (.code hintReplayStop) sG Q
      hBranchAt hPublic.geometry.word_bound (by omega)
    · intro hGo
      change Sem P E (base + 20) (base + 1486) {sG with pc := base + 20}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1489})
      have hValid : G.hints ≤ BX ∧ G.rows < G.steps := by
        by_contra hBad
        have hZero : sG.regs 1 = 0 := by simpa [hintTruth, hBad] using hFlagG
        exact hGo hZero
      have hNative := hintRowSearchStmt_sem G coords beta hValid.2 Nj parent outsideBase bitmapBase maxR table c oldCount v
        P E {sG with pc := base + 20} (base + 20) hPublic hInputG hHeaderG hCtxG
        (by rw [hMemG]; exact hLimit) (by rw [hMemG]; exact hTableMem) hTable hLookup (hCoeff hValid.2)
        (at_ite hBranchAt).2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hDone⟩ := hOut
      have hRoundBound := Nat.mul_le_mul_left (hintRowOuterBudget G Nj maxR + 2)
        (min_le_right (hintFirstIndex (hintRowQualified G coords beta Nj c v) maxR + 1) (maxR + 1))
      have hCorrect := hintRowSearch_workerPredict G coords hPublic.injective beta hValid.2 N m Nj parent outsideBase bitmapBase
        maxR table BX BY c j v sG.mem out hNj hValid.1 hMax hDone
      exact ⟨by omega, hCorrect, ⟨_, hDone.control.input⟩, hDone.control.header,
        hDone.control.context_value, hDone.control.frame⟩
    · intro hStop
      change Sem P E (base + 1487) (base + 1488) {sG with pc := base + 1487}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1489})
      have hBad : ¬ (G.hints ≤ BX ∧ G.rows < G.steps) := by
        intro hGood
        have hOne : sG.regs 1 = 1 := by simpa [hintTruth, hGood] using hFlagG
        apply hStop
        change sG.regs 1 ≠ 0
        rw [hOne]; decide
      have hAbstain := hintWorkerPredict_abstain (N := N) (BX := BX) (BY := BY) (c := c) j beta (Finset.univ.image (fun t => (coords t).val)) (List.ofFn v)
        (by rw [hJCard, List.length_ofFn]; omega : BX < (Finset.univ.image (fun t => (coords t).val)).card ∨
          ¬ (List.ofFn v).length < G.steps)
      have hNative := Sem.block P E (base + 1487) hintReplayStop {sG with pc := base + 1487}
        (at_ite hBranchAt).2.2.2.2.1 (by simp [hintReplayStop, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      dsimp only [Q]
      refine ⟨by change k = 1 at hCost; omega, ?_, ⟨oldCount, hInputG⟩, hHeaderG, ?_, ?_⟩
      · rw [hAbstain]
        simp [hintRowOutput, hintReplayStop, runBlock, execInstr]
      · simpa [hintReplayStop, runBlock, execInstr] using hCtxG
      · exact HintRowControllerFrame.refl G parent outsideBase bitmapBase Nj maxR sG.mem
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hCorrectB, hInputB, hHeaderB, hCtxB, hFrameB⟩ := hBranch
  refine ⟨hPc, kB + 19, out, hintIterate_then (step P E) hRunG hRunB, hPcB, by omega,
    hCorrectB, hInputB, hHeaderB, hCtxB, ?_⟩
  rw [← hMemG]; exact hFrameB

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowPredictStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintRowPredict20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalClassExists20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

/-- Once the shared hint matrix is injective, every nonempty original family
    contains a successful enumerated outside class, for every outside count. -/
theorem hintFamilySuccesses_nonempty (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj r : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (hMatrix : Function.Injective (hintGaussMap G coords beta hPrefix)) :
    (hintFamilySuccesses G coords beta Nj r v hPos).Nonempty ↔
      (family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).Nonempty := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨C, hClass, _⟩ := (Finset.mem_filter.mp hn).2.2
    exact ⟨C, hClass.1⟩
  · rintro ⟨C, hC⟩
    let J := Finset.univ.image (fun j => (coords j).val)
    let A := C \ J
    have hClass : hintFamilyClass G coords beta Nj r A v C := ⟨hC, rfl⟩
    have hUnique : ∃! D : Finset ℕ, hintFamilyClass G coords beta Nj r A v D :=
      ⟨C, hClass, fun D hD => hintFamilyClass_subsingleton G coords hInj beta hPrefix Nj r A v hMatrix D C hD hClass⟩
    have hDomain := hintFamilyClass_domain G coords beta hPrefix Nj r A v hUnique
    let t : HintOutsideTuple Nj J r := (hintOutsideTupleCodec Nj J r).symm ⟨A, hDomain⟩
    have hSet : hintTupleSet t.val = A := by
      have hh := congrArg (fun B : HintOutsideSet Nj J r => B.val)
        ((hintOutsideTupleCodec Nj J r).apply_symm_apply ⟨A, hDomain⟩)
      exact hh
    let e := hintOdometerEnumeration Nj r hPos
    let n := e.symm t.val
    have hEnum : e n = t.val := e.apply_symm_apply _
    refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change (StrictMono (fun i => (e n i).val) ∧ ∀ i, (e n i).val ∉ J) ∧
      ∃! D : Finset ℕ, hintFamilyClass G coords beta Nj r (hintTupleSet (e n)) v D
    rw [hEnum]
    exact ⟨t.property, by rw [hSet]; exact hUnique⟩

theorem hintFamilySuccesses_empty (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj r : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (hEmpty : family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v) = ∅) :
    hintFamilySuccesses G coords beta Nj r v hPos = ∅ := by
  classical
  apply Finset.ext
  intro n
  constructor
  · intro hn
    obtain ⟨C, hClass, _⟩ := (Finset.mem_filter.mp hn).2.2
    have hMem := hClass.1
    rw [hEmpty] at hMem
    exact False.elim (Finset.notMem_empty C hMem)
  · intro hn
    exact False.elim (Finset.notMem_empty n hn)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFamilySuccesses_nonempty
end -- Def_LinearSetReconciliation327_Main_HintFinalClassExists20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalRaw20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

theorem hintNatSum_one {ι : Type*} (S : Finset ι) (f : ι → ℕ) :
    (∑ r ∈ S, f r) = 1 ↔ ∃ r ∈ S, f r = 1 ∧ ∀ q ∈ S, q ≠ r → f q = 0 := by
  classical
  constructor
  · intro hSum
    have hEx : ∃ r ∈ S, f r ≠ 0 := by
      by_contra hNo
      have hAll : ∀ r ∈ S, f r = 0 := by
        intro r hr
        by_contra hNe
        exact hNo ⟨r, hr, hNe⟩
      have hZero : (∑ r ∈ S, f r) = 0 := Finset.sum_eq_zero hAll
      omega
    obtain ⟨r, hr, hNe⟩ := hEx
    have hLe : f r ≤ ∑ q ∈ S, f q := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr
    have hOne : f r = 1 := by omega
    have hErase := Finset.sum_erase_add S f hr
    have hEraseZero : (∑ q ∈ S.erase r, f q) = 0 := by omega
    refine ⟨r, hr, hOne, ?_⟩
    intro q hq hqr
    have hqLe : f q ≤ ∑ x ∈ S.erase r, f x :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hqr, hq⟩)
    omega
  · rintro ⟨r, hr, hOne, hOthers⟩
    calc
      (∑ q ∈ S, f q) = f r := Finset.sum_eq_single r (fun q hq hqr => hOthers q hq hqr)
        (fun hNot => False.elim (hNot hr))
      _ = 1 := hOne

noncomputable def hintFinalUnion (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj maxR : ℕ) (v : HintVec G.rows) : Finset (Finset ℕ) := by
  classical
  exact (Finset.range (maxR + 1)).biUnion (fun r => family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v))

noncomputable def hintFinalRawCount (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj maxR : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) : ℕ :=
  ∑ r ∈ Finset.range (maxR + 1), (hintFamilySuccesses G coords beta Nj r v hPos).card

theorem hintFamily_count_eq (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r s : ℕ) (v : HintVec G.rows) (C : Finset ℕ)
    (hR : C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v))
    (hS : C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) s (List.ofFn v)) : r = s := by
  have hRCard := ((hintFamily_mem hPrefix Nj beta _ C r v).mp hR).2.1
  have hSCard := ((hintFamily_mem hPrefix Nj beta _ C s v).mp hS).2.1
  exact hRCard.symm.trans hSCard

/-- The raw number of successful outside classes, summed over all outside
    counts, detects the singleton union used by the original final worker. -/
theorem hintFinalRawCount_one (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj maxR : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (hHintValid : ∀ j, (coords j).val < Nj) :
    hintFinalRawCount G coords beta Nj maxR v hPos = 1 ↔ (hintFinalUnion G coords beta Nj maxR v).card = 1 := by
  classical
  let Fam := fun r => family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)
  let S := fun r => hintFamilySuccesses G coords beta Nj r v hPos
  let U := hintFinalUnion G coords beta Nj maxR v
  constructor
  · intro hCount
    obtain ⟨r, hr, hOne, hOthers⟩ := (hintNatSum_one (Finset.range (maxR + 1)) (fun r => (S r).card)).mp hCount
    have hFamOne : (Fam r).card = 1 :=
      (hintFamilySuccesses_card_one G coords hInj beta hPrefix Nj r v hPos hHintValid).mp hOne
    obtain ⟨C, hFamEq⟩ := Finset.card_eq_one.mp hFamOne
    have hC : C ∈ Fam r := by rw [hFamEq]; simp
    have hCU : C ∈ U := Finset.mem_biUnion.mpr ⟨r, hr, hC⟩
    obtain ⟨n, hSEq⟩ := Finset.card_eq_one.mp hOne
    have hn : n ∈ S r := by rw [hSEq]; simp
    have hUniqueClass := (Finset.mem_filter.mp hn).2.2
    have hMatrix := hintFamilyClass_unique_injective G coords hInj beta hPrefix Nj r
      (hintTupleSet (hintOdometerEnumeration Nj r hPos n)) v hHintValid hUniqueClass
    have hUnique : ∀ D ∈ U, D = C := by
      intro D hDU
      obtain ⟨s, hs, hD⟩ := Finset.mem_biUnion.mp hDU
      by_cases hEq : s = r
      · subst s
        change D ∈ Fam r at hD
        simpa only [hFamEq, Finset.mem_singleton] using hD
      · have hZero : (S s).card = 0 := hOthers s hs hEq
        have hNonempty : (S s).Nonempty :=
          (hintFamilySuccesses_nonempty G coords hInj beta hPrefix Nj s v hPos hMatrix).mpr ⟨D, hD⟩
        have hPositive := Finset.card_pos.mpr hNonempty
        omega
    apply Finset.card_eq_one.mpr
    refine ⟨C, ?_⟩
    apply Finset.ext
    intro D
    simp only [Finset.mem_singleton]
    exact ⟨fun hD => hUnique D hD, fun hEq => hEq ▸ hCU⟩
  · intro hUnion
    change U.card = 1 at hUnion
    obtain ⟨C, hUEq⟩ := Finset.card_eq_one.mp hUnion
    have hCU : C ∈ U := by rw [hUEq]; simp
    obtain ⟨r, hr, hC⟩ := Finset.mem_biUnion.mp hCU
    have hFamEq : Fam r = {C} := by
      apply Finset.ext
      intro D
      simp only [Finset.mem_singleton]
      constructor
      · intro hD
        have hDU : D ∈ U := Finset.mem_biUnion.mpr ⟨r, hr, hD⟩
        simpa only [hUEq, Finset.mem_singleton] using hDU
      · intro hEq; exact hEq ▸ hC
    have hFamOne : (Fam r).card = 1 := by rw [hFamEq]; simp
    have hSOne : (S r).card = 1 :=
      (hintFamilySuccesses_card_one G coords hInj beta hPrefix Nj r v hPos hHintValid).mpr hFamOne
    apply (hintNatSum_one (Finset.range (maxR + 1)) (fun r => (S r).card)).mpr
    refine ⟨r, hr, hSOne, ?_⟩
    intro s hs hNe
    have hFamEmpty : Fam s = ∅ := by
      apply Finset.ext
      intro D
      constructor
      · intro hD
        have hDU : D ∈ U := Finset.mem_biUnion.mpr ⟨s, hs, hD⟩
        have hDC : D = C := by simpa only [hUEq, Finset.mem_singleton] using hDU
        subst D
        have hEq := hintFamily_count_eq G coords beta hPrefix Nj r s v C hC hD
        exact False.elim (hNe hEq.symm)
      · intro hFalse; exact False.elim (Finset.notMem_empty D hFalse)
    have hSEmpty : S s = ∅ := hintFamilySuccesses_empty G coords beta Nj s v hPos hFamEmpty
    rw [hSEmpty]
    rfl

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalRawCount_one
end -- Def_LinearSetReconciliation327_Main_HintFinalRaw20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalCap20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintCap2_add_capped (a b : ℕ) : min 2 (min 2 a + min 2 b) = min 2 (a + b) := by omega

noncomputable def hintFinalRawPrefix (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj j : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) : ℕ :=
  ∑ r ∈ Finset.range j, (hintFamilySuccesses G coords beta Nj r v hPos).card

theorem hintFinalRawPrefix_zero (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) :
    hintFinalRawPrefix G coords beta Nj 0 v hPos = 0 := by simp [hintFinalRawPrefix]

theorem hintFinalRawPrefix_succ (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj j : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) :
    hintFinalRawPrefix G coords beta Nj (j + 1) v hPos =
      hintFinalRawPrefix G coords beta Nj j v hPos + (hintFamilySuccesses G coords beta Nj j v hPos).card := by
  exact Finset.sum_range_succ _ _

theorem hintFinalRawPrefix_full (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj maxR : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) :
    hintFinalRawPrefix G coords beta Nj (maxR + 1) v hPos = hintFinalRawCount G coords beta Nj maxR v hPos := rfl

def hintCapAddCode : List Instr :=
  [.add 0 0 8, .imm 9 2, .lt 1 9 0, .mul 8 1 9, .imm 15 1,
    .bxor 1 1 15, .mul 0 0 1, .add 0 0 8, .store 4 0]

theorem hintCapAddCode_spec (E : RAMEnv) (state : RAMState) (dest globalCap localCap : ℕ)
    (hWord : 4 < 2 ^ E.W) (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (h4 : state.regs 4 = dest) (h0 : state.regs 0 = globalCap) (h8 : state.regs 8 = localCap) :
    let out := runBlock hintCapAddCode E state
    out.pc = state.pc + 9 ∧ out.mem = Function.update state.mem dest (min 2 (globalCap + localCap)) ∧
      out.regs 0 = min 2 (globalCap + localCap) ∧ out.regs 14 = state.regs 14 := by
  have hSum : globalCap + localCap < 2 ^ E.W := by omega
  have hOne : 1 < 2 ^ E.W := by omega
  have hTwo : 2 < 2 ^ E.W := by omega
  by_cases hLe : globalCap + localCap ≤ 2
  · have hNot : ¬ 2 < globalCap + localCap := by omega
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [hintCapAddCode, runBlock, execInstr, h4, h0, h8, hNot, min_eq_right hLe,
        Nat.mod_eq_of_lt hSum, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hTwo]
  · have hGt : 2 < globalCap + localCap := by omega
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [hintCapAddCode, runBlock, execInstr, h4, h0, h8, hGt, min_eq_left (by omega : 2 ≤ globalCap + localCap),
        Nat.mod_eq_of_lt hSum, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hTwo]

def hintFinalCapFetch : List Instr :=
  [.imm 4 7, .add 4 11 4, .load 0 4, .imm 3 3, .add 3 11 3, .load 8 3]
def hintFinalCapCode : List Instr := hintScanParent ++ hintFinalCapFetch ++ hintCapAddCode

theorem hintFinalCapFetch_spec (E : RAMEnv) (state : RAMState) (parent globalCap localCap : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hParent : state.regs 11 = parent)
    (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (hReadGlobal : state.mem (parent + 7) = globalCap) (hReadLocal : state.mem (parent + 3) = localCap) :
    let out := runBlock hintFinalCapFetch E state
    out.pc = state.pc + 6 ∧ out.mem = state.mem ∧ out.regs 4 = parent + 7 ∧ out.regs 0 = globalCap ∧
      out.regs 8 = localCap ∧ out.regs 14 = state.regs 14 := by
  have h7 : 7 < 2 ^ E.W := by omega
  have h3 : 3 < 2 ^ E.W := by omega
  have hP7 : parent + 7 < 2 ^ E.W := by omega
  have hP3 : parent + 3 < 2 ^ E.W := by omega
  have hGW : globalCap < 2 ^ E.W := by omega
  have hLW : localCap < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintFinalCapFetch, runBlock, execInstr, hParent, hReadGlobal, hReadLocal,
      Nat.mod_eq_of_lt h7, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hP7, Nat.mod_eq_of_lt hP3,
      Nat.mod_eq_of_lt hGW, Nat.mod_eq_of_lt hLW]

theorem hintFinalCapCode_spec (E : RAMEnv) (state : RAMState) (parent globalCap localCap : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (hReadGlobal : state.mem (parent + 7) = globalCap) (hReadLocal : state.mem (parent + 3) = localCap) :
    let out := runBlock hintFinalCapCode E state
    out.pc = state.pc + 17 ∧ out.mem = Function.update state.mem (parent + 7) (min 2 (globalCap + localCap)) ∧
      out.regs 0 = min 2 (globalCap + localCap) ∧ out.regs 14 = parent + 16 := by
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hFetch := hintFinalCapFetch_spec E sP parent globalCap localCap hEnd hParentP hGlobal hLocal
    (by rw [hMemP]; exact hReadGlobal) (by rw [hMemP]; exact hReadLocal)
  generalize hF : runBlock hintFinalCapFetch E sP = sF at hFetch
  obtain ⟨hPcF, hMemF, h4, h0, h8, hContextF⟩ := hFetch
  have hAdd := hintCapAddCode_spec E sF (parent + 7) globalCap localCap (by omega) hGlobal hLocal h4 h0 h8
  generalize hA : runBlock hintCapAddCode E sF = out at hAdd
  obtain ⟨hPcA, hMemA, hValueA, hContextA⟩ := hAdd
  have hRun : runBlock hintFinalCapCode E state = out := by rw [hintFinalCapCode, runBlock_append, runBlock_append, hP, hF, hA]
  rw [hRun]
  exact ⟨by omega, by rw [hMemA, hMemF, hMemP], hValueA, hContextA.trans (hContextF.trans hContextP)⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalCapCode_spec
end -- Def_LinearSetReconciliation327_Main_HintFinalCap20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalChoose20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalChooseTail : List Instr := [.imm 15 1, .lt 1 0 15, .bxor 9 8 15, .lt 9 9 15, .mul 1 1 9]
def hintFinalChooseCode : List Instr := hintScanParent ++ hintFinalCapFetch ++ hintFinalChooseTail

theorem hintFinalChooseTail_spec (E : RAMEnv) (state : RAMState) (globalCap localCap : ℕ)
    (hWord : 4 < 2 ^ E.W) (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (h0 : state.regs 0 = globalCap) (h8 : state.regs 8 = localCap) :
    let out := runBlock hintFinalChooseTail E state
    out.pc = state.pc + 5 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (globalCap = 0 ∧ localCap = 1) ∧
      out.regs 14 = state.regs 14 := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hThree : 3 < 2 ^ E.W := by omega
  interval_cases globalCap <;> interval_cases localCap <;>
    refine ⟨?_, rfl, ?_, ?_⟩ <;>
    simp [hintFinalChooseTail, runBlock, execInstr, h0, h8, hintTruth, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hThree]

theorem hintFinalChooseCode_spec (E : RAMEnv) (state : RAMState) (parent globalCap localCap : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (hReadGlobal : state.mem (parent + 7) = globalCap) (hReadLocal : state.mem (parent + 3) = localCap) :
    let out := runBlock hintFinalChooseCode E state
    out.pc = state.pc + 13 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (globalCap = 0 ∧ localCap = 1) ∧
      out.regs 14 = parent + 16 := by
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hFetch := hintFinalCapFetch_spec E sP parent globalCap localCap hEnd hParentP hGlobal hLocal
    (by rw [hMemP]; exact hReadGlobal) (by rw [hMemP]; exact hReadLocal)
  generalize hF : runBlock hintFinalCapFetch E sP = sF at hFetch
  obtain ⟨hPcF, hMemF, _, h0, h8, hContextF⟩ := hFetch
  have hChoose := hintFinalChooseTail_spec E sF globalCap localCap (by omega) hGlobal hLocal h0 h8
  generalize hC : runBlock hintFinalChooseTail E sF = out at hChoose
  obtain ⟨hPcC, hMemC, hFlagC, hContextC⟩ := hChoose
  have hRun : runBlock hintFinalChooseCode E state = out := by rw [hintFinalChooseCode, runBlock_append, runBlock_append, hP, hF, hC]
  rw [hRun]
  exact ⟨by omega, hMemC.trans (hMemF.trans hMemP), hFlagC, hContextC.trans (hContextF.trans hContextP)⟩

def hintFinalSaveTail : List Instr := [.load 4 11, .load 0 4, .imm 3 8, .add 3 11 3, .store 3 0]
def hintFinalSaveCode : List Instr := hintScanParent ++ hintFinalSaveTail

theorem hintFinalSaveCode_spec (E : RAMEnv) (state : RAMState) (parent outsideBase r : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase < 2 ^ E.W) (hR : r < 2 ^ E.W)
    (hPointer : state.mem parent = outsideBase) (hCount : state.mem outsideBase = r) :
    let out := runBlock hintFinalSaveCode E state
    out.pc = state.pc + 7 ∧ out.mem = Function.update state.mem (parent + 8) r ∧ out.regs 14 = parent + 16 := by
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hPointerP : sP.mem parent = outsideBase := by rw [hMemP]; exact hPointer
  have hCountP : sP.mem outsideBase = r := by rw [hMemP]; exact hCount
  have h8 : 8 < 2 ^ E.W := by omega
  have hAddr : parent + 8 < 2 ^ E.W := by omega
  have hTail : let out := runBlock hintFinalSaveTail E sP
      out.pc = sP.pc + 5 ∧ out.mem = Function.update sP.mem (parent + 8) r ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [hintFinalSaveTail, runBlock, execInstr, hParentP, hContextP, hPointerP, hCountP,
        Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt hAddr]
  generalize hT : runBlock hintFinalSaveTail E sP = out at hTail
  obtain ⟨hPcT, hMemT, hContextT⟩ := hTail
  have hRun : runBlock hintFinalSaveCode E state = out := by rw [hintFinalSaveCode, runBlock_append, hP, hT]
  rw [hRun]
  exact ⟨by omega, by rw [hMemT, hMemP], hContextT⟩

def hintFinalChooseStmt : Stmt := .seq (.code hintFinalChooseCode)
  (.ite (.neqz 1) (.code hintFinalSaveCode) (.code []))
theorem hintFinalChooseStmt_len : hintFinalChooseStmt.len = 23 := rfl


theorem hintFinalChooseStmt_sem (parent outsideBase r globalCap localCap : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase < 2 ^ E.W) (hR : r < 2 ^ E.W) (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (hPointer : state.mem parent = outsideBase) (hCount : state.mem outsideBase = r)
    (hReadGlobal : state.mem (parent + 7) = globalCap) (hReadLocal : state.mem (parent + 3) = localCap)
    (hAt : At P base (hintFinalChooseStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 23) state (fun k out => k ≤ 22 ∧
      out.mem = (if globalCap = 0 ∧ localCap = 1 then Function.update state.mem (parent + 8) r else state.mem) ∧
      out.regs 14 = parent + 16) := by
  classical
  have hWord : 1 < 2 ^ E.W := by omega
  obtain ⟨hChooseAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base hintFinalChooseCode at hChooseAt
  change At P (base + 13) ((Stmt.ite (.neqz 1) (.code hintFinalSaveCode) (.code [])).compile (base + 13)) at hBranchAt
  have hChoose := hintFinalChooseCode_spec E state parent globalCap localCap hEnd hContext hGlobal hLocal hReadGlobal hReadLocal
  generalize hC : runBlock hintFinalChooseCode E state = sC at hChoose
  obtain ⟨hPcC, hMemC, hFlagC, hContextC⟩ := hChoose
  have hRunC : (step P E)^[13] state = sC := by
    have hh := iterate_runBlock_of_at P E hintFinalChooseCode state (by rwa [hPc])
      (by simp [hintFinalChooseCode, hintScanParent, hintFinalCapFetch, hintFinalChooseTail, NoBranch, Instr.NoBranchI])
    rw [hC] at hh
    exact hh
  let Q : ℕ → RAMState → Prop := fun k out => k ≤ 9 ∧
    out.mem = (if globalCap = 0 ∧ localCap = 1 then Function.update state.mem (parent + 8) r else state.mem) ∧
    out.regs 14 = parent + 16
  have hBranch : Sem P E (base + 13) (base + 23) sC Q := by
    apply Sem.ite P E (base + 13) (.neqz 1) (.code hintFinalSaveCode) (.code []) sC Q hBranchAt hWord (by omega)
    · intro hGo
      change Sem P E (base + 14) (base + 21) {sC with pc := base + 14}
        (fun k out => Q (1 + k + 1) {out with pc := base + 23})
      have hGood : globalCap = 0 ∧ localCap = 1 := by
        by_contra hBad
        have hZero : sC.regs 1 = 0 := by simpa [hintTruth, hBad] using hFlagC
        exact hGo hZero
      have hSave := hintFinalSaveCode_spec E {sC with pc := base + 14} parent outsideBase r hEnd hContextC hArray hR
        (by rw [hMemC]; exact hPointer) (by rw [hMemC]; exact hCount)
      generalize hS : runBlock hintFinalSaveCode E {sC with pc := base + 14} = sS at hSave
      obtain ⟨_, hMemS, hCtxS⟩ := hSave
      have hNative := Sem.block P E (base + 14) hintFinalSaveCode {sC with pc := base + 14}
        (at_ite hBranchAt).2.2.1 (by simp [hintFinalSaveCode, hintScanParent, hintFinalSaveTail, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hOut⟩ := hOut
      rw [hS] at hOut
      subst out
      refine ⟨by change k = 7 at hCost; omega, ?_, hCtxS⟩
      change sS.mem = _
      rw [if_pos hGood, hMemS, hMemC]
    · intro hStop
      change Sem P E (base + 22) (base + 22) {sC with pc := base + 22}
        (fun k out => Q (1 + k + 1) {out with pc := base + 23})
      have hBad : ¬ (globalCap = 0 ∧ localCap = 1) := by
        intro hGood
        have hOne : sC.regs 1 = 1 := by simpa [hintTruth, hGood] using hFlagC
        apply hStop
        change sC.regs 1 ≠ 0
        rw [hOne]; decide
      have hNative := Sem.block P E (base + 22) [] {sC with pc := base + 22}
        (at_ite hBranchAt).2.2.2.2.1 (by simp [NoBranch]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      refine ⟨by change k = 0 at hCost; omega, ?_, hContextC⟩
      change sC.mem = _
      rw [if_neg hBad]
      exact hMemC
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hMemB, hCtxB⟩ := hBranch
  exact ⟨hPc, kB + 13, out, hintIterate_then (step P E) hRunC hRunB, hPcB, by omega, hMemB, hCtxB⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalChooseStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintFinalChoose20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalAccumulate20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFinalAccumulateStmt : Stmt := .seq hintFinalChooseStmt (.code hintFinalCapCode)
theorem hintFinalAccumulateStmt_len : hintFinalAccumulateStmt.len = 40 := rfl

/-- Save the first singleton class's outside count, then add the real local
    count to the global capped count. Only parent slots 7 and 8 can change. -/
theorem hintFinalAccumulateStmt_sem (parent outsideBase r globalCap localCap : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase < 2 ^ E.W) (hR : r < 2 ^ E.W) (hGlobal : globalCap ≤ 2) (hLocal : localCap ≤ 2)
    (hPointer : state.mem parent = outsideBase) (hCount : state.mem outsideBase = r)
    (hReadGlobal : state.mem (parent + 7) = globalCap) (hReadLocal : state.mem (parent + 3) = localCap)
    (hAt : At P base (hintFinalAccumulateStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 40) state (fun k out => k ≤ 39 ∧
      out.mem = Function.update
        (if globalCap = 0 ∧ localCap = 1 then Function.update state.mem (parent + 8) r else state.mem)
        (parent + 7) (min 2 (globalCap + localCap)) ∧
      out.regs 0 = min 2 (globalCap + localCap) ∧ out.regs 14 = parent + 16) := by
  classical
  obtain ⟨hChooseAt, hCapAt⟩ := At.seqStmt hAt
  change At P base (hintFinalChooseStmt.compile base) at hChooseAt
  change At P (base + 23) hintFinalCapCode at hCapAt
  obtain ⟨_, kC, sC, hRunC, hPcC, hCostC, hMemC, hCtxC⟩ :=
    hintFinalChooseStmt_sem parent outsideBase r globalCap localCap P E state base hEnd hContext
      hArray hR hGlobal hLocal hPointer hCount hReadGlobal hReadLocal hChooseAt hPc
  have hUntouched : ∀ addr, addr ≠ parent + 8 → sC.mem addr = state.mem addr := by
    intro addr hNe
    rw [hMemC]
    split_ifs <;> simp [Function.update_of_ne hNe]
  have hCap := hintFinalCapCode_spec E sC parent globalCap localCap hEnd hCtxC hGlobal hLocal
    ((hUntouched _ (by omega)).trans hReadGlobal) ((hUntouched _ (by omega)).trans hReadLocal)
  generalize hA : runBlock hintFinalCapCode E sC = out at hCap
  obtain ⟨hPcA, hMemA, hValueA, hCtxA⟩ := hCap
  have hRunA : (step P E)^[17] sC = out := by
    have hh := iterate_runBlock_of_at P E hintFinalCapCode sC (by rwa [hPcC])
      (by simp [hintFinalCapCode, hintScanParent, hintFinalCapFetch, hintCapAddCode, NoBranch, Instr.NoBranchI])
    rw [hA] at hh
    exact hh
  refine ⟨hPc, 17 + kC, out, hintIterate_then (step P E) hRunC hRunA, by omega, by omega, ?_, hValueA, hCtxA⟩
  rw [hMemA, hMemC]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFinalAccumulateStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintFinalAccumulate20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalSaved20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintSavedUnique (f : ℕ → ℕ) (j saved : ℕ) : Prop :=
  (∑ r ∈ Finset.range j, f r) = 1 → saved < j ∧ f saved = 1 ∧ ∀ r < j, r ≠ saved → f r = 0

theorem HintSavedUnique.zero (f : ℕ → ℕ) (saved : ℕ) : HintSavedUnique f 0 saved := by
  intro hSum
  simp at hSum

theorem HintSavedUnique.step (f : ℕ → ℕ) (j saved : ℕ) (hOld : HintSavedUnique f j saved) :
    HintSavedUnique f (j + 1)
      (if min 2 (∑ r ∈ Finset.range j, f r) = 0 ∧ min 2 (f j) = 1 then j else saved) := by
  classical
  intro hNew
  have hStep := Finset.sum_range_succ f j
  have hSum : (∑ r ∈ Finset.range j, f r) + f j = 1 := by rw [← hStep]; exact hNew
  by_cases hZero : (∑ r ∈ Finset.range j, f r) = 0
  · have hOne : f j = 1 := by omega
    have hCond : min 2 (∑ r ∈ Finset.range j, f r) = 0 ∧ min 2 (f j) = 1 := by omega
    rw [if_pos hCond]
    refine ⟨by omega, hOne, ?_⟩
    intro r hr hNe
    have hr' : r ∈ Finset.range j := Finset.mem_range.mpr (by omega)
    have hLe : f r ≤ ∑ s ∈ Finset.range j, f s := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr'
    omega
  · have hOne : (∑ r ∈ Finset.range j, f r) = 1 := by omega
    have hJZero : f j = 0 := by omega
    have hCond : ¬ (min 2 (∑ r ∈ Finset.range j, f r) = 0 ∧ min 2 (f j) = 1) := by omega
    rw [if_neg hCond]
    obtain ⟨hSaved, hSavedOne, hOthers⟩ := hOld hOne
    refine ⟨by omega, hSavedOne, ?_⟩
    intro r hr hNe
    by_cases hEq : r = j
    · simpa only [hEq] using hJZero
    · exact hOthers r (by omega) hNe

theorem hintCappedPrefix_step (f : ℕ → ℕ) (j : ℕ) :
    min 2 (min 2 (∑ r ∈ Finset.range j, f r) + min 2 (f j)) =
      min 2 (∑ r ∈ Finset.range (j + 1), f r) := by
  rw [Finset.sum_range_succ, hintCap2_add_capped]

theorem hintFinal_cap_one (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj maxR : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (hHintValid : ∀ j, (coords j).val < Nj) :
    min 2 (hintFinalRawPrefix G coords beta Nj (maxR + 1) v hPos) = 1 ↔
      (hintFinalUnion G coords beta Nj maxR v).card = 1 := by
  rw [hintFinalRawPrefix_full]
  exact (hintCap2_one _).trans (hintFinalRawCount_one G coords hInj beta hPrefix Nj maxR v hPos hHintValid)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintSavedUnique.step
#print axioms LinearSetReconciliation327.Main.hintFinal_cap_one
end -- Def_LinearSetReconciliation327_Main_HintFinalSaved20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalFrame20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintFinalFrame (G : HintGaussArea) (parent outsideBase bitmapBase Nj maxR : ℕ)
    (original memory : ℕ → ℕ) : Prop :=
  ∀ addr, (addr < bitmapBase ∨ bitmapBase + Nj ≤ addr) →
    (addr < outsideBase ∨ outsideBase + 1 + maxR ≤ addr) →
    addr ≠ parent + 3 → addr ≠ parent + 7 → addr ≠ parent + 8 →
    (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
    (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → memory addr = original addr

theorem HintFinalFrame.refl (G : HintGaussArea) (parent outsideBase bitmapBase Nj maxR : ℕ) (memory : ℕ → ℕ) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR memory memory := by intro _ _ _ _ _ _ _ _; rfl

theorem HintFinalFrame.trans {G : HintGaussArea} {parent outsideBase bitmapBase Nj maxR : ℕ}
    {first middle last : ℕ → ℕ}
    (h1 : HintFinalFrame G parent outsideBase bitmapBase Nj maxR first middle)
    (h2 : HintFinalFrame G parent outsideBase bitmapBase Nj maxR middle last) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR first last := by
  intro addr hB hO h3 h7 h8 hR hG
  exact (h2 addr hB hO h3 h7 h8 hR hG).trans (h1 addr hB hO h3 h7 h8 hR hG)

theorem HintFinalFrame.of_controller {G : HintGaussArea} {parent outsideBase bitmapBase Nj maxR : ℕ}
    {original memory : ℕ → ℕ} (h : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR original memory) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR original memory := by
  intro addr hB hO h3 _ _ hR hG
  exact h addr hB hO h3 hR hG

theorem HintFinalFrame.of_scan {G : HintGaussArea} {parent outsideBase bitmapBase Nj maxR r : ℕ}
    {original memory : ℕ → ℕ} (hr : r ≤ maxR) (h : HintScanFrame G parent outsideBase r original memory) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR original memory := by
  apply HintFinalFrame.of_controller
  apply HintRowControllerFrame.of_row hr
  intro addr _ hO h3 hR hG
  exact h addr hO h3 hR hG

theorem HintFinalFrame.set_meta (G : HintGaussArea) (parent outsideBase bitmapBase Nj maxR : ℕ)
    (memory : ℕ → ℕ) (i value : ℕ) (hi : i = 7 ∨ i = 8) :
    HintFinalFrame G parent outsideBase bitmapBase Nj maxR memory (Function.update memory (parent + i) value) := by
  intro addr _ _ _ h7 h8 _ _
  apply Function.update_of_ne
  rcases hi with rfl | rfl
  · exact h7
  · exact h8

theorem HintFinalFrame.parent {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR parent outsideBase bitmapBase : ℕ} {original memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hFrame : HintFinalFrame G parent outsideBase bitmapBase Nj maxR original memory)
    (i : ℕ) (hi : 4 ≤ i) (hi' : i < 16) (h7 : i ≠ 7) (h8 : i ≠ 8) :
    memory (parent + i) = original (parent + i) := by
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  have hParent := hPublic.parent_eq
  exact hFrame _ (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inl (by omega))

theorem HintScanReadOnly.set_count {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR oldCount parent outsideBase bitmapBase : ℕ} {v : HintVec G.rows} {memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hData : HintScanReadOnly G coords Nj oldCount parent outsideBase bitmapBase v memory) (count : ℕ) :
    HintScanReadOnly G coords Nj count parent outsideBase bitmapBase v (Function.update memory outsideBase count) := by
  have hInput := HintRowInput.set_count hPublic
    (HintRowInput.mk hData.outside_pointer hData.bitmap_pointer hData.radix hData.outside_count hData.hints hData.observation) count
  refine ⟨hInput.outside_pointer, hInput.bitmap_pointer, hInput.radix, hInput.outside_count, hInput.hints, hInput.observation, ?_⟩
  intro q hq
  rw [Function.update_of_ne (by have := hPublic.bitmap_span; omega : bitmapBase + q ≠ outsideBase)]
  exact hData.bitmap q hq

theorem HintScanReadOnly.set_meta {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR count parent outsideBase bitmapBase : ℕ} {v : HintVec G.rows} {memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hData : HintScanReadOnly G coords Nj count parent outsideBase bitmapBase v memory)
    (i value : ℕ) (hi : 3 ≤ i) :
    HintScanReadOnly G coords Nj count parent outsideBase bitmapBase v (Function.update memory (parent + i) value) := by
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega : parent ≠ parent + i)]; exact hData.outside_pointer
  · rw [Function.update_of_ne (by omega : parent + 1 ≠ parent + i)]; exact hData.bitmap_pointer
  · rw [Function.update_of_ne (by omega : parent + 2 ≠ parent + i)]; exact hData.radix
  · rw [Function.update_of_ne (by omega : outsideBase ≠ parent + i)]; exact hData.outside_count
  · intro j
    rw [Function.update_of_ne (by have := j.isLt; omega : G.hintList + j.val ≠ parent + i)]
    exact hData.hints j
  · intro t
    rw [Function.update_of_ne (by have := t.isLt; omega : G.hintList + G.hints + G.rows + t.val ≠ parent + i)]
    exact hData.observation t
  · intro q hq
    rw [Function.update_of_ne (by omega : bitmapBase + q ≠ parent + i)]
    exact hData.bitmap q hq

theorem hintGaussHeader_set_meta {G : HintGaussArea} {index parent : ℕ} {memory : ℕ → ℕ}
    (hParent : parent + 16 = G.context) (hHeader : HintGaussHeader G index memory)
    (i value : ℕ) (hi : i < 16) : HintGaussHeader G index (Function.update memory (parent + i) value) := by
  intro t ht
  rw [Function.update_of_ne (by omega : G.context + t ≠ parent + i)]
  exact hHeader t ht

structure HintFinalState (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj parent outsideBase bitmapBase maxR j : ℕ)
    (v : HintVec G.rows) (hPos : 0 < Nj) (original : ℕ → ℕ) (state : RAMState) : Prop where
  readonly : HintScanReadOnly G coords Nj j parent outsideBase bitmapBase v state.mem
  header : ∃ index, HintGaussHeader G index state.mem
  context_value : state.regs 14 = G.context
  limit : state.mem (parent + 4) = maxR
  total : state.mem (parent + 7) = min 2 (hintFinalRawPrefix G coords beta Nj j v hPos)
  saved : HintSavedUnique (fun r => (hintFamilySuccesses G coords beta Nj r v hPos).card) j (state.mem (parent + 8))
  frame : HintFinalFrame G parent outsideBase bitmapBase Nj maxR original state.mem

theorem HintFinalState.pc {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {Nj parent outsideBase bitmapBase maxR j : ℕ}
    {v : HintVec G.rows} {hPos : 0 < Nj} {original : ℕ → ℕ} {state : RAMState}
    (h : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original state) (pc : ℕ) :
    HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original {state with pc := pc} :=
  ⟨h.readonly, h.header, h.context_value, h.limit, h.total, h.saved, h.frame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintScanReadOnly.set_meta
end -- Def_LinearSetReconciliation327_Main_HintFinalFrame20261120

section -- Def_LinearSetReconciliation327_Main_HintFinalAccInvariant20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintFinalTallied (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj parent outsideBase bitmapBase maxR count progress : ℕ)
    (v : HintVec G.rows) (hPos : 0 < Nj) (original : ℕ → ℕ) (state : RAMState) : Prop where
  readonly : HintScanReadOnly G coords Nj count parent outsideBase bitmapBase v state.mem
  header : ∃ index, HintGaussHeader G index state.mem
  context_value : state.regs 14 = G.context
  limit : state.mem (parent + 4) = maxR
  total : state.mem (parent + 7) = min 2 (hintFinalRawPrefix G coords beta Nj progress v hPos)
  saved : HintSavedUnique (fun r => (hintFamilySuccesses G coords beta Nj r v hPos).card) progress (state.mem (parent + 8))
  frame : HintFinalFrame G parent outsideBase bitmapBase Nj maxR original state.mem

theorem HintFinalState.after_accumulate {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj parent outsideBase bitmapBase maxR j : ℕ} {v : HintVec G.rows} {hPos : 0 < Nj}
    {original : ℕ → ℕ} {state out : RAMState}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hState : HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR j v hPos original state)
    (hMemory : out.mem = Function.update
      (if min 2 (hintFinalRawPrefix G coords beta Nj j v hPos) = 0 ∧
          min 2 (hintFamilySuccesses G coords beta Nj j v hPos).card = 1
        then Function.update state.mem (parent + 8) j else state.mem)
      (parent + 7) (min 2 (min 2 (hintFinalRawPrefix G coords beta Nj j v hPos) +
        min 2 (hintFamilySuccesses G coords beta Nj j v hPos).card)))
    (hContext : out.regs 14 = G.context) :
    HintFinalTallied G coords beta Nj parent outsideBase bitmapBase maxR j (j + 1) v hPos original out := by
  classical
  let oldSum := hintFinalRawPrefix G coords beta Nj j v hPos
  let localCount := (hintFamilySuccesses G coords beta Nj j v hPos).card
  let choose := min 2 oldSum = 0 ∧ min 2 localCount = 1
  let M := if choose then Function.update state.mem (parent + 8) j else state.mem
  let value := min 2 (min 2 oldSum + min 2 localCount)
  have hMemory' : out.mem = Function.update M (parent + 7) value := hMemory
  have hDataM : HintScanReadOnly G coords Nj j parent outsideBase bitmapBase v M := by
    dsimp only [M]
    split_ifs
    · exact HintScanReadOnly.set_meta hPublic hState.readonly 8 j (by decide)
    · exact hState.readonly
  have hHeaderM : ∃ index, HintGaussHeader G index M := by
    obtain ⟨index, hHeader⟩ := hState.header
    dsimp only [M]
    split_ifs
    · exact ⟨index, hintGaussHeader_set_meta hPublic.parent_eq hHeader 8 j (by decide)⟩
    · exact ⟨index, hHeader⟩
  have hFrameM : HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem M := by
    dsimp only [M]
    split_ifs
    · exact HintFinalFrame.set_meta G parent outsideBase bitmapBase Nj maxR state.mem 8 j (Or.inr rfl)
    · exact HintFinalFrame.refl G parent outsideBase bitmapBase Nj maxR state.mem
  have hLocalFrame : HintFinalFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem := by
    rw [hMemory']
    exact hFrameM.trans (HintFinalFrame.set_meta G parent outsideBase bitmapBase Nj maxR M 7 value (Or.inl rfl))
  refine ⟨?_, ?_, hContext, (hLocalFrame.parent hPublic 4 (by decide) (by decide) (by decide) (by decide)).trans hState.limit,
    ?_, ?_, hState.frame.trans hLocalFrame⟩
  · rw [hMemory']
    exact HintScanReadOnly.set_meta hPublic hDataM 7 value (by decide)
  · obtain ⟨index, hHeader⟩ := hHeaderM
    rw [hMemory']
    exact ⟨index, hintGaussHeader_set_meta hPublic.parent_eq hHeader 7 value (by decide)⟩
  · have hValueAt : out.mem (parent + 7) = value := by simp [hMemory']
    rw [hValueAt]
    change min 2 (min 2 (hintFinalRawPrefix G coords beta Nj j v hPos) +
        min 2 (hintFamilySuccesses G coords beta Nj j v hPos).card) =
      min 2 (hintFinalRawPrefix G coords beta Nj (j + 1) v hPos)
    rw [hintFinalRawPrefix_succ, hintCap2_add_capped]
  · have hSavedValue : out.mem (parent + 8) = if choose then j else state.mem (parent + 8) := by
      rw [hMemory', Function.update_of_ne (by omega : parent + 8 ≠ parent + 7)]
      dsimp only [M]
      split_ifs <;> simp
    rw [hSavedValue]
    exact hState.saved.step

theorem HintFinalTallied.after_count {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj parent outsideBase bitmapBase maxR j : ℕ} {v : HintVec G.rows} {hPos : 0 < Nj}
    {original : ℕ → ℕ} {state out : RAMState}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase)
    (hState : HintFinalTallied G coords beta Nj parent outsideBase bitmapBase maxR j (j + 1) v hPos original state)
    (hMemory : out.mem = Function.update state.mem outsideBase (j + 1)) (hContext : out.regs 14 = G.context) :
    HintFinalState G coords beta Nj parent outsideBase bitmapBase maxR (j + 1) v hPos original out := by
  have hFrame : HintRowControllerFrame G parent outsideBase bitmapBase Nj maxR state.mem out.mem := by
    rw [hMemory]
    exact HintRowControllerFrame.set_count G parent outsideBase bitmapBase Nj maxR state.mem (j + 1)
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hParent := hPublic.parent_eq
  refine ⟨?_, ?_, hContext, (hFrame.parent hPublic 4 (by decide) (by decide)).trans hState.limit,
    (hFrame.parent hPublic 7 (by decide) (by decide)).trans hState.total, ?_,
    hState.frame.trans (HintFinalFrame.of_controller hFrame)⟩
  · rw [hMemory]
    exact HintScanReadOnly.set_count hPublic hState.readonly (j + 1)
  · obtain ⟨index, hHeader⟩ := hState.header
    refine ⟨index, ?_⟩
    intro i hi
    rw [hMemory, Function.update_of_ne (by omega : G.context + i ≠ outsideBase)]
    exact hHeader i hi
  · rw [hFrame.parent hPublic 8 (by decide) (by decide)]
    exact hState.saved

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintFinalState.after_accumulate
end -- Def_LinearSetReconciliation327_Main_HintFinalAccInvariant20261120


