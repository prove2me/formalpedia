-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_04
-- name    : LinearSetReconciliation327_Main_Bundle51_04
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T13:20:17.570906+00:00
-- url     : https://prove2.me/theorems/07e8f0ca-85c4-41a1-ba43-67eb6e95e735
-- title:
--   LinearSetReconciliation327 — Bundle51_04
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_04` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_03

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_04
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintScanFirstPass20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBitmapLoop20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowBitmap20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintReplay20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFamilySolve20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowFamily20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPublicDot20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPublicSum20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNextPrep20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNextBit20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowPredictCount20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintScanFirstPass20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintScanFillPrep : List Instr := [.imm 7 1, .imm 8 0]
def hintScanCounterInit : List Instr := [.imm 8 0, .store 4 8, .imm 1 1]
def hintScanInitializeStmt : Stmt := .seq (.code hintScanOdometerPrep)
  (.seq (.code hintScanFillPrep) (.seq hintFillStmt (.seq (.code hintScanCounterPrep) (.code hintScanCounterInit))))
theorem hintScanInitializeStmt_len : hintScanInitializeStmt.len = 26 := rfl

/-- Clear the actual tuple array and capped count from arbitrary old values. -/
theorem hintScanInitializeStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintScanInitializeStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 26) state (fun k out => k = 7 * r + 21 ∧
      HintScanInv G coords beta Nj r parent outsideBase bitmapBase v hPublic.positive 0 state.mem out) := by
  classical
  have hSource := hPublic.source
  have hParent := hPublic.parent_eq
  have hOutside := hPublic.outside_span
  have h0 := hPublic.geometry.residual_before
  have h1 := hPublic.geometry.lift_before
  have h2 := hPublic.geometry.column_before
  have h3 := hPublic.geometry.residualVec_before
  have h4 := hPublic.geometry.kernelVec_before
  have h5 := hPublic.geometry.span
  have hReserve := hPublic.reserve
  have hEnd : parent + 16 < 2 ^ E.W := by omega
  have hWord := hPublic.geometry.word_bound
  have hNjWord : Nj < 2 ^ E.W := hPublic.bucket_bound.trans_lt (hPublic.fits.values 12 (by decide))
  obtain ⟨hPrepAt, hRest1⟩ := At.seqStmt hAt
  change At P base hintScanOdometerPrep at hPrepAt
  obtain ⟨hFillPrepAt, hRest2⟩ := At.seqStmt hRest1
  change At P (base + 9) hintScanFillPrep at hFillPrepAt
  obtain ⟨hFillAt, hRest3⟩ := At.seqStmt hRest2
  change At P (base + 11) (hintFillStmt.compile (base + 11)) at hFillAt
  obtain ⟨hCountPrepAt, hCountInitAt⟩ := At.seqStmt hRest3
  change At P (base + 19) hintScanCounterPrep at hCountPrepAt
  change At P (base + 23) hintScanCounterInit at hCountInitAt
  have hPrep := hintScanOdometerPrep_spec E state parent outsideBase r Nj hEnd (hContext.trans hParent.symm)
    (by omega) (by omega) hNjWord hData.outside_pointer hData.outside_count hData.radix
  generalize hP : runBlock hintScanOdometerPrep E state = sP at hPrep
  obtain ⟨hPcP, hMemP, ⟨h4P, h6P, _, h15P⟩, hCtxP⟩ := hPrep
  have hRunP : (step P E)^[9] state = sP := by
    have hh := iterate_runBlock_of_at P E hintScanOdometerPrep state (by rwa [hPc])
      (by simp [hintScanOdometerPrep, hintScanParent, hintScanOdometerInput, hintScanOdometerRadix, NoBranch, Instr.NoBranchI])
    rw [hP] at hh
    exact hh
  have hFillPrep : let out := runBlock hintScanFillPrep E sP
      out.pc = sP.pc + 2 ∧ out.mem = sP.mem ∧ HintFillParams (outsideBase + 1) 1 r 0 out ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp [hintScanFillPrep, runBlock, execInstr, h4P, h6P, h15P, hCtxP, Nat.mod_eq_of_lt hWord]
  generalize hZ : runBlock hintScanFillPrep E sP = sZ at hFillPrep
  obtain ⟨hPcZ, hMemZ, hFillArgs, hCtxZ⟩ := hFillPrep
  have hRunZ : (step P E)^[2] sP = sZ := by
    have hh := iterate_runBlock_of_at P E hintScanFillPrep sP (by rw [hPcP, hPc]; exact hFillPrepAt)
      (by simp [hintScanFillPrep, NoBranch, Instr.NoBranchI])
    rw [hZ] at hh
    exact hh
  obtain ⟨_, kF, sF, hRunF, hPcF, hCostF, _, hMemF, _, hFrameF, hRegsF⟩ :=
    hintFillStmt_sem P E sZ (outsideBase + 1) 1 r (base + 11) 0 hWord (by omega)
      (by intro j hj; simp only [Nat.mul_one]; omega) hFillAt (by rw [hPcZ, hPcP, hPc]) hFillArgs
  have hContextF : sF.regs 14 = parent + 16 := (hRegsF 14 (by decide) (by decide) (by decide)).trans hCtxZ
  have hArrayFrame : CRMemFrame (outsideBase + 1) (outsideBase + 1 + r) state.mem sF.mem := by
    intro addr hAway
    have hNot : addr ∉ hintFillPositions (outsideBase + 1) 1 r := by
      intro hIn
      obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hIn
      have hJ : j < r := Finset.mem_range.mp hj
      simp only [Nat.mul_one] at hEq
      rcases hAway with hBefore | hAfter <;> omega
    exact (hFrameF addr hNot).trans (congrFun (hMemZ.trans hMemP) addr)
  have hCountPrep := hintScanCounterPrep_spec E sF parent hEnd hContextF
  generalize hC : runBlock hintScanCounterPrep E sF = sC at hCountPrep
  obtain ⟨hPcC, hMemC, hPointerC, _, hContextC⟩ := hCountPrep
  have hRunC : (step P E)^[4] sF = sC := by
    have hh := iterate_runBlock_of_at P E hintScanCounterPrep sF (by rwa [hPcF])
      (by simp [hintScanCounterPrep, hintScanParent, NoBranch, Instr.NoBranchI])
    rw [hC] at hh
    exact hh
  have hInit : let out := runBlock hintScanCounterInit E sC
      out.pc = sC.pc + 3 ∧ out.mem = Function.update sC.mem (parent + 3) 0 ∧
      out.regs 1 = 1 ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [hintScanCounterInit, runBlock, execInstr, hPointerC, hContextC, Nat.mod_eq_of_lt hWord]
  generalize hQ : runBlock hintScanCounterInit E sC = out at hInit
  obtain ⟨hPcQ, hMemQ, hGoQ, hContextQ⟩ := hInit
  have hRunQ : (step P E)^[3] sC = out := by
    have hh := iterate_runBlock_of_at P E hintScanCounterInit sC (by rw [hPcC, hPcF]; exact hCountInitAt)
      (by simp [hintScanCounterInit, NoBranch, Instr.NoBranchI])
    rw [hQ] at hh
    exact hh
  have hFrame : HintScanFrame G parent outsideBase r state.mem out.mem := by
    intro addr hArray hCount _ _
    rw [hMemQ, Function.update_of_ne hCount, hMemC]
    exact hArrayFrame addr hArray
  have hDataOut := HintScanReadOnly.frame hPublic hData hFrame
  have hHeaderOut : ∃ index, HintGaussHeader G index out.mem := by
    obtain ⟨idx, hH⟩ := hHeader
    refine ⟨idx, ?_⟩
    intro i hi
    rw [hMemQ, Function.update_of_ne (by omega : G.context + i ≠ parent + 3), hMemC, hArrayFrame _ (Or.inr (by omega))]
    exact hH i hi
  have hZeros : ∀ i < r, out.mem (outsideBase + 1 + i) = 0 := by
    intro i hi
    have hIn : outsideBase + 1 + i ∈ hintFillPositions (outsideBase + 1) 1 r :=
      Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, by simp⟩
    rw [hMemQ, Function.update_of_ne (by omega : outsideBase + 1 + i ≠ parent + 3), hMemC, hMemF]
    simp [hintFillMem, hIn]
  have hCountZero : out.mem (parent + 3) = 0 := by simp [hMemQ]
  have hPower : 0 < Nj ^ r := pow_pos hPublic.positive r
  refine ⟨hPc, 3 + (4 + (kF + (2 + 9))), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) (hintIterate_then (step P E)
      (hintIterate_then (step P E) hRunP hRunZ) hRunF) hRunC) hRunQ,
    ?_, by omega, ⟨hDataOut, hHeaderOut, hContextQ.trans hParent, ?_, ?_, ?_, hFrame⟩⟩
  · rw [hPcQ, hPcC, hPcF]
  · intro i hi
    simpa only [hintEnumeratedDigits_zero] using hZeros i hi
  · rw [hCountZero, hintSuccessPrefix_zero]
    rfl
  · simpa [hintTruth, hPower] using hGoQ

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintScanFirstPassStmt : Stmt := .seq hintScanInitializeStmt hintScanLoop
theorem hintScanFirstPassStmt_len : hintScanFirstPassStmt.len = 661 := rfl

/-- The full first pass has no initialized-array or initialized-counter premise.
    Its physical count detects precisely the paper's original singleton family. -/
theorem hintScanFirstPassStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintScanFirstPassStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 661) state (fun k out => k ≤ 7 * r + 22 + (hintScanBodyTime G r + 2) * Nj ^ r ∧
      out.mem (parent + 3) = min 2 (hintFamilySuccesses G coords beta Nj r v hPublic.positive).card ∧
      (out.mem (parent + 3) = 1 ↔
        (HintParams.family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).card = 1) ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintScanFrame G parent outsideBase r state.mem out.mem) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base (hintScanInitializeStmt.compile base) at hInitAt
  change At P (base + 26) (hintScanLoop.compile (base + 26)) at hLoopAt
  obtain ⟨_, kI, sI, hRunI, hPcI, hCostI, hInvI⟩ :=
    hintScanInitializeStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E state base
      hPublic hData hHeader hContext hInitAt hPc
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hCounter, hSingleton, hDataOut, hHeaderOut, hContextOut, hFrame⟩ :=
    hintScanLoop_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v state.mem P E sI (base + 26)
      hPublic hInvI hLoopAt hPcI
  refine ⟨hPc, kL + kI, out, hintIterate_then (step P E) hRunI hRunL, ?_, by omega,
    hCounter, hSingleton, hDataOut, hHeaderOut, hContextOut, hFrame⟩
  · simpa only [Nat.add_assoc] using hPcL

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintScanFirstPassStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintScanFirstPass20261120

section -- Def_LinearSetReconciliation327_Main_HintBitmapLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintBitmapValue {h K : ℕ} (coords : Fin h → Fin K) (j q : ℕ) : ℕ :=
  hintTruth (q ∈ (hintGaussDone h j).image (fun i => (coords i).val))

theorem hintBitmapValue_zero {h K : ℕ} (coords : Fin h → Fin K) (q : ℕ) : hintBitmapValue coords 0 q = 0 := by
  simp [hintBitmapValue, hintGaussDone, hintTruth]

theorem hintBitmapValue_full {h K : ℕ} (coords : Fin h → Fin K) (q : ℕ) :
    hintBitmapValue coords h q = hintTruth (q ∈ Finset.univ.image (fun i => (coords i).val)) := by
  rw [hintBitmapValue, hintGaussDone_full]

theorem hintBitmapValue_step {h K : ℕ} (coords : Fin h → Fin K) (j : Fin h) (q : ℕ) :
    hintBitmapValue coords (j.val + 1) q = if q = (coords j).val then 1 else hintBitmapValue coords j.val q := by
  classical
  unfold hintBitmapValue
  rw [← hintGaussDone_succ j, Finset.image_insert]
  by_cases hEq : q = (coords j).val <;> simp [hintTruth, hEq]

structure HintBitmapArgs (dest src count : ℕ) (state : RAMState) : Prop where
  dest_value : state.regs 4 = dest
  src_value : state.regs 5 = src
  count_value : state.regs 6 = count
  one_value : state.regs 15 = 1

def hintBitmapBody : List Instr := [.add 3 5 0, .load 9 3, .add 3 4 9, .store 3 15, .add 0 0 15]

theorem hintBitmapBody_spec (E : RAMEnv) (state : RAMState) (dest src count j coordinate : ℕ)
    (hWord : 1 < 2 ^ E.W) (hSource : src + j < 2 ^ E.W) (hDest : dest + coordinate < 2 ^ E.W)
    (hCoord : coordinate < 2 ^ E.W) (hNext : j + 1 < 2 ^ E.W)
    (hArgs : HintBitmapArgs dest src count state) (hCounter : state.regs 0 = j)
    (hRead : state.mem (src + j) = coordinate) :
    let out := runBlock hintBitmapBody E state
    out.pc = state.pc + 5 ∧ out.mem = Function.update state.mem (dest + coordinate) 1 ∧
      out.regs 0 = j + 1 ∧ HintBitmapArgs dest src count out ∧ out.regs 14 = state.regs 14 := by
  obtain ⟨h4, h5, h6, h15⟩ := hArgs
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintBitmapBody, runBlock, execInstr, h4, h5, h6, h15, hCounter, hRead,
      Nat.mod_eq_of_lt hSource, Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hCoord, Nat.mod_eq_of_lt hNext]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

structure HintBitmapInv {h K : ℕ} (coords : Fin h → Fin K) (dest src Nj j : ℕ)
    (original : ℕ → ℕ) (state : RAMState) : Prop where
  args : HintBitmapArgs dest src h state
  counter : state.regs 0 = j
  bitmap : ∀ q < Nj, state.mem (dest + q) = hintBitmapValue coords j q
  frame : CRMemFrame dest (dest + Nj) original state.mem

theorem hintBitmapInv_step {h K : ℕ} (coords : Fin h → Fin K) (j : Fin h)
    (E : RAMEnv) (state : RAMState) (dest src Nj : ℕ) (original : ℕ → ℕ)
    (hWord : 1 < 2 ^ E.W) (hSourceSpan : src + h < 2 ^ E.W) (hDestSpan : dest + Nj ≤ 2 ^ E.W)
    (hSeparate : dest + Nj ≤ src) (hValid : ∀ i, (coords i).val < Nj)
    (hHints : ∀ i : Fin h, original (src + i.val) = (coords i).val)
    (hInv : HintBitmapInv coords dest src Nj j.val original state) :
    let out := runBlock hintBitmapBody E state
    HintBitmapInv coords dest src Nj (j.val + 1) original out := by
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
    rw [hMem, hintBitmapValue_step]
    by_cases hEq : q = (coords j).val
    · subst q
      simp
    · rw [Function.update_of_ne (by omega : dest + q ≠ dest + (coords j).val), hInv.bitmap q hq, if_neg hEq]
  · intro addr hAway
    have hNe : addr ≠ dest + (coords j).val := by have := hValid j; rcases hAway with hBefore | hAfter <;> omega
    rw [hMem, Function.update_of_ne hNe, hInv.frame addr hAway]

theorem HintBitmapInv.pc {h K : ℕ} {coords : Fin h → Fin K} {dest src Nj j : ℕ}
    {original : ℕ → ℕ} {state : RAMState} (hI : HintBitmapInv coords dest src Nj j original state) (pc : ℕ) :
    HintBitmapInv coords dest src Nj j original {state with pc := pc} :=
  ⟨⟨hI.args.dest_value, hI.args.src_value, hI.args.count_value, hI.args.one_value⟩, hI.counter, hI.bitmap, hI.frame⟩

theorem HintBitmapInv.test {h K : ℕ} {coords : Fin h → Fin K} {dest src Nj j : ℕ}
    {original : ℕ → ℕ} {state : RAMState} (hI : HintBitmapInv coords dest src Nj j original state) (E : RAMEnv) :
    HintBitmapInv coords dest src Nj j original (runBlock (Cond.lt 2 0 6).code E state) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using hI.args.dest_value
  · simpa [Cond.code, runBlock, execInstr] using hI.args.src_value
  · simpa [Cond.code, runBlock, execInstr] using hI.args.count_value
  · simpa [Cond.code, runBlock, execInstr] using hI.args.one_value
  · simpa [Cond.code, runBlock, execInstr] using hI.counter
  · simpa [Cond.code, runBlock, execInstr] using hI.bitmap
  · simpa [Cond.code, runBlock, execInstr] using hI.frame

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintBitmapLoop : Stmt := .loop (.lt 2 0 6) (.code hintBitmapBody)
theorem hintBitmapLoop_len : hintBitmapLoop.len = 8 := rfl

theorem hintBitmapLoop_sem {h K : ℕ} (coords : Fin h → Fin K)
    (dest src Nj : ℕ) (original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hSourceSpan : src + h < 2 ^ E.W) (hDestSpan : dest + Nj ≤ 2 ^ E.W)
    (hSeparate : dest + Nj ≤ src) (hValid : ∀ i, (coords i).val < Nj)
    (hHints : ∀ i : Fin h, original (src + i.val) = (coords i).val)
    (hInv : HintBitmapInv coords dest src Nj 0 original state)
    (hAt : At P base (hintBitmapLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 8) state (fun k out => k ≤ 8 * h + 2 ∧
      (∀ q < Nj, out.mem (dest + q) = hintTruth (q ∈ Finset.univ.image (fun i => (coords i).val))) ∧
      HintBitmapArgs dest src h out ∧ CRMemFrame dest (dest + Nj) original out.mem ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = h ∧
    HintBitmapInv coords dest src Nj j original st ∧ st.regs 14 = state.regs 14
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
    have hStep := hintBitmapInv_step coords t E st dest src Nj original hWord hSourceSpan hDestSpan hSeparate hValid hHints hBitmap
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
  simpa only [hintBitmapValue_full] using hFinal.bitmap

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintBitmapLoop_sem
end -- Def_LinearSetReconciliation327_Main_HintBitmapLoop20261120

section -- Def_LinearSetReconciliation327_Main_HintRowBitmap20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintParentLoad (dest : Fin 16) (offset : ℕ) : List Instr :=
  [.imm 3 offset, .add 3 11 3, .load dest 3]

theorem hintParentLoad_spec (E : RAMEnv) (state : RAMState) (parent offset : ℕ) (dest : Fin 16)
    (hParent : state.regs 11 = parent) (hAddr : parent + offset < 2 ^ E.W)
    (h11 : dest ≠ 11) (h14 : dest ≠ 14) :
    let out := runBlock (hintParentLoad dest offset) E state
    out.pc = state.pc + 3 ∧ out.mem = state.mem ∧
      out.regs dest = state.mem (parent + offset) % 2 ^ E.W ∧ out.regs 11 = parent ∧
      out.regs 14 = state.regs 14 ∧
      (∀ reg : Fin 16, reg ≠ 3 → reg ≠ dest → out.regs reg = state.regs reg) := by
  have hOffset : offset < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp [hintParentLoad, runBlock, execInstr]
  · simp [hintParentLoad, runBlock, execInstr, hParent, Nat.mod_eq_of_lt hOffset, Nat.mod_eq_of_lt hAddr]
  · simp [hintParentLoad, runBlock, execInstr, hParent, Ne.symm h11]
  · simp [hintParentLoad, runBlock, execInstr, Ne.symm h14]
  · intro reg hR3 hRD
    simp [hintParentLoad, runBlock, execInstr, hR3, hRD]

structure HintRowInput (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows) (memory : ℕ → ℕ) : Prop where
  outside_pointer : memory parent = outsideBase
  bitmap_pointer : memory (parent + 1) = bitmapBase
  radix : memory (parent + 2) = Nj
  outside_count : memory outsideBase = r
  hints : ∀ j : Fin G.hints, memory (G.hintList + j.val) = (coords j).val
  observation : ∀ s : Fin G.rows, memory (G.hintList + G.hints + G.rows + s.val) = (v s).val

theorem HintRowInput.frame {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj r parent outsideBase bitmapBase : ℕ} {v : HintVec G.rows} {original memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj r parent outsideBase bitmapBase v original)
    (hFrame : CRMemFrame bitmapBase (bitmapBase + Nj) original memory) :
    HintRowInput G coords Nj r parent outsideBase bitmapBase v memory := by
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFrame _ (Or.inr (by omega))]; exact hInput.outside_pointer
  · rw [hFrame _ (Or.inr (by omega))]; exact hInput.bitmap_pointer
  · rw [hFrame _ (Or.inr (by omega))]; exact hInput.radix
  · rw [hFrame _ (Or.inr (by omega))]; exact hInput.outside_count
  · intro j
    rw [hFrame _ (Or.inr (by omega))]
    exact hInput.hints j
  · intro s
    rw [hFrame _ (Or.inr (by omega))]
    exact hInput.observation s

theorem HintRowInput.with_bitmap {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {Nj r parent outsideBase bitmapBase : ℕ} {v : HintVec G.rows} {memory : ℕ → ℕ}
    (hInput : HintRowInput G coords Nj r parent outsideBase bitmapBase v memory)
    (hBitmap : ∀ q < Nj, memory (bitmapBase + q) = hintTruth (q ∈ Finset.univ.image (fun j => (coords j).val))) :
    HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v memory :=
  ⟨hInput.outside_pointer, hInput.bitmap_pointer, hInput.radix, hInput.outside_count, hInput.hints, hInput.observation, hBitmap⟩

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintBitmapConstants : List Instr := [.imm 7 1, .imm 8 0, .imm 15 1]
def hintBitmapClearPrep : List Instr :=
  hintScanParent ++ hintParentLoad 4 1 ++ hintParentLoad 6 2 ++ hintBitmapConstants

theorem hintBitmapClearPrep_spec (E : RAMEnv) (state : RAMState) (parent bitmapBase Nj : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hBitmap : bitmapBase < 2 ^ E.W) (hNj : Nj < 2 ^ E.W)
    (hReadBitmap : state.mem (parent + 1) = bitmapBase) (hReadNj : state.mem (parent + 2) = Nj) :
    let out := runBlock hintBitmapClearPrep E state
    out.pc = state.pc + 11 ∧ out.mem = state.mem ∧ HintFillParams bitmapBase 1 Nj 0 out ∧
      out.regs 11 = parent ∧ out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hParentP, hContextP⟩ := hParentSpec
  have hLoadB := hintParentLoad_spec E sP parent 1 4 hParentP (by omega) (by decide) (by decide)
  generalize hB : runBlock (hintParentLoad 4 1) E sP = sB at hLoadB
  obtain ⟨hPcB, hMemB, hValueB, hParentB, hContextB, _⟩ := hLoadB
  have h4B : sB.regs 4 = bitmapBase := by rw [hValueB, hMemP, hReadBitmap, Nat.mod_eq_of_lt hBitmap]
  have hLoadN := hintParentLoad_spec E sB parent 2 6 hParentB (by omega) (by decide) (by decide)
  generalize hN : runBlock (hintParentLoad 6 2) E sB = sN at hLoadN
  obtain ⟨hPcN, hMemN, hValueN, hParentN, hContextN, hRegsN⟩ := hLoadN
  have h6N : sN.regs 6 = Nj := by rw [hValueN, hMemB, hMemP, hReadNj, Nat.mod_eq_of_lt hNj]
  have h4N : sN.regs 4 = bitmapBase := (hRegsN 4 (by decide) (by decide)).trans h4B
  have h14N : sN.regs 14 = parent + 16 := hContextN.trans (hContextB.trans hContextP)
  have hConst : let out := runBlock hintBitmapConstants E sN
      out.pc = sN.pc + 3 ∧ out.mem = sN.mem ∧ HintFillParams bitmapBase 1 Nj 0 out ∧
      out.regs 11 = parent ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp [hintBitmapConstants, runBlock, execInstr, h4N, h6N, hParentN, h14N, Nat.mod_eq_of_lt hWord]
  generalize hC : runBlock hintBitmapConstants E sN = out at hConst
  obtain ⟨hPcC, hMemC, hArgsC, hParentC, hContextC⟩ := hConst
  have hRun : runBlock hintBitmapClearPrep E state = out := by
    rw [hintBitmapClearPrep, runBlock_append, runBlock_append, runBlock_append, hP, hB, hN, hC]
  simpa only [hRun] using And.intro (show out.pc = state.pc + 11 by rw [hPcC, hPcN, hPcB, hPcP])
    (And.intro (hMemC.trans (hMemN.trans (hMemB.trans hMemP))) (And.intro hArgsC (And.intro hParentC hContextC)))

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintBitmapSetPrep : List Instr := hintParentLoad 5 25 ++ hintParentLoad 6 17 ++ [.imm 0 0]

theorem hintBitmapSetPrep_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState) (parent bitmapBase Nj index : ℕ)
    (hParent : parent + 16 = G.context) (hContext : state.regs 14 = G.context) (hPointer : state.regs 11 = parent)
    (hHeader : HintGaussHeader G index state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hArgs : HintFillParams bitmapBase 1 Nj 0 state) :
    let out := runBlock hintBitmapSetPrep E state
    out.pc = state.pc + 7 ∧ out.mem = state.mem ∧
      HintBitmapArgs bitmapBase G.hintList G.hints out ∧ out.regs 0 = 0 ∧ out.regs 14 = G.context := by
  have hSpan := hFits.span
  have h25 : parent + 25 = G.context + 9 := by omega
  have h17 : parent + 17 = G.context + 1 := by omega
  have hReadH : state.mem (parent + 25) = G.hintList := by rw [h25]; exact hHeader 9 (by decide)
  have hReadCount : state.mem (parent + 17) = G.hints := by rw [h17]; exact hHeader 1 (by decide)
  have hHWord : G.hintList < 2 ^ E.W := hFits.values 9 (by decide)
  have hCountWord : G.hints < 2 ^ E.W := hFits.values 1 (by decide)
  have hLoadH := hintParentLoad_spec E state parent 25 5 hPointer (by omega) (by decide) (by decide)
  generalize hH : runBlock (hintParentLoad 5 25) E state = sH at hLoadH
  obtain ⟨hPcH, hMemH, hValueH, hParentH, hContextH, hRegsH⟩ := hLoadH
  have h5H : sH.regs 5 = G.hintList := by rw [hValueH, hReadH, Nat.mod_eq_of_lt hHWord]
  have h4H : sH.regs 4 = bitmapBase := (hRegsH 4 (by decide) (by decide)).trans hArgs.dest_value
  have h15H : sH.regs 15 = 1 := (hRegsH 15 (by decide) (by decide)).trans hArgs.one_value
  have hLoadC := hintParentLoad_spec E sH parent 17 6 hParentH (by omega) (by decide) (by decide)
  generalize hC : runBlock (hintParentLoad 6 17) E sH = sC at hLoadC
  obtain ⟨hPcC, hMemC, hValueC, _, hContextC, hRegsC⟩ := hLoadC
  have h6C : sC.regs 6 = G.hints := by rw [hValueC, hMemH, hReadCount, Nat.mod_eq_of_lt hCountWord]
  have h5C : sC.regs 5 = G.hintList := (hRegsC 5 (by decide) (by decide)).trans h5H
  have h4C : sC.regs 4 = bitmapBase := (hRegsC 4 (by decide) (by decide)).trans h4H
  have h15C : sC.regs 15 = 1 := (hRegsC 15 (by decide) (by decide)).trans h15H
  have h14C : sC.regs 14 = G.context := hContextC.trans (hContextH.trans hContext)
  have hFinish : let out := runBlock [.imm 0 0] E sC
      out.pc = sC.pc + 1 ∧ out.mem = sC.mem ∧ HintBitmapArgs bitmapBase G.hintList G.hints out ∧
      out.regs 0 = 0 ∧ out.regs 14 = G.context := by
    refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp [runBlock, execInstr, h4C, h5C, h6C, h15C, h14C]
  generalize hF : runBlock [.imm 0 0] E sC = out at hFinish
  obtain ⟨hPcF, hMemF, hArgsF, hCounterF, hContextF⟩ := hFinish
  have hRun : runBlock hintBitmapSetPrep E state = out := by
    rw [hintBitmapSetPrep, runBlock_append, runBlock_append, hH, hC, hF]
  simpa only [hRun] using And.intro (show out.pc = state.pc + 7 by rw [hPcF, hPcC, hPcH])
    (And.intro (hMemF.trans (hMemC.trans hMemH)) (And.intro hArgsF (And.intro hCounterF hContextF)))

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintRowBitmapStmt : Stmt := .seq (.code hintBitmapClearPrep)
  (.seq hintFillStmt (.seq (.code hintBitmapSetPrep) hintBitmapLoop))
theorem hintRowBitmapStmt_len : hintRowBitmapStmt.len = 34 := rfl

theorem hintRowBitmapStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (hInput : HintRowInput G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintRowBitmapStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 34) state (fun k out => k ≤ 7 * Nj + 8 * G.hints + 23 ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      CRMemFrame bitmapBase (bitmapBase + Nj) state.mem out.mem) := by
  have hSource := hPublic.source
  have hParent := hPublic.parent_eq
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  have h0 := hPublic.geometry.residual_before
  have h1 := hPublic.geometry.lift_before
  have h2 := hPublic.geometry.column_before
  have h3 := hPublic.geometry.residualVec_before
  have h4 := hPublic.geometry.kernelVec_before
  have h5 := hPublic.geometry.span
  have hReserve := hPublic.reserve
  have hEnd : parent + 16 < 2 ^ E.W := by omega
  have hNjWord : Nj < 2 ^ E.W := hPublic.bucket_bound.trans_lt (hPublic.fits.values 12 (by decide))
  obtain ⟨idx, hHeader⟩ := hHeader
  obtain ⟨hPrepAt, hRest1⟩ := At.seqStmt hAt
  change At P base hintBitmapClearPrep at hPrepAt
  obtain ⟨hFillAt, hRest2⟩ := At.seqStmt hRest1
  change At P (base + 11) (hintFillStmt.compile (base + 11)) at hFillAt
  obtain ⟨hSetAt, hLoopAt⟩ := At.seqStmt hRest2
  change At P (base + 19) hintBitmapSetPrep at hSetAt
  change At P (base + 26) (hintBitmapLoop.compile (base + 26)) at hLoopAt
  have hPrep := hintBitmapClearPrep_spec E state parent bitmapBase Nj hEnd (hContext.trans hParent.symm)
    (by omega) hNjWord hInput.bitmap_pointer hInput.radix
  generalize hP : runBlock hintBitmapClearPrep E state = sP at hPrep
  obtain ⟨hPcP, hMemP, hArgsP, hPointerP, hCtxP⟩ := hPrep
  have hRunP : (step P E)^[11] state = sP := by
    have hh := iterate_runBlock_of_at P E hintBitmapClearPrep state (by rwa [hPc])
      (by simp [hintBitmapClearPrep, hintScanParent, hintParentLoad, hintBitmapConstants, NoBranch, Instr.NoBranchI])
    rw [hP] at hh
    exact hh
  obtain ⟨_, kF, sF, hRunF, hPcF, hCostF, _, hMemF, hArgsF, hFrameF, hRegsF⟩ :=
    hintFillStmt_sem P E sP bitmapBase 1 Nj (base + 11) 0 hPublic.geometry.word_bound hNjWord
      (by intro q hq; simp only [Nat.mul_one]; omega) hFillAt (by rw [hPcP, hPc]) hArgsP
  have hFrameF' : CRMemFrame bitmapBase (bitmapBase + Nj) state.mem sF.mem := by
    intro addr hAway
    have hNot : addr ∉ hintFillPositions bitmapBase 1 Nj := by
      intro hIn
      obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp hIn
      have hQ : q < Nj := Finset.mem_range.mp hq
      simp only [Nat.mul_one] at hEq
      rcases hAway with hBefore | hAfter <;> omega
    exact (hFrameF addr hNot).trans (congrFun hMemP addr)
  have hHeaderF : HintGaussHeader G idx sF.mem := by
    intro i hi
    rw [hFrameF' _ (Or.inr (by omega))]
    exact hHeader i hi
  have hContextF : sF.regs 14 = G.context :=
    (hRegsF 14 (by decide) (by decide) (by decide)).trans (hCtxP.trans hParent)
  have hPointerF : sF.regs 11 = parent := (hRegsF 11 (by decide) (by decide) (by decide)).trans hPointerP
  have hSet := hintBitmapSetPrep_spec E G sF parent bitmapBase Nj idx hParent hContextF hPointerF hHeaderF hPublic.fits hArgsF
  generalize hS : runBlock hintBitmapSetPrep E sF = sS at hSet
  obtain ⟨hPcS, hMemS, hArgsS, hCounterS, hContextS⟩ := hSet
  have hRunS : (step P E)^[7] sF = sS := by
    have hh := iterate_runBlock_of_at P E hintBitmapSetPrep sF (by rwa [hPcF])
      (by simp [hintBitmapSetPrep, hintParentLoad, NoBranch, Instr.NoBranchI])
    rw [hS] at hh
    exact hh
  have hInv : HintBitmapInv coords bitmapBase G.hintList Nj 0 state.mem sS := by
    refine ⟨hArgsS, hCounterS, ?_, ?_⟩
    · intro q hq
      have hIn : bitmapBase + q ∈ hintFillPositions bitmapBase 1 Nj :=
        Finset.mem_image.mpr ⟨q, Finset.mem_range.mpr hq, by simp⟩
      rw [hMemS, hMemF]
      simp [hintFillMem, hIn, hintBitmapValue_zero]
    · rw [hMemS]
      exact hFrameF'
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hBitmapOut, _, hFrameOut, hContextOut⟩ :=
    hintBitmapLoop_sem coords bitmapBase G.hintList Nj state.mem P E sS (base + 26) hPublic.geometry.word_bound
      (by omega) (by omega) (by omega) hPublic.hint_valid hInput.hints hInv hLoopAt (by rw [hPcS, hPcF])
  have hInputOut := HintRowInput.frame hPublic hInput hFrameOut
  have hHeaderOut : ∃ index, HintGaussHeader G index out.mem := by
    refine ⟨idx, ?_⟩
    intro i hi
    rw [hFrameOut _ (Or.inr (by omega))]
    exact hHeader i hi
  refine ⟨hPc, kL + (7 + (kF + 11)), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) (hintIterate_then (step P E) hRunP hRunF) hRunS) hRunL,
    ?_, by omega, hInputOut.with_bitmap hBitmapOut, hHeaderOut, hContextOut.trans hContextS, hFrameOut⟩
  · simpa only [Nat.add_assoc] using hPcL

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowBitmapStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintRowBitmap20261120

section -- Def_LinearSetReconciliation327_Main_HintReplay20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintScanSolution (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj r : ℕ) (A : Finset ℕ)
    (v : HintVec G.rows) (memory : ℕ → ℕ) : Prop :=
  ∃ z : HintVec G.hints,
    (∀ t : Fin G.hints, memory (G.kernelVec + t.val) = (z t).val) ∧
    hintFamilyClass G coords beta Nj r A v (hintBitsSet (fun j => (coords j).val) z ∪ A) ∧
    ∀ C : Finset ℕ, hintFamilyClass G coords beta Nj r A v C →
      C = hintBitsSet (fun j => (coords j).val) z ∪ A

theorem HintScanWitness.solution {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {Nj r : ℕ} {A : Finset ℕ}
    {v : HintVec G.rows} {out : RAMState} (h : HintScanWitness G coords beta Nj r A v out) (hOne : out.regs 1 = 1) :
    HintScanSolution G coords beta Nj r A v out.mem := h hOne

theorem hintScanSuccess_singleton (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj r : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (target n : Fin (Nj ^ r)) (hS : hintFamilySuccesses G coords beta Nj r v hPos = {target}) :
    hintScanSuccess G coords beta Nj r (hintOdometerEnumeration Nj r hPos n) v ↔ n = target := by
  have hMembership : hintScanSuccess G coords beta Nj r (hintOdometerEnumeration Nj r hPos n) v ↔
      n ∈ hintFamilySuccesses G coords beta Nj r v hPos := by
    simp [hintScanSuccess, hintTupleAccept, hintFamilySuccesses]
  simpa only [hS, Finset.mem_singleton] using hMembership

def hintReplayStop : List Instr := [.imm 1 0]
def hintReplayBody : Stmt := .seq hintScanJudgeStmt (.ite (.neqz 1) (.code hintReplayStop) hintScanAdvanceStmt)
theorem hintReplayBody_len : hintReplayBody.len = 624 := rfl

def hintReplayLoop : Stmt := .loop (.neqz 1) hintReplayBody
theorem hintReplayLoop_len : hintReplayLoop.len = 626 := rfl

def hintReplayFinish : List Instr := [.imm 1 1]
def hintReplayStmt : Stmt := .seq hintScanInitializeStmt (.seq hintReplayLoop (.code hintReplayFinish))
theorem hintReplayStmt_len : hintReplayStmt.len = 653 := rfl

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem hintReplayBody_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (target n : Fin (Nj ^ r)) (hOrder : n.val ≤ target.val)
    (hS : hintFamilySuccesses G coords beta Nj r v hPublic.positive = {target})
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hArray : ∀ i < r, state.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj n.val i)
    (hAt : At P base (hintReplayBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 624) state (fun k out => k ≤ hintScanBodyTime G r ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintScanFrame G parent outsideBase r state.mem out.mem ∧
      ((n = target ∧ out.regs 1 = 0 ∧
          HintScanSolution G coords beta Nj r (hintTupleSet (hintOdometerEnumeration Nj r hPublic.positive target)) v out.mem ∧
          ∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i) ∨
       (n.val < target.val ∧ out.regs 1 = 1 ∧
          ∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj (n.val + 1) i))) := by
  classical
  have hSource := hPublic.source
  have hParent := hPublic.parent_eq
  have hOutside := hPublic.outside_span
  let outside := hintOdometerEnumeration Nj r hPublic.positive n
  obtain ⟨idx, hHeader⟩ := hHeader
  obtain ⟨hJudgeAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base (hintScanJudgeStmt.compile base) at hJudgeAt
  change At P (base + 596) ((Stmt.ite (.neqz 1) (.code hintReplayStop) hintScanAdvanceStmt).compile (base + 596)) at hBranchAt
  have hArrayJudge : ∀ j : Fin r, state.mem (outsideBase + 1 + j.val) = (outside j).val := by
    intro j
    rw [hintOdometerEnumeration_val]
    exact hArray j.val j.isLt
  obtain ⟨_, kJ, sJ, hRunJ, hPcJ, hCostJ, hBitJ, hUniqueJ, hWitnessJ, hHeaderJ, hFrameJ, hContextJ⟩ :=
    hintScanJudgeStmt_sem G coords r parent outsideBase bitmapBase idx Nj outside beta hPrefix v P E state base
      hPublic.geometry hPublic.reserve hPublic.parent_eq hPublic.source hPublic.injective hPublic.hint_valid hPublic.bucket_bound
      hPublic.outside_span hPublic.bitmap_span hData.hints hHeader hPublic.fits hContext hData.outside_pointer
      hData.bitmap_pointer hData.outside_count hArrayJudge hData.bitmap hData.observation hPublic.steps_pos
      hPublic.coefficient_span hPublic.coefficients hJudgeAt hPc
  have hTarget : sJ.regs 1 = 1 ↔ n = target :=
    hUniqueJ.trans (hintScanSuccess_singleton G coords beta Nj r v hPublic.positive target n hS)
  have hDataJ := HintScanReadOnly.frame hPublic hData (HintScanFrame.of_judge hFrameJ)
  have hArrayJ : ∀ i < r, sJ.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj n.val i := by
    intro i hi
    rw [hFrameJ _ (Or.inl (by omega)) (Or.inl (by omega))]
    exact hArray i hi
  let Cases : RAMState → Prop := fun out =>
    (n = target ∧ out.regs 1 = 0 ∧
      HintScanSolution G coords beta Nj r (hintTupleSet (hintOdometerEnumeration Nj r hPublic.positive target)) v out.mem ∧
      ∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i) ∨
    (n.val < target.val ∧ out.regs 1 = 1 ∧
      ∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj (n.val + 1) i)
  let Q : ℕ → RAMState → Prop := fun k out => k ≤ 10 * r + 18 ∧
    HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
    (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
    HintScanFrame G parent outsideBase r sJ.mem out.mem ∧ Cases out
  have hBranch : Sem P E (base + 596) (base + 624) sJ Q := by
    apply Sem.ite P E (base + 596) (.neqz 1) (.code hintReplayStop) hintScanAdvanceStmt sJ Q
      hBranchAt hPublic.geometry.word_bound hPcJ
    · intro hGo
      change Sem P E (base + 597) (base + 598) {sJ with pc := base + 597}
        (fun k out => Q (1 + k + 1) {out with pc := base + 624})
      have hOne : sJ.regs 1 = 1 := hBitJ.resolve_left hGo
      have hEq : n = target := hTarget.mp hOne
      have hSol : HintScanSolution G coords beta Nj r
          (hintTupleSet (hintOdometerEnumeration Nj r hPublic.positive target)) v sJ.mem := by
        simpa only [outside, hEq] using hWitnessJ.solution hOne
      have hNative := Sem.block P E (base + 597) hintReplayStop {sJ with pc := base + 597}
        (at_ite hBranchAt).2.2.1 (by simp [hintReplayStop, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      change Q (1 + k + 1) {runBlock hintReplayStop E {sJ with pc := base + 597} with pc := base + 624}
      dsimp only [Q]
      refine ⟨by change k = 1 at hCost; omega, hDataJ, hHeaderJ, ?_, HintScanFrame.refl _ _ _ _ _, ?_⟩
      · simpa [hintReplayStop, runBlock, execInstr] using hContextJ
      · apply Or.inl
        refine ⟨hEq, ?_, hSol, ?_⟩
        · simp [hintReplayStop, runBlock, execInstr]
        · simpa [hEq, hintReplayStop, runBlock, execInstr] using hArrayJ
    · intro hStop
      change Sem P E (base + 599) (base + 623) {sJ with pc := base + 599}
        (fun k out => Q (1 + k + 1) {out with pc := base + 624})
      have hZero : sJ.regs 1 = 0 := by change ¬ sJ.regs 1 ≠ 0 at hStop; exact not_not.mp hStop
      have hNe : n ≠ target := by intro hEq; have := hTarget.mpr hEq; omega
      have hLt : n.val < target.val := by
        have hNeVal : n.val ≠ target.val := fun h => hNe (Fin.ext h)
        omega
      have hContinue : n.val + 1 < Nj ^ r := by have := target.isLt; omega
      have hNative := hintScanAdvanceStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v
        P E {sJ with pc := base + 599} (base + 599) hPublic n hDataJ hHeaderJ hContextJ hArrayJ
        (at_ite hBranchAt).2.2.2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hFlag, hArrayOut, hDataOut, hHeaderOut, hContextOut, _, hFrameOut⟩ := hOut
      change Q (1 + k + 1) {out with pc := base + 624}
      dsimp only [Q]
      refine ⟨by omega, hDataOut, hHeaderOut, hContextOut, HintScanFrame.of_array hFrameOut, Or.inr ⟨hLt, ?_, hArrayOut⟩⟩
      simpa [hintTruth, hContinue] using hFlag
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hDataB, hHeaderB, hContextB, hFrameB, hCasesB⟩ := hBranch
  refine ⟨hPc, kB + kJ, out, hintIterate_then (step P E) hRunJ hRunB, hPcB, ?_,
    hDataB, hHeaderB, hContextB, (HintScanFrame.of_judge hFrameJ).trans hFrameB, hCasesB⟩
  dsimp only [hintScanBodyTime]
  omega

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

structure HintReplayCommon (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows) (original : ℕ → ℕ) (state : RAMState) : Prop where
  readonly : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem
  header : ∃ index, HintGaussHeader G index state.mem
  context_value : state.regs 14 = G.context
  frame : HintScanFrame G parent outsideBase r original state.mem

theorem HintReplayCommon.pc {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {Nj r parent outsideBase bitmapBase : ℕ} {v : HintVec G.rows} {original : ℕ → ℕ} {state : RAMState}
    (h : HintReplayCommon G coords Nj r parent outsideBase bitmapBase v original state) (pc : ℕ) :
    HintReplayCommon G coords Nj r parent outsideBase bitmapBase v original {state with pc := pc} :=
  ⟨h.readonly, h.header, h.context_value, h.frame⟩

def HintReplayDone (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj r parent outsideBase bitmapBase : ℕ)
    (v : HintVec G.rows) (hPos : 0 < Nj) (target : Fin (Nj ^ r)) (original : ℕ → ℕ) (state : RAMState) : Prop :=
  HintReplayCommon G coords Nj r parent outsideBase bitmapBase v original state ∧ state.regs 1 = 0 ∧
    HintScanSolution G coords beta Nj r (hintTupleSet (hintOdometerEnumeration Nj r hPos target)) v state.mem ∧
    ∀ i < r, state.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i

theorem hintReplayLoop_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows) (original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (target : Fin (Nj ^ r)) (hS : hintFamilySuccesses G coords beta Nj r v hPublic.positive = {target})
    (hInv : HintScanInv G coords beta Nj r parent outsideBase bitmapBase v hPublic.positive 0 original state)
    (hAt : At P base (hintReplayLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 626) state (fun k out => k ≤ (hintScanBodyTime G r + 2) * (target.val + 1) + 1 ∧
      HintReplayDone G coords beta Nj r parent outsideBase bitmapBase v hPublic.positive target original out) := by
  let I : ℕ → RAMState → Prop := fun left st => if left = 0 then
    HintReplayDone G coords beta Nj r parent outsideBase bitmapBase v hPublic.positive target original st else
    ∃ rank, rank + left = target.val + 1 ∧
      HintReplayCommon G coords Nj r parent outsideBase bitmapBase v original st ∧ st.regs 1 = 1 ∧
      ∀ i < r, st.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj rank i
  have hBodyAt : At P (base + 1) (hintReplayBody.compile (base + 1)) := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    dsimp only [I] at hI ⊢
    by_cases hLeft : left = 0
    · rw [if_pos hLeft] at hI ⊢
      obtain ⟨hCommon, hFlag, hSol, hArray⟩ := hI
      exact ⟨hCommon.pc pc, hFlag, hSol, hArray⟩
    · rw [if_neg hLeft] at hI ⊢
      obtain ⟨rank, hRank, hCommon, hFlag, hArray⟩ := hI
      exact ⟨rank, hRank, hCommon.pc pc, hFlag, hArray⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.neqz 1).code E st) := by
    intro left st hI
    exact hI
  have hGo : ∀ left st, I (left + 1) st → (Cond.neqz 1).eval st := by
    intro left st hI
    dsimp only [I] at hI
    rw [if_neg (by omega : left + 1 ≠ 0)] at hI
    obtain ⟨rank, _, _, hFlag, _⟩ := hI
    change st.regs 1 ≠ 0
    rw [hFlag]
    decide
  have hStop : ∀ st, I 0 st → ¬ (Cond.neqz 1).eval st := by
    intro st hI
    change HintReplayDone G coords beta Nj r parent outsideBase bitmapBase v hPublic.positive target original st at hI
    change ¬ st.regs 1 ≠ 0
    rw [hI.2.1]
    simp
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.neqz 1).code.length + 1 →
      Sem P E (base + (Cond.neqz 1).code.length + 1)
        (base + (Cond.neqz 1).code.length + 1 + hintReplayBody.len) st
        (fun k out => k ≤ hintScanBodyTime G r ∧ I left out) := by
    intro left st hI hStart
    dsimp only [I] at hI
    rw [if_neg (by omega : left + 1 ≠ 0)] at hI
    obtain ⟨rank, hRank, hCommon, hFlag, hArray⟩ := hI
    have hn : rank < Nj ^ r := by have := target.isLt; omega
    let n : Fin (Nj ^ r) := ⟨rank, hn⟩
    have hNative := hintReplayBody_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E st (base + 1)
      hPublic target n (by dsimp only [n]; omega) hS hCommon.readonly hCommon.header hCommon.context_value hArray hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hData, hHeader, hContext, hFrame, hCases⟩ := hOut
    have hCommonOut : HintReplayCommon G coords Nj r parent outsideBase bitmapBase v original out :=
      ⟨hData, hHeader, hContext, hCommon.frame.trans hFrame⟩
    refine ⟨hCost, ?_⟩
    dsimp only [I]
    rcases hCases with ⟨hEq, hStopFlag, hSol, hArrayOut⟩ | ⟨hLt, hGoFlag, hArrayOut⟩
    · have hEqVal : rank = target.val := congrArg Fin.val hEq
      have hLeft : left = 0 := by omega
      rw [if_pos hLeft]
      exact ⟨hCommonOut, hStopFlag, hSol, hArrayOut⟩
    · have hLeft : left ≠ 0 := by change rank < target.val at hLt; omega
      rw [if_neg hLeft]
      exact ⟨rank + 1, by omega, hCommonOut, hGoFlag, hArrayOut⟩
  have hPower : 0 < Nj ^ r := pow_pos hPublic.positive r
  have hOne : state.regs 1 = 1 := by simpa [hintTruth, hPower] using hInv.flag
  have hInitial : I (target.val + 1) state := by
    dsimp only [I]
    rw [if_neg (by omega : target.val + 1 ≠ 0)]
    exact ⟨0, by omega, ⟨hInv.readonly, hInv.header, hInv.context_value, hInv.frame⟩, hOne, hInv.array⟩
  have hNative := hintLoopFuel_sem P E base (.neqz 1) hintReplayBody hAt hPublic.geometry.word_bound I (hintScanBodyTime G r)
    hIpc hItest hGo hStop hBody (target.val + 1) state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, hDone⟩ := hOut
  simp only [Cond.code, List.length_nil, Nat.zero_add] at hCost
  exact ⟨hCost, hDone⟩

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem hintReplayStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (target : Fin (Nj ^ r)) (hS : hintFamilySuccesses G coords beta Nj r v hPublic.positive = {target})
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintReplayStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 653) state (fun k out => k ≤ 7 * r + 23 + (hintScanBodyTime G r + 2) * Nj ^ r ∧
      out.regs 1 = 1 ∧
      HintScanSolution G coords beta Nj r (hintTupleSet (hintOdometerEnumeration Nj r hPublic.positive target)) v out.mem ∧
      (∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i) ∧
      HintReplayCommon G coords Nj r parent outsideBase bitmapBase v state.mem out) := by
  obtain ⟨hInitAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintScanInitializeStmt.compile base) at hInitAt
  change At P (base + 26) ((Stmt.seq hintReplayLoop (.code hintReplayFinish)).compile (base + 26)) at hRestAt
  obtain ⟨hLoopAt, hFinishAt⟩ := At.seqStmt hRestAt
  change At P (base + 26) (hintReplayLoop.compile (base + 26)) at hLoopAt
  change At P (base + 652) hintReplayFinish at hFinishAt
  obtain ⟨_, kI, sI, hRunI, hPcI, hCostI, hInvI⟩ :=
    hintScanInitializeStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E state base
      hPublic hData hHeader hContext hInitAt hPc
  obtain ⟨_, kL, sL, hRunL, hPcL, hCostL, hCommonL, _, hSolutionL, hArrayL⟩ :=
    hintReplayLoop_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v state.mem P E sI (base + 26)
      hPublic target hS hInvI hLoopAt hPcI
  have hFinish : let out := runBlock hintReplayFinish E sL
      out.pc = sL.pc + 1 ∧ out.mem = sL.mem ∧ out.regs 1 = 1 ∧ out.regs 14 = sL.regs 14 := by
    refine ⟨?_, rfl, ?_, ?_⟩ <;>
      simp [hintReplayFinish, runBlock, execInstr, Nat.mod_eq_of_lt hPublic.geometry.word_bound]
  generalize hOut : runBlock hintReplayFinish E sL = out at hFinish
  obtain ⟨hPcOut, hMemoryOut, hFlagOut, hContextOut⟩ := hFinish
  have hRunOut : (step P E)^[1] sL = out := by
    have hh := iterate_runBlock_of_at P E hintReplayFinish sL (by rwa [hPcL])
      (by simp [hintReplayFinish, NoBranch, Instr.NoBranchI])
    rw [hOut] at hh
    exact hh
  have hCommonOut : HintReplayCommon G coords Nj r parent outsideBase bitmapBase v state.mem out := by
    refine ⟨?_, ?_, hContextOut.trans hCommonL.context_value, ?_⟩ <;> rw [hMemoryOut]
    · exact hCommonL.readonly
    · exact hCommonL.header
    · exact hCommonL.frame
  have hTarget : target.val + 1 ≤ Nj ^ r := Nat.succ_le_of_lt target.isLt
  have hTime := Nat.mul_le_mul_left (hintScanBodyTime G r + 2) hTarget
  refine ⟨hPc, 1 + (kL + kI), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunI hRunL) hRunOut,
    ?_, by omega, hFlagOut, ?_, ?_, hCommonOut⟩
  · rw [hPcOut, hPcL]
  · rw [hMemoryOut]
    exact hSolutionL
  · rw [hMemoryOut]
    exact hArrayL

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintReplayStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintReplay20261120

section -- Def_LinearSetReconciliation327_Main_HintFamilySolve20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintFamilyCheckTail : List Instr := [.load 1 4, .imm 8 1, .bxor 1 1 8, .lt 1 1 8]
def hintFamilyCheckCode : List Instr := hintScanCounterPrep ++ hintFamilyCheckTail

theorem hintFamilyCheck_spec (E : RAMEnv) (state : RAMState) (parent count : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hCount : count ≤ 2) (hRead : state.mem (parent + 3) = count) :
    let out := runBlock hintFamilyCheckCode E state
    out.pc = state.pc + 8 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (count = 1) ∧ out.regs 14 = parent + 16 := by
  classical
  have hWord : 1 < 2 ^ E.W := by omega
  have hTwo : 2 < 2 ^ E.W := by omega
  have hThree : 3 < 2 ^ E.W := by omega
  have hPrep := hintScanCounterPrep_spec E state parent hEnd hContext
  generalize hMid : runBlock hintScanCounterPrep E state = mid at hPrep
  obtain ⟨hPcMid, hMemMid, hPointerMid, _, hContextMid⟩ := hPrep
  have hReadMid : mid.mem (parent + 3) = count := by rw [hMemMid]; exact hRead
  have hTail : let out := runBlock hintFamilyCheckTail E mid
      out.pc = mid.pc + 4 ∧ out.mem = mid.mem ∧ out.regs 1 = hintTruth (count = 1) ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · simp [hintFamilyCheckTail, runBlock, execInstr]
    · interval_cases count <;>
        simp [hintFamilyCheckTail, runBlock, execInstr, hPointerMid, hReadMid, hintTruth,
          Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hTwo, Nat.mod_eq_of_lt hThree]
    · simpa [hintFamilyCheckTail, runBlock, execInstr] using hContextMid
  dsimp only
  rw [hintFamilyCheckCode, runBlock_append, hMid]
  exact ⟨by rw [hTail.1, hPcMid], hTail.2.1.trans hMemMid, hTail.2.2.1, hTail.2.2.2⟩

def hintFamilySolveStmt : Stmt := .seq hintScanFirstPassStmt
  (.seq (.code hintFamilyCheckCode) (.ite (.neqz 1) hintReplayStmt (.code hintReplayStop)))
theorem hintFamilySolveStmt_len : hintFamilySolveStmt.len = 1326 := rfl

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem hintFamilySolveStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintFamilySolveStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1326) state (fun k out =>
      k ≤ 14 * r + 55 + 2 * ((hintScanBodyTime G r + 2) * Nj ^ r) ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
      (out.regs 1 = 1 ↔
        (HintParams.family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).card = 1) ∧
      (out.regs 1 = 1 → ∃ target : Fin (Nj ^ r),
        hintFamilySuccesses G coords beta Nj r v hPublic.positive = {target} ∧
        HintScanSolution G coords beta Nj r (hintTupleSet (hintOdometerEnumeration Nj r hPublic.positive target)) v out.mem ∧
        ∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i) ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintScanFrame G parent outsideBase r state.mem out.mem) := by
  classical
  let S := hintFamilySuccesses G coords beta Nj r v hPublic.positive
  let Fam := HintParams.family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)
  let D := (hintScanBodyTime G r + 2) * Nj ^ r
  have hSource := hPublic.source
  have hParent := hPublic.parent_eq
  have hReserve := hPublic.reserve
  have h0 := hPublic.geometry.residual_before
  have h1 := hPublic.geometry.lift_before
  have h2 := hPublic.geometry.column_before
  have h3 := hPublic.geometry.residualVec_before
  have h4 := hPublic.geometry.kernelVec_before
  have h5 := hPublic.geometry.span
  have hEnd : parent + 16 < 2 ^ E.W := by omega
  obtain ⟨hFirstAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintScanFirstPassStmt.compile base) at hFirstAt
  change At P (base + 661) ((Stmt.seq (.code hintFamilyCheckCode) (.ite (.neqz 1) hintReplayStmt (.code hintReplayStop))).compile (base + 661)) at hRestAt
  obtain ⟨hCheckAt, hBranchAt⟩ := At.seqStmt hRestAt
  change At P (base + 661) hintFamilyCheckCode at hCheckAt
  change At P (base + 669) ((Stmt.ite (.neqz 1) hintReplayStmt (.code hintReplayStop)).compile (base + 669)) at hBranchAt
  obtain ⟨_, kF, sF, hRunF, hPcF, hCostF, hCountF, _, hDataF, hHeaderF, hContextF, hFrameF⟩ :=
    hintScanFirstPassStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E state base
      hPublic hData hHeader hContext hFirstAt hPc
  have hCheck := hintFamilyCheck_spec E sF parent (min 2 S.card) hEnd (hContextF.trans hParent.symm) (by omega) hCountF
  generalize hMid : runBlock hintFamilyCheckCode E sF = mid at hCheck
  obtain ⟨hPcMid, hMemMid, hFlagMid, hContextMid⟩ := hCheck
  have hRunMid : (step P E)^[8] sF = mid := by
    have hh := iterate_runBlock_of_at P E hintFamilyCheckCode sF (by rwa [hPcF])
      (by simp [hintFamilyCheckCode, hintScanCounterPrep, hintScanParent, hintFamilyCheckTail, NoBranch, Instr.NoBranchI])
    rw [hMid] at hh
    exact hh
  have hFlag : mid.regs 1 = hintTruth (S.card = 1) := hFlagMid.trans (hintTruth_congr (hintCap2_one S.card))
  have hDataMid : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v mid.mem := by rw [hMemMid]; exact hDataF
  have hHeaderMid : ∃ index, HintGaussHeader G index mid.mem := by rw [hMemMid]; exact hHeaderF
  have hCtxMid : mid.regs 14 = G.context := hContextMid.trans hParent
  have hPaper : S.card = 1 ↔ Fam.card = 1 :=
    hintFamilySuccesses_card_one G coords hPublic.injective beta hPrefix Nj r v hPublic.positive hPublic.hint_valid
  let Q : ℕ → RAMState → Prop := fun k out => k ≤ 7 * r + 25 + D ∧
    (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧ (out.regs 1 = 1 ↔ Fam.card = 1) ∧
    (out.regs 1 = 1 → ∃ target : Fin (Nj ^ r), S = {target} ∧
      HintScanSolution G coords beta Nj r (hintTupleSet (hintOdometerEnumeration Nj r hPublic.positive target)) v out.mem ∧
      ∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i) ∧
    HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
    (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧ HintScanFrame G parent outsideBase r mid.mem out.mem
  have hBranch : Sem P E (base + 669) (base + 1326) mid Q := by
    apply Sem.ite P E (base + 669) (.neqz 1) hintReplayStmt (.code hintReplayStop) mid Q
      hBranchAt hPublic.geometry.word_bound (by rw [hPcMid, hPcF])
    · intro hGo
      change Sem P E (base + 670) (base + 1323) {mid with pc := base + 670}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1326})
      have hCard : S.card = 1 := by
        by_contra hBad
        have hZero : mid.regs 1 = 0 := by simpa [hintTruth, hBad] using hFlag
        exact hGo hZero
      obtain ⟨target, hS⟩ := Finset.card_eq_one.mp hCard
      have hNative := hintReplayStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v
        P E {mid with pc := base + 670} (base + 670) hPublic target hS hDataMid hHeaderMid hCtxMid
        (at_ite hBranchAt).2.2.1 rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, hOne, hSolution, hArray, hCommon⟩ := hOut
      change Q (1 + k + 1) {out with pc := base + 1326}
      dsimp only [Q]
      refine ⟨by dsimp only [D]; omega, Or.inr hOne, ?_, ?_, hCommon.readonly, hCommon.header, hCommon.context_value, hCommon.frame⟩
      · exact ⟨fun _ => hPaper.mp hCard, fun _ => hOne⟩
      · intro _
        exact ⟨target, hS, hSolution, hArray⟩
    · intro hStop
      change Sem P E (base + 1324) (base + 1325) {mid with pc := base + 1324}
        (fun k out => Q (1 + k + 1) {out with pc := base + 1326})
      have hBad : ¬ S.card = 1 := by
        intro hc
        have hOne : mid.regs 1 = 1 := by simpa [hintTruth, hc] using hFlag
        apply hStop
        change mid.regs 1 ≠ 0
        rw [hOne]
        decide
      have hNative := Sem.block P E (base + 1324) hintReplayStop {mid with pc := base + 1324}
        (at_ite hBranchAt).2.2.2.2.1 (by simp [hintReplayStop, NoBranch, Instr.NoBranchI]) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      change Q (1 + k + 1) {runBlock hintReplayStop E {mid with pc := base + 1324} with pc := base + 1326}
      dsimp only [Q]
      refine ⟨by change k = 1 at hCost; omega, Or.inl ?_, ?_, ?_, hDataMid, hHeaderMid, ?_, HintScanFrame.refl _ _ _ _ _⟩
      · simp [hintReplayStop, runBlock, execInstr]
      · constructor
        · intro hs
          simp [hintReplayStop, runBlock, execInstr] at hs
        · intro hf
          exact False.elim (hBad (hPaper.mpr hf))
      · intro hs
        simp [hintReplayStop, runBlock, execInstr] at hs
      · simpa [hintReplayStop, runBlock, execInstr] using hCtxMid
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hBitB, hSingletonB, hSolutionB, hDataB, hHeaderB, hContextB, hFrameB⟩ := hBranch
  have hFrameB' : HintScanFrame G parent outsideBase r sF.mem out.mem := by rw [← hMemMid]; exact hFrameB
  refine ⟨hPc, kB + (8 + kF), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunF hRunMid) hRunB, hPcB, ?_,
    hBitB, hSingletonB, hSolutionB, hDataB, hHeaderB, hContextB, hFrameF.trans hFrameB'⟩
  dsimp only [D] at hCostB
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFamilySolveStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintFamilySolve20261120

section -- Def_LinearSetReconciliation327_Main_HintRowFamily20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintRowWork_span {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj r parent outsideBase bitmapBase : ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase) :
    G.context + 16 ≤ G.pivotRow + G.rows ∧ bitmapBase + Nj ≤ G.pivotRow + G.rows := by
  have h0 := hPublic.geometry.residual_before
  have h1 := hPublic.geometry.lift_before
  have h2 := hPublic.geometry.column_before
  have h3 := hPublic.geometry.residualVec_before
  have h4 := hPublic.geometry.kernelVec_before
  have hReserve := hPublic.reserve
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  constructor <;> omega

theorem HintScanFrame.to_row_frame {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj r parent outsideBase bitmapBase : ℕ} {original memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (hFrame : HintScanFrame G parent outsideBase r original memory) :
    CRMemFrame bitmapBase (G.pivotRow + G.rows) original memory := by
  have hEnd := hintRowWork_span hPublic
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  intro addr hAway
  rcases hAway with hBefore | hAfter
  · exact hFrame addr (Or.inl (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · exact hFrame addr (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr hAfter)

def hintRowFamilyStmt : Stmt := .seq hintRowBitmapStmt hintFamilySolveStmt
theorem hintRowFamilyStmt_len : hintRowFamilyStmt.len = 1360 := rfl

/-- Native recovery for a fixed outside count, from real hint and observation
    arrays; even the hint bitmap is constructed by the program itself. -/
theorem hintRowFamilyStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
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
      CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem) := by
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
    hBitS, hSingletonS, hSolutionS, hDataS, hHeaderS, hContextS, ?_⟩
  · simpa only [Nat.add_assoc] using hPcS
  · intro addr hAway
    rw [hFrameS' addr hAway]
    apply hFrameB addr
    rcases hAway with hBefore | hAfter
    · exact Or.inl hBefore
    · exact Or.inr (by omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowFamilyStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintRowFamily20261120

section -- Def_LinearSetReconciliation327_Main_HintPublicDot20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintPublicDotHead : List Instr := [.add 3 4 0, .load 8 3, .add 3 5 0, .load 11 3]
def hintPublicDotTail : List Instr := [.add 8 7 8, .qCoeff 8 10 8, .mul 8 11 8, .bxor 9 9 8, .add 0 0 15]
def hintPublicDotBody : List Instr := hintPublicDotHead ++ hintPublicDotTail

theorem hintPublicDotHead_spec (E : RAMEnv) (state : RAMState) (array weights j coordinate : ℕ) (weight : ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hArray : array + j < 2 ^ E.W) (hWeights : weights + j < 2 ^ E.W)
    (hCoordinate : coordinate < 2 ^ E.W) (h4 : state.regs 4 = array) (h5 : state.regs 5 = weights)
    (h0 : state.regs 0 = j) (hCoord : state.mem (array + j) = coordinate)
    (hWeight : state.mem (weights + j) = weight.val) :
    let out := runBlock hintPublicDotHead E state
    out.pc = state.pc + 4 ∧ out.mem = state.mem ∧ out.regs 8 = coordinate ∧ out.regs 11 = weight.val ∧
      (∀ reg : Fin 16, reg ≠ 3 → reg ≠ 8 → reg ≠ 11 → out.regs reg = state.regs reg) := by
  have hWeightWord : weight.val < 2 ^ E.W := (ZMod.val_lt weight).trans_le hWord
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [hintPublicDotHead, runBlock, execInstr]
  · simp [hintPublicDotHead, runBlock, execInstr, h4, h0, hCoord, Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hCoordinate]
  · simp [hintPublicDotHead, runBlock, execInstr, h5, h0, hWeight, Nat.mod_eq_of_lt hWeights, Nat.mod_eq_of_lt hWeightWord]
  · intro reg hR3 hR8 hR11
    simp [hintPublicDotHead, runBlock, execInstr, hR3, hR8, hR11]

theorem hintPublicDotTail_spec (E : RAMEnv) (state : RAMState) (query key j coordinate : ℕ)
    (weight coefficient acc : ZMod 2) (hWord : 1 < 2 ^ E.W)
    (hQuery : query + coordinate < 2 ^ E.W) (hNext : j + 1 < 2 ^ E.W)
    (h7 : state.regs 7 = query) (h8 : state.regs 8 = coordinate) (h10 : state.regs 10 = key)
    (h11 : state.regs 11 = weight.val) (h9 : state.regs 9 = acc.val) (h0 : state.regs 0 = j) (h15 : state.regs 15 = 1)
    (hCoeff : E.coeff key (query + coordinate) = coefficient.val) :
    let out := runBlock hintPublicDotTail E state
    out.pc = state.pc + 5 ∧ out.mem = state.mem ∧ out.regs 0 = j + 1 ∧
      out.regs 9 = (acc + weight * coefficient).val ∧
      (∀ reg : Fin 16, reg ≠ 0 → reg ≠ 8 → reg ≠ 9 → out.regs reg = state.regs reg) := by
  have hCoeffWord : coefficient.val < 2 ^ E.W := (ZMod.val_lt coefficient).trans_le hWord
  have hProductWord : (weight * coefficient).val < 2 ^ E.W := (ZMod.val_lt _).trans_le hWord
  have hSumWord : (acc + weight * coefficient).val < 2 ^ E.W := (ZMod.val_lt _).trans_le hWord
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [hintPublicDotTail, runBlock, execInstr]
  · simp [hintPublicDotTail, runBlock, execInstr, h0, h15, Nat.mod_eq_of_lt hNext]
  · simp [hintPublicDotTail, runBlock, execInstr, h7, h8, h10, h11, h9, hCoeff,
      Nat.mod_eq_of_lt hQuery, Nat.mod_eq_of_lt hCoeffWord, hintBit_mul, Nat.mod_eq_of_lt hProductWord,
      hintBit_xor, Nat.mod_eq_of_lt hSumWord]
  · intro reg hR0 hR8 hR9
    simp [hintPublicDotTail, runBlock, execInstr, hR0, hR8, hR9]


structure HintPublicDotArgs (array weights count query key : ℕ) (state : RAMState) : Prop where
  array_value : state.regs 4 = array
  weights_value : state.regs 5 = weights
  count_value : state.regs 6 = count
  query_value : state.regs 7 = query
  key_value : state.regs 10 = key
  one_value : state.regs 15 = 1

def hintPublicPartial {count : ℕ} (weight coefficient : Fin count → ZMod 2) (initial : ZMod 2) (j : ℕ) : ZMod 2 :=
  initial + ∑ i ∈ hintGaussDone count j, weight i * coefficient i

theorem hintPublicPartial_zero {count : ℕ} (weight coefficient : Fin count → ZMod 2) (initial : ZMod 2) :
    hintPublicPartial weight coefficient initial 0 = initial := by
  simp [hintPublicPartial, hintGaussDone]

theorem hintPublicPartial_full {count : ℕ} (weight coefficient : Fin count → ZMod 2) (initial : ZMod 2) :
    hintPublicPartial weight coefficient initial count = initial + ∑ i, weight i * coefficient i := by
  simp [hintPublicPartial, hintGaussDone_full]

theorem hintPublicPartial_step {count : ℕ} (weight coefficient : Fin count → ZMod 2) (initial : ZMod 2) (j : Fin count) :
    hintPublicPartial weight coefficient initial (j.val + 1) =
      hintPublicPartial weight coefficient initial j.val + weight j * coefficient j := by
  classical
  unfold hintPublicPartial
  rw [← hintGaussDone_succ j, Finset.sum_insert (by simp [hintGaussDone])]
  ring

theorem hintPublicDotBody_spec {count : ℕ} (E : RAMEnv) (state : RAMState)
    (array weights query key : ℕ) (coordinate : Fin count → ℕ) (weight coefficient : Fin count → ZMod 2)
    (initial : ZMod 2) (j : Fin count)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hArray : array + j.val < 2 ^ E.W) (hWeights : weights + j.val < 2 ^ E.W)
    (hQuery : query + coordinate j < 2 ^ E.W)
    (hArgs : HintPublicDotArgs array weights count query key state)
    (hCounter : state.regs 0 = j.val) (hAcc : state.regs 9 = (hintPublicPartial weight coefficient initial j.val).val)
    (hCoord : state.mem (array + j.val) = coordinate j) (hWeight : state.mem (weights + j.val) = (weight j).val)
    (hCoeff : E.coeff key (query + coordinate j) = (coefficient j).val) :
    let out := runBlock hintPublicDotBody E state
    out.pc = state.pc + 9 ∧ out.mem = state.mem ∧ out.regs 0 = j.val + 1 ∧
      out.regs 9 = (hintPublicPartial weight coefficient initial (j.val + 1)).val ∧
      HintPublicDotArgs array weights count query key out ∧ out.regs 14 = state.regs 14 := by
  have hHead := hintPublicDotHead_spec E state array weights j.val (coordinate j) (weight j) hWord hArray hWeights
    (by omega) hArgs.array_value hArgs.weights_value hCounter hCoord hWeight
  generalize hMid : runBlock hintPublicDotHead E state = mid at hHead
  obtain ⟨hPc, hMem, h8, h11, hRegs⟩ := hHead
  have hTail := hintPublicDotTail_spec E mid query key j.val (coordinate j) (weight j) (coefficient j)
    (hintPublicPartial weight coefficient initial j.val) hWord hQuery (by have := j.isLt; omega)
    ((hRegs 7 (by decide) (by decide) (by decide)).trans hArgs.query_value) h8
    ((hRegs 10 (by decide) (by decide) (by decide)).trans hArgs.key_value) h11
    ((hRegs 9 (by decide) (by decide) (by decide)).trans hAcc)
    ((hRegs 0 (by decide) (by decide) (by decide)).trans hCounter)
    ((hRegs 15 (by decide) (by decide) (by decide)).trans hArgs.one_value) hCoeff
  generalize hEnd : runBlock hintPublicDotTail E mid = out at hTail
  obtain ⟨hPc', hMem', hCounter', hAcc', hRegs'⟩ := hTail
  have hRun : runBlock hintPublicDotBody E state = out := by
    rw [hintPublicDotBody, runBlock_append, hMid, hEnd]
  rw [hRun]
  refine ⟨by omega, hMem'.trans hMem, hCounter', ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [hintPublicPartial_step] using hAcc'
  all_goals first
    | exact (hRegs' _ (by decide) (by decide) (by decide)).trans
        ((hRegs _ (by decide) (by decide) (by decide)).trans hArgs.array_value)
    | exact (hRegs' _ (by decide) (by decide) (by decide)).trans
        ((hRegs _ (by decide) (by decide) (by decide)).trans hArgs.weights_value)
    | exact (hRegs' _ (by decide) (by decide) (by decide)).trans
        ((hRegs _ (by decide) (by decide) (by decide)).trans hArgs.count_value)
    | exact (hRegs' _ (by decide) (by decide) (by decide)).trans
        ((hRegs _ (by decide) (by decide) (by decide)).trans hArgs.query_value)
    | exact (hRegs' _ (by decide) (by decide) (by decide)).trans
        ((hRegs _ (by decide) (by decide) (by decide)).trans hArgs.key_value)
    | exact (hRegs' _ (by decide) (by decide) (by decide)).trans
        ((hRegs _ (by decide) (by decide) (by decide)).trans hArgs.one_value)
    | exact (hRegs' _ (by decide) (by decide) (by decide)).trans (hRegs _ (by decide) (by decide) (by decide))


structure HintPublicDotInv {count : ℕ} (array weights query key : ℕ)
    (weight coefficient : Fin count → ZMod 2) (initial : ZMod 2) (j : ℕ)
    (original : ℕ → ℕ) (state : RAMState) : Prop where
  args : HintPublicDotArgs array weights count query key state
  counter : state.regs 0 = j
  sum_value : state.regs 9 = (hintPublicPartial weight coefficient initial j).val
  memory : state.mem = original

theorem HintPublicDotInv.pc {count array weights query key j : ℕ}
    {weight coefficient : Fin count → ZMod 2} {initial : ZMod 2} {original : ℕ → ℕ} {state : RAMState}
    (h : HintPublicDotInv array weights query key weight coefficient initial j original state) (pc : ℕ) :
    HintPublicDotInv array weights query key weight coefficient initial j original {state with pc := pc} :=
  ⟨⟨h.args.array_value, h.args.weights_value, h.args.count_value, h.args.query_value, h.args.key_value, h.args.one_value⟩,
    h.counter, h.sum_value, h.memory⟩

theorem HintPublicDotInv.test {count array weights query key j : ℕ}
    {weight coefficient : Fin count → ZMod 2} {initial : ZMod 2} {original : ℕ → ℕ} {state : RAMState}
    (h : HintPublicDotInv array weights query key weight coefficient initial j original state) (E : RAMEnv) :
    HintPublicDotInv array weights query key weight coefficient initial j original
      (runBlock (Cond.lt 2 0 6).code E state) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.args.array_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.weights_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.count_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.query_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.key_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.one_value
  · simpa [Cond.code, runBlock, execInstr] using h.counter
  · simpa [Cond.code, runBlock, execInstr] using h.sum_value
  · simpa [Cond.code, runBlock, execInstr] using h.memory

def hintPublicDotLoop : Stmt := .loop (.lt 2 0 6) (.code hintPublicDotBody)
theorem hintPublicDotLoop_len : hintPublicDotLoop.len = 12 := rfl

theorem hintPublicDotLoop_sem {count : ℕ} (array weights query key : ℕ)
    (coordinate : Fin count → ℕ) (weight coefficient : Fin count → ZMod 2) (initial : ZMod 2)
    (original : ℕ → ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hArray : ∀ j : Fin count, array + j.val < 2 ^ E.W)
    (hWeights : ∀ j : Fin count, weights + j.val < 2 ^ E.W)
    (hQuery : ∀ j, query + coordinate j < 2 ^ E.W)
    (hCoord : ∀ j, original (array + j.val) = coordinate j)
    (hWeight : ∀ j, original (weights + j.val) = (weight j).val)
    (hCoeff : ∀ j, E.coeff key (query + coordinate j) = (coefficient j).val)
    (hInv : HintPublicDotInv array weights query key weight coefficient initial 0 original state)
    (hAt : At P base (hintPublicDotLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 12) state (fun k out => k ≤ 12 * count + 2 ∧
      out.regs 9 = (initial + ∑ j, weight j * coefficient j).val ∧
      HintPublicDotArgs array weights count query key out ∧ out.mem = original ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = count ∧
    HintPublicDotInv array weights query key weight coefficient initial j original st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintPublicDotBody := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hDot, hCtx⟩ := hI
    exact ⟨j, hJ, hDot.pc pc, hCtx⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 0 6).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, hDot, hCtx⟩ := hI
    refine ⟨j, hJ, hDot.test E, ?_⟩
    simpa [Cond.code, runBlock, execInstr] using hCtx
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 0 6).eval st := by
    intro left st hI
    obtain ⟨j, hJ, hDot, _⟩ := hI
    change st.regs 0 < st.regs 6
    rw [hDot.counter, hDot.args.count_value]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 6).eval st := by
    intro st hI
    obtain ⟨j, hJ, hDot, _⟩ := hI
    change ¬ st.regs 0 < st.regs 6
    rw [hDot.counter, hDot.args.count_value]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintPublicDotBody).len) st
        (fun k out => k ≤ 9 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hDot, hContext⟩ := hI
    have hj : j < count := by omega
    let t : Fin count := ⟨j, hj⟩
    have hStep := hintPublicDotBody_spec E st array weights query key coordinate weight coefficient initial t
      hWord hCount (hArray t) (hWeights t) (hQuery t) hDot.args hDot.counter hDot.sum_value
      (hDot.memory ▸ hCoord t) (hDot.memory ▸ hWeight t) (hCoeff t)
    generalize hMid : runBlock hintPublicDotBody E st = mid at hStep
    obtain ⟨_, hMem, hCounter, hSum, hArgs, hCtx⟩ := hStep
    have hNative := Sem.block P E (base + 2) hintPublicDotBody st hBodyAt
      (by simp [hintPublicDotBody, hintPublicDotHead, hintPublicDotTail, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨hCost.le, j + 1, by omega, ⟨hArgs, hCounter, hSum, hMem.trans hDot.memory⟩, hCtx.trans hContext⟩
  have hInitial : I count state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintPublicDotBody) hAt hWord I 9
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, hFinal, hContext⟩ := hOut
  have hEnd : j = count := by omega
  rw [hEnd] at hFinal
  refine ⟨hCost, ?_, hFinal.args, hFinal.memory, hContext⟩
  simpa only [hintPublicPartial_full] using hFinal.sum_value

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPublicDotLoop_sem
end -- Def_LinearSetReconciliation327_Main_HintPublicDot20261120

section -- Def_LinearSetReconciliation327_Main_HintPublicSum20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintPublicSumBody : List Instr :=
  [.add 3 4 0, .load 8 3, .add 8 7 8, .qCoeff 8 10 8, .bxor 9 9 8, .add 0 0 15]

theorem hintPublicSumBody_spec {count : ℕ} (E : RAMEnv) (state : RAMState)
    (array unused query key : ℕ) (coordinate : Fin count → ℕ) (coefficient : Fin count → ZMod 2)
    (initial : ZMod 2) (j : Fin count)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hArray : array + j.val < 2 ^ E.W) (hQuery : query + coordinate j < 2 ^ E.W)
    (hArgs : HintPublicDotArgs array unused count query key state)
    (hCounter : state.regs 0 = j.val)
    (hAcc : state.regs 9 = (hintPublicPartial (fun _ => 1) coefficient initial j.val).val)
    (hCoord : state.mem (array + j.val) = coordinate j)
    (hCoeff : E.coeff key (query + coordinate j) = (coefficient j).val) :
    let out := runBlock hintPublicSumBody E state
    out.pc = state.pc + 6 ∧ out.mem = state.mem ∧ out.regs 0 = j.val + 1 ∧
      out.regs 9 = (hintPublicPartial (fun _ => 1) coefficient initial (j.val + 1)).val ∧
      HintPublicDotArgs array unused count query key out ∧ out.regs 14 = state.regs 14 := by
  obtain ⟨h4, h5, h6, h7, h10, h15⟩ := hArgs
  have hCoordWord : coordinate j < 2 ^ E.W := by omega
  have hCoeffWord : (coefficient j).val < 2 ^ E.W := (ZMod.val_lt _).trans_le hWord
  have hSumWord : (hintPublicPartial (fun _ => 1) coefficient initial j.val + coefficient j).val < 2 ^ E.W :=
    (ZMod.val_lt _).trans_le hWord
  have hNext : j.val + 1 < 2 ^ E.W := by have := j.isLt; omega
  refine ⟨?_, rfl, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintPublicSumBody, runBlock, execInstr, h4, h5, h6, h7, h10, h15, hCounter, hAcc, hCoord, hCoeff,
      Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hCoordWord, Nat.mod_eq_of_lt hQuery,
      Nat.mod_eq_of_lt hCoeffWord, Nat.mod_eq_of_lt hNext, hintPublicPartial_step,
      hintBit_xor, Nat.mod_eq_of_lt hSumWord]

def hintPublicSumLoop : Stmt := .loop (.lt 2 0 6) (.code hintPublicSumBody)
theorem hintPublicSumLoop_len : hintPublicSumLoop.len = 9 := rfl

theorem hintPublicSumLoop_sem {count : ℕ} (array unused query key : ℕ)
    (coordinate : Fin count → ℕ) (coefficient : Fin count → ZMod 2) (initial : ZMod 2)
    (original : ℕ → ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hArray : ∀ j : Fin count, array + j.val < 2 ^ E.W)
    (hQuery : ∀ j, query + coordinate j < 2 ^ E.W)
    (hCoord : ∀ j, original (array + j.val) = coordinate j)
    (hCoeff : ∀ j, E.coeff key (query + coordinate j) = (coefficient j).val)
    (hInv : HintPublicDotInv array unused query key (fun _ => 1) coefficient initial 0 original state)
    (hAt : At P base (hintPublicSumLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 9) state (fun k out => k ≤ 9 * count + 2 ∧
      out.regs 9 = (initial + ∑ j, coefficient j).val ∧
      HintPublicDotArgs array unused count query key out ∧ out.mem = original ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = count ∧
    HintPublicDotInv array unused query key (fun _ => 1) coefficient initial j original st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintPublicSumBody := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hDot, hCtx⟩ := hI
    exact ⟨j, hJ, hDot.pc pc, hCtx⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 0 6).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, hDot, hCtx⟩ := hI
    refine ⟨j, hJ, hDot.test E, ?_⟩
    simpa [Cond.code, runBlock, execInstr] using hCtx
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 0 6).eval st := by
    intro left st hI
    obtain ⟨j, hJ, hDot, _⟩ := hI
    change st.regs 0 < st.regs 6
    rw [hDot.counter, hDot.args.count_value]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 6).eval st := by
    intro st hI
    obtain ⟨j, hJ, hDot, _⟩ := hI
    change ¬ st.regs 0 < st.regs 6
    rw [hDot.counter, hDot.args.count_value]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintPublicSumBody).len) st
        (fun k out => k ≤ 6 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hDot, hContext⟩ := hI
    have hj : j < count := by omega
    let t : Fin count := ⟨j, hj⟩
    have hStep := hintPublicSumBody_spec E st array unused query key coordinate coefficient initial t
      hWord hCount (hArray t) (hQuery t) hDot.args hDot.counter hDot.sum_value
      (hDot.memory ▸ hCoord t) (hCoeff t)
    generalize hMid : runBlock hintPublicSumBody E st = mid at hStep
    obtain ⟨_, hMem, hCounter, hSum, hArgs, hCtx⟩ := hStep
    have hNative := Sem.block P E (base + 2) hintPublicSumBody st hBodyAt
      (by simp [hintPublicSumBody, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨hCost.le, j + 1, by omega, ⟨hArgs, hCounter, hSum, hMem.trans hDot.memory⟩, hCtx.trans hContext⟩
  have hInitial : I count state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintPublicSumBody) hAt hWord I 6
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, hFinal, hContext⟩ := hOut
  have hEnd : j = count := by omega
  rw [hEnd] at hFinal
  refine ⟨hCost, ?_, hFinal.args, hFinal.memory, hContext⟩
  simpa only [hintPublicPartial_full, one_mul] using hFinal.sum_value


end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPublicSumLoop_sem
end -- Def_LinearSetReconciliation327_Main_HintPublicSum20261120

section -- Def_LinearSetReconciliation327_Main_HintNextPrep20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintNextFields : List (Fin 16 × ℕ) :=
  [(4,9),(5,6),(6,1),(10,10),(7,11),(13,13),(8,0),(12,12)]
def hintNextTail : List Instr :=
  [.mul 7 7 13, .add 7 7 8, .mul 7 7 12, .imm 15 1, .imm 0 0, .imm 9 0]
def hintNextSetup : List Instr := hintLoadFields hintNextFields ++ hintNextTail
theorem hintNextSetup_length : hintNextSetup.length = 30 := rfl

theorem hintNextTail_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState)
    (hWord : 1 < 2 ^ E.W) (hBuckets : 0 < G.buckets)
    (hQuery : (G.row * G.steps + G.rows) * G.buckets < 2 ^ E.W)
    (h4 : state.regs 4 = G.hintList) (h5 : state.regs 5 = G.kernelVec) (h6 : state.regs 6 = G.hints)
    (h10 : state.regs 10 = G.node) (h7 : state.regs 7 = G.row) (h13 : state.regs 13 = G.steps)
    (h8 : state.regs 8 = G.rows) (h12 : state.regs 12 = G.buckets) (h14 : state.regs 14 = G.context) :
    let out := runBlock hintNextTail E state
    out.pc = state.pc + 6 ∧ out.mem = state.mem ∧
      HintPublicDotArgs G.hintList G.kernelVec G.hints ((G.row * G.steps + G.rows) * G.buckets) G.node out ∧
      out.regs 0 = 0 ∧ out.regs 9 = 0 ∧ out.regs 14 = G.context := by
  have hLe : G.row * G.steps + G.rows ≤ (G.row * G.steps + G.rows) * G.buckets := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (G.row * G.steps + G.rows) hBuckets
  have hFirst : G.row * G.steps < 2 ^ E.W := by omega
  have hSecond : G.row * G.steps + G.rows < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp [hintNextTail, runBlock, execInstr, h4, h5, h6, h10, h7, h13, h8, h12, h14,
      Nat.mod_eq_of_lt hFirst, Nat.mod_eq_of_lt hSecond, Nat.mod_eq_of_lt hQuery, Nat.mod_eq_of_lt hWord]

theorem hintNextSetup_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState) (index : ℕ)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G index state.mem)
    (hFits : HintGaussHeaderFits E G 0) (hBuckets : 0 < G.buckets)
    (hQuery : (G.row * G.steps + G.rows) * G.buckets < 2 ^ E.W) :
    let out := runBlock hintNextSetup E state
    out.pc = state.pc + 30 ∧ out.mem = state.mem ∧
      HintPublicDotArgs G.hintList G.kernelVec G.hints ((G.row * G.steps + G.rows) * G.buckets) G.node out ∧
      out.regs 0 = 0 ∧ out.regs 9 = 0 ∧ out.regs 14 = G.context := by
  have hWord : 1 < 2 ^ E.W := by have := hFits.span; omega
  have hValid : ∀ pair ∈ hintNextFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintNextFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintNextFields state hContext hValid
  generalize hMid : runBlock (hintLoadFields hintNextFields) E state = mid at hLoad
  have hV9 : state.mem (G.context + 9) % 2 ^ E.W = G.hintList := by
    rw [hHeader 9 (by decide)]
    exact Nat.mod_eq_of_lt (hFits.values 9 (by decide))
  have hV6 : state.mem (G.context + 6) % 2 ^ E.W = G.kernelVec := by
    rw [hHeader 6 (by decide)]
    exact Nat.mod_eq_of_lt (hFits.values 6 (by decide))
  have hV1 : state.mem (G.context + 1) % 2 ^ E.W = G.hints := by
    rw [hHeader 1 (by decide)]
    exact Nat.mod_eq_of_lt (hFits.values 1 (by decide))
  have hV10 : state.mem (G.context + 10) % 2 ^ E.W = G.node := by
    rw [hHeader 10 (by decide)]
    exact Nat.mod_eq_of_lt (hFits.values 10 (by decide))
  have hV11 : state.mem (G.context + 11) % 2 ^ E.W = G.row := by
    rw [hHeader 11 (by decide)]
    exact Nat.mod_eq_of_lt (hFits.values 11 (by decide))
  have hV13 : state.mem (G.context + 13) % 2 ^ E.W = G.steps := by
    rw [hHeader 13 (by decide)]
    exact Nat.mod_eq_of_lt (hFits.values 13 (by decide))
  have hV0 : state.mem (G.context + 0) % 2 ^ E.W = G.rows := by
    rw [hHeader 0 (by decide)]
    exact Nat.mod_eq_of_lt (hFits.values 0 (by decide))
  have hV12 : state.mem (G.context + 12) % 2 ^ E.W = G.buckets := by
    rw [hHeader 12 (by decide)]
    exact Nat.mod_eq_of_lt (hFits.values 12 (by decide))
  have hZero : state.mem G.context % 2 ^ E.W = G.rows := by simpa only [Nat.add_zero] using hV0
  have hR4 : mid.regs 4 = G.hintList := by
    have hh := hLoad.2.2.2 4 (by decide)
    simpa [hintNextFields, hintLoadedValue, hZero, hV9, hV6, hV1, hV10, hV11, hV13, hV0, hV12] using hh
  have hR5 : mid.regs 5 = G.kernelVec := by
    have hh := hLoad.2.2.2 5 (by decide)
    simpa [hintNextFields, hintLoadedValue, hZero, hV9, hV6, hV1, hV10, hV11, hV13, hV0, hV12] using hh
  have hR6 : mid.regs 6 = G.hints := by
    have hh := hLoad.2.2.2 6 (by decide)
    simpa [hintNextFields, hintLoadedValue, hZero, hV9, hV6, hV1, hV10, hV11, hV13, hV0, hV12] using hh
  have hR10 : mid.regs 10 = G.node := by
    have hh := hLoad.2.2.2 10 (by decide)
    simpa [hintNextFields, hintLoadedValue, hZero, hV9, hV6, hV1, hV10, hV11, hV13, hV0, hV12] using hh
  have hR7 : mid.regs 7 = G.row := by
    have hh := hLoad.2.2.2 7 (by decide)
    simpa [hintNextFields, hintLoadedValue, hZero, hV9, hV6, hV1, hV10, hV11, hV13, hV0, hV12] using hh
  have hR13 : mid.regs 13 = G.steps := by
    have hh := hLoad.2.2.2 13 (by decide)
    simpa [hintNextFields, hintLoadedValue, hZero, hV9, hV6, hV1, hV10, hV11, hV13, hV0, hV12] using hh
  have hR8 : mid.regs 8 = G.rows := by
    have hh := hLoad.2.2.2 8 (by decide)
    simpa [hintNextFields, hintLoadedValue, hZero, hV9, hV6, hV1, hV10, hV11, hV13, hV0, hV12] using hh
  have hR12 : mid.regs 12 = G.buckets := by
    have hh := hLoad.2.2.2 12 (by decide)
    simpa [hintNextFields, hintLoadedValue, hZero, hV9, hV6, hV1, hV10, hV11, hV13, hV0, hV12] using hh
  have hTail := hintNextTail_spec E G mid hWord hBuckets hQuery hR4 hR5 hR6 hR10 hR7 hR13 hR8 hR12 hLoad.2.2.1
  generalize hOut : runBlock hintNextTail E mid = out at hTail
  obtain ⟨hPc, hMem, hArgs, hCounter, hAcc, hCtx⟩ := hTail
  have hRun : runBlock hintNextSetup E state = out := by rw [hintNextSetup, runBlock_append, hMid, hOut]
  rw [hRun]
  exact ⟨by have := hLoad.1; simp only [hintNextFields, List.length_cons, List.length_nil] at this; omega,
    hMem.trans hLoad.2.1, hArgs, hCounter, hAcc, hCtx⟩



def hintNextOutsidePrep : List Instr := hintScanParent ++ hintScanOdometerInput ++ [.imm 0 0]
theorem hintNextOutsidePrep_length : hintNextOutsidePrep.length = 7 := rfl

theorem hintNextOutsidePrep_spec (E : RAMEnv) (state : RAMState) (parent outsideBase count unused query key : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase + 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hPointer : state.mem parent = outsideBase) (hCountMem : state.mem outsideBase = count)
    (h5 : state.regs 5 = unused) (h7 : state.regs 7 = query) (h10 : state.regs 10 = key) :
    let out := runBlock hintNextOutsidePrep E state
    out.pc = state.pc + 7 ∧ out.mem = state.mem ∧
      HintPublicDotArgs (outsideBase + 1) unused count query key out ∧
      out.regs 0 = 0 ∧ out.regs 9 = state.regs 9 ∧ out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hParent := hintScanParent_spec E state parent hEnd hContext
  have hRegs : ∀ reg : Fin 16, reg ≠ 3 → reg ≠ 11 →
      (runBlock hintScanParent E state).regs reg = state.regs reg := by
    intro reg h3 h11
    simp [hintScanParent, runBlock, execInstr, h3, h11]
  generalize hMid : runBlock hintScanParent E state = mid at hParent hRegs
  obtain ⟨hPc, hMem, h11, h14⟩ := hParent
  have hPointer' : mid.mem parent = outsideBase := by rw [hMem]; exact hPointer
  have hCountMem' : mid.mem outsideBase = count := by rw [hMem]; exact hCountMem
  have h5' := (hRegs 5 (by decide) (by decide)).trans h5
  have h7' := (hRegs 7 (by decide) (by decide)).trans h7
  have h10' := (hRegs 10 (by decide) (by decide)).trans h10
  have h9' := hRegs 9 (by decide) (by decide)
  have hTail : let out := runBlock (hintScanOdometerInput ++ [.imm 0 0]) E mid
      out.pc = mid.pc + 5 ∧ out.mem = mid.mem ∧ HintPublicDotArgs (outsideBase + 1) unused count query key out ∧
      out.regs 0 = 0 ∧ out.regs 9 = state.regs 9 ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
      simp [hintScanOdometerInput, runBlock, execInstr, h11, h14, hPointer', hCountMem', h5', h7', h10', h9',
        Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt (show outsideBase < 2 ^ E.W by omega),
        Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hCount]
  generalize hOut : runBlock (hintScanOdometerInput ++ [.imm 0 0]) E mid = out at hTail
  obtain ⟨hPc', hMem', hArgs, hCounter, hAcc, hCtx⟩ := hTail
  have hRun : runBlock hintNextOutsidePrep E state = out := by
    rw [hintNextOutsidePrep, List.append_assoc, runBlock_append, hMid, hOut]
  rw [hRun]
  exact ⟨by omega, hMem'.trans hMem, hArgs, hCounter, hAcc, hCtx⟩

def hintNextFinish : List Instr := [.mul 8 9 15, .imm 1 1]

theorem hintNextFinish_spec (E : RAMEnv) (state : RAMState) (value : ZMod 2)
    (hWord : 1 < 2 ^ E.W) (hAcc : state.regs 9 = value.val) (hOne : state.regs 15 = 1) :
    let out := runBlock hintNextFinish E state
    out.pc = state.pc + 2 ∧ out.mem = state.mem ∧ out.regs 1 = 1 ∧ out.regs 8 = value.val ∧ out.regs 14 = state.regs 14 := by
  have hValue : value.val < 2 ^ E.W := (ZMod.val_lt _).trans_le hWord
  refine ⟨?_, rfl, ?_, ?_, ?_⟩ <;>
    simp [hintNextFinish, runBlock, execInstr, hAcc, hOne, Nat.mod_eq_of_lt hValue, Nat.mod_eq_of_lt hWord]


end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNextSetup_spec
#print axioms LinearSetReconciliation327.Main.hintNextOutsidePrep_spec
end -- Def_LinearSetReconciliation327_Main_HintNextPrep20261120

section -- Def_LinearSetReconciliation327_Main_HintNextBit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintNextBitStmt : Stmt := .seq (.code hintNextSetup)
  (.seq hintPublicDotLoop (.seq (.code hintNextOutsidePrep) (.seq hintPublicSumLoop (.code hintNextFinish))))
theorem hintNextBitStmt_len : hintNextBitStmt.len = 60 := rfl

theorem hintNextBitStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hNext : G.rows < G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (outside : Fin r → Fin G.buckets) (z : HintVec G.hints)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hNext.le Nj r parent outsideBase bitmapBase)
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hOutside : ∀ i : Fin r, state.mem (outsideBase + 1 + i.val) = (outside i).val)
    (hSolution : ∀ j : Fin G.hints, state.mem (G.kernelVec + j.val) = (z j).val)
    (hCoeff : ∀ c : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + c.val) = (beta ⟨G.rows, hNext⟩ c).val)
    (hAt : At P base (hintNextBitStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 60) state (fun k out => k ≤ 12 * G.hints + 9 * r + 43 ∧
      out.regs 1 = 1 ∧
      out.regs 8 = ((∑ j, z j * beta ⟨G.rows, hNext⟩ (coords j)) +
        ∑ i, beta ⟨G.rows, hNext⟩ (outside i)).val ∧
      out.mem = state.mem ∧ out.regs 14 = G.context) := by
  have hFits := hPublic.fits
  have hSource := hPublic.source
  have hParent := hPublic.parent_eq
  have hSpan := hFits.span
  have hOutsideSpan := hPublic.outside_span
  have hWord : 1 < 2 ^ E.W := by omega
  have hBuckets : 0 < G.buckets := lt_of_lt_of_le hPublic.positive hPublic.bucket_bound
  have hQuery : ∀ c : Fin G.buckets,
      (G.row * G.steps + G.rows) * G.buckets + c.val < 2 ^ E.W := by
    intro c
    have hh := hintGauss_query_index_lt G.row G.steps G.buckets G.rows c.val hNext c.isLt
    have heq : G.row * G.steps * G.buckets + c.val + G.rows * G.buckets =
        (G.row * G.steps + G.rows) * G.buckets + c.val := by ring
    rw [heq] at hh
    exact hh.trans_le hPublic.coefficient_span
  have hQueryBase : (G.row * G.steps + G.rows) * G.buckets < 2 ^ E.W := by
    simpa using hQuery ⟨0, hBuckets⟩
  have hHints : G.hints < 2 ^ E.W := hFits.values 1 (by decide)
  have hKernel := hPublic.geometry.kernelVec_before
  have hGaussSpan := hPublic.geometry.span
  obtain ⟨hSetupAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintNextSetup at hSetupAt
  change At P (base + 30) ((Stmt.seq hintPublicDotLoop
    (.seq (.code hintNextOutsidePrep) (.seq hintPublicSumLoop (.code hintNextFinish)))).compile (base + 30)) at hRestAt
  obtain ⟨hDotAt, hTailAt⟩ := At.seqStmt hRestAt
  change At P (base + 30) (hintPublicDotLoop.compile (base + 30)) at hDotAt
  change At P (base + 42) ((Stmt.seq (.code hintNextOutsidePrep)
    (.seq hintPublicSumLoop (.code hintNextFinish))).compile (base + 42)) at hTailAt
  obtain ⟨hPrepAt, hFinalAt⟩ := At.seqStmt hTailAt
  change At P (base + 42) hintNextOutsidePrep at hPrepAt
  change At P (base + 49) ((Stmt.seq hintPublicSumLoop (.code hintNextFinish)).compile (base + 49)) at hFinalAt
  obtain ⟨hSumAt, hFinishAt⟩ := At.seqStmt hFinalAt
  change At P (base + 49) (hintPublicSumLoop.compile (base + 49)) at hSumAt
  change At P (base + 58) hintNextFinish at hFinishAt
  obtain ⟨index, hHeader⟩ := hHeader
  have hSetup := hintNextSetup_spec E G state index hContext hHeader hFits hBuckets hQueryBase
  generalize hS : runBlock hintNextSetup E state = sS at hSetup
  obtain ⟨hPcS, hMemS, hArgsS, hCounterS, hAccS, hCtxS⟩ := hSetup
  have hRunS : (step P E)^[30] state = sS := by
    have hh := iterate_runBlock_of_at P E hintNextSetup state (by rwa [hPc])
      (by rw [hintNextSetup, upNoBranch_append]; exact ⟨hintLoadFields_noBranch _, by simp [hintNextTail, NoBranch, Instr.NoBranchI]⟩)
    simpa only [hintNextSetup_length, hS] using hh
  have hInvS : HintPublicDotInv G.hintList G.kernelVec ((G.row * G.steps + G.rows) * G.buckets) G.node
      z (fun j => beta ⟨G.rows, hNext⟩ (coords j)) 0 0 state.mem sS :=
    ⟨hArgsS, hCounterS, by simpa only [hintPublicPartial_zero, ZMod.val_zero] using hAccS, hMemS⟩
  obtain ⟨_, kD, sD, hRunD, hPcD, hCostD, hAccD, hArgsD, hMemD, hCtxD⟩ :=
    hintPublicDotLoop_sem G.hintList G.kernelVec ((G.row * G.steps + G.rows) * G.buckets) G.node
      (fun j => (coords j).val) z (fun j => beta ⟨G.rows, hNext⟩ (coords j)) 0 state.mem P E sS (base + 30)
      hWord hHints (fun j => by have := j.isLt; omega) (fun j => by have := j.isLt; omega)
      (fun j => hQuery (coords j)) hData.hints hSolution (fun j => hCoeff (coords j)) hInvS hDotAt (by omega)
  simp only [zero_add] at hAccD
  have hPrep := hintNextOutsidePrep_spec E sD parent outsideBase r G.kernelVec
    ((G.row * G.steps + G.rows) * G.buckets) G.node (by omega) (hCtxD.trans (hCtxS.trans hParent.symm))
    (by omega) (by omega) (by rw [hMemD]; exact hData.outside_pointer)
    (by rw [hMemD]; exact hData.outside_count) hArgsD.weights_value hArgsD.query_value hArgsD.key_value
  generalize hP : runBlock hintNextOutsidePrep E sD = sP at hPrep
  obtain ⟨hPcP, hMemP, hArgsP, hCounterP, hAccP, hCtxP⟩ := hPrep
  have hRunP : (step P E)^[7] sD = sP := by
    have hh := iterate_runBlock_of_at P E hintNextOutsidePrep sD (by rwa [hPcD])
      (by simp [hintNextOutsidePrep, hintScanParent, hintScanOdometerInput, NoBranch, Instr.NoBranchI])
    simpa only [hintNextOutsidePrep_length, hP] using hh
  have hInvP : HintPublicDotInv (outsideBase + 1) G.kernelVec ((G.row * G.steps + G.rows) * G.buckets) G.node
      (fun _ => 1) (fun i => beta ⟨G.rows, hNext⟩ (outside i))
      (∑ j, z j * beta ⟨G.rows, hNext⟩ (coords j)) 0 state.mem sP :=
    ⟨hArgsP, hCounterP, by simpa only [hintPublicPartial_zero] using hAccP.trans hAccD, hMemP.trans hMemD⟩
  obtain ⟨_, kO, sO, hRunO, hPcO, hCostO, hAccO, hArgsO, hMemO, hCtxO⟩ :=
    hintPublicSumLoop_sem (outsideBase + 1) G.kernelVec ((G.row * G.steps + G.rows) * G.buckets) G.node
      (fun i => (outside i).val) (fun i => beta ⟨G.rows, hNext⟩ (outside i))
      (∑ j, z j * beta ⟨G.rows, hNext⟩ (coords j)) state.mem P E sP (base + 49)
      hWord (by omega) (fun i => by have := i.isLt; omega) (fun i => hQuery (outside i))
      hOutside (fun i => hCoeff (outside i)) hInvP hSumAt (by omega)
  have hFinish := hintNextFinish_spec E sO
    ((∑ j, z j * beta ⟨G.rows, hNext⟩ (coords j)) + ∑ i, beta ⟨G.rows, hNext⟩ (outside i))
    hWord hAccO hArgsO.one_value
  generalize hF : runBlock hintNextFinish E sO = out at hFinish
  obtain ⟨hPcF, hMemF, hFlagF, hBitF, hCtxF⟩ := hFinish
  have hRunF : (step P E)^[2] sO = out := by
    have hh := iterate_runBlock_of_at P E hintNextFinish sO (by rwa [hPcO])
      (by simp [hintNextFinish, NoBranch, Instr.NoBranchI])
    rw [hF] at hh
    exact hh
  refine ⟨hPc, 2 + (kO + (7 + (kD + 30))), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) (hintIterate_then (step P E)
      (hintIterate_then (step P E) hRunS hRunD) hRunP) hRunO) hRunF,
    by omega, by omega, hFlagF, hBitF, hMemF.trans hMemO, ?_⟩
  exact hCtxF.trans (hCtxO.trans (hCtxP.trans hParent))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNextBitStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintNextBit20261120

section -- Def_LinearSetReconciliation327_Main_HintRowPredictCount20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

theorem hintNextCandidate_value {h r ell K : ℕ} (coords : Fin h → Fin K)
    (hInj : Function.Injective coords) (outside : Fin r → Fin K) (hOutInj : Function.Injective outside)
    (hSeparate : Disjoint (Finset.univ.image (fun i => (outside i).val))
      (Finset.univ.image (fun j => (coords j).val)))
    (beta : Fin ell → Fin K → ZMod 2) (z : HintVec h) (s : Fin ell) :
    rowBit beta (hintBitsSet (fun j => (coords j).val) z ∪ Finset.univ.image (fun i => (outside i).val)) s =
      (∑ j, z j * beta s (coords j)) + ∑ i, beta s (outside i) := by
  have hNatInj : Function.Injective (fun j => (coords j).val) := fun _ _ heq => hInj (Fin.ext heq)
  rw [hintBitsUnion_rowBit _ _ hSeparate,
    hintBitsSet_rowBit _ hNatInj (fun j => (coords j).isLt), hintRowBit_image outside hOutInj]

theorem hintNextRecoveredStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hNext : G.rows < G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hNext.le Nj r parent outsideBase bitmapBase)
    (target : Fin (Nj ^ r)) (hSuccess : hintFamilySuccesses G coords beta Nj r v hPublic.positive = {target})
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hArray : ∀ i < r, state.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj target.val i)
    (hSolution : HintScanSolution G coords beta Nj r
      (hintTupleSet (hintOdometerEnumeration Nj r hPublic.positive target)) v state.mem)
    (hCoeff : ∀ c : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + c.val) = (beta ⟨G.rows, hNext⟩ c).val)
    (hAt : At P base (hintNextBitStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 60) state (fun k out => k ≤ 12 * G.hints + 9 * r + 43 ∧ out.regs 1 = 1 ∧
      (∃ C ∈ HintParams.family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v),
        (∀ D ∈ HintParams.family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v), D = C) ∧
        out.regs 8 = (rowBit beta C ⟨G.rows, hNext⟩).val) ∧
      out.mem = state.mem ∧ out.regs 14 = G.context) := by
  classical
  let digits := hintOdometerEnumeration Nj r hPublic.positive target
  let outside : Fin r → Fin G.buckets := fun i => ⟨(digits i).val, (digits i).isLt.trans_le hPublic.bucket_bound⟩
  have hAccept : hintTupleAccept (Finset.univ.image (fun j => (coords j).val)) digits := by
    have ht : target ∈ hintFamilySuccesses G coords beta Nj r v hPublic.positive := by rw [hSuccess]; simp
    exact (Finset.mem_filter.mp ht).2.1
  have hOutsideInj : Function.Injective outside := by
    intro i j heq
    have hval : (outside i).val = (outside j).val := congrArg (fun x : Fin G.buckets => x.val) heq
    exact hAccept.1.injective hval
  have hSeparate : Disjoint (Finset.univ.image (fun i => (outside i).val))
      (Finset.univ.image (fun j => (coords j).val)) := by
    apply Finset.disjoint_left.mpr
    intro q hq hqJ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact hAccept.2 i hqJ
  obtain ⟨z, hStored, hClass, _⟩ := hSolution
  let C := hintBitsSet (fun j => (coords j).val) z ∪ Finset.univ.image (fun i => (outside i).val)
  have hMember : C ∈ HintParams.family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v) := hClass.1
  have hCard : (HintParams.family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).card = 1 := by
    apply (hintFamilySuccesses_card_one G coords hPublic.injective beta hNext.le Nj r v hPublic.positive hPublic.hint_valid).mp
    rw [hSuccess]; simp
  have hUnique : ∀ D ∈ HintParams.family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v), D = C := by
    obtain ⟨only, hOnly⟩ := Finset.card_eq_one.mp hCard
    have hCEq : C = only := by simpa only [hOnly, Finset.mem_singleton] using hMember
    intro D hD
    have hDEq : D = only := by simpa only [hOnly, Finset.mem_singleton] using hD
    exact hDEq.trans hCEq.symm
  have hArray' : ∀ i : Fin r, state.mem (outsideBase + 1 + i.val) = (outside i).val := by
    intro i
    exact (hArray i.val i.isLt).trans (hintOdometerEnumeration_val Nj r hPublic.positive target i).symm
  have hNative := hintNextBitStmt_sem G coords beta hNext Nj r parent outsideBase bitmapBase v outside z
    P E state base hPublic hData hHeader hContext hArray' hStored hCoeff hAt hPc
  have hValue := hintNextCandidate_value coords hPublic.injective outside hOutsideInj hSeparate beta z ⟨G.rows, hNext⟩
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, hFlag, hBit, hMem, hCtx⟩ := hOut
  exact ⟨hCost, hFlag, ⟨C, hMember, hUnique, hBit.trans (congrArg ZMod.val hValue.symm)⟩, hMem, hCtx⟩


def hintRowPredictCountStmt : Stmt := .seq hintRowFamilyStmt
  (.ite (.neqz 1) hintNextBitStmt (.code hintReplayStop))
theorem hintRowPredictCountStmt_len : hintRowPredictCountStmt.len = 1424 := rfl

/-- Actual fixed-count row prediction from the original hints and observation.
    The output flag is one exactly when the original candidate family is a singleton. -/
theorem hintRowPredictCountStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
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
      CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem) := by
  let Fam := family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)
  obtain ⟨hFamilyAt, hBranchAt⟩ := At.seqStmt hAt
  change At P base (hintRowFamilyStmt.compile base) at hFamilyAt
  change At P (base + 1360) ((Stmt.ite (.neqz 1) hintNextBitStmt (.code hintReplayStop)).compile (base + 1360)) at hBranchAt
  obtain ⟨_, kR, sR, hRunR, hPcR, hCostR, hFlagR, hSingletonR, hSolvedR, hDataR, hHeaderR, hCtxR, hFrameR⟩ :=
    hintRowFamilyStmt_sem G coords beta hNext.le Nj r parent outsideBase bitmapBase v P E state base
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
    hFlagB, hSingletonB, hPredB, ?_, ?_, hCtxB, ?_⟩
  · rw [hMemB]; exact hDataR
  · rw [hMemB]; exact hHeaderR
  · rw [hMemB]; exact hFrameR

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowPredictCountStmt_sem
end -- Def_LinearSetReconciliation327_Main_HintRowPredictCount20261120


