-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_06Bitmap
-- name    : LinearSetReconciliation327_Main_B65_06Bitmap
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T03:33:15.343771+00:00
-- url     : https://prove2.me/theorems/444b2fd1-9484-4ac3-b886-77d3e7a5468d
-- title:
--   Theorem 6.5 supporting machine proof B65_06Bitmap
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_05
set_option autoImplicit false

section S_HintWeightedBitmapLoop20261120
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
end S_HintWeightedBitmapLoop20261120
section S_HintBitmapUnionLoop20261120
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
end S_HintBitmapUnionLoop20261120
section S_HintOutputSetup20261120
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
end S_HintOutputSetup20261120
section S_HintBitmapClear20261120
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
end S_HintBitmapClear20261120
section S_HintCandidateBitmap20261120
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
end S_HintCandidateBitmap20261120


