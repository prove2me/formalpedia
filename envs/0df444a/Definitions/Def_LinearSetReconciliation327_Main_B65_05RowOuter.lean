-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_05RowOuter
-- name    : LinearSetReconciliation327_Main_B65_05RowOuter
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-25T15:20:35.771916+00:00
-- url     : https://prove2.me/theorems/4e74d013-c97f-5254-ab9a-99e62b25d332
-- title:
--   Theorem 6.5 supporting machine proof B65_05RowOuter
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_04
set_option autoImplicit false

section S_HintRowOuterBody20261120
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
end S_HintRowOuterBody20261120
section S_HintRowGuard20261120
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
end S_HintRowGuard20261120
section S_HintRowOuterLoop20261120
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
end S_HintRowOuterLoop20261120


