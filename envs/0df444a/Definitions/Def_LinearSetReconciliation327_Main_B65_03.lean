-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_03
-- name    : LinearSetReconciliation327_Main_B65_03
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-25T01:12:56.296351+00:00
-- url     : https://prove2.me/theorems/49572b1c-b56d-4ea8-9103-573ae6f7c26a
-- title:
--   Theorem 6.5 dependency bundle 03
-- statement:
--   Theorem 6.5 dependency bundle 03
-- source:
--   arXiv:2611.11409, Theorem 6.5 dependency closure (bundled for publication).

import Definitions.Def_LinearSetReconciliation327_Main_B65_02
set_option autoImplicit false

section S_HintOdometer20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintOdometerCarry (b : ℕ) (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => (g i + hintOdometerCarry b g i) / b

def hintOdometerDigit (b : ℕ) (g : ℕ → ℕ) (i : ℕ) : ℕ :=
  (g i + hintOdometerCarry b g i) % b

theorem hintOdometerCarry_le (b : ℕ) (g : ℕ → ℕ) (hPos : 0 < b) (hBound : ∀ i, g i < b) (i : ℕ) :
    hintOdometerCarry b g i ≤ 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change (g i + hintOdometerCarry b g i) / b ≤ 1
      have hh : g i + hintOdometerCarry b g i ≤ b := by have := hBound i; omega
      have hDiv : (g i + hintOdometerCarry b g i) / b ≤ b / b := Nat.div_le_div_right hh
      simpa only [Nat.div_self hPos] using hDiv

def hintOdometerParams (arrayBase count radix : ℕ) (state : RAMState) : Prop :=
  state.regs 4 = arrayBase ∧ state.regs 6 = count ∧ state.regs 7 = radix ∧ state.regs 15 = 1

def hintOdometerBody : List Instr :=
  [.add 3 4 0, .load 8 3, .add 8 8 1, .div 1 8 7, .mod 8 8 7, .store 3 8, .add 0 0 15]

theorem hintOdometerBody_spec (E : RAMEnv) (state : RAMState) (arrayBase count radix j : ℕ)
    (g : ℕ → ℕ) (hWord : 1 < 2 ^ E.W) (hPos : 0 < radix) (hRadix : radix < 2 ^ E.W)
    (hBound : ∀ i, g i < radix) (hSpan : arrayBase + count < 2 ^ E.W) (hj : j < count)
    (hArgs : hintOdometerParams arrayBase count radix state)
    (hCounter : state.regs 0 = j) (hCarry : state.regs 1 = hintOdometerCarry radix g j)
    (hDigit : state.mem (arrayBase + j) = g j) :
    let out := runBlock hintOdometerBody E state
    out.pc = state.pc + 7 ∧
    out.mem = Function.update state.mem (arrayBase + j) (hintOdometerDigit radix g j) ∧
    out.regs 0 = j + 1 ∧ out.regs 1 = hintOdometerCarry radix g (j + 1) ∧
    hintOdometerParams arrayBase count radix out ∧
    (∀ reg : Fin 16, reg ≠ 0 → reg ≠ 1 → reg ≠ 3 → reg ≠ 8 → out.regs reg = state.regs reg) := by
  obtain ⟨h4, h6, h7, h15⟩ := hArgs
  have hAddr : arrayBase + j < 2 ^ E.W := by omega
  have hG : g j < 2 ^ E.W := (hBound j).trans hRadix
  have hC := hintOdometerCarry_le radix g hPos hBound j
  have hTotal : g j + hintOdometerCarry radix g j < 2 ^ E.W := by have := hBound j; omega
  have hNewC : hintOdometerCarry radix g (j + 1) < 2 ^ E.W := by
    have := hintOdometerCarry_le radix g hPos hBound (j + 1)
    omega
  have hDiv : (g j + hintOdometerCarry radix g j) / radix < 2 ^ E.W := hNewC
  have hMod : (g j + hintOdometerCarry radix g j) % radix < 2 ^ E.W :=
    (Nat.mod_lt _ hPos).trans hRadix
  have hNext : j + 1 < 2 ^ E.W := by omega
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hintOdometerBody, runBlock, execInstr]
  · simp [hintOdometerBody, runBlock, execInstr, h4, h6, h7, h15, hCounter, hCarry, hDigit,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hG, Nat.mod_eq_of_lt hTotal,
      Nat.mod_eq_of_lt hDiv, Nat.mod_eq_of_lt hMod, hintOdometerDigit]
  · simp [hintOdometerBody, runBlock, execInstr, hCounter, h15, Nat.mod_eq_of_lt hNext]
  · simp [hintOdometerBody, runBlock, execInstr, h4, h7, hCounter, hCarry, hDigit,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hG, Nat.mod_eq_of_lt hTotal, Nat.mod_eq_of_lt hDiv, hintOdometerCarry]
  · simp [hintOdometerParams, hintOdometerBody, runBlock, execInstr, h4, h6, h7, h15]
  · intro reg h0 h1 h3 h8
    simp [hintOdometerBody, runBlock, execInstr, h0, h1, h3, h8]

structure HintOdometerInv (arrayBase count radix : ℕ) (g : ℕ → ℕ) (j : ℕ)
    (original : ℕ → ℕ) (state : RAMState) : Prop where
  params : hintOdometerParams arrayBase count radix state
  counter : state.regs 0 = j
  carry : state.regs 1 = hintOdometerCarry radix g j
  digits : ∀ i < count, state.mem (arrayBase + i) = if i < j then hintOdometerDigit radix g i else g i
  frame : CRMemFrame arrayBase (arrayBase + count) original state.mem

theorem hintOdometerInv_step (E : RAMEnv) (state : RAMState) (arrayBase count radix j : ℕ)
    (g : ℕ → ℕ) (original : ℕ → ℕ) (hWord : 1 < 2 ^ E.W) (hPos : 0 < radix)
    (hRadix : radix < 2 ^ E.W) (hBound : ∀ i, g i < radix)
    (hSpan : arrayBase + count < 2 ^ E.W) (hj : j < count)
    (hInv : HintOdometerInv arrayBase count radix g j original state) :
    let out := runBlock hintOdometerBody E state
    HintOdometerInv arrayBase count radix g (j + 1) original out := by
  have hDigit : state.mem (arrayBase + j) = g j := by simpa only [lt_self_iff_false, if_false] using hInv.digits j hj
  have hSpec := hintOdometerBody_spec E state arrayBase count radix j g hWord hPos hRadix hBound hSpan hj
    hInv.params hInv.counter hInv.carry hDigit
  generalize hOut : runBlock hintOdometerBody E state = out at hSpec
  dsimp only
  obtain ⟨_, hMem, hCounter, hCarry, hArgs, _⟩ := hSpec
  refine ⟨hArgs, hCounter, hCarry, ?_, ?_⟩
  · intro i hi
    rw [hMem]
    by_cases hEq : i = j
    · subst i
      simp
    · have hAddrNe : arrayBase + i ≠ arrayBase + j := by omega
      rw [Function.update_of_ne hAddrNe, hInv.digits i hi]
      by_cases hLt : i < j
      · rw [if_pos hLt, if_pos (by omega)]
      · rw [if_neg hLt, if_neg (by omega)]
  · intro addr hOutside
    have hNe : addr ≠ arrayBase + j := by rcases hOutside with hBefore | hAfter <;> omega
    rw [hMem, Function.update_of_ne hNe, hInv.frame addr hOutside]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem HintOdometerInv.pc {arrayBase count radix j : ℕ} {g original : ℕ → ℕ} {state : RAMState}
    (h : HintOdometerInv arrayBase count radix g j original state) (pc : ℕ) :
    HintOdometerInv arrayBase count radix g j original {state with pc := pc} :=
  ⟨h.params, h.counter, h.carry, h.digits, h.frame⟩

theorem HintOdometerInv.test {arrayBase count radix j : ℕ} {g original : ℕ → ℕ} {state : RAMState}
    (h : HintOdometerInv arrayBase count radix g j original state) (E : RAMEnv) :
    HintOdometerInv arrayBase count radix g j original (runBlock (Cond.lt 2 0 6).code E state) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [hintOdometerParams, Cond.code, runBlock, execInstr] using h.params
  · simpa [Cond.code, runBlock, execInstr] using h.counter
  · simpa [Cond.code, runBlock, execInstr] using h.carry
  · simpa [Cond.code, runBlock, execInstr] using h.digits
  · simpa [Cond.code, runBlock, execInstr] using h.frame

def hintOdometerLoop : Stmt := .loop (.lt 2 0 6) (.code hintOdometerBody)
theorem hintOdometerLoop_len : hintOdometerLoop.len = 10 := rfl

theorem hintOdometerLoop_sem (arrayBase count radix : ℕ) (g original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hPos : 0 < radix) (hRadix : radix < 2 ^ E.W)
    (hBound : ∀ i, g i < radix) (hSpan : arrayBase + count < 2 ^ E.W)
    (hInv : HintOdometerInv arrayBase count radix g 0 original state)
    (hAt : At P base (hintOdometerLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 10) state (fun k out => k ≤ 10 * count + 2 ∧
      HintOdometerInv arrayBase count radix g count original out ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = count ∧
    HintOdometerInv arrayBase count radix g j original st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintOdometerBody := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hDigits, hContext⟩ := hI
    exact ⟨j, hJ, hDigits.pc pc, hContext⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 0 6).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, hDigits, hContext⟩ := hI
    refine ⟨j, hJ, hDigits.test E, ?_⟩
    simpa [Cond.code, runBlock, execInstr] using hContext
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 0 6).eval st := by
    intro left st hI
    obtain ⟨j, hJ, hDigits, _⟩ := hI
    change st.regs 0 < st.regs 6
    rw [hDigits.counter, hDigits.params.2.1]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 6).eval st := by
    intro st hI
    obtain ⟨j, hJ, hDigits, _⟩ := hI
    change ¬ st.regs 0 < st.regs 6
    rw [hDigits.counter, hDigits.params.2.1]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintOdometerBody).len) st
        (fun k out => k ≤ 7 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hDigits, hContext⟩ := hI
    have hj : j < count := by omega
    have hNative := Sem.block P E (base + 2) hintOdometerBody st hBodyAt
      (by simp [hintOdometerBody, NoBranch, Instr.NoBranchI]) hStart
    have hSpec := hintOdometerInv_step E st arrayBase count radix j g original hWord hPos hRadix hBound hSpan hj hDigits
    have hRegisters := (hintOdometerBody_spec E st arrayBase count radix j g hWord hPos hRadix hBound hSpan hj
      hDigits.params hDigits.counter hDigits.carry (by simpa only [lt_self_iff_false, if_false] using hDigits.digits j hj)).2.2.2.2.2
    generalize hMid : runBlock hintOdometerBody E st = mid at hSpec hRegisters
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hK, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨by simpa [hintOdometerBody] using hK.le, j + 1, by omega, hSpec,
      (hRegisters 14 (by decide) (by decide) (by decide) (by decide)).trans hContext⟩
  have hInitial : I count state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintOdometerBody) hAt hWord I 7
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, hFinal, hContext⟩ := hOut
  have hj : j = count := by omega
  rw [hj] at hFinal
  exact ⟨hCost, hFinal, hContext⟩

def hintOdometerInit : List Instr := [.imm 0 0, .imm 1 1, .imm 15 1]
def hintOdometerStmt : Stmt := .seq (.code hintOdometerInit) hintOdometerLoop
theorem hintOdometerStmt_len : hintOdometerStmt.len = 13 := rfl

/-- A whole native increment of a radix-r array, from real memory. The carry
    reports wrap-around. The iteration count is never stored in a machine word. -/
theorem hintOdometerStmt_sem (arrayBase count radix : ℕ) (g : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hPos : 0 < radix) (hRadix : radix < 2 ^ E.W)
    (hBound : ∀ i, g i < radix) (hSpan : arrayBase + count < 2 ^ E.W)
    (hArray : state.regs 4 = arrayBase) (hCount : state.regs 6 = count) (hBase : state.regs 7 = radix)
    (hDigits : ∀ i < count, state.mem (arrayBase + i) = g i)
    (hAt : At P base (hintOdometerStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 13) state (fun k out => k ≤ 10 * count + 5 ∧
      hintOdometerParams arrayBase count radix out ∧ out.regs 0 = count ∧
      out.regs 1 = hintOdometerCarry radix g count ∧
      (∀ i < count, out.mem (arrayBase + i) = hintOdometerDigit radix g i) ∧
      CRMemFrame arrayBase (arrayBase + count) state.mem out.mem ∧ out.regs 14 = state.regs 14) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintOdometerInit at hInitAt
  change At P (base + 3) (hintOdometerLoop.compile (base + 3)) at hLoopAt
  have hNativeInit := Sem.block P E base hintOdometerInit state hInitAt
    (by simp [hintOdometerInit, NoBranch, Instr.NoBranchI]) hPc
  obtain ⟨_, kI, sI, hRunI, hPcI, hCostI, hStateI⟩ := hNativeInit
  have hMemI : sI.mem = state.mem := by rw [hStateI]; rfl
  have hContextI : sI.regs 14 = state.regs 14 := by rw [hStateI]; simp [hintOdometerInit, runBlock, execInstr]
  have hInvI : HintOdometerInv arrayBase count radix g 0 state.mem sI := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hStateI]
      simp [hintOdometerParams, hintOdometerInit, runBlock, execInstr, hArray, hCount, hBase, Nat.mod_eq_of_lt hWord]
    · rw [hStateI]
      simp [hintOdometerInit, runBlock, execInstr]
    · rw [hStateI]
      simp [hintOdometerInit, runBlock, execInstr, hintOdometerCarry, Nat.mod_eq_of_lt hWord]
    · intro i hi
      rw [hMemI]
      simpa using hDigits i hi
    · intro addr _
      exact congrFun hMemI addr
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hInvL, hContextL⟩ :=
    hintOdometerLoop_sem arrayBase count radix g state.mem P E sI (base + 3) hWord hPos hRadix hBound hSpan hInvI
      hLoopAt hPcI
  refine ⟨hPc, kL + kI, out, hintIterate_then (step P E) hRunI hRunL, ?_, ?_, hInvL.params,
    hInvL.counter, hInvL.carry, ?_, hInvL.frame, hContextL.trans hContextI⟩
  · simpa only [Nat.add_assoc] using hPcL
  · change kI = 3 at hCostI
    omega
  · intro i hi
    simpa only [if_pos hi] using hInvL.digits i hi

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintOdometerStmt_sem
end S_HintOdometer20261120
section S_HintScanControl20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintScanCounterPrep : List Instr := hintScanParent ++ [.imm 4 3, .add 4 11 4]

theorem hintScanCounterPrep_spec (E : RAMEnv) (state : RAMState) (parent : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16) :
    let out := runBlock hintScanCounterPrep E state
    out.pc = state.pc + 4 ∧ out.mem = state.mem ∧ out.regs 4 = parent + 3 ∧
      out.regs 1 = state.regs 1 ∧ out.regs 14 = parent + 16 := by
  have h16 : 16 < 2 ^ E.W := by omega
  have h3 : 3 < 2 ^ E.W := by omega
  have hP : parent < 2 ^ E.W := by omega
  have hCount : parent + 3 < 2 ^ E.W := by omega
  have hSub : parent + 16 + 2 ^ E.W - 16 = parent + 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_, ?_⟩ <;>
    simp [hintScanCounterPrep, hintScanParent, runBlock, execInstr, hContext, hSub,
      Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt hCount, Nat.add_mod,
      Nat.mod_self, Nat.mod_eq_of_lt hP]

def hintScanOdometerInput : List Instr := [.load 4 11, .load 6 4, .imm 15 1, .add 4 4 15]
def hintScanOdometerRadix : List Instr := [.imm 3 2, .add 3 11 3, .load 7 3]
def hintScanOdometerPrep : List Instr := hintScanParent ++ hintScanOdometerInput ++ hintScanOdometerRadix

theorem hintScanOdometerPrep_spec (E : RAMEnv) (state : RAMState) (parent outsideBase count radix : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16)
    (hArray : outsideBase + 1 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hRadix : radix < 2 ^ E.W)
    (hReadPointer : state.mem parent = outsideBase) (hReadCount : state.mem outsideBase = count)
    (hReadRadix : state.mem (parent + 2) = radix) :
    let out := runBlock hintScanOdometerPrep E state
    out.pc = state.pc + 9 ∧ out.mem = state.mem ∧
      hintOdometerParams (outsideBase + 1) count radix out ∧ out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hTwo : 2 < 2 ^ E.W := by omega
  have hP2 : parent + 2 < 2 ^ E.W := by omega
  have hBase : outsideBase < 2 ^ E.W := by omega
  have hParentSpec := hintScanParent_spec E state parent hEnd hContext
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hPtrP, hCtxP⟩ := hParentSpec
  have hReadPointerP : sP.mem parent = outsideBase := by rw [hMemP]; exact hReadPointer
  have hReadCountP : sP.mem outsideBase = count := by rw [hMemP]; exact hReadCount
  have hInput : let out := runBlock hintScanOdometerInput E sP
      out.pc = sP.pc + 4 ∧ out.mem = sP.mem ∧ out.regs 4 = outsideBase + 1 ∧ out.regs 6 = count ∧
      out.regs 15 = 1 ∧ out.regs 11 = parent ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hintScanOdometerInput, runBlock, execInstr, hPtrP, hCtxP, hReadPointerP, hReadCountP,
        Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hBase, Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hCount]
  generalize hI : runBlock hintScanOdometerInput E sP = sI at hInput
  obtain ⟨hPcI, hMemI, hArrayI, hCountI, hOneI, hParentI, hContextI⟩ := hInput
  have hReadRadixI : sI.mem (parent + 2) = radix := by rw [hMemI, hMemP]; exact hReadRadix
  have hRadixSpec : let out := runBlock hintScanOdometerRadix E sI
      out.pc = sI.pc + 3 ∧ out.mem = sI.mem ∧
      hintOdometerParams (outsideBase + 1) count radix out ∧ out.regs 14 = parent + 16 := by
    refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      simp [hintScanOdometerRadix, runBlock, execInstr, hArrayI, hCountI, hOneI, hParentI, hContextI, hReadRadixI,
        Nat.mod_eq_of_lt hTwo, Nat.mod_eq_of_lt hP2, Nat.mod_eq_of_lt hRadix]
  generalize hR : runBlock hintScanOdometerRadix E sI = out at hRadixSpec
  obtain ⟨hPcR, hMemR, hArgsR, hCtxR⟩ := hRadixSpec
  have hRun : runBlock hintScanOdometerPrep E state = out := by
    rw [hintScanOdometerPrep, runBlock_append, runBlock_append, hP, hI, hR]
  simpa only [hRun] using And.intro (show out.pc = state.pc + 9 by rw [hPcR, hPcI, hPcP])
    (And.intro (hMemR.trans (hMemI.trans hMemP)) (And.intro hArgsR hCtxR))

def hintScanGoCode : List Instr := [.imm 15 1, .lt 1 1 15]

theorem hintScanGo_spec (E : RAMEnv) (state : RAMState) (carry : ℕ)
    (hWord : 1 < 2 ^ E.W) (hCarry : carry ≤ 1) (hValue : state.regs 1 = carry) :
    let out := runBlock hintScanGoCode E state
    out.pc = state.pc + 2 ∧ out.mem = state.mem ∧ out.regs 1 = hintTruth (carry = 0) ∧ out.regs 14 = state.regs 14 := by
  classical
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [hintScanGoCode, runBlock, execInstr]
  · interval_cases carry <;> simp [hintScanGoCode, runBlock, execInstr, hValue, hintTruth, Nat.mod_eq_of_lt hWord]
  · simp [hintScanGoCode, runBlock, execInstr]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintScanCounterPrep_spec
#print axioms LinearSetReconciliation327.Main.hintScanOdometerPrep_spec
#print axioms LinearSetReconciliation327.Main.hintScanGo_spec
end S_HintScanControl20261120
section S_HintCapCounter20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintCapCounterHead : List Instr := [.load 8 4, .imm 10 1, .lt 10 8 10, .mul 10 10 1]
def hintCapCounterTail : List Instr := [.imm 9 2, .lt 9 8 9, .mul 9 9 1, .add 8 8 9, .store 4 8]
def hintCapCounterCode : List Instr := hintCapCounterHead ++ hintCapCounterTail

theorem hintCapCounter_spec (E : RAMEnv) (state : RAMState) (addr count : ℕ) (accepted : Prop)
    (hWord : 2 < 2 ^ E.W) (hAddr : addr < 2 ^ E.W) (hCount : count ≤ 2)
    (hPointer : state.regs 4 = addr) (hRead : state.mem addr = count)
    (hAccept : state.regs 1 = hintTruth accepted) :
    let out := runBlock hintCapCounterCode E state
    out.pc = state.pc + 9 ∧
      out.mem = Function.update state.mem addr (min 2 (count + hintTruth accepted)) ∧
      out.regs 10 = hintTruth (count = 0 ∧ accepted) ∧ out.regs 1 = state.regs 1 ∧
      out.regs 4 = addr ∧ out.regs 14 = state.regs 14 := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hCountW : count < 2 ^ E.W := by omega
  have hHead : let mid := runBlock hintCapCounterHead E state
      mid.pc = state.pc + 4 ∧ mid.mem = state.mem ∧ mid.regs 8 = count ∧
      mid.regs 10 = hintTruth (count = 0 ∧ accepted) ∧ mid.regs 1 = state.regs 1 ∧
      mid.regs 4 = addr ∧ mid.regs 14 = state.regs 14 := by
    refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hintCapCounterHead, runBlock, execInstr]
    · simp [hintCapCounterHead, runBlock, execInstr, hPointer, hRead, Nat.mod_eq_of_lt hCountW]
    · interval_cases count <;> by_cases hA : accepted <;>
        simp [hintCapCounterHead, runBlock, execInstr, hintTruth, hPointer, hRead, hAccept, hA,
          Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hWord]
    · simp [hintCapCounterHead, runBlock, execInstr]
    · simpa [hintCapCounterHead, runBlock, execInstr] using hPointer
    · simp [hintCapCounterHead, runBlock, execInstr]
  generalize hMid : runBlock hintCapCounterHead E state = mid at hHead
  obtain ⟨hPcMid, hMemMid, hCountMid, hFirstMid, hFlagMid, hPointerMid, hContextMid⟩ := hHead
  have hAcceptMid : mid.regs 1 = hintTruth accepted := hFlagMid.trans hAccept
  have hTail : let out := runBlock hintCapCounterTail E mid
      out.pc = mid.pc + 5 ∧ out.mem = Function.update mid.mem addr (min 2 (count + hintTruth accepted)) ∧
      out.regs 10 = mid.regs 10 ∧ out.regs 1 = mid.regs 1 ∧ out.regs 4 = addr ∧ out.regs 14 = mid.regs 14 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hintCapCounterTail, runBlock, execInstr]
    · interval_cases count <;> by_cases hA : accepted <;>
        simp [hintCapCounterTail, runBlock, execInstr, hintTruth, hPointerMid, hCountMid, hAcceptMid, hA,
          Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hWord]
    · simp [hintCapCounterTail, runBlock, execInstr]
    · simp [hintCapCounterTail, runBlock, execInstr]
    · simpa [hintCapCounterTail, runBlock, execInstr] using hPointerMid
    · simp [hintCapCounterTail, runBlock, execInstr]
  dsimp only
  rw [hintCapCounterCode, runBlock_append, hMid]
  exact ⟨by rw [hTail.1, hPcMid], by rw [hTail.2.1, hMemMid],
    hTail.2.2.1.trans hFirstMid, hTail.2.2.2.1.trans hFlagMid, hTail.2.2.2.2.1, hTail.2.2.2.2.2.trans hContextMid⟩

theorem hintCapCounter_sem (P : Program) (E : RAMEnv) (state : RAMState) (base addr count : ℕ) (accepted : Prop)
    (hWord : 2 < 2 ^ E.W) (hAddr : addr < 2 ^ E.W) (hCount : count ≤ 2)
    (hPointer : state.regs 4 = addr) (hRead : state.mem addr = count)
    (hAccept : state.regs 1 = hintTruth accepted) (hAt : At P base hintCapCounterCode) (hPc : state.pc = base) :
    Sem P E base (base + 9) state (fun k out => k = 9 ∧
      out.mem addr = min 2 (count + hintTruth accepted) ∧
      (∀ other, other ≠ addr → out.mem other = state.mem other) ∧
      out.regs 10 = hintTruth (count = 0 ∧ accepted) ∧ out.regs 1 = state.regs 1 ∧
      out.regs 4 = addr ∧ out.regs 14 = state.regs 14) := by
  have hSpec := hintCapCounter_spec E state addr count accepted hWord hAddr hCount hPointer hRead hAccept
  generalize hMid : runBlock hintCapCounterCode E state = mid at hSpec
  obtain ⟨_, hMem, hFirst, hFlag, hPointerOut, hContext⟩ := hSpec
  have hNative := Sem.block P E base hintCapCounterCode state hAt
    (by simp [hintCapCounterCode, hintCapCounterHead, hintCapCounterTail, NoBranch, Instr.NoBranchI]) hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hK, hOut⟩ := hOut
  rw [hMid] at hOut
  subst out
  refine ⟨by simpa [hintCapCounterCode, hintCapCounterHead, hintCapCounterTail] using hK, ?_, ?_, hFirst, hFlag, hPointerOut, hContext⟩
  · simp [hMem]
  · intro other hNe
    rw [hMem, Function.update_of_ne hNe]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCapCounter_sem
end S_HintCapCounter20261120
section S_HintSuccessPrefix20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintSuccessPrefix {L : ℕ} (S : Finset (Fin L)) (j : ℕ) : ℕ :=
  (S.filter (fun i => i.val < j)).card

theorem hintSuccessPrefix_zero {L : ℕ} (S : Finset (Fin L)) : hintSuccessPrefix S 0 = 0 := by
  simp [hintSuccessPrefix]

theorem hintSuccessPrefix_full {L : ℕ} (S : Finset (Fin L)) : hintSuccessPrefix S L = S.card := by
  have hEq : S.filter (fun i => i.val < L) = S := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨And.left, fun h => ⟨h, i.isLt⟩⟩
  rw [hintSuccessPrefix, hEq]

theorem hintSuccessPrefix_succ {L : ℕ} (S : Finset (Fin L)) (j : Fin L) :
    hintSuccessPrefix S (j.val + 1) = hintSuccessPrefix S j.val + hintTruth (j ∈ S) := by
  classical
  have hInsert : S.filter (fun i => i.val < j.val + 1) =
      if j ∈ S then insert j (S.filter (fun i => i.val < j.val)) else S.filter (fun i => i.val < j.val) := by
    ext i
    by_cases hj : j ∈ S
    · rw [if_pos hj]
      simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]
      constructor
      · rintro ⟨hi, hLt⟩
        by_cases hEq : i.val = j.val
        · exact Or.inl hEq
        · exact Or.inr ⟨hi, by omega⟩
      · rintro (hEq | ⟨hi, hLt⟩)
        · have hFin : i = j := Fin.ext hEq
          subst i
          exact ⟨hj, by omega⟩
        · exact ⟨hi, by omega⟩
    · rw [if_neg hj]
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi, hLt⟩
        have hNe : i.val ≠ j.val := by
          intro hEq
          have hFin : i = j := Fin.ext hEq
          exact hj (hFin ▸ hi)
        exact ⟨hi, by omega⟩
      · rintro ⟨hi, hLt⟩
        exact ⟨hi, by omega⟩
  have hFresh : j ∉ S.filter (fun i => i.val < j.val) := by simp
  unfold hintSuccessPrefix
  rw [hInsert]
  by_cases hj : j ∈ S <;> simp [hj, hFresh, hintTruth]

theorem hintCap2_step (n bit : ℕ) : min 2 (min 2 n + bit) = min 2 (n + bit) := by omega

theorem hintCap2_one (n : ℕ) : min 2 n = 1 ↔ n = 1 := by omega

theorem hintCapCounter_prefix_sem {L : ℕ} (S : Finset (Fin L)) (j : Fin L)
    (P : Program) (E : RAMEnv) (state : RAMState) (base addr : ℕ)
    (hWord : 2 < 2 ^ E.W) (hAddr : addr < 2 ^ E.W)
    (hPointer : state.regs 4 = addr) (hRead : state.mem addr = min 2 (hintSuccessPrefix S j.val))
    (hAccept : state.regs 1 = hintTruth (j ∈ S)) (hAt : At P base hintCapCounterCode) (hPc : state.pc = base) :
    Sem P E base (base + 9) state (fun k out => k = 9 ∧
      out.mem addr = min 2 (hintSuccessPrefix S (j.val + 1)) ∧
      (∀ other, other ≠ addr → out.mem other = state.mem other) ∧
      out.regs 1 = state.regs 1 ∧ out.regs 4 = addr ∧ out.regs 14 = state.regs 14) := by
  have hNative := hintCapCounter_sem P E state base addr (min 2 (hintSuccessPrefix S j.val)) (j ∈ S)
    hWord hAddr (by omega) hPointer hRead hAccept hAt hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, hCounter, hFrame, _, hFlag, hPointerOut, hContext⟩ := hOut
  refine ⟨hCost, ?_, hFrame, hFlag, hPointerOut, hContext⟩
  rw [hCounter, hintCap2_step, hintSuccessPrefix_succ]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCapCounter_prefix_sem
end S_HintSuccessPrefix20261120
section S_HintOdometerEnumeration20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintOdometerRank (b : ℕ) (g : ℕ → ℕ) (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, g i * b ^ i

theorem hintOdometerRank_succ (b : ℕ) (g : ℕ → ℕ) (r : ℕ) :
    hintOdometerRank b g (r + 1) = hintOdometerRank b g r + g r * b ^ r :=
  Finset.sum_range_succ _ _

theorem hintOdometerRank_lt (b : ℕ) (g : ℕ → ℕ) (hBound : ∀ i, g i < b) (r : ℕ) :
    hintOdometerRank b g r < b ^ r := by
  induction r with
  | zero => simp [hintOdometerRank]
  | succ r ih =>
    rw [hintOdometerRank_succ, pow_succ]
    have hDigit : (g r + 1) * b ^ r ≤ b * b ^ r :=
      Nat.mul_le_mul_right (b ^ r) (Nat.succ_le_of_lt (hBound r))
    have hPrefix : hintOdometerRank b g r + g r * b ^ r < b ^ r + g r * b ^ r :=
      Nat.add_lt_add_right ih _
    have hEnd : b ^ r + g r * b ^ r ≤ b ^ r * b := by nlinarith only [hDigit]
    exact hPrefix.trans_le hEnd

/-- The processed low digits plus the outgoing carry have exactly the original
    integer value plus one. This identity does not require storing that value. -/
theorem hintOdometer_telescope (b : ℕ) (g : ℕ → ℕ) (r : ℕ) :
    hintOdometerRank b (hintOdometerDigit b g) r + hintOdometerCarry b g r * b ^ r =
      hintOdometerRank b g r + 1 := by
  induction r with
  | zero => simp [hintOdometerRank, hintOdometerCarry]
  | succ r ih =>
    have hDecomp : hintOdometerDigit b g r + hintOdometerCarry b g (r + 1) * b =
        g r + hintOdometerCarry b g r := by
      simpa only [hintOdometerDigit, hintOdometerCarry, Nat.mul_comm] using
        Nat.mod_add_div (g r + hintOdometerCarry b g r) b
    rw [hintOdometerRank_succ, hintOdometerRank_succ, pow_succ]
    calc
      hintOdometerRank b (hintOdometerDigit b g) r + hintOdometerDigit b g r * b ^ r +
          hintOdometerCarry b g (r + 1) * (b ^ r * b) =
        hintOdometerRank b (hintOdometerDigit b g) r +
          (hintOdometerDigit b g r + hintOdometerCarry b g (r + 1) * b) * b ^ r := by ring
      _ = hintOdometerRank b (hintOdometerDigit b g) r +
          (g r + hintOdometerCarry b g r) * b ^ r := by rw [hDecomp]
      _ = (hintOdometerRank b (hintOdometerDigit b g) r + hintOdometerCarry b g r * b ^ r) +
          g r * b ^ r := by ring
      _ = hintOdometerRank b g r + g r * b ^ r + 1 := by rw [ih]; omega

theorem hintOdometer_carry_iff (b : ℕ) (g : ℕ → ℕ) (hPos : 0 < b)
    (hBound : ∀ i, g i < b) (r : ℕ) :
    hintOdometerCarry b g r = 1 ↔ hintOdometerRank b g r + 1 = b ^ r := by
  have hOld := hintOdometerRank_lt b g hBound r
  have hNew := hintOdometerRank_lt b (hintOdometerDigit b g) (fun _ => Nat.mod_lt _ hPos) r
  have hCarry := hintOdometerCarry_le b g hPos hBound r
  have hValue := hintOdometer_telescope b g r
  constructor
  · intro hOne
    rw [hOne, Nat.one_mul] at hValue
    omega
  · intro hLast
    by_cases hZero : hintOdometerCarry b g r = 0
    · rw [hZero, Nat.zero_mul, Nat.add_zero, hLast] at hValue
      omega
    · omega

theorem hintOdometer_rank_next (b : ℕ) (g : ℕ → ℕ) (hPos : 0 < b)
    (hBound : ∀ i, g i < b) (r : ℕ) :
    hintOdometerRank b (hintOdometerDigit b g) r =
      if hintOdometerRank b g r + 1 = b ^ r then 0 else hintOdometerRank b g r + 1 := by
  have hValue := hintOdometer_telescope b g r
  have hCarry := hintOdometerCarry_le b g hPos hBound r
  by_cases hLast : hintOdometerRank b g r + 1 = b ^ r
  · rw [(hintOdometer_carry_iff b g hPos hBound r).mpr hLast, Nat.one_mul, hLast] at hValue
    rw [if_pos hLast]
    omega
  · have hZero : hintOdometerCarry b g r = 0 := by
      have hNot := mt (hintOdometer_carry_iff b g hPos hBound r).mp hLast
      omega
    rw [if_neg hLast]
    simpa only [hZero, Nat.zero_mul, Nat.add_zero] using hValue

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem hintOdometerRank_congr (b r : ℕ) (g f : ℕ → ℕ) (h : ∀ i < r, g i = f i) :
    hintOdometerRank b g r = hintOdometerRank b f r := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

def hintEnumeratedDigits (b n : ℕ) : ℕ → ℕ :=
  (hintOdometerDigit b)^[n] (fun _ => 0)

theorem hintEnumeratedDigits_zero (b : ℕ) : hintEnumeratedDigits b 0 = (fun _ => 0) := rfl

theorem hintEnumeratedDigits_succ (b n : ℕ) :
    hintEnumeratedDigits b (n + 1) = hintOdometerDigit b (hintEnumeratedDigits b n) := by
  unfold hintEnumeratedDigits
  rw [Function.iterate_succ_apply']

theorem hintEnumeratedDigits_bound (b n : ℕ) (hPos : 0 < b) (i : ℕ) : hintEnumeratedDigits b n i < b := by
  cases n with
  | zero => exact hPos
  | succ n => rw [hintEnumeratedDigits_succ]; exact Nat.mod_lt _ hPos

theorem hintEnumeratedDigits_rank (b r n : ℕ) (hPos : 0 < b) (hn : n < b ^ r) :
    hintOdometerRank b (hintEnumeratedDigits b n) r = n := by
  induction n with
  | zero => simp [hintEnumeratedDigits_zero, hintOdometerRank]
  | succ n ih =>
    have hn' : n < b ^ r := by omega
    rw [hintEnumeratedDigits_succ, hintOdometer_rank_next b _ hPos (hintEnumeratedDigits_bound b n hPos) r,
      ih hn', if_neg (by omega)]

/-- Every bounded coordinate array occurs exactly once before the first wrap.
    Finiteness is used only in this proof, not as an exponential hint search. -/
noncomputable def hintOdometerEnumeration (b r : ℕ) (hPos : 0 < b) : Fin (b ^ r) ≃ (Fin r → Fin b) := by
  let encode : Fin (b ^ r) → (Fin r → Fin b) := fun n i =>
    ⟨hintEnumeratedDigits b n.val i.val, hintEnumeratedDigits_bound b n.val hPos i.val⟩
  have hInj : Function.Injective encode := by
    intro n m hEq
    have hDigits : ∀ i < r, hintEnumeratedDigits b n.val i = hintEnumeratedDigits b m.val i := by
      intro i hi
      exact congrArg Fin.val (congrFun hEq ⟨i, hi⟩)
    have hRanks := hintOdometerRank_congr b r _ _ hDigits
    rw [hintEnumeratedDigits_rank b r n.val hPos n.isLt, hintEnumeratedDigits_rank b r m.val hPos m.isLt] at hRanks
    exact Fin.ext hRanks
  apply Equiv.ofBijective encode
  refine ⟨hInj, ?_⟩
  by_contra hNot
  have hLt := Fintype.card_lt_of_injective_not_surjective encode hInj hNot
  have hImpossible : b ^ r < b ^ r := by simpa only [Fintype.card_fin, Fintype.card_fun] using hLt
  exact (Nat.lt_irrefl _) hImpossible

theorem hintOdometerEnumeration_val (b r : ℕ) (hPos : 0 < b) (n : Fin (b ^ r)) (i : Fin r) :
    (hintOdometerEnumeration b r hPos n i).val = hintEnumeratedDigits b n.val i.val := rfl

theorem hintOdometerStmt_rank_sem (arrayBase count radix : ℕ) (g : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hPos : 0 < radix) (hRadix : radix < 2 ^ E.W)
    (hBound : ∀ i, g i < radix) (hSpan : arrayBase + count < 2 ^ E.W)
    (hArray : state.regs 4 = arrayBase) (hCount : state.regs 6 = count) (hBase : state.regs 7 = radix)
    (hDigits : ∀ i < count, state.mem (arrayBase + i) = g i)
    (hAt : At P base (hintOdometerStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 13) state (fun k out => k ≤ 10 * count + 5 ∧
      hintOdometerParams arrayBase count radix out ∧ out.regs 0 = count ∧
      (out.regs 1 = 1 ↔ hintOdometerRank radix g count + 1 = radix ^ count) ∧
      hintOdometerRank radix (fun i => out.mem (arrayBase + i)) count =
        (if hintOdometerRank radix g count + 1 = radix ^ count then 0 else hintOdometerRank radix g count + 1) ∧
      CRMemFrame arrayBase (arrayBase + count) state.mem out.mem ∧ out.regs 14 = state.regs 14) := by
  have hNative := hintOdometerStmt_sem arrayBase count radix g P E state base hWord hPos hRadix hBound hSpan
    hArray hCount hBase hDigits hAt hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, hArgs, hCounter, hCarry, hValues, hFrame, hContext⟩ := hOut
  refine ⟨hCost, hArgs, hCounter, ?_, ?_, hFrame, hContext⟩
  · rw [hCarry]
    exact hintOdometer_carry_iff radix g hPos hBound count
  · rw [hintOdometerRank_congr radix count _ _ hValues]
    exact hintOdometer_rank_next radix g hPos hBound count

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintOdometerEnumeration
#print axioms LinearSetReconciliation327.Main.hintOdometerStmt_rank_sem
end S_HintOdometerEnumeration20261120
section S_HintFamilySingleton20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

theorem hintLinear_injective_of_unique {a h : ℕ} (A : HintVec h →ₗ[ZMod 2] HintVec a)
    (b : HintVec a) (hUnique : ∃! z, A z = b) : Function.Injective A := by
  obtain ⟨z, hz, hOnly⟩ := hUnique
  intro x y hEq
  have hOther : A (z + (x - y)) = b := by rw [map_add, map_sub, hEq, sub_self, add_zero, hz]
  have hZ : z + (x - y) = z := hOnly _ hOther
  have hZero : x - y = 0 := add_left_cancel (hZ.trans (add_zero z).symm)
  exact sub_eq_zero.mp hZero

/-- A singleton in any one outside class forces the same hint matrix to have
    trivial kernel. This is the uniformity needed when aggregating all classes. -/
theorem hintFamilyClass_unique_injective (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj r : ℕ) (A : Finset ℕ) (v : HintVec G.rows)
    (hHintValid : ∀ j, (coords j).val < Nj)
    (hClass : ∃! C : Finset ℕ, hintFamilyClass G coords beta Nj r A v C) :
    Function.Injective (hintGaussMap G coords beta hPrefix) := by
  obtain ⟨C, hC⟩ := hClass.exists
  have hMem := (hintFamily_mem hPrefix Nj beta _ C r v).mp hC.1
  have hA : A ⊆ Finset.range Nj := by
    intro x hx
    rw [← hC.2] at hx
    exact hMem.1 (Finset.mem_sdiff.mp hx).1
  have hCard : A.card = r := by rw [← hC.2]; exact hMem.2.1
  have hSeparate : Disjoint A (Finset.univ.image (fun j => (coords j).val)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hJ
    rw [← hC.2] at hx
    exact (Finset.mem_sdiff.mp hx).2 hJ
  have hVector := (hintFamily_affine_unique G coords hInj beta hPrefix Nj r A v hHintValid hA hCard hSeparate).mpr hClass
  exact hintLinear_injective_of_unique _ _ hVector

theorem hintFamilyClass_subsingleton (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj r : ℕ) (A : Finset ℕ) (v : HintVec G.rows)
    (hMatrix : Function.Injective (hintGaussMap G coords beta hPrefix))
    (C D : Finset ℕ) (hC : hintFamilyClass G coords beta Nj r A v C)
    (hD : hintFamilyClass G coords beta Nj r A v D) : C = D := by
  let iota := fun j => (coords j).val
  let zC := hintSetBits iota C
  let zD := hintSetBits iota D
  have hDecodeC : hintBitsSet iota zC ∪ A = C := hintBitsUnion_decode iota A C hC.2
  have hDecodeD : hintBitsSet iota zD ∪ A = D := hintBitsUnion_decode iota A D hD.2
  have hSeparate : Disjoint A (Finset.univ.image iota) := by
    apply Finset.disjoint_left.mpr
    intro x hx hJ
    rw [← hC.2] at hx
    exact (Finset.mem_sdiff.mp hx).2 hJ
  have hRowsC := ((hintFamily_mem hPrefix Nj beta _ C r v).mp hC.1).2.2
  have hRowsD := ((hintFamily_mem hPrefix Nj beta _ D r v).mp hD.1).2.2
  have hAffineC : hintGaussMap G coords beta hPrefix zC = hintOutsideRhs G beta hPrefix A v := by
    apply (hintBitsUnion_affine G coords hInj beta hPrefix A v zC hSeparate).mp
    rw [hDecodeC]
    exact hRowsC
  have hAffineD : hintGaussMap G coords beta hPrefix zD = hintOutsideRhs G beta hPrefix A v := by
    apply (hintBitsUnion_affine G coords hInj beta hPrefix A v zD hSeparate).mp
    rw [hDecodeD]
    exact hRowsD
  have hz : zC = zD := hMatrix (hAffineC.trans hAffineD.symm)
  exact hDecodeC.symm.trans ((congrArg (fun z => hintBitsSet iota z ∪ A) hz).trans hDecodeD)

/-- Singleton fibers identify the singleton union exactly when one singleton
    fiber implies all fibers are subsingleton. Without this premise the claim
    would fail in the presence of a second, nonsingleton fiber. -/
theorem hintUniqueFiberPartition {α β : Type*} (P : α → Prop) (f : α → β)
    (hUniform : ∀ b, (∃! x, P x ∧ f x = b) →
      ∀ b' x y, P x → P y → f x = b' → f y = b' → x = y) :
    (∃! x, P x) ↔ ∃! b, ∃! x, P x ∧ f x = b := by
  constructor
  · rintro ⟨x, hx, hOnly⟩
    refine ⟨f x, ⟨x, ⟨hx, rfl⟩, fun y hy => hOnly y hy.1⟩, ?_⟩
    intro b hFiber
    obtain ⟨y, ⟨hy, hf⟩, _⟩ := hFiber
    exact hf.symm.trans (congrArg f (hOnly y hy))
  · rintro ⟨b, hFiber, hOnlyFiber⟩
    have hFiberCopy := hFiber
    obtain ⟨x, ⟨hx, hfx⟩, hOnly⟩ := hFiber
    refine ⟨x, hx, ?_⟩
    intro y hy
    have hFiberY : ∃! z, P z ∧ f z = f y := by
      refine ⟨y, ⟨hy, rfl⟩, ?_⟩
      intro z hz
      exact hUniform b hFiberCopy (f y) z y hz.1 hy hz.2 rfl
    exact hOnly y ⟨hy, hOnlyFiber (f y) hFiberY⟩

/-- The original family is a singleton iff exactly one outside class is a
    singleton. Noninjective hint matrices yield no singleton on either side. -/
theorem hintFamily_singleton_classes (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj r : ℕ) (v : HintVec G.rows)
    (hHintValid : ∀ j, (coords j).val < Nj) :
    (∃! C : Finset ℕ, C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)) ↔
      ∃! A : Finset ℕ, ∃! C : Finset ℕ, hintFamilyClass G coords beta Nj r A v C := by
  apply hintUniqueFiberPartition
    (fun C => C ∈ family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v))
    (fun C => C \ Finset.univ.image (fun j => (coords j).val))
  intro A hUnique A' C D hC hD hDiffC hDiffD
  have hMatrix := hintFamilyClass_unique_injective G coords hInj beta hPrefix Nj r A v hHintValid hUnique
  exact hintFamilyClass_subsingleton G coords hInj beta hPrefix Nj r A' v hMatrix C D ⟨hC, hDiffC⟩ ⟨hD, hDiffD⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFamily_singleton_classes
end S_HintFamilySingleton20261120
section S_HintFamilyEnumeration20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

theorem hintFinset_card_one {α : Type*} (S : Finset α) : S.card = 1 ↔ ∃! x, x ∈ S := by
  classical
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨x, by simp, fun y hy => Finset.mem_singleton.mp hy⟩
  · rintro ⟨x, hx, hOnly⟩
    have hEq : S = {x} := by
      ext y
      constructor
      · intro hy; exact Finset.mem_singleton.mpr (hOnly y hy)
      · intro hy; exact (Finset.mem_singleton.mp hy) ▸ hx
    rw [hEq, Finset.card_singleton]

theorem hintFamilyClass_domain (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r : ℕ) (A : Finset ℕ) (v : HintVec G.rows)
    (hClass : ∃! C : Finset ℕ, hintFamilyClass G coords beta Nj r A v C) :
    A ⊆ Finset.range Nj \ Finset.univ.image (fun j => (coords j).val) ∧ A.card = r := by
  obtain ⟨C, hC, _⟩ := hClass
  have hMem := (hintFamily_mem hPrefix Nj beta _ C r v).mp hC.1
  constructor
  · intro x hx
    rw [← hC.2] at hx
    obtain ⟨hxC, hxJ⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hMem.1 hxC, hxJ⟩
  · rw [← hC.2]
    exact hMem.2.1

noncomputable def hintFamilySuccesses (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj r : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj) :
    Finset (Fin (Nj ^ r)) := by
  classical
  let J := Finset.univ.image (fun j => (coords j).val)
  exact Finset.univ.filter (fun n =>
    let g := hintOdometerEnumeration Nj r hPos n
    (StrictMono (fun i => (g i).val) ∧ ∀ i, (g i).val ∉ J) ∧
      ∃! C : Finset ℕ, hintFamilyClass G coords beta Nj r (hintTupleSet g) v C)

/-- The successful filtered odometer positions are exactly the original family's
    singleton outside classes. Thus counting them detects the original singleton
    predicate even when the common hint matrix is noninjective. -/
theorem hintFamilySuccesses_card_one (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (hInj : Function.Injective coords) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (Nj r : ℕ) (v : HintVec G.rows) (hPos : 0 < Nj)
    (hHintValid : ∀ j, (coords j).val < Nj) :
    (hintFamilySuccesses G coords beta Nj r v hPos).card = 1 ↔
      (family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).card = 1 := by
  classical
  let J := Finset.univ.image (fun j => (coords j).val)
  let Q : Finset ℕ → Prop := fun A => ∃! C : Finset ℕ, hintFamilyClass G coords beta Nj r A v C
  let D : Finset ℕ → Prop := fun A => A ⊆ Finset.range Nj \ J ∧ A.card = r
  let Pred : (Fin r → Fin Nj) → Prop := fun g => StrictMono (fun i => (g i).val) ∧ ∀ i, (g i).val ∉ J
  let U : (Fin r → Fin Nj) → Prop := fun g => Q (hintTupleSet g)
  let e := hintOdometerEnumeration Nj r hPos
  have hDomain : ∀ A, Q A → D A := fun A hA => hintFamilyClass_domain G coords beta hPrefix Nj r A v hA
  have hRestrict : (∃! A : Finset ℕ, Q A) ↔ ∃! A : HintOutsideSet Nj J r, Q A.val := by
    apply (hintUnique_congr Q (fun A => D A ∧ Q A) (fun A => ?_)).trans (hintSubtype_unique D Q).symm
    exact ⟨fun hA => ⟨hDomain A hA, hA⟩, And.right⟩
  have hTuple : (∃! g : HintOutsideTuple Nj J r, Q (hintTupleSet g.val)) ↔
      ∃! A : HintOutsideSet Nj J r, Q A.val :=
    hintEquiv_unique (hintOutsideTupleCodec Nj J r) (fun A => Q A.val)
  have hArrays : (∃! g : HintOutsideTuple Nj J r, Q (hintTupleSet g.val)) ↔
      ∃! g : Fin r → Fin Nj, Pred g ∧ U g := hintSubtype_unique Pred U
  have hIndices : (∃! n : Fin (Nj ^ r), Pred (e n) ∧ U (e n)) ↔
      ∃! g : Fin r → Fin Nj, Pred g ∧ U g := hintEquiv_unique e (fun g => Pred g ∧ U g)
  have hSuccess : (hintFamilySuccesses G coords beta Nj r v hPos).card = 1 ↔
      ∃! n : Fin (Nj ^ r), Pred (e n) ∧ U (e n) := by
    apply (hintFinset_card_one _).trans
    apply hintUnique_congr
    intro n
    simp [hintFamilySuccesses, Pred, U, e, Q, J]
  calc
    (hintFamilySuccesses G coords beta Nj r v hPos).card = 1 ↔
        ∃! n : Fin (Nj ^ r), Pred (e n) ∧ U (e n) := hSuccess
    _ ↔ ∃! g : Fin r → Fin Nj, Pred g ∧ U g := hIndices
    _ ↔ ∃! g : HintOutsideTuple Nj J r, Q (hintTupleSet g.val) := hArrays.symm
    _ ↔ ∃! A : HintOutsideSet Nj J r, Q A.val := hTuple
    _ ↔ ∃! A : Finset ℕ, Q A := hRestrict.symm
    _ ↔ ∃! C : Finset ℕ, C ∈ family Nj beta J r (List.ofFn v) :=
      (hintFamily_singleton_classes G coords hInj beta hPrefix Nj r v hHintValid).symm
    _ ↔ (family Nj beta J r (List.ofFn v)).card = 1 := (hintFinset_card_one _).symm

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFamilySuccesses_card_one
end S_HintFamilyEnumeration20261120
section S_HintScanCountStep20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintScanPublic (E : RAMEnv) (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) : Prop where
  geometry : HintGaussGeometry E G
  reserve : G.context + 16 ≤ G.residual
  parent_eq : parent + 16 = G.context
  source : G.hintList + G.hints + 2 * G.rows ≤ parent
  outside_span : outsideBase + 1 + r ≤ G.hintList
  bitmap_span : bitmapBase + Nj ≤ outsideBase
  injective : Function.Injective coords
  hint_valid : ∀ j, (coords j).val < Nj
  bucket_bound : Nj ≤ G.buckets
  positive : 0 < Nj
  fits : HintGaussHeaderFits E G 0
  steps_pos : 0 < G.steps
  coefficient_span : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W
  coefficients : ∀ c : Fin G.buckets, ∀ s : Fin G.rows,
    E.coeff G.node (G.row * G.steps * G.buckets + c.val + s.val * G.buckets) =
      (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ c).val

structure HintScanReadOnly (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows) (memory : ℕ → ℕ) : Prop where
  outside_pointer : memory parent = outsideBase
  bitmap_pointer : memory (parent + 1) = bitmapBase
  radix : memory (parent + 2) = Nj
  outside_count : memory outsideBase = r
  hints : ∀ j : Fin G.hints, memory (G.hintList + j.val) = (coords j).val
  observation : ∀ s : Fin G.rows, memory (G.hintList + G.hints + G.rows + s.val) = (v s).val
  bitmap : ∀ q < Nj, memory (bitmapBase + q) = hintTruth (q ∈ Finset.univ.image (fun j => (coords j).val))

/-- The mutable parts of one scan: tuple, count, affine RHS and Gaussian work. -/
def HintScanFrame (G : HintGaussArea) (parent outsideBase r : ℕ) (original memory : ℕ → ℕ) : Prop :=
  ∀ addr, (addr < outsideBase + 1 ∨ outsideBase + 1 + r ≤ addr) → addr ≠ parent + 3 →
    (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
    (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → memory addr = original addr

theorem HintScanFrame.refl (G : HintGaussArea) (parent outsideBase r : ℕ) (memory : ℕ → ℕ) :
    HintScanFrame G parent outsideBase r memory memory := by intro _ _ _ _ _; rfl

theorem HintScanFrame.trans {G : HintGaussArea} {parent outsideBase r : ℕ} {first middle last : ℕ → ℕ}
    (hFirst : HintScanFrame G parent outsideBase r first middle)
    (hLast : HintScanFrame G parent outsideBase r middle last) : HintScanFrame G parent outsideBase r first last := by
  intro addr hArray hCount hRhs hGauss
  exact (hLast addr hArray hCount hRhs hGauss).trans (hFirst addr hArray hCount hRhs hGauss)

theorem HintScanFrame.of_judge {G : HintGaussArea} {parent outsideBase r : ℕ} {original memory : ℕ → ℕ}
    (h : ∀ addr, (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
      (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → memory addr = original addr) :
    HintScanFrame G parent outsideBase r original memory := by intro addr _ _; exact h addr

theorem HintScanFrame.of_counter {G : HintGaussArea} {parent outsideBase r : ℕ} {original memory : ℕ → ℕ}
    (h : ∀ addr, addr ≠ parent + 3 → memory addr = original addr) :
    HintScanFrame G parent outsideBase r original memory := by intro addr _ hCount _ _; exact h addr hCount

theorem HintScanFrame.of_array {G : HintGaussArea} {parent outsideBase r : ℕ} {original memory : ℕ → ℕ}
    (h : CRMemFrame (outsideBase + 1) (outsideBase + 1 + r) original memory) :
    HintScanFrame G parent outsideBase r original memory := by intro addr hArray _ _ _; exact h addr hArray

theorem HintScanReadOnly.frame {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj r parent outsideBase bitmapBase : ℕ} {v : HintVec G.rows} {original memory : ℕ → ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v original)
    (hFrame : HintScanFrame G parent outsideBase r original memory) :
    HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v memory := by
  have hParent := hPublic.parent_eq
  have hSource := hPublic.source
  have hOutside := hPublic.outside_span
  have hBitmap := hPublic.bitmap_span
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFrame _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hData.outside_pointer
  · rw [hFrame _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hData.bitmap_pointer
  · rw [hFrame _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hData.radix
  · rw [hFrame _ (Or.inl (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
    exact hData.outside_count
  · intro j
    rw [hFrame _ (Or.inr (by have := j.isLt; omega)) (by have := j.isLt; omega)
      (Or.inl (by have := j.isLt; omega)) (Or.inl (by have := j.isLt; omega))]
    exact hData.hints j
  · intro s
    rw [hFrame _ (Or.inr (by have := s.isLt; omega)) (by have := s.isLt; omega)
      (Or.inr (by omega)) (Or.inl (by have := s.isLt; omega))]
    exact hData.observation s
  · intro q hq
    rw [hFrame _ (Or.inl (by omega)) (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
    exact hData.bitmap q hq

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintScanCountStepStmt : Stmt := .seq hintScanJudgeStmt
  (.seq (.code hintScanCounterPrep) (.code hintCapCounterCode))
theorem hintScanCountStepStmt_len : hintScanCountStepStmt.len = 609 := rfl

theorem hintScanCountStepStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (n : Fin (Nj ^ r))
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hArray : ∀ j : Fin r, state.mem (outsideBase + 1 + j.val) =
      (hintOdometerEnumeration Nj r hPublic.positive n j).val)
    (hCounter : state.mem (parent + 3) =
      min 2 (hintSuccessPrefix (hintFamilySuccesses G coords beta Nj r v hPublic.positive) n.val))
    (hAt : At P base (hintScanCountStepStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 609) state (fun k out =>
      k ≤ 11 * r * r + 13 * r + 36 + (9 * G.rows + 23 + (20 * G.rows + 50) * r + 512 * (G.rows + G.hints + 1) ^ 3) ∧
      out.mem (parent + 3) = min 2 (hintSuccessPrefix (hintFamilySuccesses G coords beta Nj r v hPublic.positive) (n.val + 1)) ∧
      out.regs 1 = hintTruth (n ∈ hintFamilySuccesses G coords beta Nj r v hPublic.positive) ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      (∀ j : Fin r, out.mem (outsideBase + 1 + j.val) = (hintOdometerEnumeration Nj r hPublic.positive n j).val) ∧
      HintScanFrame G parent outsideBase r state.mem out.mem) := by
  classical
  let S := hintFamilySuccesses G coords beta Nj r v hPublic.positive
  let outside := hintOdometerEnumeration Nj r hPublic.positive n
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
  have hWord : 2 < 2 ^ E.W := by omega
  obtain ⟨index, hHeader⟩ := hHeader
  obtain ⟨hJudgeAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintScanJudgeStmt.compile base) at hJudgeAt
  change At P (base + 596) ((Stmt.seq (.code hintScanCounterPrep) (.code hintCapCounterCode)).compile (base + 596)) at hRestAt
  obtain ⟨hPrepAt, hCounterAt⟩ := At.seqStmt hRestAt
  change At P (base + 596) hintScanCounterPrep at hPrepAt
  change At P (base + 600) hintCapCounterCode at hCounterAt
  obtain ⟨_, kJ, sJ, hRunJ, hPcJ, hCostJ, hBitJ, hUniqueJ, _, hHeaderJ, hFrameJ, hContextJ⟩ :=
    hintScanJudgeStmt_sem G coords r parent outsideBase bitmapBase index Nj outside beta hPrefix v P E state base
      hPublic.geometry hPublic.reserve hPublic.parent_eq hPublic.source hPublic.injective hPublic.hint_valid hPublic.bucket_bound
      hPublic.outside_span hPublic.bitmap_span hData.hints hHeader hPublic.fits hContext hData.outside_pointer
      hData.bitmap_pointer hData.outside_count hArray hData.bitmap hData.observation hPublic.steps_pos
      hPublic.coefficient_span hPublic.coefficients hJudgeAt hPc
  have hMembership : hintScanSuccess G coords beta Nj r outside v ↔ n ∈ S := by
    simp [hintScanSuccess, hintTupleAccept, hintFamilySuccesses, S, outside]
  have hAgree : sJ.regs 1 = 1 ↔ n ∈ S := hUniqueJ.trans hMembership
  have hFlagJ : sJ.regs 1 = hintTruth (n ∈ S) := by
    by_cases hn : n ∈ S
    · simpa [hintTruth, hn] using hAgree.mpr hn
    · have hz : sJ.regs 1 = 0 := hBitJ.resolve_right (fun hone => hn (hAgree.mp hone))
      simpa [hintTruth, hn] using hz
  have hCountJ : sJ.mem (parent + 3) = min 2 (hintSuccessPrefix S n.val) := by
    rw [hFrameJ _ (Or.inr (by omega)) (Or.inl (by omega))]
    exact hCounter
  have hPrep := hintScanCounterPrep_spec E sJ parent hEnd (hContextJ.trans hParent.symm)
  generalize hMid : runBlock hintScanCounterPrep E sJ = mid at hPrep
  obtain ⟨hPcMid, hMemMid, hPointerMid, hFlagMid, hContextMid⟩ := hPrep
  have hRunMid : (step P E)^[4] sJ = mid := by
    have hh := iterate_runBlock_of_at P E hintScanCounterPrep sJ (by rwa [hPcJ])
      (by simp [hintScanCounterPrep, hintScanParent, NoBranch, Instr.NoBranchI])
    rw [hMid] at hh
    exact hh
  have hReadMid : mid.mem (parent + 3) = min 2 (hintSuccessPrefix S n.val) := by rw [hMemMid]; exact hCountJ
  obtain ⟨_, kC, out, hRunC, hPcC, hCostC, hCountC, hFrameC, hFlagC, _, hContextC⟩ :=
    hintCapCounter_prefix_sem S n P E mid (base + 600) (parent + 3) hWord (by omega) hPointerMid hReadMid
      (hFlagMid.trans hFlagJ) hCounterAt (by rw [hPcMid, hPcJ])
  have hExact : ∀ addr, addr ≠ parent + 3 →
      (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
      (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → out.mem addr = state.mem addr := by
    intro addr hNe hRhs hGauss
    rw [hFrameC addr hNe, hMemMid, hFrameJ addr hRhs hGauss]
  have hFrame : HintScanFrame G parent outsideBase r state.mem out.mem := by
    intro addr _ hCount hRhs hGauss
    exact hExact addr hCount hRhs hGauss
  have hHeaderOut : ∃ index, HintGaussHeader G index out.mem := by
    obtain ⟨idx, hH⟩ := hHeaderJ
    refine ⟨idx, ?_⟩
    intro i hi
    rw [hFrameC _ (by omega), hMemMid]
    exact hH i hi
  have hArrayOut : ∀ j : Fin r, out.mem (outsideBase + 1 + j.val) = (outside j).val := by
    intro j
    rw [hExact _ (by have := j.isLt; omega) (Or.inl (by have := j.isLt; omega)) (Or.inl (by have := j.isLt; omega))]
    exact hArray j
  refine ⟨hPc, kC + (4 + kJ), out, hintIterate_then (step P E) (hintIterate_then (step P E) hRunJ hRunMid) hRunC,
    ?_, by omega, hCountC, hFlagC.trans (hFlagMid.trans hFlagJ), hData.frame hPublic hFrame,
    hHeaderOut, hContextC.trans (hContextMid.trans hParent), hArrayOut, hFrame⟩
  · simpa only [Nat.add_assoc] using hPcC

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintScanCountStepStmt_sem
end S_HintScanCountStep20261120
section S_HintScanLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintScanAdvanceStmt : Stmt := .seq (.code hintScanOdometerPrep)
  (.seq hintOdometerStmt (.code hintScanGoCode))
theorem hintScanAdvanceStmt_len : hintScanAdvanceStmt.len = 24 := rfl

theorem hintScanAdvanceStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (n : Fin (Nj ^ r))
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hArray : ∀ i < r, state.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj n.val i)
    (hAt : At P base (hintScanAdvanceStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 24) state (fun k out => k ≤ 10 * r + 16 ∧
      out.regs 1 = hintTruth (n.val + 1 < Nj ^ r) ∧
      (∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj (n.val + 1) i) ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      out.mem (parent + 3) = state.mem (parent + 3) ∧
      CRMemFrame (outsideBase + 1) (outsideBase + 1 + r) state.mem out.mem) := by
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
  have hNjWord : Nj < 2 ^ E.W := hPublic.bucket_bound.trans_lt (hPublic.fits.values 12 (by decide))
  let g := hintEnumeratedDigits Nj n.val
  have hBound : ∀ i, g i < Nj := hintEnumeratedDigits_bound Nj n.val hPublic.positive
  obtain ⟨hPrepAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintScanOdometerPrep at hPrepAt
  change At P (base + 9) ((Stmt.seq hintOdometerStmt (.code hintScanGoCode)).compile (base + 9)) at hRestAt
  obtain ⟨hOdoAt, hGoAt⟩ := At.seqStmt hRestAt
  change At P (base + 9) (hintOdometerStmt.compile (base + 9)) at hOdoAt
  change At P (base + 22) hintScanGoCode at hGoAt
  have hPrep := hintScanOdometerPrep_spec E state parent outsideBase r Nj hEnd (hContext.trans hParent.symm)
    (by omega) (by omega) hNjWord hData.outside_pointer hData.outside_count hData.radix
  generalize hMid : runBlock hintScanOdometerPrep E state = mid at hPrep
  obtain ⟨hPcMid, hMemoryMid, hArgsMid, hContextMid⟩ := hPrep
  have hRunMid : (step P E)^[9] state = mid := by
    have hh := iterate_runBlock_of_at P E hintScanOdometerPrep state (by rwa [hPc])
      (by simp [hintScanOdometerPrep, hintScanParent, hintScanOdometerInput, hintScanOdometerRadix, NoBranch, Instr.NoBranchI])
    rw [hMid] at hh
    exact hh
  have hArrayMid : ∀ i < r, mid.mem (outsideBase + 1 + i) = g i := by rw [hMemoryMid]; exact hArray
  obtain ⟨_, kO, sO, hRunO, hPcO, hCostO, _, _, hCarryO, hValuesO, hFrameO, hContextO⟩ :=
    hintOdometerStmt_sem (outsideBase + 1) r Nj g P E mid (base + 9) hPublic.geometry.word_bound hPublic.positive hNjWord
      hBound (by omega) hArgsMid.1 hArgsMid.2.1 hArgsMid.2.2.1 hArrayMid hOdoAt (by rw [hPcMid, hPc])
  have hCarryBound := hintOdometerCarry_le Nj g hPublic.positive hBound r
  have hGo := hintScanGo_spec E sO (hintOdometerCarry Nj g r) hPublic.geometry.word_bound hCarryBound hCarryO
  generalize hOut : runBlock hintScanGoCode E sO = out at hGo
  obtain ⟨hPcOut, hMemoryOut, hFlagOut, hContextOut⟩ := hGo
  have hRunOut : (step P E)^[2] sO = out := by
    have hh := iterate_runBlock_of_at P E hintScanGoCode sO (by rwa [hPcO])
      (by simp [hintScanGoCode, NoBranch, Instr.NoBranchI])
    rw [hOut] at hh
    exact hh
  have hLast : hintOdometerCarry Nj g r = 1 ↔ n.val + 1 = Nj ^ r := by
    rw [hintOdometer_carry_iff Nj g hPublic.positive hBound r, hintEnumeratedDigits_rank Nj r n.val hPublic.positive n.isLt]
  have hContinue : hintOdometerCarry Nj g r = 0 ↔ n.val + 1 < Nj ^ r := by have := n.isLt; omega
  have hFrame : CRMemFrame (outsideBase + 1) (outsideBase + 1 + r) state.mem out.mem := by
    intro addr hAway
    rw [hMemoryOut, hFrameO addr hAway, hMemoryMid]
  have hDataOut := HintScanReadOnly.frame hPublic hData (HintScanFrame.of_array hFrame)
  have hHeaderOut : ∃ index, HintGaussHeader G index out.mem := by
    obtain ⟨idx, hH⟩ := hHeader
    refine ⟨idx, ?_⟩
    intro i hi
    rw [hFrame _ (Or.inr (by omega))]
    exact hH i hi
  refine ⟨hPc, 2 + (kO + 9), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunMid hRunO) hRunOut,
    ?_, by omega, hFlagOut.trans (hintTruth_congr hContinue), ?_, hDataOut, hHeaderOut,
    hContextOut.trans (hContextO.trans (hContextMid.trans hParent)), hFrame _ (Or.inr (by omega)), hFrame⟩
  · rw [hPcOut, hPcO]
  · intro i hi
    rw [hMemoryOut, hValuesO i hi, hintEnumeratedDigits_succ]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintScanBody : Stmt := .seq hintScanCountStepStmt hintScanAdvanceStmt
theorem hintScanBody_len : hintScanBody.len = 633 := rfl

def hintScanBodyTime (G : HintGaussArea) (r : ℕ) : ℕ :=
  11 * r * r + 23 * r + 52 + (9 * G.rows + 23 + (20 * G.rows + 50) * r + 512 * (G.rows + G.hints + 1) ^ 3)

theorem hintScanBody_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (n : Fin (Nj ^ r))
    (hData : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem)
    (hHeader : ∃ index, HintGaussHeader G index state.mem) (hContext : state.regs 14 = G.context)
    (hArray : ∀ i < r, state.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj n.val i)
    (hCounter : state.mem (parent + 3) = min 2 (hintSuccessPrefix (hintFamilySuccesses G coords beta Nj r v hPublic.positive) n.val))
    (hAt : At P base (hintScanBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 633) state (fun k out => k ≤ hintScanBodyTime G r ∧
      out.mem (parent + 3) = min 2 (hintSuccessPrefix (hintFamilySuccesses G coords beta Nj r v hPublic.positive) (n.val + 1)) ∧
      out.regs 1 = hintTruth (n.val + 1 < Nj ^ r) ∧
      (∀ i < r, out.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj (n.val + 1) i) ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintScanFrame G parent outsideBase r state.mem out.mem) := by
  obtain ⟨hCountAt, hAdvanceAt⟩ := At.seqStmt hAt
  change At P base (hintScanCountStepStmt.compile base) at hCountAt
  change At P (base + 609) (hintScanAdvanceStmt.compile (base + 609)) at hAdvanceAt
  have hArrayCount : ∀ j : Fin r, state.mem (outsideBase + 1 + j.val) =
      (hintOdometerEnumeration Nj r hPublic.positive n j).val := by
    intro j
    rw [hintOdometerEnumeration_val]
    exact hArray j.val j.isLt
  obtain ⟨_, kC, sC, hRunC, hPcC, hCostC, hCountC, _, hDataC, hHeaderC, hContextC, hArrayC, hFrameC⟩ :=
    hintScanCountStepStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E state base
      hPublic n hData hHeader hContext hArrayCount hCounter hCountAt hPc
  have hArrayAdvance : ∀ i < r, sC.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj n.val i := by
    intro i hi
    simpa only [hintOdometerEnumeration_val] using hArrayC ⟨i, hi⟩
  obtain ⟨_, kA, out, hRunA, hPcA, hCostA, hFlagA, hArrayA, hDataA, hHeaderA, hContextA, hCountA, hFrameA⟩ :=
    hintScanAdvanceStmt_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E sC (base + 609)
      hPublic n hDataC hHeaderC hContextC hArrayAdvance hAdvanceAt hPcC
  refine ⟨hPc, kA + kC, out, hintIterate_then (step P E) hRunC hRunA, ?_, ?_, hCountA.trans hCountC,
    hFlagA, hArrayA, hDataA, hHeaderA, hContextA, hFrameC.trans (HintScanFrame.of_array hFrameA)⟩
  · simpa only [Nat.add_assoc] using hPcA
  · dsimp only [hintScanBodyTime]
    omega

structure HintScanInv (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj r parent outsideBase bitmapBase : ℕ)
    (v : HintVec G.rows) (hPos : 0 < Nj) (rank : ℕ) (original : ℕ → ℕ) (state : RAMState) : Prop where
  readonly : HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v state.mem
  header : ∃ index, HintGaussHeader G index state.mem
  context_value : state.regs 14 = G.context
  array : ∀ i < r, state.mem (outsideBase + 1 + i) = hintEnumeratedDigits Nj rank i
  counter : state.mem (parent + 3) = min 2 (hintSuccessPrefix (hintFamilySuccesses G coords beta Nj r v hPos) rank)
  flag : state.regs 1 = hintTruth (rank < Nj ^ r)
  frame : HintScanFrame G parent outsideBase r original state.mem

theorem HintScanInv.pc {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {Nj r parent outsideBase bitmapBase : ℕ}
    {v : HintVec G.rows} {hPos : 0 < Nj} {rank : ℕ} {original : ℕ → ℕ} {state : RAMState}
    (h : HintScanInv G coords beta Nj r parent outsideBase bitmapBase v hPos rank original state) (pc : ℕ) :
    HintScanInv G coords beta Nj r parent outsideBase bitmapBase v hPos rank original {state with pc := pc} :=
  ⟨h.readonly, h.header, h.context_value, h.array, h.counter, h.flag, h.frame⟩

def hintScanLoop : Stmt := .loop (.neqz 1) hintScanBody
theorem hintScanLoop_len : hintScanLoop.len = 635 := rfl

/-- A complete native first pass over all outside arrays: its physical capped
    count equals the capped number of successful filtered positions. -/
theorem hintScanLoop_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (Nj r parent outsideBase bitmapBase : ℕ) (v : HintVec G.rows) (original : ℕ → ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj r parent outsideBase bitmapBase)
    (hInv : HintScanInv G coords beta Nj r parent outsideBase bitmapBase v hPublic.positive 0 original state)
    (hAt : At P base (hintScanLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 635) state (fun k out => k ≤ (hintScanBodyTime G r + 2) * Nj ^ r + 1 ∧
      out.mem (parent + 3) = min 2 (hintFamilySuccesses G coords beta Nj r v hPublic.positive).card ∧
      (out.mem (parent + 3) = 1 ↔
        (HintParams.family Nj beta (Finset.univ.image (fun j => (coords j).val)) r (List.ofFn v)).card = 1) ∧
      HintScanReadOnly G coords Nj r parent outsideBase bitmapBase v out.mem ∧
      (∃ index, HintGaussHeader G index out.mem) ∧ out.regs 14 = G.context ∧
      HintScanFrame G parent outsideBase r original out.mem) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ rank, rank + left = Nj ^ r ∧
    HintScanInv G coords beta Nj r parent outsideBase bitmapBase v hPublic.positive rank original st
  have hBodyAt : At P (base + 1) (hintScanBody.compile (base + 1)) := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨rank, hRank, hScan⟩ := hI
    exact ⟨rank, hRank, hScan.pc pc⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.neqz 1).code E st) := by
    intro left st hI
    exact hI
  have hGo : ∀ left st, I (left + 1) st → (Cond.neqz 1).eval st := by
    intro left st hI
    obtain ⟨rank, hRank, hScan⟩ := hI
    have hActive : rank < Nj ^ r := by omega
    change st.regs 1 ≠ 0
    rw [hScan.flag]
    simp [hintTruth, hActive]
  have hStop : ∀ st, I 0 st → ¬ (Cond.neqz 1).eval st := by
    intro st hI
    obtain ⟨rank, hRank, hScan⟩ := hI
    have hEnd : rank = Nj ^ r := by omega
    change ¬ st.regs 1 ≠ 0
    rw [hScan.flag, hEnd]
    simp [hintTruth]
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.neqz 1).code.length + 1 →
      Sem P E (base + (Cond.neqz 1).code.length + 1)
        (base + (Cond.neqz 1).code.length + 1 + hintScanBody.len) st
        (fun k out => k ≤ hintScanBodyTime G r ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨rank, hRank, hScan⟩ := hI
    have hn : rank < Nj ^ r := by omega
    let n : Fin (Nj ^ r) := ⟨rank, hn⟩
    have hNative := hintScanBody_sem G coords beta hPrefix Nj r parent outsideBase bitmapBase v P E st (base + 1)
      hPublic n hScan.readonly hScan.header hScan.context_value hScan.array hScan.counter hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hCounter, hFlag, hArray, hData, hHeader, hContext, hFrame⟩ := hOut
    exact ⟨hCost, rank + 1, by omega, ⟨hData, hHeader, hContext, hArray, hCounter, hFlag, hScan.frame.trans hFrame⟩⟩
  have hInitial : I (Nj ^ r) state := ⟨0, by omega, hInv⟩
  have hNative := hintLoopFuel_sem P E base (.neqz 1) hintScanBody hAt hPublic.geometry.word_bound I (hintScanBodyTime G r)
    hIpc hItest hGo hStop hBody (Nj ^ r) state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, rank, hRank, hFinal⟩ := hOut
  have hEnd : rank = Nj ^ r := by omega
  rw [hEnd] at hFinal
  have hCount : out.mem (parent + 3) = min 2 (hintFamilySuccesses G coords beta Nj r v hPublic.positive).card := by
    rw [hFinal.counter, hintSuccessPrefix_full]
  simp only [Cond.code, List.length_nil, Nat.zero_add] at hCost
  refine ⟨hCost, hCount, ?_, hFinal.readonly, hFinal.header, hFinal.context_value, hFinal.frame⟩
  rw [hCount, hintCap2_one]
  exact hintFamilySuccesses_card_one G coords hPublic.injective beta hPrefix Nj r v hPublic.positive hPublic.hint_valid

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintScanLoop_sem
end S_HintScanLoop20261120
section S_HintScanFirstPass20261120
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
end S_HintScanFirstPass20261120
section S_HintBitmapLoop20261120
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
end S_HintBitmapLoop20261120
section S_HintRowBitmap20261120
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
end S_HintRowBitmap20261120


