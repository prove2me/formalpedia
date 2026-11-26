-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_07
-- name    : LinearSetReconciliation327_Main_B65_07
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T05:20:44.173221+00:00
-- url     : https://prove2.me/theorems/e4cba058-0582-5754-b9bb-93626b3cc638
-- title:
--   Theorem 6.5 supporting machine proof B65_07
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_07Part1
set_option autoImplicit false

section S_HintDispatchBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDispatchBody (actions : List Stmt) : Stmt :=
  .seq (.code hintDispatchFetch) (.seq (hintActionSwitch actions) (.code hintDispatchAdvance))

theorem hintDispatchBody_len (actions : List Stmt) :
    (hintDispatchBody actions).len = 10 + ((hintActionSwitch actions).len + 9) := rfl

/-- The work claim for a table of actions. The descriptor is supplied in
register 6. Actions return to the control area and retain the schedule cursor. -/
def HintDispatchActions (P : Program) (E : RAMEnv) (control table : ℕ)
    (actions : List Stmt) (events : List (ℕ × ℕ)) (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) : Prop :=
  ∀ (j : Fin events.length) (action : Stmt) (base : ℕ) (s : RAMState),
    actions[events[j.val].1]? = some action → At P base (action.compile base) → s.pc = base →
    s.regs 6 = events[j.val].2 → s.regs 1 = 0 → HintDispatchData control table events.length j.val s →
    I j.val s.mem →
    Sem P E base (base + action.len) s (fun k out => k ≤ budget j.val ∧
      I (j.val + 1) out.mem ∧ HintDispatchData control table events.length j.val out)

theorem HintDispatchData.pc {control table count index : ℕ} {s : RAMState}
    (h : HintDispatchData control table count index s) (pc : ℕ) :
    HintDispatchData control table count index {s with pc := pc} :=
  ⟨h.context, h.table_pointer, h.size, h.cursor⟩

theorem HintDispatchData.switch {control table count index : ℕ} {s t : RAMState}
    (h : HintDispatchData control table count index s) (hSame : HintDispatchSame s t) :
    HintDispatchData control table count index t :=
  ⟨(hSame.regs 14 (by decide)).trans h.context,
    (congrFun hSame.memory control).trans h.table_pointer,
    (congrFun hSame.memory (control + 1)).trans h.size,
    (congrFun hSame.memory (control + 2)).trans h.cursor⟩

theorem hintDispatchBody_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (j : Fin events.length)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTag : events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length j.val state) (hInv : I j.val state.mem)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintDispatchActions P E control table actions events budget I)
    (hAt : At P base ((hintDispatchBody actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchBody actions).len) state (fun k out =>
      k ≤ budget j.val + 3 * actions.length + 21 ∧ I (j.val + 1) out.mem ∧
      HintDispatchData control table events.length (j.val + 1) out ∧ out.regs 13 = hintTruth (j.val + 1 < events.length)) := by
  let switch := hintActionSwitch actions
  obtain ⟨hFetchAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintDispatchFetch at hFetchAt
  change At P (base + 10) ((Stmt.seq switch (.code hintDispatchAdvance)).compile (base + 10)) at hRestAt
  obtain ⟨hSwitchAt, hAdvanceAt⟩ := At.seqStmt hRestAt
  change At P (base + 10) (switch.compile (base + 10)) at hSwitchAt
  change At P (base + 10 + switch.len) hintDispatchAdvance at hAdvanceAt
  have hFetch := hintDispatchFetch_spec E state control table events j hWord hControl hData hTable
  generalize hF : runBlock hintDispatchFetch E state = sF at hFetch
  obtain ⟨hPcF, hTagF, hDescF, hOneF, hMemF, hDataF⟩ := hFetch
  have hRunF : (step P E)^[10] state = sF := by
    have hh := iterate_runBlock_of_at P E hintDispatchFetch state (by rwa [hPc])
      (by simp [hintDispatchFetch, NoBranch, Instr.NoBranchI])
    rw [hF] at hh
    exact hh
  let action := actions[events[j.val].1]
  have hSelect : actions[events[j.val].1]? = some action := List.getElem?_eq_getElem hTag
  have hSwitch := hintActionSwitch_sem actions action events[j.val].1 P E sF (base + 10) (budget j.val)
    (fun out => I (j.val + 1) out.mem ∧ HintDispatchData control table events.length j.val out)
    (by omega) hTagF (hTable.fits j).1 hOneF hSelect hSwitchAt (by omega)
    (by
      intro entry s hSame hZero hPcS hAtS
      exact hActions j action entry s hSelect hAtS hPcS ((hSame.regs 6 (by decide)).trans hDescF)
        hZero (hDataF.switch hSame) (by rw [hSame.memory, hMemF]; exact hInv))
    (by intro out pc hPost; exact ⟨hPost.1, hPost.2.pc pc⟩)
  obtain ⟨_, kS, mid, hRunS, hPcS, hCostS, hInvS, hDataS⟩ := hSwitch
  have hAdvance := hintDispatchAdvance_spec E mid control table events.length j.val hWord hControl hCount j.isLt hDataS
  generalize hA : runBlock hintDispatchAdvance E mid = out at hAdvance
  obtain ⟨hPcA, hMemA, hGoA, hDataA⟩ := hAdvance
  have hRunA : (step P E)^[9] mid = out := by
    have hh := iterate_runBlock_of_at P E hintDispatchAdvance mid (by rwa [hPcS])
      (by simp [hintDispatchAdvance, NoBranch, Instr.NoBranchI])
    rw [hA] at hh
    exact hh
  refine ⟨hPc, 9 + (kS + 10), out, hintIterate_then (step P E) (hintIterate_then (step P E) hRunF hRunS) hRunA,
    ?_, by omega, ?_, hDataA, hGoA⟩
  · rw [hPcA, hPcS, hintDispatchBody_len]
    change base + 10 + switch.len + 9 = base + (10 + (switch.len + 9))
    omega
  · rw [hMemA]
    exact hCursor _ _ _ hInvS

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDispatchBody_sem
end S_HintDispatchBody20261120
section S_HintDispatch20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDispatchLoop (actions : List Stmt) : Stmt := .loop (.neqz 13) (hintDispatchBody actions)
def hintDispatchStmt (actions : List Stmt) : Stmt := .seq (.code hintDispatchInit) (hintDispatchLoop actions)

def hintDispatchBudget (actions : List Stmt) (count : ℕ) (budget : ℕ → ℕ) : ℕ :=
  ∑ left ∈ Finset.range count, (budget (count - (left + 1)) + 3 * actions.length + 23)

theorem hintDispatchLoop_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTags : ∀ j : Fin events.length, events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length 0 state) (hInv : I 0 state.mem)
    (hGoInitial : state.regs 13 = hintTruth (0 < events.length))
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintDispatchActions P E control table actions events budget I)
    (hAt : At P base ((hintDispatchLoop actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchLoop actions).len) state (fun k out =>
      k ≤ hintDispatchBudget actions events.length budget + 1 ∧ I events.length out.mem ∧
      HintDispatchData control table events.length events.length out) := by
  let count := events.length
  let J : ℕ → RAMState → Prop := fun left st =>
    ∃ j, j + left = count ∧ HintDispatchData control table count j st ∧ I j st.mem ∧
      st.regs 13 = hintTruth (j < count)
  let B : ℕ → ℕ := fun left => budget (count - (left + 1)) + 3 * actions.length + 21
  have hBodyAt : At P (base + 1) ((hintDispatchBody actions).compile (base + 1)) := (at_loop hAt).2.2.1
  have hJpc : ∀ left st pc, J left st → J left {st with pc := pc} := by
    intro left st pc h
    obtain ⟨j, hLeft, hDataJ, hInvJ, hGo⟩ := h
    exact ⟨j, hLeft, hDataJ.pc pc, hInvJ, hGo⟩
  have hTest : ∀ left st, J left st → J left (runBlock (Cond.neqz 13).code E st) := fun _ _ h => h
  have hGo : ∀ left st, J (left + 1) st → (Cond.neqz 13).eval st := by
    intro left st h
    obtain ⟨j, hLeft, _, _, hFlag⟩ := h
    have hj : j < count := by omega
    change st.regs 13 ≠ 0
    rw [hFlag]
    simp [hintTruth, hj]
  have hStop : ∀ st, J 0 st → ¬ (Cond.neqz 13).eval st := by
    intro st h
    obtain ⟨j, hLeft, _, _, hFlag⟩ := h
    have hj : ¬ j < count := by omega
    change ¬ st.regs 13 ≠ 0
    rw [hFlag]
    simp [hintTruth, hj]
  have hBody : ∀ left st, J (left + 1) st → st.pc = base + (Cond.neqz 13).code.length + 1 →
      Sem P E (base + (Cond.neqz 13).code.length + 1)
        (base + (Cond.neqz 13).code.length + 1 + (hintDispatchBody actions).len) st
        (fun k out => k ≤ B left ∧ J left out) := by
    intro left st h hStart
    obtain ⟨j, hLeft, hDataJ, hInvJ, _⟩ := h
    have hJlt : j < events.length := by
      change j < count
      omega
    let pos : Fin events.length := ⟨j, hJlt⟩
    have hNative := hintDispatchBody_sem P E st control table (base + 1) actions events budget I pos
      hWord hControl hCount hTable (hTags pos) hDataJ hInvJ hCursor hActions hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hInvOut, hDataOut, hFlag⟩ := hOut
    have hPos : count - (left + 1) = j := by omega
    refine ⟨?_, j + 1, by omega, hDataOut, hInvOut, hFlag⟩
    dsimp only [B]
    rw [hPos]
    exact hCost
  have hInitial : J count state := ⟨0, Nat.zero_add _, hData, hInv, hGoInitial⟩
  have hNative := hintLoopBudget_sem P E base (.neqz 13) (hintDispatchBody actions) hAt (by omega)
    J B hJpc hTest hGo hStop hBody count state hInitial hPc
  have hEnd : base + (hintDispatchLoop actions).len = base + (Cond.neqz 13).code.length +
      (hintDispatchBody actions).len + 2 := by simp [hintDispatchLoop, Stmt.len, Nat.add_assoc]
  rw [hEnd]
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hLeft, hDataOut, hInvOut, _⟩ := hOut
  have hEq : j = events.length := by simpa [count] using hLeft
  subst j
  refine ⟨?_, hInvOut, hDataOut⟩
  simp only [Cond.code, List.length_nil, Nat.zero_add, B] at hCost
  unfold hintDispatchBudget
  simpa only [count, Nat.add_assoc] using hCost

theorem hintDispatchStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base old : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTags : ∀ j : Fin events.length, events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length old state) (hInv : I 0 state.mem)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintDispatchActions P E control table actions events budget I)
    (hAt : At P base ((hintDispatchStmt actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchStmt actions).len) state (fun k out =>
      k ≤ hintDispatchBudget actions events.length budget + 9 ∧ I events.length out.mem ∧
      HintDispatchData control table events.length events.length out) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintDispatchInit at hInitAt
  change At P (base + 8) ((hintDispatchLoop actions).compile (base + 8)) at hLoopAt
  have hInit := hintDispatchInit_spec E state control table events.length old hWord hControl hCount hData
  generalize hI : runBlock hintDispatchInit E state = mid at hInit
  obtain ⟨hPcI, hMemI, hGoI, hDataI⟩ := hInit
  have hRunI : (step P E)^[8] state = mid := by
    have hh := iterate_runBlock_of_at P E hintDispatchInit state (by rwa [hPc])
      (by simp [hintDispatchInit, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  have hInvI : I 0 mid.mem := by rw [hMemI]; exact hCursor _ _ _ hInv
  obtain ⟨_, k, out, hRun, hEnd, hCost, hInvOut, hDataOut⟩ :=
    hintDispatchLoop_sem P E mid control table (base + 8) actions events budget I hWord hControl hCount
      hTable hTags hDataI hInvI hGoI hCursor hActions hLoopAt (by omega)
  refine ⟨hPc, k + 8, out, hintIterate_then (step P E) hRunI hRun, ?_, by omega, hInvOut, hDataOut⟩
  change out.pc = base + (8 + (hintDispatchLoop actions).len)
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDispatchStmt_sem
end S_HintDispatch20261120
section S_HintLocatedSwitch20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- The absolute entry address of a selected action in a compiled switch. -/
def hintActionEntry : List Stmt → ℕ → ℕ → ℕ
  | [], base, _ => base
  | _ :: rest, base, 0 => base + (hintActionSwitch rest).len + 3
  | _ :: rest, base, n + 1 => hintActionEntry rest (base + 2) n

/-- A fixed switch on the event tag in register 1. Each selected action sees
register 1 equal to zero and the original memory and all other registers. -/
theorem hintLocatedSwitch_sem (actions : List Stmt) (action : Stmt) (tag : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base budget : ℕ) (Q : RAMState → Prop)
    (hWord : 1 < 2 ^ E.W) (hTag : state.regs 1 = tag) (hTagFit : tag < 2 ^ E.W)
    (hOne : state.regs 15 = 1) (hSelect : actions[tag]? = some action)
    (hAt : At P base ((hintActionSwitch actions).compile base)) (hPc : state.pc = base)
    (hAction : ∀ entry (s : RAMState), entry = hintActionEntry actions base tag → HintDispatchSame state s → s.regs 1 = 0 → s.pc = entry →
      At P entry (action.compile entry) →
      Sem P E entry (entry + action.len) s (fun k out => k ≤ budget ∧ Q out))
    (hQpc : ∀ out pc, Q out → Q {out with pc := pc}) :
    Sem P E base (base + (hintActionSwitch actions).len) state (fun k out => k ≤ budget + 3 * tag + 2 ∧ Q out) := by
  induction actions generalizing tag base state with
  | nil => simp at hSelect
  | cons first rest ih =>
    let tail := Stmt.seq (.code hintDispatchDec) (hintActionSwitch rest)
    change At P base ((Stmt.ite (.neqz 1) tail first).compile base) at hAt
    change Sem P E base (base + (Stmt.ite (.neqz 1) tail first).len) state _
    have hEnd : base + (Stmt.ite (.neqz 1) tail first).len =
        base + (Cond.neqz 1).code.length + tail.len + first.len + 3 := by
      simp only [Stmt.len]
      omega
    rw [hEnd]
    apply Sem.ite P E base (.neqz 1) tail first state _ hAt hWord hPc
    · intro hGo
      have hPositive : tag ≠ 0 := by intro hZero; apply hGo; omega
      obtain ⟨t, ht⟩ : ∃ t, tag = t + 1 := ⟨tag - 1, by omega⟩
      have hSelectT : rest[t]? = some action := by
        simpa only [ht, List.getElem?_cons_succ] using hSelect
      let entered : RAMState := {state with pc := base + 1}
      have hTailAt : At P (base + 1) (tail.compile (base + 1)) := (at_ite hAt).2.2.1
      change Sem P E (base + 1) (base + 1 + tail.len) entered _
      obtain ⟨hDecAt, hRestAt⟩ := At.seqStmt hTailAt
      change At P (base + 1) hintDispatchDec at hDecAt
      change At P (base + 1 + 1) ((hintActionSwitch rest).compile (base + 1 + 1)) at hRestAt
      have hDec := hintDispatchDec_spec E entered t (by exact hTag.trans ht) (by omega) hOne
      generalize hD : runBlock hintDispatchDec E entered = mid at hDec
      obtain ⟨hPcD, hTagD, hSameD⟩ := hDec
      have hSame : HintDispatchSame state mid := ⟨hSameD.memory, hSameD.regs⟩
      have hRunD : (step P E)^[1] entered = mid := by
        have h := iterate_runBlock_of_at P E hintDispatchDec entered hDecAt
          (by simp [hintDispatchDec, NoBranch, Instr.NoBranchI])
        rw [hD] at h
        exact h
      have hSuffix := ih t mid (base + 1 + 1) hTagD (by omega)
        ((hSame.regs 15 (by decide)).trans hOne) hSelectT hRestAt hPcD
        (fun entry st he hSame' => hAction entry st (by simpa only [ht, hintActionEntry] using he) (hSame.trans hSame'))
      obtain ⟨_, k, out, hRun, hPcOut, hCost, hPost⟩ := hSuffix
      refine ⟨rfl, k + 1, out, hintIterate_then (step P E) hRunD hRun, ?_, ?_, hQpc _ _ hPost⟩
      · change out.pc = base + 1 + (1 + (hintActionSwitch rest).len)
        omega
      · change 1 + (k + 1) + 1 ≤ budget + 3 * tag + 2
        omega
    · intro hStop
      have hZero : tag = 0 := by
        by_contra hNe
        exact hStop (by change state.regs 1 ≠ 0; rwa [hTag])
      have hFirst : first = action := by simpa [hZero] using hSelect
      subst first
      let start := base + tail.len + 2
      let entered : RAMState := {state with pc := start}
      have hRight : At P start (action.compile start) := by
        have h := (at_ite hAt).2.2.2.2.1
        simpa only [Cond.code, List.length_nil, Nat.add_zero, Nat.add_assoc,
          show 1 + (tail.len + 1) = tail.len + 2 by omega, start] using h
      simp only [Cond.code, List.length_nil, Nat.add_zero, Nat.zero_add]
      rw [show base + 1 + tail.len + 1 + action.len = start + action.len by dsimp [start]; omega]
      change Sem P E start (start + action.len) entered _
      have hEntry : start = hintActionEntry (action :: rest) base tag := by
        rw [hZero]
        change base + (1 + (hintActionSwitch rest).len) + 2 = base + (hintActionSwitch rest).len + 3
        omega
      have hNative := hAction _ entered hEntry ⟨rfl, fun _ _ => rfl⟩ (hTag.trans hZero) rfl hRight
      apply Sem.mono hNative
      intro k out hOut
      exact ⟨by omega, hQpc _ _ hOut.2⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintLocatedSwitch_sem
end S_HintLocatedSwitch20261120
section S_HintLocatedBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- The work claim for a table of actions. The descriptor is supplied in
register 6. Actions return to the control area and retain the schedule cursor. -/
def HintLocatedActions (P : Program) (E : RAMEnv) (control table switchBase : ℕ)
    (actions : List Stmt) (events : List (ℕ × ℕ)) (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) : Prop :=
  ∀ (j : Fin events.length) (action : Stmt) (base : ℕ) (s : RAMState),
    actions[events[j.val].1]? = some action →
    base = hintActionEntry actions switchBase events[j.val].1 → At P base (action.compile base) → s.pc = base →
    s.regs 6 = events[j.val].2 → s.regs 1 = 0 → HintDispatchData control table events.length j.val s →
    UpWordState E s → I j.val s.mem →
    Sem P E base (base + action.len) s (fun k out => k ≤ budget j.val ∧
      I (j.val + 1) out.mem ∧ HintDispatchData control table events.length j.val out)

theorem hintLocatedBody_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (j : Fin events.length)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTag : events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length j.val state) (hInv : I j.val state.mem)
    (hWordState : UpWordState E state)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintLocatedActions P E control table (base + 10) actions events budget I)
    (hAt : At P base ((hintDispatchBody actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchBody actions).len) state (fun k out =>
      k ≤ budget j.val + 3 * actions.length + 21 ∧ I (j.val + 1) out.mem ∧
      HintDispatchData control table events.length (j.val + 1) out ∧ out.regs 13 = hintTruth (j.val + 1 < events.length) ∧ UpWordState E out) := by
  let switch := hintActionSwitch actions
  obtain ⟨hFetchAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintDispatchFetch at hFetchAt
  change At P (base + 10) ((Stmt.seq switch (.code hintDispatchAdvance)).compile (base + 10)) at hRestAt
  obtain ⟨hSwitchAt, hAdvanceAt⟩ := At.seqStmt hRestAt
  change At P (base + 10) (switch.compile (base + 10)) at hSwitchAt
  change At P (base + 10 + switch.len) hintDispatchAdvance at hAdvanceAt
  have hFetch := hintDispatchFetch_spec E state control table events j hWord hControl hData hTable
  generalize hF : runBlock hintDispatchFetch E state = sF at hFetch
  obtain ⟨hPcF, hTagF, hDescF, hOneF, hMemF, hDataF⟩ := hFetch
  have hRunF : (step P E)^[10] state = sF := by
    have hh := iterate_runBlock_of_at P E hintDispatchFetch state (by rwa [hPc])
      (by simp [hintDispatchFetch, NoBranch, Instr.NoBranchI])
    rw [hF] at hh
    exact hh
  have hWordF : UpWordState E sF := hRunF ▸ upIterate_word_bound P E state 10 hWordState
  let action := actions[events[j.val].1]
  have hSelect : actions[events[j.val].1]? = some action := List.getElem?_eq_getElem hTag
  have hSwitch := hintLocatedSwitch_sem actions action events[j.val].1 P E sF (base + 10) (budget j.val)
    (fun out => I (j.val + 1) out.mem ∧ HintDispatchData control table events.length j.val out)
    (by omega) hTagF (hTable.fits j).1 hOneF hSelect hSwitchAt (by omega)
    (by
      intro entry s hEntry hSame hZero hPcS hAtS
      have hWordS : UpWordState E s := by
        refine ⟨?_, by rw [hSame.memory]; exact hWordF.2⟩
        intro r
        by_cases hr : r = 1
        · subst r
          rw [hZero]
          exact Nat.two_pow_pos E.W
        · rw [hSame.regs r hr]
          exact hWordF.1 r
      exact hActions j action entry s hSelect hEntry hAtS hPcS ((hSame.regs 6 (by decide)).trans hDescF)
        hZero (hDataF.switch hSame) hWordS (by rw [hSame.memory, hMemF]; exact hInv))
    (by intro out pc hPost; exact ⟨hPost.1, hPost.2.pc pc⟩)
  obtain ⟨_, kS, mid, hRunS, hPcS, hCostS, hInvS, hDataS⟩ := hSwitch
  have hAdvance := hintDispatchAdvance_spec E mid control table events.length j.val hWord hControl hCount j.isLt hDataS
  generalize hA : runBlock hintDispatchAdvance E mid = out at hAdvance
  obtain ⟨hPcA, hMemA, hGoA, hDataA⟩ := hAdvance
  have hRunA : (step P E)^[9] mid = out := by
    have hh := iterate_runBlock_of_at P E hintDispatchAdvance mid (by rwa [hPcS])
      (by simp [hintDispatchAdvance, NoBranch, Instr.NoBranchI])
    rw [hA] at hh
    exact hh
  have hRun : (step P E)^[9 + (kS + 10)] state = out :=
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunF hRunS) hRunA
  refine ⟨hPc, 9 + (kS + 10), out, hRun,
    ?_, by omega, ?_, hDataA, hGoA, hRun ▸ upIterate_word_bound P E state _ hWordState⟩
  · rw [hPcA, hPcS, hintDispatchBody_len]
    change base + 10 + switch.len + 9 = base + (10 + (switch.len + 9))
    omega
  · rw [hMemA]
    exact hCursor _ _ _ hInvS

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintLocatedBody_sem
end S_HintLocatedBody20261120
section S_HintLocatedDispatch20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintLocatedLoop_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTags : ∀ j : Fin events.length, events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length 0 state) (hInv : I 0 state.mem)
    (hGoInitial : state.regs 13 = hintTruth (0 < events.length))
    (hWordState : UpWordState E state)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintLocatedActions P E control table (base + 11) actions events budget I)
    (hAt : At P base ((hintDispatchLoop actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchLoop actions).len) state (fun k out =>
      k ≤ hintDispatchBudget actions events.length budget + 1 ∧ I events.length out.mem ∧
      HintDispatchData control table events.length events.length out) := by
  let count := events.length
  let J : ℕ → RAMState → Prop := fun left st =>
    ∃ j, j + left = count ∧ HintDispatchData control table count j st ∧ I j st.mem ∧
      st.regs 13 = hintTruth (j < count) ∧ UpWordState E st
  let B : ℕ → ℕ := fun left => budget (count - (left + 1)) + 3 * actions.length + 21
  have hBodyAt : At P (base + 1) ((hintDispatchBody actions).compile (base + 1)) := (at_loop hAt).2.2.1
  have hJpc : ∀ left st pc, J left st → J left {st with pc := pc} := by
    intro left st pc h
    obtain ⟨j, hLeft, hDataJ, hInvJ, hGo, hWordJ⟩ := h
    exact ⟨j, hLeft, hDataJ.pc pc, hInvJ, hGo, hWordJ⟩
  have hTest : ∀ left st, J left st → J left (runBlock (Cond.neqz 13).code E st) := fun _ _ h => h
  have hGo : ∀ left st, J (left + 1) st → (Cond.neqz 13).eval st := by
    intro left st h
    obtain ⟨j, hLeft, _, _, hFlag, _⟩ := h
    have hj : j < count := by omega
    change st.regs 13 ≠ 0
    rw [hFlag]
    simp [hintTruth, hj]
  have hStop : ∀ st, J 0 st → ¬ (Cond.neqz 13).eval st := by
    intro st h
    obtain ⟨j, hLeft, _, _, hFlag, _⟩ := h
    have hj : ¬ j < count := by omega
    change ¬ st.regs 13 ≠ 0
    rw [hFlag]
    simp [hintTruth, hj]
  have hBody : ∀ left st, J (left + 1) st → st.pc = base + (Cond.neqz 13).code.length + 1 →
      Sem P E (base + (Cond.neqz 13).code.length + 1)
        (base + (Cond.neqz 13).code.length + 1 + (hintDispatchBody actions).len) st
        (fun k out => k ≤ B left ∧ J left out) := by
    intro left st h hStart
    obtain ⟨j, hLeft, hDataJ, hInvJ, _, hWordJ⟩ := h
    have hJlt : j < events.length := by
      change j < count
      omega
    let pos : Fin events.length := ⟨j, hJlt⟩
    have hNative := hintLocatedBody_sem P E st control table (base + 1) actions events budget I pos
      hWord hControl hCount hTable (hTags pos) hDataJ hInvJ hWordJ hCursor hActions hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hInvOut, hDataOut, hFlag, hWordOut⟩ := hOut
    have hPos : count - (left + 1) = j := by omega
    refine ⟨?_, j + 1, by omega, hDataOut, hInvOut, hFlag, hWordOut⟩
    dsimp only [B]
    rw [hPos]
    exact hCost
  have hInitial : J count state := ⟨0, Nat.zero_add _, hData, hInv, hGoInitial, hWordState⟩
  have hNative := hintLoopBudget_sem P E base (.neqz 13) (hintDispatchBody actions) hAt (by omega)
    J B hJpc hTest hGo hStop hBody count state hInitial hPc
  have hEnd : base + (hintDispatchLoop actions).len = base + (Cond.neqz 13).code.length +
      (hintDispatchBody actions).len + 2 := by simp [hintDispatchLoop, Stmt.len, Nat.add_assoc]
  rw [hEnd]
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hLeft, hDataOut, hInvOut, _, _⟩ := hOut
  have hEq : j = events.length := by simpa [count] using hLeft
  subst j
  refine ⟨?_, hInvOut, hDataOut⟩
  simp only [Cond.code, List.length_nil, Nat.zero_add, B] at hCost
  unfold hintDispatchBudget
  simpa only [count, Nat.add_assoc] using hCost

theorem hintLocatedDispatch_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (control table base old : ℕ) (actions : List Stmt) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : events.length < 2 ^ E.W)
    (hTable : HintDispatchTable E table events) (hTags : ∀ j : Fin events.length, events[j.val].1 < actions.length)
    (hData : HintDispatchData control table events.length old state) (hInv : I 0 state.mem)
    (hWordState : UpWordState E state)
    (hCursor : ∀ n memory cursor, I n memory → I n (Function.update memory (control + 2) cursor))
    (hActions : HintLocatedActions P E control table (base + 19) actions events budget I)
    (hAt : At P base ((hintDispatchStmt actions).compile base)) (hPc : state.pc = base) :
    Sem P E base (base + (hintDispatchStmt actions).len) state (fun k out =>
      k ≤ hintDispatchBudget actions events.length budget + 9 ∧ I events.length out.mem ∧
      HintDispatchData control table events.length events.length out) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintDispatchInit at hInitAt
  change At P (base + 8) ((hintDispatchLoop actions).compile (base + 8)) at hLoopAt
  have hInit := hintDispatchInit_spec E state control table events.length old hWord hControl hCount hData
  generalize hI : runBlock hintDispatchInit E state = mid at hInit
  obtain ⟨hPcI, hMemI, hGoI, hDataI⟩ := hInit
  have hRunI : (step P E)^[8] state = mid := by
    have hh := iterate_runBlock_of_at P E hintDispatchInit state (by rwa [hPc])
      (by simp [hintDispatchInit, NoBranch, Instr.NoBranchI])
    rw [hI] at hh
    exact hh
  have hWordI : UpWordState E mid := hRunI ▸ upIterate_word_bound P E state 8 hWordState
  have hInvI : I 0 mid.mem := by rw [hMemI]; exact hCursor _ _ _ hInv
  obtain ⟨_, k, out, hRun, hEnd, hCost, hInvOut, hDataOut⟩ :=
    hintLocatedLoop_sem P E mid control table (base + 8) actions events budget I hWord hControl hCount
      hTable hTags hDataI hInvI hGoI hWordI hCursor hActions hLoopAt (by omega)
  refine ⟨hPc, k + 8, out, hintIterate_then (step P E) hRunI hRun, ?_, by omega, hInvOut, hDataOut⟩
  change out.pc = base + (8 + (hintDispatchLoop actions).len)
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintLocatedDispatch_sem
end S_HintLocatedDispatch20261120
section S_HintPlaceCR20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintCRAction (S : CRSourceBundle) (entry : ℕ) (finish : Stmt) : Stmt :=
  .seq (.code (crSourceInputCode S entry)) finish

def hintActionsWithCR (S : CRSourceBundle) (switchBase : ℕ)
    (actions : List Stmt) (finish : Stmt) : List Stmt :=
  actions ++ [hintCRAction S (switchBase + 2 * actions.length + 3) finish]

theorem hintLastActionEntry (actions : List Stmt) (last : Stmt) (switchBase : ℕ) :
    hintActionEntry (actions ++ [last]) switchBase actions.length = switchBase + 2 * actions.length + 3 := by
  induction actions generalizing switchBase with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.cons_append, List.length_cons, hintActionEntry]
    rw [ih]
    omega

theorem hintLastAction_select (actions : List Stmt) (last : Stmt) :
    (actions ++ [last])[actions.length]? = some last := by
  induction actions with
  | nil => rfl
  | cons first rest ih => exact ih

theorem hintCRAction_parts (S : CRSourceBundle) (P : Program)
    (switchBase : ℕ) (actions : List Stmt) (finish act : Stmt) (entry : ℕ)
    (hSelect : (hintActionsWithCR S switchBase actions finish)[actions.length]? = some act)
    (hEntry : entry = hintActionEntry (hintActionsWithCR S switchBase actions finish) switchBase actions.length)
    (hAt : At P entry (act.compile entry)) :
    act.len = (crSourceInputCode S entry).length + finish.len ∧
    At P entry (crSourceInputCode S entry) ∧
    At P (entry + (crSourceInputCode S entry).length)
      (finish.compile (entry + (crSourceInputCode S entry).length)) := by
  have hAddress : entry = switchBase + 2 * actions.length + 3 := hEntry.trans (hintLastActionEntry _ _ _)
  have hAct : act = hintCRAction S entry finish := by
    rw [hintActionsWithCR, hintLastAction_select, ← hAddress] at hSelect
    exact (Option.some.inj hSelect).symm
  subst act
  exact ⟨rfl, At.seqStmt hAt⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCRAction_parts
end S_HintPlaceCR20261120
section S_HintDetCopy20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDetCopyBody : List Instr :=
  [.add 3 5 0, .qDet 9 3, .add 3 4 0, .store 3 9, .add 0 0 15]

def hintDetCopyLoop : Stmt := .loop (.lt 2 0 6) (.code hintDetCopyBody)
def hintDetCopyStmt : Stmt := .seq (.code [.imm 0 0]) hintDetCopyLoop

structure HintDetCopyArgs (dest source count : ℕ) (state : RAMState) : Prop where
  destination : state.regs 4 = dest
  source_value : state.regs 5 = source
  length : state.regs 6 = count
  one : state.regs 15 = 1

structure HintDetCopyPre (E : RAMEnv) (dest source count : ℕ) : Prop where
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  destination : dest + count ≤ 2 ^ E.W
  source_span : source + count ≤ 2 ^ E.W
  values : ∀ i < count, E.det (source + i) < 2 ^ E.W

structure HintDetCopyInv (E : RAMEnv) (dest source count index : ℕ)
    (initial : RAMState) (state : RAMState) : Prop where
  args : HintDetCopyArgs dest source count state
  position : state.regs 0 = index
  context : state.regs 14 = initial.regs 14
  data : ∀ i < index, state.mem (dest + i) = E.det (source + i)
  frame : CRMemFrame dest (dest + count) initial.mem state.mem

theorem hintDetCopyBody_spec (E : RAMEnv) (state initial : RAMState)
    (dest source count i : ℕ) (pre : HintDetCopyPre E dest source count)
    (inv : HintDetCopyInv E dest source count i initial state) (hi : i < count) :
    HintDetCopyInv E dest source count (i + 1) initial (runBlock hintDetCopyBody E state) := by
  classical
  have hd : dest + i < 2 ^ E.W := by have := pre.destination; omega
  have hs : source + i < 2 ^ E.W := by have := pre.source_span; omega
  have hn : i + 1 < 2 ^ E.W := by have := pre.count_fit; omega
  have hval := pre.values i hi
  have hMem : (runBlock hintDetCopyBody E state).mem =
      Function.update state.mem (dest + i) (E.det (source + i)) := by
    simp [hintDetCopyBody, runBlock, execInstr, inv.position, inv.args.source_value, inv.args.destination,
      Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hval]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [hintDetCopyBody, runBlock, execInstr] using inv.args.destination
  · simpa [hintDetCopyBody, runBlock, execInstr] using inv.args.source_value
  · simpa [hintDetCopyBody, runBlock, execInstr] using inv.args.length
  · simpa [hintDetCopyBody, runBlock, execInstr] using inv.args.one
  · simp [hintDetCopyBody, runBlock, execInstr, inv.position, inv.args.one, Nat.mod_eq_of_lt hn]
  · simpa [hintDetCopyBody, runBlock, execInstr] using inv.context
  · intro j hj
    by_cases h : j = i
    · subst j; simp [hMem]
    · rw [hMem, Function.update_of_ne (by omega : dest + j ≠ dest + i)]
      exact inv.data j (by omega)
  · intro address hAway
    have hne : address ≠ dest + i := by rcases hAway with h | h <;> omega
    rw [hMem, Function.update_of_ne hne, inv.frame address hAway]

theorem hintDetCopyLoop_sem (P : Program) (E : RAMEnv) (state initial : RAMState)
    (dest source count base : ℕ) (pre : HintDetCopyPre E dest source count)
    (inv : HintDetCopyInv E dest source count 0 initial state)
    (hAt : At P base (hintDetCopyLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 8) state (fun k out => k ≤ 8 * count + 2 ∧
      HintDetCopyInv E dest source count count initial out) := by
  let I : ℕ → RAMState → Prop := fun left s => ∃ i, i + left = count ∧
    HintDetCopyInv E dest source count i initial s
  have hIpc : ∀ left s pc, I left s → I left {s with pc := pc} := by
    rintro left s pc ⟨i, hi, h⟩
    exact ⟨i, hi, ⟨⟨h.args.destination, h.args.source_value, h.args.length, h.args.one⟩,
      h.position, h.context, h.data, h.frame⟩⟩
  have hTest : ∀ left s, I left s → I left (runBlock (Cond.lt 2 0 6).code E s) := by
    rintro left s ⟨i, hi, h⟩
    refine ⟨i, hi, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, h.data, h.frame⟩⟩
    all_goals simp [Cond.code, runBlock, execInstr, h.args.destination, h.args.source_value,
      h.args.length, h.args.one, h.position, h.context]
  have hGo : ∀ left s, I (left + 1) s → (Cond.lt 2 0 6).eval s := by
    rintro left s ⟨i, hi, h⟩
    change s.regs 0 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hStop : ∀ s, I 0 s → ¬ (Cond.lt 2 0 6).eval s := by
    rintro s ⟨i, hi, h⟩
    change ¬ s.regs 0 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hBodyAt : At P (base + 2) hintDetCopyBody := (at_loop hAt).2.2.1
  have hBody : ∀ left s, I (left + 1) s → s.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintDetCopyBody).len) s
        (fun k out => k ≤ 5 ∧ I left out) := by
    rintro left s ⟨i, hi, h⟩ hStart
    have hp : s.pc = base + 2 := by exact hStart
    have hNative := Sem.block P E (base + 2) hintDetCopyBody s hBodyAt
      (by simp [hintDetCopyBody, NoBranch, Instr.NoBranchI]) hp
    apply Sem.mono hNative
    rintro k out ⟨hk, rfl⟩
    exact ⟨hk.le, i + 1, by omega, hintDetCopyBody_spec E s initial dest source count i pre h (by omega)⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintDetCopyBody) hAt pre.word I 5
    hIpc hTest hGo hStop hBody count state ⟨0, by omega, inv⟩ hPc
  apply Sem.mono hNative
  rintro k out ⟨hk, i, hi, h⟩
  have he : i = count := by omega
  exact ⟨hk, he ▸ h⟩

theorem hintDetCopyStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source count base : ℕ) (pre : HintDetCopyPre E dest source count)
    (args : HintDetCopyArgs dest source count state)
    (hAt : At P base (hintDetCopyStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 9) state (fun k out => k ≤ 8 * count + 3 ∧
      HintDetCopyInv E dest source count count state out) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  let mid := runBlock [.imm 0 0] E state
  have hRunI : (step P E)^[1] state = mid :=
    iterate_runBlock_of_at P E [.imm 0 0] state (by rwa [hPc])
      (by simp [NoBranch, Instr.NoBranchI])
  have hInv : HintDetCopyInv E dest source count 0 state mid := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, (by omega), fun _ _ => rfl⟩
    all_goals simp [mid, runBlock, execInstr, args.destination, args.source_value, args.length, args.one]
  have hPcI : mid.pc = base + 1 := by simp [mid, runBlock, execInstr, hPc]
  obtain ⟨_, k, out, hRun, hEnd, hk, h⟩ :=
    hintDetCopyLoop_sem P E mid state dest source count (base + 1) pre hInv hLoopAt hPcI
  exact ⟨hPc, k + 1, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega, h⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDetCopyStmt_sem
end S_HintDetCopy20261120
section S_HintStampBody20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- Mark one list entry in a bitmap. Entries outside the coordinate range mark the
reserved cell immediately after the bitmap. -/
def hintStampBody : List Instr :=
  [.add 3 5 0, .load 9 3, .lt 10 9 7, .mul 9 9 10, .bxor 10 10 15,
    .mul 10 7 10, .add 9 9 10, .add 3 4 9, .store 3 15, .add 0 0 15]

structure HintStampArgs (dest source count N : ℕ) (s : RAMState) : Prop where
  destination : s.regs 4 = dest
  source_value : s.regs 5 = source
  length : s.regs 6 = count
  limit : s.regs 7 = N
  one : s.regs 15 = 1

theorem hintStampBody_spec (E : RAMEnv) (s : RAMState) (dest source count N j q : ℕ)
    (hWord : 1 < 2 ^ E.W) (hSrc : source + j < 2 ^ E.W) (hEnd : dest + N < 2 ^ E.W)
    (hNext : j + 1 < 2 ^ E.W)
    (args : HintStampArgs dest source count N s) (hIndex : s.regs 0 = j)
    (hRead : s.mem (source + j) % 2 ^ E.W = q) :
    let out := runBlock hintStampBody E s
    out.pc = s.pc + 10 ∧ out.regs 0 = j + 1 ∧ HintStampArgs dest source count N out ∧
      out.regs 14 = s.regs 14 ∧ out.mem = Function.update s.mem (dest + min q N) 1 := by
  have hUniverse : N < 2 ^ E.W := by omega
  have hQ : q < 2 ^ E.W := by
    rw [← hRead]
    exact Nat.mod_lt _ (by omega)
  by_cases h : q < N
  · have hDest : dest + q < 2 ^ E.W := by omega
    rw [Nat.min_eq_left h.le]
    refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp [hintStampBody, runBlock, execInstr, args.destination, args.source_value, args.length, args.limit,
        args.one, hIndex, hRead, h, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hSrc,
        Nat.mod_eq_of_lt hQ, Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hNext]
  · rw [Nat.min_eq_right (by omega)]
    refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp [hintStampBody, runBlock, execInstr, args.destination, args.source_value, args.length, args.limit,
        args.one, hIndex, hRead, h, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hSrc,
        Nat.mod_eq_of_lt hUniverse, Nat.mod_eq_of_lt hEnd, Nat.mod_eq_of_lt hNext]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStampBody_spec
end S_HintStampBody20261120
section S_HintStamp20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintStampLoop : Stmt := .loop (.lt 2 0 6) (.code hintStampBody)
def hintStampStmt : Stmt := .seq (.code [.imm 0 0]) hintStampLoop

noncomputable def hintStampValue (E : RAMEnv) (source index : ℕ) (memory : ℕ → ℕ) (q : ℕ) : ℕ :=
  hintTruth (∃ i < index, memory (source + i) % 2 ^ E.W = q)

structure HintStampPre (E : RAMEnv) (dest source count N : ℕ) : Prop where
  word : 1 < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  destination : dest + N < 2 ^ E.W
  source_span : source + count ≤ 2 ^ E.W
  separate : source + count ≤ dest ∨ dest + N < source

structure HintStampInv (E : RAMEnv) (dest source count N index : ℕ)
    (initial : RAMState) (state : RAMState) : Prop where
  args : HintStampArgs dest source count N state
  position : state.regs 0 = index
  context : state.regs 14 = initial.regs 14
  data : ∀ q < N, state.mem (dest + q) = hintStampValue E source index initial.mem q
  frame : CRMemFrame dest (dest + N + 1) initial.mem state.mem

theorem hintStampInv_step (E : RAMEnv) (state initial : RAMState)
    (dest source count N i : ℕ) (pre : HintStampPre E dest source count N)
    (inv : HintStampInv E dest source count N i initial state) (hi : i < count) :
    HintStampInv E dest source count N (i + 1) initial (runBlock hintStampBody E state) := by
  classical
  let coord := initial.mem (source + i) % 2 ^ E.W
  have hs : source + i < 2 ^ E.W := by have := pre.source_span; omega
  have hn : i + 1 < 2 ^ E.W := by have := pre.count_fit; omega
  have hCoord : state.mem (source + i) % 2 ^ E.W = coord := by
    unfold coord
    rw [inv.frame]
    rcases pre.separate with h | h <;> omega
  obtain ⟨_, hIter, hArgs, hCtx, hMem⟩ := hintStampBody_spec E state dest source count N i coord
    pre.word hs pre.destination hn inv.args inv.position hCoord
  have hMinLe : min coord N ≤ N := min_le_right _ _
  refine ⟨hArgs, hIter, hCtx.trans inv.context, ?_, ?_⟩
  · intro q hq
    have hStep : hintStampValue E source (i + 1) initial.mem q =
        if q = coord then 1 else hintStampValue E source i initial.mem q := by
      unfold hintStampValue
      by_cases he : q = coord
      · subst q
        have hw : ∃ j < i + 1, initial.mem (source + j) % 2 ^ E.W = coord := ⟨i, by omega, rfl⟩
        simp only [hintTruth, if_pos hw, if_true]
      · rw [if_neg he]
        apply hintTruth_congr
        constructor
        · rintro ⟨j, hj, hv⟩
          have hne : j ≠ i := by intro h; subst j; exact he hv.symm
          exact ⟨j, by omega, hv⟩
        · rintro ⟨j, hj, hv⟩
          exact ⟨j, by omega, hv⟩
    rw [hStep, hMem]
    by_cases he : q = coord
    · subst q
      simp [Nat.min_eq_left hq.le]
    · have hh : dest + q ≠ dest + min coord N := by
        by_cases h : coord ≤ N
        · rw [Nat.min_eq_left h]; omega
        · rw [Nat.min_eq_right (by omega)]; omega
      rw [Function.update_of_ne hh, if_neg he, inv.data q hq]
  · intro address hAway
    have hne : address ≠ dest + min coord N := by rcases hAway with h | h <;> omega
    rw [hMem, Function.update_of_ne hne, inv.frame address hAway]

theorem hintStampLoop_sem (P : Program) (E : RAMEnv) (state initial : RAMState)
    (dest source count N base : ℕ) (pre : HintStampPre E dest source count N)
    (inv : HintStampInv E dest source count N 0 initial state)
    (hAt : At P base (hintStampLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 13) state (fun k out => k ≤ 13 * count + 2 ∧
      HintStampInv E dest source count N count initial out) := by
  let I : ℕ → RAMState → Prop := fun left s => ∃ i, i + left = count ∧
    HintStampInv E dest source count N i initial s
  have hIpc : ∀ left s pc, I left s → I left {s with pc := pc} := by
    rintro left s pc ⟨i, hi, h⟩
    exact ⟨i, hi, ⟨⟨h.args.destination, h.args.source_value, h.args.length, h.args.limit, h.args.one⟩,
      h.position, h.context, h.data, h.frame⟩⟩
  have hTest : ∀ left s, I left s → I left (runBlock (Cond.lt 2 0 6).code E s) := by
    rintro left s ⟨i, hi, h⟩
    refine ⟨i, hi, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, h.data, h.frame⟩⟩
    all_goals simp [Cond.code, runBlock, execInstr, h.args.destination, h.args.source_value,
      h.args.length, h.args.limit, h.args.one, h.position, h.context]
  have hGo : ∀ left s, I (left + 1) s → (Cond.lt 2 0 6).eval s := by
    rintro left s ⟨i, hi, h⟩
    change s.regs 0 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hStop : ∀ s, I 0 s → ¬ (Cond.lt 2 0 6).eval s := by
    rintro s ⟨i, hi, h⟩
    change ¬ s.regs 0 < s.regs 6
    rw [h.position, h.args.length]; omega
  have hBodyAt : At P (base + 2) hintStampBody := (at_loop hAt).2.2.1
  have hBody : ∀ left s, I (left + 1) s → s.pc = base + (Cond.lt 2 0 6).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 6).code.length + 1)
        (base + (Cond.lt 2 0 6).code.length + 1 + (Stmt.code hintStampBody).len) s
        (fun k out => k ≤ 10 ∧ I left out) := by
    rintro left s ⟨i, hi, h⟩ hStart
    have hp : s.pc = base + 2 := by exact hStart
    have hNative := Sem.block P E (base + 2) hintStampBody s hBodyAt
      (by simp [hintStampBody, NoBranch, Instr.NoBranchI]) hp
    apply Sem.mono hNative
    rintro k out ⟨hk, rfl⟩
    exact ⟨hk.le, i + 1, by omega, hintStampInv_step E s initial dest source count N i pre h (by omega)⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 6) (.code hintStampBody) hAt pre.word I 10
    hIpc hTest hGo hStop hBody count state ⟨0, by omega, inv⟩ hPc
  apply Sem.mono hNative
  rintro k out ⟨hk, i, hi, h⟩
  have he : i = count := by omega
  exact ⟨hk, he ▸ h⟩

theorem hintStampStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (dest source count N base : ℕ) (pre : HintStampPre E dest source count N)
    (args : HintStampArgs dest source count N state)
    (hClear : ∀ q < N, state.mem (dest + q) = 0)
    (hAt : At P base (hintStampStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 14) state (fun k out => k ≤ 13 * count + 3 ∧
      HintStampInv E dest source count N count state out) := by
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  let mid := runBlock [.imm 0 0] E state
  have hRunI : (step P E)^[1] state = mid :=
    iterate_runBlock_of_at P E [.imm 0 0] state (by rwa [hPc])
      (by simp [NoBranch, Instr.NoBranchI])
  have hInv : HintStampInv E dest source count N 0 state mid := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun _ _ => rfl⟩
    all_goals simp [mid, runBlock, execInstr, args.destination, args.source_value, args.length, args.limit, args.one]
    intro q hq
    simpa [hintStampValue, hintTruth, mid, runBlock, execInstr] using hClear q hq
  have hPcI : mid.pc = base + 1 := by simp [mid, runBlock, execInstr, hPc]
  obtain ⟨_, k, out, hRun, hEnd, hk, h⟩ :=
    hintStampLoop_sem P E mid state dest source count N (base + 1) pre hInv hLoopAt hPcI
  exact ⟨hPc, k + 1, out, hintIterate_then (step P E) hRunI hRun, by omega, by omega, h⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStampStmt_sem
end S_HintStamp20261120
section S_HintNormalizeSetup20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintNormalizeTable (E : RAMEnv) (metaBase dest count control : ℕ) : Prop where
  word : 11 < 2 ^ E.W
  span : metaBase + 11 < 2 ^ E.W
  dest_address : E.det (metaBase + 9) = dest
  count_value : E.det (metaBase + 10) = count
  control_address : E.det (metaBase + 11) = control
  dest_span : dest + count < 2 ^ E.W
  control_fit : control < 2 ^ E.W

def hintNormalizeSetup : List Instr :=
  [.imm 13 0, .add 5 0 13, .imm 15 1, .imm 3 9, .add 3 6 3, .qDet 4 3,
    .add 3 3 15, .qDet 6 3, .add 3 3 15, .qDet 14 3, .imm 7 1, .imm 8 0]

def hintNormalizeClamp : List Instr :=
  [.add 7 6 8, .lt 10 1 7, .mul 6 1 10, .bxor 10 10 15, .mul 10 7 10, .add 6 6 10]

theorem hintNormalizeSetup_spec (E : RAMEnv) (state : RAMState) (metaBase dest count control : ℕ)
    (layout : HintNormalizeTable E metaBase dest count control) (hMeta : state.regs 6 = metaBase)
    (hSourceFit : state.regs 0 < 2 ^ E.W) :
    let out := runBlock hintNormalizeSetup E state
    out.pc = state.pc + 12 ∧
      out.regs 5 = state.regs 0 ∧ out.regs 1 = state.regs 1 ∧ out.regs 14 = control ∧
      out.mem = state.mem ∧ HintFillParams dest 1 count 0 out := by
  have hs := layout.span
  have hWord := layout.word
  have hDest := layout.dest_span
  have hOne : 1 < 2 ^ E.W := by omega
  have h9 : 9 < 2 ^ E.W := by omega
  have hMeta9 : metaBase + 9 < 2 ^ E.W := by omega
  have hMeta10 : metaBase + 9 + 1 < 2 ^ E.W := by omega
  have hMeta11 : metaBase + 9 + 1 + 1 < 2 ^ E.W := by omega
  have hD : dest < 2 ^ E.W := by omega
  have hN : count < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_, ?_, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintNormalizeSetup, runBlock, execInstr, hMeta, layout.dest_address, layout.count_value,
      layout.control_address, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt h9, Nat.mod_eq_of_lt hMeta9,
      Nat.mod_eq_of_lt hMeta10, Nat.mod_eq_of_lt hMeta11, Nat.mod_eq_of_lt hD, Nat.mod_eq_of_lt hN,
      Nat.mod_eq_of_lt layout.control_fit, Nat.mod_eq_of_lt hSourceFit]

theorem hintNormalizeClamp_spec (E : RAMEnv) (state : RAMState) (dest source count raw : ℕ)
    (hWord : 1 < 2 ^ E.W) (hN : count < 2 ^ E.W) (hSource : state.regs 5 = source)
    (hRaw : state.regs 1 = raw) (hFill : HintFillParams dest 1 count 0 state) :
    let out := runBlock hintNormalizeClamp E state
    out.pc = state.pc + 6 ∧ out.mem = state.mem ∧ out.regs 14 = state.regs 14 ∧
      HintStampArgs dest source (min raw count) count out := by
  have hZero : state.regs 8 = 0 := hFill.fill_value
  by_cases h : raw < count
  · have hr : raw < 2 ^ E.W := by omega
    rw [Nat.min_eq_left h.le]
    refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      simp [hintNormalizeClamp, runBlock, execInstr, hSource, hRaw, hFill.dest_value, hFill.count_value,
        hFill.one_value, hZero, h, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hr]
  · rw [Nat.min_eq_right (by omega)]
    refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;>
      simp [hintNormalizeClamp, runBlock, execInstr, hSource, hRaw, hFill.dest_value, hFill.count_value,
        hFill.one_value, hZero, h, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hN]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNormalizeSetup_spec
#print axioms LinearSetReconciliation327.Main.hintNormalizeClamp_spec
end S_HintNormalizeSetup20261120
section S_HintNormalize20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintNormalizeStmt : Stmt := .seq (.code hintNormalizeSetup)
  (.seq hintFillStmt (.seq (.code hintNormalizeClamp) hintStampStmt))

/-- Convert a possibly malformed output list into an in-range bitmap in bounded
time. The list is clipped to the universe size before the scan. -/
theorem hintNormalizeStmt_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (metaBase dest N control base : ℕ) (layout : HintNormalizeTable E metaBase dest N control)
    (hMeta : state.regs 6 = metaBase) (hSource : state.regs 0 < 2 ^ E.W)
    (hSpan : state.regs 0 + min (state.regs 1) N ≤ 2 ^ E.W)
    (hSeparate : state.regs 0 + min (state.regs 1) N ≤ dest ∨ dest + N < state.regs 0)
    (hAt : At P base (hintNormalizeStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 40) state (fun k out => k ≤ 20 * N + 24 ∧
      out.regs 14 = control ∧
      (∀ q < N, out.mem (dest + q) = hintStampValue E (state.regs 0) (min (state.regs 1) N) state.mem q) ∧
      CRMemFrame dest (dest + N + 1) state.mem out.mem) := by
  let source := state.regs 0
  let raw := state.regs 1
  have hD := layout.dest_span
  have hN : N < 2 ^ E.W := by omega
  have hWord : 1 < 2 ^ E.W := by have := layout.word; omega
  obtain ⟨hSetupAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintNormalizeSetup at hSetupAt
  change At P (base + 12) ((Stmt.seq hintFillStmt
    (.seq (.code hintNormalizeClamp) hintStampStmt)).compile (base + 12)) at hRestAt
  obtain ⟨hClearAt, hClampStampAt⟩ := At.seqStmt hRestAt
  change At P (base + 12) (hintFillStmt.compile (base + 12)) at hClearAt
  change At P (base + 20) ((Stmt.seq (.code hintNormalizeClamp) hintStampStmt).compile (base + 20)) at hClampStampAt
  obtain ⟨hClampAt, hStampAt⟩ := At.seqStmt hClampStampAt
  change At P (base + 20) hintNormalizeClamp at hClampAt
  change At P (base + 26) (hintStampStmt.compile (base + 26)) at hStampAt
  have hSetup := hintNormalizeSetup_spec E state metaBase dest N control layout hMeta hSource
  generalize hSetupEq : runBlock hintNormalizeSetup E state = setup at hSetup
  obtain ⟨hSetupPc, hSetupSrc, hSetupRaw, hSetupCtx, hSetupMem, hFill⟩ := hSetup
  have hRunSetup : (step P E)^[12] state = setup := by
    have hh := iterate_runBlock_of_at P E hintNormalizeSetup state (by rwa [hPc])
      (by simp [hintNormalizeSetup, NoBranch, Instr.NoBranchI])
    rw [hSetupEq] at hh
    exact hh
  obtain ⟨_, kc, cleared, hRunClear, hClearPc, hClearCost, _, hClearMem, hFillClear, hClearFrame, hClearRegs⟩ :=
    hintFillStmt_sem P E setup dest 1 N (base + 12) 0 hWord hN (by intro j hj; simp; omega) hClearAt
      (by omega) hFill
  have hClamp := hintNormalizeClamp_spec E cleared dest source N raw hWord hN
    ((hClearRegs 5 (by decide) (by decide) (by decide)).trans hSetupSrc)
    ((hClearRegs 1 (by decide) (by decide) (by decide)).trans hSetupRaw) hFillClear
  generalize hClampEq : runBlock hintNormalizeClamp E cleared = clamped at hClamp
  obtain ⟨hClampPc, hClampMem, hClampCtx, hClampArgs⟩ := hClamp
  have hRunClamp : (step P E)^[6] cleared = clamped := by
    have hh := iterate_runBlock_of_at P E hintNormalizeClamp cleared (by rwa [hClearPc])
      (by simp [hintNormalizeClamp, NoBranch, Instr.NoBranchI])
    rw [hClampEq] at hh
    exact hh
  have hClear (q : ℕ) (hq : q < N) : clamped.mem (dest + q) = 0 := by
    rw [hClampMem, hClearMem]
    have hIn : dest + q ∈ hintFillPositions dest 1 N := Finset.mem_image.mpr
      ⟨q, Finset.mem_range.mpr hq, by simp⟩
    simp [hintFillMem, hIn]
  have hSeparate' : source + min raw N ≤ dest ∨ dest + N < source := hSeparate
  have hClampFrame : CRMemFrame dest (dest + N) state.mem clamped.mem := by
    intro addr hAway
    rw [hClampMem, hClearFrame, hSetupMem]
    intro hIn
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hIn
    have hq' := Finset.mem_range.mp hq
    simp at he
    rcases hAway with h | h <;> omega
  have hPre : HintStampPre E dest source (min raw N) N :=
    ⟨hWord, (min_le_right _ _).trans_lt hN, hD, hSpan, hSeparate'⟩
  obtain ⟨_, ks, out, hRunStamp, hEnd, hCost, hFinal⟩ :=
    hintStampStmt_sem P E clamped dest source (min raw N) N (base + 26) hPre hClampArgs hClear hStampAt
      (by omega)
  have hMin := min_le_right raw N
  refine ⟨hPc, ks + (6 + (kc + 12)), out,
    hintIterate_then (step P E) (hintIterate_then (step P E)
      (hintIterate_then (step P E) hRunSetup hRunClear) hRunClamp) hRunStamp,
    by omega, by omega, hFinal.context.trans (hClampCtx.trans
      ((hClearRegs 14 (by decide) (by decide) (by decide)).trans hSetupCtx)), ?_, ?_⟩
  · intro q hq
    rw [hFinal.data q hq]
    apply hintTruth_congr
    have hRead (i : ℕ) (hi : i < min raw N) :
        clamped.mem (source + i) = state.mem (source + i) :=
      hClampFrame _ (by rcases hSeparate' with h | h <;> omega)
    constructor
    · rintro ⟨i, hi, hv⟩
      exact ⟨i, hi, by rwa [hRead i hi] at hv⟩
    · rintro ⟨i, hi, hv⟩
      exact ⟨i, hi, by rwa [hRead i hi]⟩
  · intro addr hAway
    exact (hFinal.frame addr hAway).trans (hClampFrame addr (by rcases hAway with h | h <;> omega))

theorem hintNormalize_support {N : ℕ} (E : RAMEnv) (state : RAMState) (x : Fin N → ZMod 2)
    (hWidth : N < 2 ^ E.W) (hOut : OutputsSupport state x) (i : Fin N) :
    hintStampValue E (state.regs 0) (min (state.regs 1) N) state.mem i.val = (x i).val := by
  classical
  have hSub : (outList state).toFinset ⊆ Finset.range N := by
    intro v hv
    obtain ⟨j, rfl, _⟩ := (hOut.2 v).mp (List.mem_toFinset.mp hv)
    exact Finset.mem_range.mpr j.isLt
  have hCount : state.regs 1 ≤ N := by
    have hc := Finset.card_le_card hSub
    rw [List.toFinset_card_of_nodup hOut.1, Finset.card_range] at hc
    simpa only [outList, List.length_map, List.length_range] using hc
  rw [Nat.min_eq_left hCount]
  have hc i (hi : i < state.regs 1) : state.mem (state.regs 0 + i) < 2 ^ E.W := by
    have hx : state.mem (state.regs 0 + i) ∈ outList state :=
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    exact (Finset.mem_range.mp (hSub (List.mem_toFinset.mpr hx))).trans hWidth
  have hMem : (∃ j < state.regs 1, state.mem (state.regs 0 + j) % 2 ^ E.W = i.val) ↔
      i.val ∈ outList state := by
    constructor
    · rintro ⟨j, hj, hq⟩
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, by simpa only [Nat.mod_eq_of_lt (hc j hj)] using hq⟩
    · rintro hj
      obtain ⟨j, hj, hq⟩ := List.mem_map.mp hj
      have hj' := List.mem_range.mp hj
      exact ⟨j, hj', by simpa only [Nat.mod_eq_of_lt (hc j hj')] using hq⟩
  have hEq : i.val ∈ outList state ↔ x i = 1 := by
    rw [hOut.2]
    constructor
    · rintro ⟨j, hj, h⟩
      rw [← Fin.ext hj]
      exact h
    · exact fun h => ⟨i, rfl, h⟩
  unfold hintStampValue
  rw [hintTruth_congr (hMem.trans hEq)]
  have hBinary : ∀ bit : ZMod 2, bit = 0 ∨ bit = 1 := by decide
  rcases hBinary (x i) with hZero | hOne
  · simp [hintTruth, hZero]
  · rw [hOne, hintTruth, if_pos rfl]
    decide

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNormalizeStmt_sem
#print axioms LinearSetReconciliation327.Main.hintNormalize_support
end S_HintNormalize20261120


