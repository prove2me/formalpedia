-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintToggleGateAction20261120
-- name    : LinearSetReconciliation327_Main_HintToggleGateAction20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:59:31.073896+00:00
-- url     : https://prove2.me/theorems/1f5cccc3-5758-421a-91b0-75b5e475c3b7
-- title:
--   LinearSetReconciliation327 — HintToggleGateAction (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintToggleGateAction20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintToggleGate20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintToggleGateAction_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (descriptor gate coordinate detBase payBase control base budget : ℕ) (Q : (ℕ → ℕ) → Prop)
    (tbl : HintToggleGateTable E descriptor gate coordinate detBase payBase control)
    (hWord : UpWordState E state) (hArg : state.regs 6 = descriptor)
    (hAt : At P base (hintToggleGateAction.compile base)) (hPc : state.pc = base)
    (hSkip : state.mem gate = 0 → Q state.mem)
    (hToggle : state.mem gate ≠ 0 → ∀ st, At P (base + 10) (upSavedSup.compile (base + 10)) →
      st.pc = base + 10 → st.mem = state.mem → UpWordState E st →
      st.regs 0 = coordinate → st.regs 14 = detBase → st.regs 15 = payBase →
      Sem P E (base + 10) (base + 10 + upSavedSup.len) st
        (fun k out => k ≤ budget ∧ out.regs 14 = detBase ∧ Q out.mem)) :
    Sem P E base (base + hintToggleGateAction.len) state (fun k out =>
      k ≤ budget + 14 ∧ out.regs 14 = control ∧ Q out.mem) := by
  have h1 : 1 < 2 ^ E.W := by have := tbl.word; omega
  obtain ⟨hSetupAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintToggleGateSetup at hSetupAt
  change At P (base + 9) ((Stmt.seq hintToggleGateBranch (.code hintToggleGateRestore)).compile (base + 9))
    at hRestAt
  obtain ⟨hBranchAt, hRestoreAt⟩ := At.seqStmt hRestAt
  change At P (base + 9) ((Stmt.ite (.neqz 1) upSavedSup (.code [])).compile (base + 9)) at hBranchAt
  change At P (base + 9 + hintToggleGateBranch.len) hintToggleGateRestore at hRestoreAt
  have hSetup := hintToggleGateSetup_spec E state descriptor gate coordinate detBase payBase control
    tbl hArg (hWord.2 gate)
  generalize hz : runBlock hintToggleGateSetup E state = entered at hSetup
  obtain ⟨hPcEntered, hMem, hFlag, hCoord, hDet, hPay⟩ := hSetup
  have hRunSetup : (step P E)^[9] state = entered := by
    have hh := iterate_runBlock_of_at P E hintToggleGateSetup state (by rwa [hPc])
      (by simp [hintToggleGateSetup, NoBranch, Instr.NoBranchI])
    rw [hz] at hh
    exact hh
  have hStateEntered : UpWordState E entered := hRunSetup ▸ upIterate_word_bound P E state 9 hWord
  have hStart : entered.pc = base + 9 := by omega
  have hBranch : Sem P E (base + 9) (base + 9 + hintToggleGateBranch.len) entered
      (fun k out => k ≤ budget + 2 ∧ out.regs 14 = detBase ∧ Q out.mem) := by
    change Sem P E (base + 9) (base + 9 + ((Cond.neqz 1).code.length + upSavedSup.len + (.code [] : Stmt).len + 3))
      entered _
    apply Sem.ite P E (base + 9) (.neqz 1) upSavedSup (.code []) entered _ hBranchAt h1 hStart
    · intro hYes
      have hOn : state.mem gate ≠ 0 := by
        change entered.regs 1 ≠ 0 at hYes
        rwa [hFlag] at hYes
      have hThen : At P (base + 10) (upSavedSup.compile (base + 10)) := (at_ite hBranchAt).2.2.1
      have hRun := hToggle hOn {entered with pc := base + 10} hThen rfl hMem hStateEntered hCoord hDet hPay
      apply Sem.mono hRun
      rintro k out ⟨hk, h14, hq⟩
      exact ⟨by simp only [Cond.code, List.length_nil]; omega, h14, hq⟩
    · intro hNo
      have hOff : state.mem gate = 0 := by
        change ¬ entered.regs 1 ≠ 0 at hNo
        rw [hFlag] at hNo
        exact not_not.mp hNo
      refine ⟨rfl, 0, _, rfl, ?_, by simp only [Cond.code, List.length_nil]; omega, hDet, ?_⟩
      · simp only [Function.iterate_zero, id_eq, Stmt.len, List.length_nil, Nat.add_zero]
        omega
      · exact hMem ▸ hSkip hOff
  obtain ⟨_, k, mid, hRun, hPcMid, hTime, hDetMid, hPost⟩ := hBranch
  have hClose := hintToggleGateRestore_spec E mid descriptor gate coordinate detBase payBase control tbl hDetMid
  generalize hf : runBlock hintToggleGateRestore E mid = out at hClose
  obtain ⟨hPcOut, hMemOut, hControl⟩ := hClose
  have hRunClose : (step P E)^[3] mid = out := by
    have hh := iterate_runBlock_of_at P E hintToggleGateRestore mid (by rwa [hPcMid])
      (by simp [hintToggleGateRestore, NoBranch, Instr.NoBranchI])
    rw [hf] at hh
    exact hh
  refine ⟨hPc, 3 + (k + 9), out, ?_, ?_, by omega, hControl, hMemOut ▸ hPost⟩
  · rw [Function.iterate_add_apply, Function.iterate_add_apply, hRunSetup, hRun, hRunClose]
  · change out.pc = base + (9 + (hintToggleGateBranch.len + 3))
    omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintToggleGateAction_sem


