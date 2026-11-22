-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintLoopFuel20261120
-- name    : LinearSetReconciliation327_Main_HintLoopFuel20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:36:14.189543+00:00
-- url     : https://prove2.me/theorems/41c3288f-990d-4263-8f70-bb056b6ed6c6
-- title:
--   LinearSetReconciliation327 — HintLoopFuel (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintLoopFuel20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowOps20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- A loop rule with a mathematical fuel invariant. The fuel need not fit in
    one RAM word: the concrete body may use a bounded-digit enumeration cursor. -/
theorem hintLoopFuel_sem (P : Program) (E : RAMEnv) (base : ℕ) (c : Cond) (body : Stmt)
    (hAt : At P base (Stmt.compile (.loop c body) base)) (hWord : 1 < 2 ^ E.W)
    (I : ℕ → RAMState → Prop) (B : ℕ)
    (hPcFrame : ∀ n state pc, I n state → I n {state with pc := pc})
    (hTestFrame : ∀ n state, I n state → I n (runBlock c.code E state))
    (hGo : ∀ n state, I (n + 1) state → c.eval state)
    (hStop : ∀ state, I 0 state → ¬ c.eval state)
    (hBody : ∀ n state, I (n + 1) state → state.pc = base + c.code.length + 1 →
      Sem P E (base + c.code.length + 1) (base + c.code.length + 1 + body.len) state
        (fun k out => k ≤ B ∧ I n out)) :
    ∀ n state, I n state → state.pc = base →
      Sem P E base (base + c.code.length + body.len + 2) state
        (fun k out => k ≤ (c.code.length + B + 2) * n + (c.code.length + 1) ∧ I 0 out) := by
  intro n
  induction n with
  | zero =>
      intro state hInv hPc
      have hExit := Sem.loopExit P E base c body state hAt hWord hPc (hStop state hInv)
      apply Sem.mono hExit
      intro k out hOut
      obtain ⟨hK, rfl⟩ := hOut
      exact ⟨by omega, hPcFrame 0 _ _ (hTestFrame 0 state hInv)⟩
  | succ n ih =>
      intro state hInv hPc
      let entered := {runBlock c.code E state with pc := base + c.code.length + 1}
      have hEntered : I (n + 1) entered := hPcFrame _ _ _ (hTestFrame _ _ hInv)
      obtain ⟨_, kBody, mid, hRunBody, hMidPc, hCost, hMidInv⟩ := hBody n entered hEntered rfl
      have hJump : P[mid.pc]? = some (.jmp base) := by
        rw [hMidPc]
        exact (at_loop hAt).2.2.2
      let returned := {mid with pc := base}
      have hRunJump : step P E mid = returned := by
        rw [crStep_fetch P E mid _ hJump]
        rfl
      have hReturn : Sem P E (base + c.code.length + 1) base entered
          (fun k out => k = kBody + 1 ∧ out = returned) := by
        refine ⟨rfl, kBody + 1, returned, ?_, rfl, rfl, rfl⟩
        rw [show kBody + 1 = 1 + kBody by omega, Function.iterate_add_apply]
        change step P E ((step P E)^[kBody] entered) = returned
        rw [hRunBody, hRunJump]
      have hStep := Sem.loopStep P E base c body state returned (kBody + 1) hAt hWord
        hPc (hGo n state hInv) hReturn
      have hStepBound : Sem P E base base state
          (fun k out => k ≤ c.code.length + B + 2 ∧ out = returned) := by
        apply Sem.mono hStep
        intro k out hOut
        exact ⟨by omega, hOut.2⟩
      have hRest := ih returned (hPcFrame n mid base hMidInv) rfl
      have hCombined := Sem.seq_bound hStepBound (fun next hNextPc hEq => by rw [hEq]; exact hRest)
      apply Sem.mono hCombined
      intro k out hOut
      refine ⟨?_, hOut.2⟩
      rw [Nat.mul_succ]
      omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintLoopFuel_sem


