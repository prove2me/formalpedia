-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_SemLoopLeDet20261122
-- name    : LinearSetReconciliation327_Main_SemLoopLeDet20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:19:42.277365+00:00
-- url     : https://prove2.me/theorems/516cdae3-3cfe-43f1-95bd-617b65ab9d45
-- title:
--   Row-stage mirror: the bounded loop rule, free of `DecoderLemmas`
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_SemLoopLeDet20261122` of the Theorem 6.5 development.  It is a re-hosted mirror of the project's published row-stage bundle with only the recorded edits (the import of the `DecoderLemmas` side replaced by the `P21DetBndComp` chain, and — for the `Pay` mirrors — the per-row payload base re-pointed to the arithmetic progression `payTabAddr + j * stageLen`); the statements of the row chain are byte-identical.  It contains definitions and fully proved lemmas only (no `sorry`, no new axiom) and exists so that the later nodes of the chain compile inside the platform's per-definition budget.  This is a supporting node, not a statement of independent mathematical interest.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder) and Proposition 2.1 (the base-relative decoder); the project's verified row-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_RowScratchDet20261122

/-!
# `Sem.loopLe`, re-hosted so the row stage does not need `MergeStep`

Byte-identical copy of the declaration `LinearSetReconciliation327.Main.RMR.Sem.loopLe` from
`Def_LinearSetReconciliation327_Main_MergeStep20261121` (which imports `DecoderLemmas` and therefore
cannot be loaded together with `P21DetBndComp`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace RMR

/-- **The loop rule with upper-bounded iterations.**  `Sem.loop` demands an exact cost per
iteration; the nested merge needs only an upper bound, so it is re-proved here with `≤`. -/
theorem Sem.loopLe (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W) :
    ∀ (n : ℕ) (s : ℕ → RAMState) (cost : ℕ → ℕ),
      (∀ j, (s j).pc = a) →
      (∀ j < n, c.eval (s j)) →
      (¬ c.eval (s n)) →
      (∀ j < n, Sem P E (a + c.code.length + 1) a
        { runBlock c.code E (s j) with pc := a + c.code.length + 1 }
        (fun k s' => k ≤ cost j ∧ s' = s (j + 1))) →
      Sem P E a (a + c.code.length + b.len + 2) (s 0)
        (fun k s' => k ≤ (c.code.length + 1) +
            ∑ j ∈ Finset.range n, (c.code.length + 1 + cost j) ∧
          s' = { runBlock c.code E (s n) with pc := a + c.code.length + b.len + 2 }) := by
  intro n
  induction n with
  | zero =>
      intro s cost hpc _ hstop _
      refine Sem.mono (Sem.loopExit P E a c b (s 0) hAt hW (hpc 0) hstop) ?_
      intro k s' h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, rfl⟩
  | succ n ih =>
      intro s cost hpc hgo hstop hstep
      obtain ⟨hcode, hjz, -, -⟩ := at_loop hAt
      have htest : Sem P E a (a + c.code.length) (s 0)
          (fun k s' => k ≤ c.code.length ∧ s' = runBlock c.code E (s 0)) := by
        refine Sem.mono (Sem.block P E a c.code (s 0) hcode (Cond.noBranch_code c) (hpc 0)) ?_
        intro k s' h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨le_rfl, rfl⟩
      have hpcT : (runBlock c.code E (s 0)).pc = a + c.code.length := by
        rw [runBlock_pc c.code E (s 0) (Cond.noBranch_code c), hpc 0]
      have hne : (runBlock c.code E (s 0)).regs c.test ≠ 0 :=
        (Cond.eval_iff c E (s 0) hW).mp (hgo 0 (by omega))
      have hfall : Sem P E (a + c.code.length) (a + c.code.length + 1) (runBlock c.code E (s 0))
          (fun k s' => k ≤ 1 ∧
            s' = { runBlock c.code E (s 0) with pc := a + c.code.length + 1 }) := by
        refine Sem.mono (Sem.jz_next P E (a + c.code.length)
          (a + c.code.length + b.len + 2) c _ hjz hpcT hne) ?_
        intro k s' h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨le_rfl, rfl⟩
      have hfirst : Sem P E a a (s 0)
          (fun k s' => k ≤ (c.code.length + 1) + cost 0 ∧ s' = s 1) :=
        R66.Sem.trans_le (R66.Sem.trans_le htest hfall) (hstep 0 (by omega))
      have hrest : Sem P E a (a + c.code.length + b.len + 2) (s 1)
          (fun k s' => k ≤ (c.code.length + 1) +
              ∑ j ∈ Finset.range n, (c.code.length + 1 + cost (j + 1)) ∧
            s' = { runBlock c.code E (s (n + 1)) with pc := a + c.code.length + b.len + 2 }) :=
        ih (fun j => s (j + 1)) (fun j => cost (j + 1)) (fun j => hpc (j + 1))
          (fun j hj => hgo (j + 1) (by omega)) (by simpa using hstop)
          (fun j hj => hstep (j + 1) (by omega))
      refine Sem.mono (R66.Sem.trans_le hfirst hrest) ?_
      intro k s' h
      obtain ⟨hk, hs⟩ := h
      rw [Finset.sum_range_succ']
      exact ⟨by omega, hs⟩


end RMR
end LinearSetReconciliation327.Main


