-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_ColWire2aPart120261122
-- name    : LinearSetReconciliation327_Main_ColWire2aPart120261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T16:18:07.108365+00:00
-- url     : https://prove2.me/theorems/b8806b94-8185-4192-afcc-a00a0d965b3a
-- title:
--   The column loop and counter contract (ColWire2a, part 1/2)
-- statement:
--   Part 1 of the column `StageRun` construction, split out because the single-module node exceeded the platform's per-definition compile budget: `ColCounter`, its empty-program instance, `ColStep`, `colLoop_len`, `colLoop_stageRun` (the counted loop from an arbitrary `ColIn n` state, cost `n * T + 2`) and `colTail_sem` (`d65Inc` then the trailing jump, 3 steps).  The spans are copied byte-identically from `ColWire2a`; the umbrella node `…_ColWire2a20261122` re-exports both parts under the original import path.  Axiom-clean; local `cpl` 6 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's column stage and Theorem 5.1's decoder (the two-window `DownBlkSemAtW` contract).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_ColWire20261122

/-!
# `ColWire` II — the column `StageRun`, from `DownBlkSemAtW`

`Def_…_ColWire20261122` supplied the allocation (`colWs N = 2N + 5`, per-child payload blocks, the
hint list `J` strictly below `γ`).  This file turns `DownBlkSemAtW` into the column stage's
`StageRun`:

* `ColStep` — one iteration of the loop, as an existential step (no loop-head family needed);
* `colLoop_stageRun` — **the loop**, from an arbitrary `ColIn n` state, cost `n · T + 2`;
* `colTail_sem` — `d65Inc` then the trailing `jmp`, in 3 steps;
* `colStep_of_downBlk` — one iteration, **discharged from `DownBlkSemAtW`** at cost `Tdec + 5`;
* `zColStageRun` — the column `StageRun` from `zDColHead` to `zDAsBase`, cost
  `ℓ · (Tdec + 5) + 2`, i.e. `ℓ · (T + 2) + 2` with `T = Tdec + 3`;
* non-vacuity at `ℓ = 3`, `N = 4`, `d ≥ 1`, with a non-zero payload.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace W65

open RSD

/-! ## 0. The child's register discipline -/

/-- **The one hypothesis `DownBlkSemAtW` does not supply: the child preserves the two loop
registers.**  `DownBlkSemAtW` fixes the child's memory effects and its exit address, but says
nothing about registers, while the loop counter lives in `r1` and the bound in `r2`.

This is where the published `col` field's shape (`topLoop Sdec`, counter `r1`) meets reality:
Theorem 5.1's decoder *reads* `r1`/`r2` as its payload source and length (`decoderStart` sets
`r1 = wordsOf W M`, `r2 = J.length`), so a real child must be wrapped (`save; setup; Sinner;
restore`) for this to hold.  The predicate is stated for all runs of the child, so it is a clean
stand-alone hypothesis, and it is exactly what a `save`/`restore` wrapper establishes. -/
def ColCounter (Sdec : Stmt) (E : RAMEnv) (T : ℝ) : Prop :=
  ∀ (G : Program) (base : ℕ) (s out : RAMState) (k : ℕ),
    At G base (Sdec.compile base) → s.pc = base → (step G E)^[k] s = out →
    (k : ℝ) ≤ T → out.pc = base + Sdec.len → out.regs 1 = s.regs 1 ∧ out.regs 2 = s.regs 2

/-- The empty child preserves the loop registers trivially at `T = 0` (its only run is `0` steps). -/
theorem colCounter_empty (E : RAMEnv) : ColCounter (.code [] : Stmt) E 0 := by
  intro G base s out k _ hpc hrun hk _
  have hk0 : k = 0 := by
    have : (k : ℝ) ≤ 0 := hk
    exact_mod_cast le_antisymm this (Nat.cast_nonneg k)
  subst hk0
  rw [Function.iterate_zero] at hrun
  subst hrun
  exact ⟨rfl, rfl⟩

/-! ## 1. The loop, from a per-iteration step -/

/-- **One iteration of the column loop, abstractly.** -/
def ColStep (P : Program) (E : RAMEnv) (a n : ℕ) (T : ℝ) : Prop :=
  ∀ (j : ℕ) (s : RAMState), j < n → s.pc = a → s.regs 1 = j → s.regs 2 = n →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧ s'.pc = a ∧
      s'.regs 1 = j + 1 ∧ s'.regs 2 = n

theorem colLoop_len {Sdec : Stmt} : (topLoop Sdec).len = Sdec.len + 5 := by
  have h1 : d65Cond.code.length = 1 := rfl
  have h2 : d65Inc.length = 2 := rfl
  simp only [topLoop, Stmt.len, h1, h2]
  omega

/-- **The counted column loop, from an arbitrary `ColIn n` state.**  `Sem.loop`/`loopExit` with the
fixed loop-head family replaced by the existential `ColStep`: the deterministic machine's actual
successors are threaded through the induction, so no family has to be named.  Cost `n · T + 2`. -/
theorem colLoop_stageRun {P : Program} {E : RAMEnv} {a n : ℕ} {T : ℝ} {Sdec : Stmt}
    (hAt : At P a (Stmt.compile (Stmt.loop d65Cond (.seq Sdec (.code d65Inc))) a))
    (hW : 1 < 2 ^ E.W) (hT : 0 ≤ T) (hell : n < 2 ^ E.W)
    (hstep : ColStep P E a n T) :
    StageRun P E a (a + (topLoop Sdec).len) ((n : ℝ) * T + 2) (ColIn n)
      (fun s => s.regs 1 = n ∧ s.regs 2 = n) := by
  have hcl : d65Cond.code.length = 1 := rfl
  have hbl : (Stmt.seq Sdec (.code d65Inc)).len = Sdec.len + 2 := rfl
  have hexit : ∀ s : RAMState, s.pc = a → s.regs 1 = n → s.regs 2 = n →
      ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ 2 ∧ (step P E)^[k] s = s' ∧
        s'.pc = a + (topLoop Sdec).len ∧ s'.regs 1 = n ∧ s'.regs 2 = n := by
    intro s hpc h1 h2
    have hstop : ¬ d65Cond.eval s := by
      simp only [d65Cond, Cond.eval, h1, h2]
      omega
    obtain ⟨-, k, s', hstep', hpc', hQ⟩ := Sem.loopExit P E a d65Cond
      (.seq Sdec (.code d65Inc)) s hAt hW hpc hstop
    refine ⟨k, s', ?_, hstep', ?_, ?_, ?_⟩
    · rw [hQ.1, hcl]; norm_num
    · rw [hpc', hcl, hbl, colLoop_len]; omega
    · rw [hQ.2]; exact (zCond_regs_pres E s).1.trans h1
    · rw [hQ.2]; exact (zCond_regs_pres E s).2.trans h2
  have key : ∀ m : ℕ, m ≤ n → ∀ s : RAMState, s.pc = a → s.regs 1 = n - m → s.regs 2 = n →
      ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ (m : ℝ) * T + 2 ∧ (step P E)^[k] s = s' ∧
        s'.pc = a + (topLoop Sdec).len ∧ s'.regs 1 = n ∧ s'.regs 2 = n := by
    intro m
    induction m with
    | zero =>
        intro _ s hpc h1 h2
        have h1' : s.regs 1 = n := by simpa using h1
        simpa using hexit s hpc h1' h2
    | succ m ih =>
        intro hm s hpc h1 h2
        have hmn : m ≤ n := by omega
        have hj : n - (m + 1) < n := by omega
        obtain ⟨k1, s1, hk1, hrun1, hpc1, hregs1, hregs2⟩ :=
          hstep (n - (m + 1)) s hj hpc h1 h2
        have h1next : s1.regs 1 = n - m := by omega
        obtain ⟨k2, s2, hk2, hrun2, hpc2, h1f, h2f⟩ := ih hmn s1 hpc1 h1next hregs2
        refine ⟨k1 + k2, s2, ?_, ?_, hpc2, h1f, h2f⟩
        · push_cast
          nlinarith
        · rw [Nat.add_comm, Function.iterate_add_apply, hrun1, hrun2]
  intro s hpc hI
  obtain ⟨h1, h2⟩ := hI
  have h0 : s.regs 1 = n - n := by omega
  simpa using key n (le_refl n) s hpc h0 h2

/-! ## 2. One child call, and therefore one iteration -/

/-- **The loop tail.**  From any state at `base + Sdec.len` (just past the child), `d65Inc` followed
by the trailing `jmp a` reaches the loop head in `3` steps. -/
theorem colTail_sem {P : Program} {E : RAMEnv} {base a : ℕ} {Sdec : Stmt}
    (hAtInc : At P (base + Sdec.len) d65Inc)
    (hjmp : P[base + Sdec.len + 2]? = some (iJmp a))
    (hW : 1 < 2 ^ E.W) (s : RAMState) (hpc : s.pc = base + Sdec.len) :
    Sem P E (base + Sdec.len) a s
      (fun k z => k = 3 ∧ z = ⟨a, Function.update (Function.update s.regs r7 1) r1
        ((s.regs 1 + 1) % 2 ^ E.W), s.mem⟩) := by
  obtain ⟨p, r, m⟩ := s
  simp only at hpc
  subst hpc
  have hinc : Sem P E (base + Sdec.len) (base + Sdec.len + 2) ⟨base + Sdec.len, r, m⟩
      (fun k z => k = 2 ∧ z = ⟨base + Sdec.len + 2,
        Function.update (Function.update r r7 1) r1 ((r r1 + 1) % 2 ^ E.W), m⟩) :=
    zD65Inc_sem (P := P) (E := E) (pc := base + Sdec.len) (r := r) (m := m) hAtInc hW
  have hjr : Sem P E (base + Sdec.len + 2) a
      ⟨base + Sdec.len + 2, Function.update (Function.update r r7 1) r1
        ((r r1 + 1) % 2 ^ E.W), m⟩
      (fun k z => k = 1 ∧ z = ⟨a, Function.update (Function.update r r7 1) r1
        ((r r1 + 1) % 2 ^ E.W), m⟩) := by
    refine Sem.mono (Sem.exec P E (base + Sdec.len + 2) a _ (iJmp a) hjmp rfl ?_) ?_
    · simp [execInstr]
    · rintro k z ⟨hk, rfl⟩
      refine ⟨hk, ?_⟩
      simp [execInstr]
  exact Sem.trans hinc hjr

end W65
end LinearSetReconciliation327.Main


