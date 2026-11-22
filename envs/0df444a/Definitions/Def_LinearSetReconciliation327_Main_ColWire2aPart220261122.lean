-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_ColWire2aPart220261122
-- name    : LinearSetReconciliation327_Main_ColWire2aPart220261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T16:19:04.719804+00:00
-- url     : https://prove2.me/theorems/b05d9939-e179-4531-9562-02bef0bdfb08
-- title:
--   The column `StageRun` from `DownBlkSemAtW` (ColWire2a, part 2/2)
-- statement:
--   Part 2 of the column `StageRun` construction: `colStep_of_downBlk` discharges one loop iteration from the two-window child contract `DownBlkSemAtW` at cost `Tdec + 5`, `stageRun_post'` weakens a postcondition, and `zColStageRun` (cost `ell * (Tdec + 5) + 2`, post `r1 = r2 = ell`) / `zColStageRun_true` are the column stage at `zDColHead → zDAsBase`.  The spans are copied byte-identically from `ColWire2a`; the umbrella node re-exports both parts.  Axiom-clean; local `cpl` 5 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's column stage and Theorem 5.1's decoder (the two-window `DownBlkSemAtW` contract).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_ColWire20261122
import Definitions.Def_LinearSetReconciliation327_Main_ColWire2aPart120261122

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
/-- **One iteration, discharged from `DownBlkSemAtW`.**  The body is `Sdec ; d65Inc ; jmp a`.  Cost
`Tdec + 5`: the test, the `jz`, the child, the increment and the jump. -/
theorem colStep_of_downBlk {P : Program} {E : RAMEnv} {a n : ℕ} {Tdec : ℝ} {Sdec : Stmt}
    {Bw ms ws N Ms : ℕ} {I : ℕ → (ℕ → ℕ) → Prop}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (hdown : DownBlkSemAtW Sdec E Tdec Bw ms ws I Hs)
    (hcnt : ColCounter Sdec E Tdec)
    (hAtLoop : At P a (Stmt.compile (Stmt.loop d65Cond (.seq Sdec (.code d65Inc))) a))
    (hW : 1 < 2 ^ E.W) (hell : n < 2 ^ E.W)
    (δ β γ header control hintMap resultMap listBase table count : ℕ)
    (y : Fin Ms → ZMod 2) (J : List ℕ) (j : ℕ) (s : RAMState)
    (hj : j < n) (hpc : s.pc = a) (h1 : s.regs 1 = j) (h2 : s.regs 2 = n)
    (hfit : wordsOf E.W Ms ≤ ms)
    (hδB : δ + Bw ≤ 2 ^ E.W) (hβ : β + ms ≤ 2 ^ E.W)
    (hws : ws ≤ 2 ^ E.W) (hγws : γ + ws ≤ 2 ^ E.W)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (h14 : s.regs 14 = δ) (h15 : s.regs 15 = β)
    (hmem : ∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q)
    (hHint : γ ≤ hintMap) (hHintTop : hintMap + N < γ + ws)
    (hControl : γ ≤ control) (hControlTop : control + 4 ≤ γ + ws)
    (hList : γ ≤ listBase) (hListTop : listBase + N ≤ γ + ws)
    (hDisj : β + ms ≤ γ ∨ γ + ws ≤ β)
    (hIFrame : ∀ n' mem, I n' mem → ∀ a', a' < γ ∨ γ + ws ≤ a' → mem a' = s.mem a') :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ Tdec + 5 ∧ (step P E)^[k] s = s' ∧ s'.pc = a ∧
      s'.regs 1 = j + 1 ∧ s'.regs 2 = n := by
  have hcl : d65Cond.code.length = 1 := rfl
  obtain ⟨htestAt, hjzAt, hbodyAt, hjmpAt⟩ := at_loop hAtLoop
  have hbodyAt' : At P (a + 2) (Sdec.compile (a + 2) ++ d65Inc) := by
    have h := hbodyAt
    rw [show a + d65Cond.code.length + 1 = a + 2 from by rw [hcl]] at h
    rw [show Stmt.compile (.seq Sdec (.code d65Inc)) (a + 2) =
      Sdec.compile (a + 2) ++ d65Inc from by
        simp only [Stmt.compile, Stmt.length_compile, Stmt.len]] at h
    exact h
  have hAtSdec : At P (a + 2) (Sdec.compile (a + 2)) := (At.append.mp hbodyAt').1
  have hAtInc : At P (a + 2 + Sdec.len) d65Inc := by
    have h2' := (At.append.mp hbodyAt').2
    have hlen : (Sdec.compile (a + 2)).length = Sdec.len := Stmt.length_compile Sdec (a + 2)
    rwa [hlen] at h2'
  have hjmp : P[a + 2 + Sdec.len + 2]? = some (iJmp a) := by
    have h := hjmpAt
    rw [show a + d65Cond.code.length + 1 + (Stmt.seq Sdec (.code d65Inc)).len
        = a + 2 + Sdec.len + 2 from by rw [hcl]; rfl] at h
    exact h
  have hlt : s.regs r1 < s.regs r2 := by rw [h1, h2]; exact hj
  have htest : Sem P E a (a + 1) s
      (fun k s' => k = 1 ∧ s' = { s with pc := a + 1, regs := Function.update s.regs r7 1 }) := by
    have h := Sem.block P E a d65Cond.code s htestAt (Cond.noBranch_code d65Cond) hpc
    refine Sem.mono h ?_
    rintro k s' ⟨hk, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hk, hcl]
    · rw [zCond_run_true E s hlt hW, hpc]
  have hjz : Sem P E (a + 1) (a + 2)
      { s with pc := a + 1, regs := Function.update s.regs r7 1 }
      (fun k s' => k = 1 ∧ s' = { s with pc := a + 2, regs := Function.update s.regs r7 1 }) := by
    have h0 : ({ s with pc := a + 1, regs := Function.update s.regs r7 1 } : RAMState).regs r7 ≠ 0 := by
      show 1 ≠ 0
      omega
    have hjzAt' : P[a + 1]? = some (iJz d65Cond.test (a + 1 + (Stmt.seq Sdec (.code d65Inc)).len + 2)) := by
      simpa [hcl] using hjzAt
    exact Sem.jz_next P E (a + 1) (a + 1 + (Stmt.seq Sdec (.code d65Inc)).len + 2) d65Cond
      { s with pc := a + 1, regs := Function.update s.regs r7 1 } hjzAt' rfl h0
  have hfirst : Sem P E a (a + 2) s
      (fun k s' => k = 2 ∧ s' = { s with pc := a + 2, regs := Function.update s.regs r7 1 }) := by
    have h := Sem.trans htest hjz
    refine Sem.mono h ?_
    rintro k z ⟨hk, rfl⟩
    exact ⟨by omega, rfl⟩
  set t2 : RAMState := { s with pc := a + 2, regs := Function.update s.regs r7 1 } with ht2
  have h14' : t2.regs 14 = δ := by rw [ht2]; simpa using h14
  have h15' : t2.regs 15 = β := by rw [ht2]; simpa using h15
  have hmem' : ∀ q < wordsOf E.W Ms, t2.mem (β + q) = packMem E.W y q := by
    rw [ht2]; simpa using hmem
  have hIFrame' : ∀ n' mem, I n' mem → ∀ a', a' < γ ∨ γ + ws ≤ a' → mem a' = t2.mem a' := by
    rw [ht2]; simpa using hIFrame
  obtain ⟨kchild, outc, hkchild, hrunC, hpcC, -, -⟩ :=
    hdown P (a + 2) δ β γ hfit hβ hws hγws header control hintMap resultMap listBase table
      count y J t2 hAtSdec rfl hδB hdr h14' h15' hmem' hHint hHintTop hControl hControlTop
      hList hListTop hDisj hIFrame'
  obtain ⟨hregs1, hregs2⟩ := hcnt P (a + 2) t2 outc kchild hAtSdec rfl hrunC hkchild hpcC
  have ht1 : t2.regs 1 = j := by rw [ht2]; simpa using h1
  have ht2r : t2.regs 2 = n := by rw [ht2]; simpa using h2
  have htail : Sem P E (a + 2 + Sdec.len) a outc
      (fun k z => k = 3 ∧ z = ⟨a, Function.update (Function.update outc.regs r7 1) r1
        ((outc.regs 1 + 1) % 2 ^ E.W), outc.mem⟩) :=
    colTail_sem hAtInc hjmp hW outc hpcC
  have hchild : Sem P E (a + 2) (a + 2 + Sdec.len) t2
      (fun k out' => k = kchild ∧ out' = outc) :=
    ⟨rfl, kchild, outc, hrunC, hpcC, rfl, rfl⟩
  obtain ⟨-, k, z, hrun, hpc', hk, hz⟩ := Sem.trans (Sem.trans hfirst hchild) htail
  refine ⟨k, z, ?_, hrun, ?_, ?_, ?_⟩
  · have hkR : (k : ℝ) = 2 + (kchild : ℝ) + 3 := by rw [hk]; push_cast; ring
    rw [hkR]; linarith [hkchild]
  · rw [hz]
  · rw [hz]
    have h1' : outc.regs 1 = j := hregs1.trans ht1
    simp [h1', Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ E.W)]
  · rw [hz]; exact hregs2.trans ht2r

/-! ## 3. The column `StageRun` -/

/-- Weakening a stage's postcondition (local copy; `CRS.stageRun_post` lives in the `CrStage`
bundle, which this file does not import). -/
theorem stageRun_post' {P : Program} {E : RAMEnv} {a b : ℕ} {T : ℝ} {I Q Q' : RAMState → Prop}
    (h : StageRun P E a b T I Q) (hQ : ∀ s, Q s → Q' s) : StageRun P E a b T I Q' := by
  intro s hpc hI
  obtain ⟨k, s', hk, hstep, hb, hQ'⟩ := h s hpc hI
  exact ⟨k, s', hk, hstep, hb, hQ s' hQ'⟩

/-- **The column stage, from `zDColHead` to `zDAsBase`.**  Cost `ℓ · (Tdec + 5) + 2`, i.e.
`ℓ · (T + 2) + 2` with `T = Tdec + 3` the cost of the child *plus* the two-instruction increment
and the jump.  The post is the register shape the loop actually leaves (`r1 = r2 = ℓ`), from which
`fun _ => True` follows.

The hypothesis `hstep` is `ColStep`; `colStep_of_downBlk` discharges it from `DownBlkSemAtW` +
`ColCounter` + the per-head interface facts, and `ZColLayout` supplies all the arithmetic. -/
theorem zColStageRun {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv} {ell Tdec : ℕ}
    (hW : 1 < 2 ^ E.W) (hell : ell < 2 ^ E.W)
    (hstep : ColStep (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (zDColHead Sinit Srow ell) ell ((Tdec : ℝ) + 5)) :
    StageRun (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (zDColHead Sinit Srow ell) (zDAsBase Sinit Srow Sdec ell)
      ((ell : ℝ) * ((Tdec : ℝ) + 5) + 2) (ColIn ell)
      (fun s => s.regs 1 = ell ∧ s.regs 2 = ell) := by
  have h := colLoop_stageRun (Sdec := Sdec)
    (zAt_col_loopD Sinit Srow Sdec Sassem Sres Scr ell) hW (by positivity) hell hstep
  simpa only [zDAsBase] using h

/-- **The same stage with `fun _ => True` as post** — the shape the published `col` field asks for. -/
theorem zColStageRun_true {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv} {ell Tdec : ℕ}
    (hW : 1 < 2 ^ E.W) (hell : ell < 2 ^ E.W)
    (hstep : ColStep (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (zDColHead Sinit Srow ell) ell ((Tdec : ℝ) + 5)) :
    StageRun (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (zDColHead Sinit Srow ell) (zDAsBase Sinit Srow Sdec ell)
      ((ell : ℝ) * ((Tdec : ℝ) + 5) + 2) (ColIn ell) (fun _ => True) :=
  stageRun_post' (zColStageRun hW hell hstep) (fun _ _ => trivial)

end W65
end LinearSetReconciliation327.Main


