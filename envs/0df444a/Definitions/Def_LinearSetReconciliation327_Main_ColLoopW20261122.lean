-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_ColLoopW20261122
-- name    : LinearSetReconciliation327_Main_ColLoopW20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T08:35:41.782851+00:00
-- url     : https://prove2.me/theorems/f4eb7e4e-e370-45e6-92df-25b14fad2f52
-- title:
--   The column loop over the wrapper: `zColStageRun_wrap`, cost `ell * (Tdec + 18) + 2`
-- statement:
--   Lifts the per-child wrapper to the whole column loop: `cwIter` is one iteration (test, `jz`, wrapper, `d65Inc`, `jmp`) at cost `Tdec + 18`, preserving every child payload `[beta0 + r*ms, beta0 + (r+1)*ms)`; `cwInv`/`cwLoop` are the counted loop with the payload layout as invariant; and `zColStageRun_wrap` is the column `StageRun` for the wrapper program, from `zDColHead` to `zDAsBase`, cost `ell * (Tdec + 18) + 2`, with only `DownBlkSemAtW` and `Sdec` as hypotheses.  The child is instantiated at `I := fun _ _ => False`, which makes the `I`-frame premise vacuous — the natural instance, since the column stage maintains no invariant of its own.  Axiom-clean; local `cpl` 6 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's column stage and Theorem 5.1's decoder (the two-window `DownBlkSemAtW` contract).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_ColWrap20261122

/-!
# `ColLoopW` — the column loop over the wrapper

`ColWrap` proved the per-child `save / setup / restore` run.  This bundle lifts it to the loop:

* `cwIter` — one iteration (test, `jz`, wrapper, `d65Inc`, `jmp`), cost `Tdec + 18`, preserving
  **every** child payload `[β0 + r·ms, β0 + (r+1)·ms)`, `r < ell`;
* `cwInv` / `cwLoop` — the counted loop with the payload layout as its invariant;
* `zColStageRun_wrap` — the column `StageRun` for the wrapper program, with the payload layout as
  the pre and only `DownBlkSemAtW` (at `I := fun _ _ => False`) and `Sdec` as hypotheses.

The `I := False` instantiation is what removes the frame obstruction isolated in `ColWrap`: the
`I`-frame premise becomes vacuous, so the wrapper's two scratch cells need no treatment.  The
column stage's post is `fun _ => True`; it maintains no invariant of its own, so this instance is
the natural one for 6.5's `col` field.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace W65C

open RSD

/-! ## 1. The payload invariant -/

/-- The column loop's invariant: the two counters plus the rowwise payload layout of all `ell`
children. -/
def cwInv (E : RAMEnv) (ell Ms : ℕ) (y : Fin Ms → ZMod 2) (β0 ms j : ℕ)
    (s : RAMState) : Prop :=
  s.regs 1 = j ∧ s.regs 2 = ell ∧
    ∀ r < ell, ∀ q < wordsOf E.W Ms, s.mem (β0 + r * ms + q) = packMem E.W y q

theorem cwInv_regs1 {E ell Ms y β0 ms j s} (h : cwInv E ell Ms y β0 ms j s) :
    s.regs 1 = j := h.1

theorem cwInv_regs2 {E ell Ms y β0 ms j s} (h : cwInv E ell Ms y β0 ms j s) :
    s.regs 2 = ell := h.2.1

theorem cwInv_mem {E ell Ms y β0 ms j s} (h : cwInv E ell Ms y β0 ms j s)
    {r : ℕ} (hr : r < ell) {q : ℕ} (hq : q < wordsOf E.W Ms) :
    s.mem (β0 + r * ms + q) = packMem E.W y q := h.2.2 r hr q hq

/-! ## 2. One iteration -/

/-- **One iteration of the column loop over the wrapper.**  From a head with `r1 = j`, `r2 = ell`,
the payload of child `j` at `β0 + j·ms`, and the payloads of all children in place, the test, the
`jz`, the wrapper, `d65Inc` and the trailing `jmp` return to the head with `r1 = j + 1`,
`r2 = ell`, and every payload unchanged.  Cost `Tdec + 18`. -/
theorem cwIter {P : Program} {E : RAMEnv} {a ell : ℕ} {Tdec : ℝ} {Sdec : Stmt}
    {Bw ms ws N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    {δ β0 γ : ℕ} {j : ℕ} {s : RAMState}
    {header control hintMap resultMap listBase table count : ℕ}
    {y : Fin Ms → ZMod 2} {J : List ℕ}
    (hdown : DownBlkSemAtW Sdec E Tdec Bw ms ws (fun _ _ => False) Hs)
    (hAt : At P a (Stmt.compile (Stmt.loop d65Cond
      (.seq (cwWrap Sdec δ β0 ms γ ws) (.code d65Inc))) a))
    (hW : 1 < 2 ^ E.W) (hell : ell < 2 ^ E.W) (hj : j < ell)
    (hpc : s.pc = a) (h1 : s.regs 1 = j) (h2 : s.regs 2 = ell)
    (hfit : wordsOf E.W Ms ≤ ms) (hβtop : β0 + j * ms + ms ≤ 2 ^ E.W)
    (hpayTop : β0 + ell * ms ≤ γ)
    (hws : ws ≤ 2 ^ E.W) (hγws : γ + ws ≤ 2 ^ E.W) (hcell1 : γ + ws + 1 < 2 ^ E.W)
    (hδ : δ + Bw ≤ 2 ^ E.W) (hδW : δ < 2 ^ E.W) (hmsW : ms < 2 ^ E.W)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hmem : ∀ q < wordsOf E.W Ms, s.mem (β0 + j * ms + q) = packMem E.W y q)
    (hHint : γ ≤ hintMap) (hHintTop : hintMap + N < γ + ws)
    (hControl : γ ≤ control) (hControlTop : control + 4 ≤ γ + ws)
    (hList : γ ≤ listBase) (hListTop : listBase + N ≤ γ + ws) :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ Tdec + 18 ∧ (step P E)^[k] s = s' ∧
      s'.pc = a ∧ s'.regs 1 = j + 1 ∧ s'.regs 2 = ell ∧
      (∀ r < ell, ∀ q < wordsOf E.W Ms,
        s'.mem (β0 + r * ms + q) = s.mem (β0 + r * ms + q)) := by
  have hcl : d65Cond.code.length = 1 := rfl
  obtain ⟨htestAt, hjzAt, hbodyAt, hjmpAt⟩ := at_loop hAt
  have hbodyAt' : At P (a + 2)
      (Stmt.compile (.seq (cwWrap Sdec δ β0 ms γ ws) (.code d65Inc)) (a + 2)) := by
    have h := hbodyAt
    rw [show a + d65Cond.code.length + 1 = a + 2 from by rw [hcl]] at h
    exact h
  obtain ⟨hAtWrap, hAtInc0⟩ := At.append.mp hbodyAt'
  have hAtInc : At P (a + 2 + (cwWrap Sdec δ β0 ms γ ws).len) d65Inc := by
    have h := hAtInc0
    rw [Stmt.length_compile] at h
    exact h
  have hjmp : P[a + 2 + (cwWrap Sdec δ β0 ms γ ws).len + 2]? = some (iJmp a) := by
    have h := hjmpAt
    simp only [hcl, Stmt.len, d65Inc] at h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
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
    have hjzAt' : P[a + 1]? = some (iJz d65Cond.test
        (a + 1 + (Stmt.seq (cwWrap Sdec δ β0 ms γ ws) (.code d65Inc)).len + 2)) := by
      simpa [hcl] using hjzAt
    exact Sem.jz_next P E (a + 1)
      (a + 1 + (Stmt.seq (cwWrap Sdec δ β0 ms γ ws) (.code d65Inc)).len + 2) d65Cond
      { s with pc := a + 1, regs := Function.update s.regs r7 1 } hjzAt' rfl h0
  have hfirst : Sem P E a (a + 2) s
      (fun k s' => k = 2 ∧ s' = { s with pc := a + 2, regs := Function.update s.regs r7 1 }) := by
    have h := Sem.trans htest hjz
    refine Sem.mono h ?_
    rintro k z ⟨hk, rfl⟩
    exact ⟨by omega, rfl⟩
  set t2 : RAMState := { s with pc := a + 2, regs := Function.update s.regs r7 1 } with ht2
  have ht2r1 : t2.regs 1 = j := by rw [ht2]; simpa using h1
  have ht2r2 : t2.regs 2 = ell := by rw [ht2]; simpa using h2
  have ht2mem : t2.mem = s.mem := by rw [ht2]
  have hmem2 : ∀ q < wordsOf E.W Ms, t2.mem (β0 + j * ms + q) = packMem E.W y q := by
    intro q hq; rw [ht2mem]; exact hmem q hq
  have hβj : β0 + j * ms + ms ≤ γ := by
    have h1' : (j + 1) * ms ≤ ell * ms := Nat.mul_le_mul_right ms (by omega)
    have h2' : β0 + j * ms + ms = β0 + (j + 1) * ms := by ring
    rw [h2']; omega
  obtain ⟨kc, s2, hkc, hrun2, hpc2, hr2a, hr2b, hframe2⟩ :=
    cwRun (P := P) (E := E) (a := a + 2) (Tdec := Tdec) (Sdec := Sdec)
      (Bw := Bw) (ms := ms) (ws := ws) (N := N) (Ms := Ms)
      (I := fun _ _ => False) (Hs := Hs) (δ := δ) (β0 := β0) (γ := γ) (j := j) (n := ell)
      (s := t2) (header := header) (control := control) (hintMap := hintMap)
      (resultMap := resultMap) (listBase := listBase) (table := table) (count := count)
      (y := y) (J := J)
      hdown hAtWrap hW hell hj rfl ht2r1 ht2r2 hfit hβtop hβj hws hγws hcell1 hδ hδW hmsW
      hdr hmem2 hHint hHintTop hControl hControlTop hList hListTop
      (by intro n' mem h; exact h.elim) (by intro n' mem h; exact h.elim)
  have hpc2' : s2.pc = a + 2 + (cwWrap Sdec δ β0 ms γ ws).len := hpc2
  have htail : Sem P E (a + 2 + (cwWrap Sdec δ β0 ms γ ws).len) a s2
      (fun k z => k = 3 ∧ z = ⟨a, Function.update (Function.update s2.regs r7 1) r1
        ((s2.regs 1 + 1) % 2 ^ E.W), s2.mem⟩) :=
    W65.colTail_sem (P := P) (E := E) (base := a + 2) (a := a)
      (Sdec := cwWrap Sdec δ β0 ms γ ws) hAtInc hjmp hW s2 hpc2'
  have hchild : Sem P E (a + 2) (a + 2 + (cwWrap Sdec δ β0 ms γ ws).len) t2
      (fun k out' => k = kc ∧ out' = s2) := ⟨rfl, kc, s2, hrun2, hpc2', rfl, rfl⟩
  obtain ⟨-, k, z, hrun, hpc', hk, hz⟩ := Sem.trans (Sem.trans hfirst hchild) htail
  refine ⟨k, z, ?_, hrun, ?_, ?_, ?_, ?_⟩
  · have hkR : (k : ℝ) = 2 + (kc : ℝ) + 3 := by rw [hk]; push_cast; ring
    rw [hkR]; linarith
  · rw [hz]
  · rw [hz]
    have h1' : s2.regs 1 = j := by simpa [ht2r1] using hr2a
    simp [h1', Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ E.W)]
  · rw [hz]; simpa [ht2r2] using hr2b
  · intro r hr q hq
    rw [hz]
    have hqms : q < ms := lt_of_lt_of_le hq hfit
    have hr1 : r + 1 ≤ ell := by omega
    have hmul : (r + 1) * ms ≤ ell * ms := Nat.mul_le_mul_right ms hr1
    have heq : β0 + r * ms + q < β0 + (r + 1) * ms := by
      have hrm : r * ms + ms = (r + 1) * ms := by ring
      omega
    have hlt : β0 + r * ms + q < γ := by omega
    exact hframe2 (β0 + r * ms + q) hlt

/-! ## 3. The counted loop -/

/-- **The column loop with the payload invariant.**  From `cwInv … 0` at `a`, `ell` iterations of
`cwIter` plus the failing test reach `a + (topLoop …).len` with `r1 = r2 = ell`, at cost
`ell · (Tdec + 18) + 2`. -/
theorem cwLoop {P : Program} {E : RAMEnv} {a ell : ℕ} {Tdec : ℝ} {Sdec : Stmt}
    {Bw ms ws N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    {δ β0 γ : ℕ} {header control hintMap resultMap listBase table count : ℕ}
    {y : Fin Ms → ZMod 2} {J : List ℕ}
    (hAt : At P a (Stmt.compile (Stmt.loop d65Cond
      (.seq (cwWrap Sdec δ β0 ms γ ws) (.code d65Inc))) a))
    (hW : 1 < 2 ^ E.W) (hT : 0 ≤ Tdec + 18) (hell : ell < 2 ^ E.W)
    (hiter : ∀ (j : ℕ) (s : RAMState), j < ell → s.pc = a →
      cwInv E ell Ms y β0 ms j s →
      ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ Tdec + 18 ∧ (step P E)^[k] s = s' ∧
        s'.pc = a ∧ s'.regs 1 = j + 1 ∧ s'.regs 2 = ell ∧
        (∀ r < ell, ∀ q < wordsOf E.W Ms,
          s'.mem (β0 + r * ms + q) = s.mem (β0 + r * ms + q))) :
    StageRun P E a (a + (topLoop (cwWrap Sdec δ β0 ms γ ws)).len)
      ((ell : ℝ) * (Tdec + 18) + 2) (cwInv E ell Ms y β0 ms 0)
      (fun s => s.regs 1 = ell ∧ s.regs 2 = ell) := by
  have hcl : d65Cond.code.length = 1 := rfl
  have hbl : (Stmt.seq (cwWrap Sdec δ β0 ms γ ws) (.code d65Inc)).len
      = (cwWrap Sdec δ β0 ms γ ws).len + 2 := rfl
  have hlooplen : (topLoop (cwWrap Sdec δ β0 ms γ ws)).len
      = (cwWrap Sdec δ β0 ms γ ws).len + 5 := by
    simp [topLoop, Stmt.len, hcl, d65Inc]
    omega
  have hexit : ∀ s : RAMState, s.pc = a → cwInv E ell Ms y β0 ms ell s →
      ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ 2 ∧ (step P E)^[k] s = s' ∧
        s'.pc = a + (topLoop (cwWrap Sdec δ β0 ms γ ws)).len ∧
        s'.regs 1 = ell ∧ s'.regs 2 = ell := by
    intro s hpc hI
    have hstop : ¬ d65Cond.eval s := by
      simp only [d65Cond, Cond.eval, hI.1, hI.2.1]
      omega
    obtain ⟨-, k, s', hstep', hpc', hQ⟩ := Sem.loopExit P E a d65Cond
      (.seq (cwWrap Sdec δ β0 ms γ ws) (.code d65Inc)) s hAt hW hpc hstop
    refine ⟨k, s', ?_, hstep', ?_, ?_, ?_⟩
    · rw [hQ.1, hcl]; norm_num
    · rw [hpc', hcl, hbl, hlooplen]; omega
    · rw [hQ.2]; exact (zCond_regs_pres E s).1.trans hI.1
    · rw [hQ.2]; exact (zCond_regs_pres E s).2.trans hI.2.1
  have key : ∀ m : ℕ, m ≤ ell → ∀ s : RAMState, s.pc = a →
      cwInv E ell Ms y β0 ms (ell - m) s →
      ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ (m : ℝ) * (Tdec + 18) + 2 ∧
        (step P E)^[k] s = s' ∧ s'.pc = a + (topLoop (cwWrap Sdec δ β0 ms γ ws)).len ∧
        s'.regs 1 = ell ∧ s'.regs 2 = ell := by
    intro m
    induction m with
    | zero =>
        intro _ s hpc hI
        have hI' : cwInv E ell Ms y β0 ms ell s := by
          simpa using hI
        simpa using hexit s hpc hI'
    | succ m ih =>
        intro hm s hpc hI
        have hmn : m ≤ ell := by omega
        have hj : ell - (m + 1) < ell := by omega
        obtain ⟨k1, s1, hk1, hrun1, hpc1, hregs1, hregs2, hframe⟩ :=
          hiter (ell - (m + 1)) s hj hpc hI
        have hI1 : cwInv E ell Ms y β0 ms (ell - m) s1 := by
          refine ⟨by omega, hregs2, ?_⟩
          intro r hr q hq
          rw [hframe r hr q hq]
          exact cwInv_mem hI hr hq
        obtain ⟨k2, s2, hk2, hrun2, hpc2, h1f, h2f⟩ := ih hmn s1 hpc1 hI1
        refine ⟨k1 + k2, s2, ?_, ?_, hpc2, h1f, h2f⟩
        · push_cast
          nlinarith
        · rw [Nat.add_comm, Function.iterate_add_apply, hrun1, hrun2]
  intro s hpc hI
  exact key ell (le_refl ell) s hpc (by simpa using hI)

/-! ## 4. The column `StageRun` for the wrapper -/

/-- **The column stage over the wrapper.**  `zProgDecOfTop` with the wrapper as its child: from
`zDColHead` with the payload layout in place, `ell` wrapped child calls reach `zDAsBase` at cost
`ell · (Tdec + 18) + 2`, with `r1 = r2 = ell`.  Only `DownBlkSemAtW` (at the empty invariant) and
`Sdec` are hypotheses. -/
theorem zColStageRun_wrap {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {ell : ℕ} {Tdec : ℝ} {Bw ms ws N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    {δ β0 γ : ℕ} {header control hintMap resultMap listBase table count : ℕ}
    {y : Fin Ms → ZMod 2} {J : List ℕ}
    (hdown : DownBlkSemAtW Sdec E Tdec Bw ms ws (fun _ _ => False) Hs)
    (hW : 1 < 2 ^ E.W) (hT : 0 ≤ Tdec) (hell : ell < 2 ^ E.W) (hfit : wordsOf E.W Ms ≤ ms)
    (hβtop : β0 + ell * ms ≤ 2 ^ E.W) (hpayTop : β0 + ell * ms ≤ γ)
    (hws : ws ≤ 2 ^ E.W) (hγws : γ + ws ≤ 2 ^ E.W) (hcell1 : γ + ws + 1 < 2 ^ E.W)
    (hδ : δ + Bw ≤ 2 ^ E.W) (hδW : δ < 2 ^ E.W) (hmsW : ms < 2 ^ E.W)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hHint : γ ≤ hintMap) (hHintTop : hintMap + N < γ + ws)
    (hControl : γ ≤ control) (hControlTop : control + 4 ≤ γ + ws)
    (hList : γ ≤ listBase) (hListTop : listBase + N ≤ γ + ws) :
    StageRun (zProgDecOfTop Sinit Srow (cwWrap Sdec δ β0 ms γ ws) Sassem Sres Scr ell) E
      (zDColHead Sinit Srow ell) (zDAsBase Sinit Srow (cwWrap Sdec δ β0 ms γ ws) ell)
      ((ell : ℝ) * (Tdec + 18) + 2) (cwInv E ell Ms y β0 ms 0)
      (fun s => s.regs 1 = ell ∧ s.regs 2 = ell) := by
  have hAt := zAt_col_loopD Sinit Srow (cwWrap Sdec δ β0 ms γ ws) Sassem Sres Scr ell
  have hloop := cwLoop (P := zProgDecOfTop Sinit Srow (cwWrap Sdec δ β0 ms γ ws) Sassem Sres Scr ell)
    (E := E) (a := zDColHead Sinit Srow ell) (ell := ell) (Tdec := Tdec)
    (Sdec := Sdec) (Bw := Bw) (ms := ms) (ws := ws) (N := N) (Ms := Ms) (Hs := Hs)
    (δ := δ) (β0 := β0) (γ := γ) (header := header) (control := control)
    (hintMap := hintMap) (resultMap := resultMap) (listBase := listBase) (table := table)
    (count := count) (y := y) (J := J) hAt hW (by linarith) hell ?_
  · simpa only [zDAsBase] using hloop
  · intro j s hj hpc hinv
    have hβj : β0 + j * ms + ms ≤ 2 ^ E.W := by
      have hmul : (j + 1) * ms ≤ ell * ms := Nat.mul_le_mul_right ms (by omega)
      have heq : β0 + j * ms + ms = β0 + (j + 1) * ms := by ring
      omega
    exact cwIter (P := zProgDecOfTop Sinit Srow (cwWrap Sdec δ β0 ms γ ws) Sassem Sres Scr ell)
      (E := E) (a := zDColHead Sinit Srow ell) (ell := ell) (Tdec := Tdec)
      (Sdec := Sdec) (Bw := Bw) (ms := ms) (ws := ws) (N := N) (Ms := Ms) (Hs := Hs)
      (δ := δ) (β0 := β0) (γ := γ) (j := j) (s := s) (header := header)
      (control := control) (hintMap := hintMap) (resultMap := resultMap)
      (listBase := listBase) (table := table) (count := count) (y := y) (J := J)
      hdown hAt hW hell hj hpc hinv.1 hinv.2.1 hfit hβj hpayTop hws hγws hcell1
      hδ hδW hmsW hdr (fun q hq => hinv.2.2 j hj q hq) hHint hHintTop hControl hControlTop
      hList hListTop

/-- **The column invariant is inhabited non-degenerately**: `ell = 1`, `Ms = 8`, `y = winY ≠ 0`,
`β0 = 0`, `ms = 1`. -/
theorem cwInv_nonvacuous :
    cwInv winEnv 1 8 winY 0 1 0
      ⟨0, (fun i => if i = r1 then 0 else if i = r2 then 1 else 0),
        (fun a => if a < 1 then packMem 8 winY a else 0)⟩ := by
  refine ⟨rfl, rfl, ?_⟩
  intro r hr q hq
  have hr0 : r = 0 := by omega
  subst hr0
  have hq0 : q = 0 := by
    have h : wordsOf winEnv.W 8 = 1 := by decide
    omega
  subst hq0
  rfl

end W65C
end LinearSetReconciliation327.Main


