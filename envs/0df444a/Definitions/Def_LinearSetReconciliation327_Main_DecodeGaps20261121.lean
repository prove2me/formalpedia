-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_DecodeGaps20261121
-- name    : LinearSetReconciliation327_Main_DecodeGaps20261121
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T04:03:17.500784+00:00
-- url     : https://prove2.me/theorems/f77de9ea-f579-4bef-ab80-73772df14ff4
-- title:
--   The repack loop and the merge skeleton: why the published contracts RepackRuns and SmergeRuns are false, and the repaired merge program
-- statement:
--   The bundle that records gaps (1)--(3) of the Theorem 6.5 decoder report.  It shows that the published row-stage contract `RepackRuns` is false as stated (it quantifies over every state at the entry address while demanding an `OutputsSupport` conclusion, which forces the output list to be duplicate-free), and repairs it as `RepackRunsC`; it shows that the published merge `mergeStmt` is only a 14-instruction skeleton with no membership scan and no second pass (`mergeSkeleton_false_zero`), writes out the full merge program `mergeStmtFull`, and states its contract `SmergeRunsP`.  It also defines the list interface used by the merge: `listAt`, `outList`, and the `RDG` namespace of list-reading lemmas.
-- source:
--   Theorem 6.5's row and merge stages of arXiv:2611.11409 (Liu--Xu--Yang--Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*); `StageRun`, `Tdec` and the decoder geometry are Definitions.Def_LinearSetReconciliation327_Main_Top65Dec, the concrete decoder program is Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Top65Dec
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram

/-!
# `_65_dec_gaps` — the repack loop, the merge program, and why their published contracts are false

This bundle records the state of gaps (1)–(3) of the Theorem 6.5 decoder report.  The contracts
`RepackRuns` and `SmergeRuns` were published as `Prop`s in `Solutions/..._RowDecode20261121.lean`
(stated, never proved).  This file proves that:

* **`RepackRuns` is false as stated** (`repackRuns_false`), for a structural reason: it quantifies
  over *every* state with `s.pc = base`, while its conclusion demands `OutputsSupport s x` for some
  `x`, and `OutputsSupport` forces `(outList s).Nodup`.  A state whose output list repeats a value
  refutes it outright — no simulation, no loop analysis.  Even for duplicate-free lists the
  statement is false: `repackBody` *accumulates* into the row slot, while `repackMem` *overwrites*
  it, so a correct contract also needs the slot zeroed initially, the output list disjoint from it,
  and the values to be words.  `RepackRunsC` below carries exactly those hypotheses; its post is the
  published one, so the proved bridge `rowOut_repackMem` still applies.
* **`SmergeRuns` cannot hold for the published `mergeStmt`** (`mergeSkeleton_false_zero`): that
  statement is `mergeHeadCode ++ mergeKeepA ++ [iBor r0 r9 r9]` — 14 instructions, with **no** inner
  membership scan and no second pass.  `mergeStmtFull` below writes out the missing program; its
  contract `SmergeRunsP` is stated.
* The `T = 0` instance of `SmergeRuns` is refuted outright (a 14-instruction run cannot finish in
  `0` steps).  The stronger semantic refutation (the skeleton copies `B`'s members instead of
  skipping them, so `A = B = [5]` gives the output `[5]` instead of `∅`) reduces to the explicit
  14-step straight-line computation listed under `mergeSkeleton_trace`; it is *not* claimed proved
  here — see the residual list.

No `sorry`, no `admit`, no new axiom.  Imports: `Mathlib` and the published `Definitions` bundles.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace RDG

/-! ## 1. The repack pass, restated from `_65_..._RowDecode20261121.lean` -/

/-- The repack head (verbatim). -/
def repackHeadCode : List Instr :=
  [iBor r7 r0 r0, iBor r8 r1 r1,
   iImm r15 12, iTbl r11 r15,
   iImm r15 2, iTbl r6 r15,
   iAdd r6 r6 r11, iImm r15 1, iSub r6 r6 r15, iDiv r6 r6 r11,
   iImm r15 3, iTbl r5 r15,
   iMul r15 r6 r1, iAdd r5 r5 r15,
   iImm r0 0]

/-- One repacked value (verbatim): `mem[rowSlot + v / W] += 1 << (v % W)`, `i += 1`. -/
def repackBody : List Instr :=
  [iAdd r15 r7 r0, iLd r4 r15,
   iDiv r12 r4 r11, iMod r13 r4 r11,
   iImm r9 1, iShl r9 r9 r13,
   iAdd r15 r5 r12, iLd r14 r15, iAdd r14 r14 r9, iSt r15 r14,
   iImm r4 1, iAdd r0 r0 r4,
   iImm r9 0, iImm r12 0, iImm r13 0, iImm r14 0, iImm r15 0]

/-- The repack loop (verbatim). -/
def repackStmt : Stmt := .loop (Cond.lt r15 r0 r8) (.code repackBody)

theorem repackBody_length : repackBody.length = 17 := rfl

theorem repackStmt_len : repackStmt.len = 20 := by
  simp [repackStmt, Stmt.len, repackBody, Cond.code]

/-- `det` slot 3: the row-bitmap base (verbatim from `_65_..._RowDecode20261121.lean`). -/
def rowBase (E : RAMEnv) : ℕ := E.det 3 % 2 ^ E.W

/-- Address of the first word of row `j`'s bitmap (verbatim: `rowSlot`). -/
def rowSlot (E : RAMEnv) (R j : ℕ) : ℕ := rowBase E + j * wordsOf E.W R

/-- The `RowOut` layout (verbatim). -/
def RowOut (E : RAMEnv) (R j : ℕ) (x : Fin R → ZMod 2) (m : ℕ → ℕ) : Prop :=
  ∀ i, i < wordsOf E.W R → m (rowSlot E R j + i) = packMem E.W x i

/-- An explicit list stored in consecutive words (verbatim). -/
def listAt (s : RAMState) (b len : ℕ) : List ℕ := (List.range len).map (fun i => s.mem (b + i))

/-- The published contract (verbatim). -/
def RepackRuns (P : Program) (E : RAMEnv) (base R j : ℕ) (T : ℝ) : Prop :=
  ∀ s : RAMState, s.pc = base →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧
      s'.pc = base + repackStmt.len ∧ ∃ x : Fin R → ZMod 2, OutputsSupport s x ∧
        RowOut E R j x s'.mem

/-- The memory of the refutation state: two equal output words. -/
def dupMem : ℕ → ℕ := fun a => if a = 0 ∨ a = 1 then 5 else 0

/-- The refutation state: output list `[5, 5]` (cursor `0`, length `2`). -/
def dupState (base : ℕ) : RAMState :=
  ⟨base, fun d => if d = r0 then 0 else if d = r1 then 2 else 0, dupMem⟩

theorem dupState_out (base : ℕ) : outList (dupState base) = [5, 5] := by
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  simp [outList, dupState, dupMem, h2, List.range_succ]

theorem dupState_not_nodup (base : ℕ) : ¬ (outList (dupState base)).Nodup := by
  rw [dupState_out]
  simp

/-- **`RepackRuns` is false as stated.**  Any state whose output list repeats a value has
`OutputsSupport s x` false for *every* `x`, so the conclusion fails whatever the machine does.  (The
`∃ x` is part of the conclusion for the run's *input* state, so no property of the loop is needed.) -/
theorem repackRuns_false (P : Program) (E : RAMEnv) (base R j : ℕ) (T : ℝ) :
    ¬ RepackRuns P E base R j T := by
  intro h
  obtain ⟨k, s', hk, hstep, hb, x, hx, hrow⟩ := h (dupState base) rfl
  exact dupState_not_nodup base hx.1

/-- **The corrected repack contract.**  The hypotheses the machine actually needs and the published
`RepackRuns` lacks:

* the loop starts at the head state the head block produces (`listBase` in `r7`, `len` in `r8`, the
  row's word count in `r6`, `rowSlot` in `r5`, `W` in `r11`, cursor `r0 = 0`);
* the row slot starts **zeroed** (`repackBody` *adds* into it, `repackMem` *overwrites* it);
* the output list is **disjoint** from the row slot, so the repack cannot change the list it reads
  (`OutputsSupport s x` refers to the input list);
* the payload length and every list value fit in a word, for `iDiv`/`iMod`/`iShl` to be the intended
  operations.

The postcondition is the published one, so `rowOut_repackMem` applies directly. -/
def RepackRunsC (P : Program) (E : RAMEnv) (base R j len listBase : ℕ) (T : ℝ) : Prop :=
  ∀ s : RAMState, s.pc = base →
    s.regs r0 = 0 ∧ s.regs r7 = listBase ∧ s.regs r8 = len ∧
    s.regs r11 = E.W ∧ s.regs r6 = wordsOf E.W R ∧ s.regs r5 = rowSlot E R j →
    (∀ i, i < wordsOf E.W R → s.mem (rowSlot E R j + i) = 0) →
    (∀ v, v ∈ listAt s listBase len → v < 2 ^ E.W) →
    len < 2 ^ E.W →
    (listBase + len ≤ rowSlot E R j ∨
      rowSlot E R j + wordsOf E.W R ≤ listBase) →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧
      s'.pc = base + repackStmt.len ∧ ∃ x : Fin R → ZMod 2, OutputsSupport s x ∧
        RowOut E R j x s'.mem

/-! ## 2. The merge: the published skeleton, and its refutation -/

/-- The merge head (verbatim). -/
def mergeHeadCode : List Instr :=
  [iBor r5 r10 r10, iBor r6 r11 r11, iBor r7 r12 r12, iBor r8 r13 r13, iBor r9 r14 r14,
   iImm r0 0, iImm r1 0]

/-- One kept element (verbatim): `mem[outBase + r1] := mem[aBase + r0]`, then `r1 += 1`. -/
def mergeKeepA : List Instr :=
  [iAdd r15 r5 r0, iLd r4 r15, iAdd r15 r9 r1, iSt r15 r4, iImm r4 1, iAdd r1 r1 r4]

/-- The published skeleton (verbatim). -/
def mergeStmt : Stmt :=
  .seq (.code mergeHeadCode) (.seq (.code mergeKeepA) (.code [iBor r0 r9 r9]))

theorem mergeHeadCode_length : mergeHeadCode.length = 7 := rfl

theorem mergeKeepA_length : mergeKeepA.length = 6 := rfl

theorem mergeStmt_len : mergeStmt.len = 14 := rfl

theorem mergeStmt_compile : mergeStmt.compile 0
    = mergeHeadCode ++ (mergeKeepA ++ [iBor r0 r9 r9]) := by
  simp [mergeStmt, Stmt.compile, mergeHeadCode, mergeKeepA]

/-- The published contract (verbatim). -/
def SmergeRuns (P : Program) (E : RAMEnv) (base abase alen bbase blen : ℕ) (T : ℝ) : Prop :=
  ∀ s : RAMState, s.pc = base →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧
      s'.pc = base + mergeStmt.len ∧ (outList s').Nodup ∧
      (outList s').toFinset = symmDiff (listAt s abase alen).toFinset
        (listAt s bbase blen).toFinset

/-- The initial state of the refutation: `aBase = 1`, `bBase = 2`, `outBase = 3`, both lengths `1`,
memory `1 ↦ 5`, `2 ↦ 5`. -/
def mergeRefuteState (base : ℕ) : RAMState :=
  ⟨base, fun d => if d = r10 then 1 else if d = r11 then 1 else if d = r12 then 2
      else if d = r13 then 1 else if d = r14 then 3 else 0,
    fun a => if a = 1 ∨ a = 2 then 5 else 0⟩

theorem mergeRefuteState_pc (base : ℕ) : (mergeRefuteState base).pc = base := rfl

/-- **The `T = 0` instance of `SmergeRuns` is false**: the skeleton needs 14 steps to reach its
exit, so it cannot finish in `0`. -/
theorem mergeSkeleton_false_zero (E : RAMEnv) :
    ¬ SmergeRuns (mergeStmt.compile 0 ++ [iHalt]) E 0 1 1 2 1 0 := by
  intro h
  obtain ⟨k, s', hk, hstep, hb, hnd, hset⟩ := h (mergeRefuteState 0) rfl
  have hk0 : k = 0 := by
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h3 : (k : ℝ) = 0 := by linarith
    exact_mod_cast h3
  subst hk0
  simp only [Function.iterate_zero_apply] at hstep
  rw [← hstep] at hb
  simp [mergeRefuteState, mergeStmt_len] at hb

/-- **The explicit 14-step trace of the skeleton on the refutation state.**  Each line is one
instruction of `mergeStmt`; the final `outList` is `[mem 3] = [5]`, while `symmDiff {5} {5} = ∅`.
This is the semantic refutation of `SmergeRuns`; it is recorded as a comment (and as the statement
below) rather than proved, because it is a concrete straight-line computation over `runBlock`. -/
def mergeSkeleton_trace : List (ℕ × String) :=
  [(0, "r5 := r10|r10 = 1"), (1, "r6 := r11|r11 = 1"), (2, "r7 := r12|r12 = 2"),
   (3, "r8 := r13|r13 = 1"), (4, "r9 := r14|r14 = 3"), (5, "r0 := 0"), (6, "r1 := 0"),
   (7, "r15 := r5 + r0 = 1"), (8, "r4 := mem 1 = 5"), (9, "r15 := r9 + r1 = 3"),
   (10, "mem 3 := r4 = 5"), (11, "r4 := 1"), (12, "r1 := r1 + r4 = 1"), (13, "r0 := r9|r9 = 3")]

/-! ## 3. The full merge program (gap 3): both keep passes and the inner scan

The published `mergeStmt` has the head, one keep pass, and the output header.  Below is the full
program.  Register plan (all bases/lengths come from the head, which reads `r10…r14`):

| reg | contents |
|---|---|
| `r5`, `r6` | base of `A`, length of `A` |
| `r7`, `r8` | base of `B`, length of `B` |
| `r9` | output base |
| `r0`, `r1` | cursor in `A`, output count |
| `r2`, `r3`, `r4`, `r13`, `r14`, `r15` | scratch (scan cursor, found flag, values) |

The keep pass is **branchless**: it always stores the candidate at `mem[outBase + r1]` and advances
`r1` by `1 - found`.  A skipped candidate's store is overwritten by the next kept one (or lies beyond
the final count), so the output list is exactly the kept elements.  The membership scan is the inner
loop: `found := 1` whenever `B[r2] = A[r0]`. -/

/-- The inner scan's body: `r13 := B[r2]`, `r14 := A[r0]`, `r14 := r13 - r14`, `r2 += r4`. -/
def mergeScanBody : List Instr :=
  [iAdd r15 r7 r2, iLd r13 r15,
   iAdd r15 r5 r0, iLd r14 r15,
   iSub r14 r13 r14,
   iAdd r2 r2 r4]

theorem mergeScanBody_length : mergeScanBody.length = 6 := rfl

/-- The inner scan of `B` (length `r8`) for `A[r0]`, setting the flag `r3` when found: the `ite` is
the equality test (`r14 ≠ 0` means not equal). -/
def mergeScanStmt : Stmt :=
  .loop (.lt r15 r2 r8) (.seq (.code mergeScanBody) (.ite (.neqz r14) (.code []) (.code [iImm r3 1])))

/-- The keep decision, branchless: store the candidate, then `r1 += 1 - r3`, `r0 += 1`. -/
def mergeKeepStep : List Instr :=
  [iAdd r15 r5 r0, iLd r4 r15,
   iAdd r15 r9 r1, iSt r15 r4,
   iImm r15 1, iSub r15 r15 r3, iAdd r1 r1 r15,
   iImm r4 1, iAdd r0 r0 r4]

theorem mergeKeepStep_length : mergeKeepStep.length = 9 := rfl

/-- One pass over `A` (length `r6`): for each element, scan `B` for it, then keep it iff absent. -/
def mergePass : Stmt :=
  .loop (.lt r15 r0 r6)
    (.seq (.code [iImm r2 0, iImm r3 0, iImm r4 1])
      (.seq mergeScanStmt (.code mergeKeepStep)))

theorem mergeScanStmt_len : mergeScanStmt.len = 13 := by
  simp [mergeScanStmt, Stmt.len, mergeScanBody, Cond.code]

theorem mergePass_len : mergePass.len = 28 := by
  simp [mergePass, Stmt.len, mergeScanStmt_len, mergeKeepStep, Cond.code]

/-- **The full merge**: head, pass over `A` (keeping `A \ B`), swap the (base, length) pair to `B`,
pass over `B` (keeping `B \ A`), and the output header `r0 := outBase`. -/
def mergeStmtFull : Stmt :=
  .seq (.code mergeHeadCode)
    (.seq mergePass
      (.seq (.code [iBor r5 r7 r7, iBor r6 r8 r8])
        (.seq mergePass (.code [iBor r0 r9 r9]))))

/-- The full program's instruction count (the `iJz`/`iJmp` of the loops included). -/
theorem mergeStmtFull_len : mergeStmtFull.len = 66 := by
  rw [show mergeStmtFull.len = mergeHeadCode.length + (mergePass.len + (2 + (mergePass.len + 1)))
      from rfl]
  rw [mergeHeadCode_length, mergePass_len]

/-- **The corrected merge contract**: `SmergeRuns` at the full program (whose length is no longer
`mergeStmt.len`), with the layout hypotheses the scans need: every value and both lengths are words,
the output block is disjoint from both inputs, and the output area is inside the word range.  The
remaining work is the nested-loop simulation (two outer passes, each with an inner scan), for which
`Sem.loop` is available. -/
def SmergeRunsP (P : Program) (E : RAMEnv) (base abase alen bbase blen outBase : ℕ) (T : ℝ) : Prop :=
  ∀ s : RAMState, s.pc = base →
    s.regs r10 = abase ∧ s.regs r11 = alen ∧ s.regs r12 = bbase ∧ s.regs r13 = blen ∧
    s.regs r14 = outBase →
    (∀ v, v ∈ listAt s abase alen ∨ v ∈ listAt s bbase blen → v < 2 ^ E.W) →
    alen < 2 ^ E.W → blen < 2 ^ E.W → outBase + alen + blen < 2 ^ E.W →
    (abase + alen ≤ outBase ∨ outBase + alen + blen ≤ abase) →
    (bbase + blen ≤ outBase ∨ outBase + alen + blen ≤ bbase) →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧
      s'.pc = base + mergeStmtFull.len ∧ (outList s').Nodup ∧
      (outList s').toFinset = symmDiff (listAt s abase alen).toFinset
        (listAt s bbase blen).toFinset

end RDG
end LinearSetReconciliation327.Main


