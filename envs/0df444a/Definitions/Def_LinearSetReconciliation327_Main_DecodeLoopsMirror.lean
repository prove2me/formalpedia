-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_DecodeLoopsMirror
-- name    : LinearSetReconciliation327_Main_DecodeLoopsMirror
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T09:36:17.268011+00:00
-- url     : https://prove2.me/theorems/287e0e95-7b16-4dd1-9ac9-f65d9dc893e1
-- title:
--   Row-chain mirror: the decode loops re-hosted on the `DecoderLemmas` side
-- statement:
--   A byte-identical re-host of the published `…_DecodeLoopsPay20261122` node with only the `import` lines replaced (`DecodeGapsDet`→`DecodeGaps20261121`, `DecodeCloseDet`→`DecodeClose20261121`, `RowDecodePay`→`RowDecode20261121`), so its content can be loaded in an environment that also contains `DecoderLemmas`, `CrField`, `ColWire` and `HintDecBase51At`.  Every declaration span is copied verbatim from the published source.  Definitions and proved lemmas only; no `sorry`, no new axiom; local `cpl` 8 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder); the project's verified row-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecodeGaps20261121
import Definitions.Def_LinearSetReconciliation327_Main_DecodeClose20261121
import Definitions.Def_LinearSetReconciliation327_Main_RowDecode20261121
/-!
# `_65_dec_loops` — the three iteration arguments of the Theorem 6.5 decoder

This bundle finishes the loop simulations that the published contracts of
`Solutions/..._RowDecode20261121.lean` left as `Prop`s, and records what is *not* provable
because the contract (or the program) is false.

What is here:

1. the straight-line rule `straightline_run`, and the **machine-checked 14-step trace** of the
   published merge skeleton: `mergeSkeleton_false` refutes `SmergeRuns` for *every* time bound;
2. the repack loop's `List.take`-partial-sum simulation: `repackLoop_sem`, the endpoint
   `repackLoopMem_end = RDec.repackMem`, the repaired contract `RepackRunsS` (`repackRunsS_proved`),
   a full `StageRun` for the row stage (`repackStageRun`), a non-degenerate inhabitant
   (`repackRunsS_inhabited`), and a machine-checked refutation of the published contract
   (`repackRunsC_false`);
3. the merge: `SmergeRunsP` is **false** — the published "swap" does not swap (`mergeSwap_not_swap`),
   the cursor is not reset, and the contract has no `Nodup` hypothesis — so the nested-loop
   simulation it asks for would be a simulation of the wrong program; §5 records the
   machine-checked part.

No `sorry`, no `admit`, no new axiom.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace RDL

open RDG

/-! ## 1. The straight-line rule

`Sem.block` already says that a branch-free block runs as `runBlock` in exactly its length many
steps.  The form needed for a machine-checked trace also records that the exit state is *halted*
and therefore frozen, which is what turns a concrete 14-step computation into a refutation for
*every* time bound `T` (not only `T < 14`). -/

/-- A halted state does not move. -/
theorem step_halted {P : Program} {E : RAMEnv} {s : RAMState} (h : P[s.pc]? = some .halt) :
    step P E s = s := by
  unfold step
  rw [h]

/-- A halted state is fixed by every iterate. -/
theorem step_iterate_halted {P : Program} {E : RAMEnv} {s : RAMState}
    (h : P[s.pc]? = some .halt) : ∀ k : ℕ, (step P E)^[k] s = s := by
  intro k
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (by rw [ih]; exact step_halted h : step P E ((step P E)^[n] s) = s)

/-- **The straight-line rule.**  Over branch-free code of length `l.length` placed at `pc` and
followed by a `halt`, the machine reaches `runBlock l E s` in exactly `l.length` steps, is halted
there, and never moves again. -/
theorem straightline_run {P : Program} {E : RAMEnv} {pc : ℕ} {l : List Instr} {s : RAMState}
    (hAt : At P pc l) (hno : NoBranch l) (hhalt : P[pc + l.length]? = some .halt)
    (hpc : s.pc = pc) :
    ∃ k : ℕ, k = l.length ∧ (step P E)^[k] s = runBlock l E s ∧
      (runBlock l E s).pc = pc + l.length ∧
      (∀ k' ≥ k, (step P E)^[k'] s = runBlock l E s) := by
  have hrun : (step P E)^[l.length] s = runBlock l E s :=
    iterate_runBlock_of_at P E l s (hpc ▸ hAt) hno
  have hpc' : (runBlock l E s).pc = pc + l.length := by
    rw [runBlock_pc l E s hno, hpc]
  have hhalt' : P[(runBlock l E s).pc]? = some .halt := by rw [hpc']; exact hhalt
  refine ⟨l.length, rfl, hrun, hpc', ?_⟩
  intro k' hk'
  rw [show k' = (k' - l.length) + l.length from by omega, Function.iterate_add_apply, hrun]
  exact step_iterate_halted hhalt' (k' - l.length)

/-- A prefix of branch-free code is branch-free. -/
theorem noBranch_take (l : List Instr) (k : ℕ) (h : NoBranch l) : NoBranch (l.take k) := by
  induction l generalizing k with
  | nil => simp
  | cons i tl ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [List.take_succ_cons]
          exact ⟨h.1, ih k h.2⟩

/-- `At` restricts to prefixes. -/
theorem At.take' {P : Program} {a : ℕ} {l : List Instr} (h : At P a l) (n : ℕ) :
    At P a (l.take n) := by
  intro r hr
  have hlt : r < l.length := by
    rw [List.length_take] at hr
    omega
  have hrn : r < n := by
    rw [List.length_take] at hr
    omega
  rw [List.getElem?_take, if_pos hrn]
  exact h r hlt

/-! ## 2. The published merge skeleton, traced

`mergeStmt = head(7) ++ keep(6) ++ header(1)` is `14` instructions with no branch.  On the
refutation state of `RDG.mergeRefuteState` it copies `B`'s single member `5` into the output
instead of skipping it, leaving the output list `[5]` while the symmetric difference is `∅`. -/

/-- The published skeleton with the terminal `halt`. -/
def mergeProg : Program := mergeStmt.compile 0 ++ [iHalt]

/-- The skeleton occupies `[0, 14)`. -/
theorem mergeProg_at : At mergeProg 0 (mergeStmt.compile 0) := by
  intro r hr
  simp only [mergeProg]
  rw [List.getElem?_append_left]
  · simp
  · simpa using hr

theorem mergeProg_length : (mergeStmt.compile 0).length = 14 := by
  rw [Stmt.length_compile, mergeStmt_len]

theorem mergeProg_halt : mergeProg[0 + (mergeStmt.compile 0).length]? = some iHalt := by
  change (mergeStmt.compile 0 ++ [iHalt])[0 + (mergeStmt.compile 0).length]? = some iHalt
  rw [Nat.zero_add, List.getElem?_append_right (le_refl _)]
  simp

theorem mergeProg_noBranch : NoBranch (mergeStmt.compile 0) := by
  rw [mergeStmt_compile]
  simp [mergeHeadCode, mergeKeepA]

/-- The exact state after the skeleton's 14 instructions on `RDG.mergeRefuteState`. -/
def mergeSkelFinal : RAMState where
  pc := 14
  regs := fun d =>
    if d = r0 then 3 else if d = r1 then 1 else if d = r4 then 1 else if d = r5 then 1 else
      if d = r6 then 1 else if d = r7 then 2 else if d = r8 then 1 else if d = r9 then 3 else
        if d = r10 then 1 else if d = r11 then 1 else if d = r12 then 2 else
          if d = r13 then 1 else if d = r14 then 3 else if d = r15 then 3 else 0
  mem := Function.update (fun a => if a = 1 ∨ a = 2 then 5 else 0) 3 5

theorem mergeSkelFinal_pc : mergeSkelFinal.pc = 14 := rfl

theorem mergeSkelFinal_out : outList mergeSkelFinal = [5] := by
  simp [outList, mergeSkelFinal]

/-- **The 14-instruction run, computed.**  Every line of `RDG.mergeSkeleton_trace` is checked
here at once: the machine ends at `pc = 14` with `r0 = 3`, `r1 = 1` and `mem 3 = 5`. -/
theorem mergeSkeleton_runBlock (E : RAMEnv) (hW : 3 ≤ E.W) :
    runBlock (mergeStmt.compile 0) E (mergeRefuteState 0) = mergeSkelFinal := by
  have hW8 : (8 : ℕ) ≤ 2 ^ E.W := by
    have h : (2 : ℕ) ^ 3 ≤ 2 ^ E.W := Nat.pow_le_pow_right (by norm_num) hW
    simpa using h
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt (by omega)
  have h2' : (2 : ℕ) % 2 ^ E.W = 2 := Nat.mod_eq_of_lt (by omega)
  have h3' : (3 : ℕ) % 2 ^ E.W = 3 := Nat.mod_eq_of_lt (by omega)
  have h5' : (5 : ℕ) % 2 ^ E.W = 5 := Nat.mod_eq_of_lt (by omega)
  rw [mergeStmt_compile, ← List.append_assoc, runBlock_append, runBlock_append]
  apply ramState_eq_of
  · simp only [mergeHeadCode, mergeKeepA, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
      Function.update_self, Function.update_of_ne, Fin.reduceEq, ne_eq, not_false_eq_true,
      mergeRefuteState, mergeSkelFinal, h1, h2', h3', h5', Nat.zero_mod, Nat.add_right_cancel_iff,
      Nat.add_left_cancel_iff, ↓reduceIte, Nat.or_self, true_or, or_true, eq_self_iff_true, Nat.mod_mod, Nat.mod_self, Nat.add_zero,
      Nat.zero_add] <;> omega
  · simp only [mergeHeadCode, mergeKeepA, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
      Function.update_self, Function.update_of_ne, Fin.reduceEq, ne_eq, not_false_eq_true,
      mergeRefuteState, mergeSkelFinal, h1, h2', h3', h5', Nat.zero_mod, Nat.add_mod, Nat.mod_mod,
      ↓reduceIte, Nat.or_self, true_or, or_true, eq_self_iff_true, Nat.mod_self, Nat.add_zero,
      Nat.zero_add]
  · intro d
    fin_cases d <;>
      simp only [mergeHeadCode, mergeKeepA, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, Fin.reduceEq, ne_eq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, mergeRefuteState, mergeSkelFinal, h1, h2', h3',
        h5', Nat.zero_mod, Nat.add_left_cancel_iff, ↓reduceIte, Nat.or_self, true_or, or_true, eq_self_iff_true, Nat.mod_mod,
        Nat.mod_self, Nat.add_zero, Nat.zero_add]

/-- **The 14-step trace, as a `step`-iterate.** -/
theorem mergeSkeleton_trace_run (E : RAMEnv) (hW : 3 ≤ E.W) :
    (step mergeProg E)^[14] (mergeRefuteState 0) = mergeSkelFinal := by
  obtain ⟨k, hk, hrun, -, -⟩ :=
    straightline_run (P := mergeProg) (E := E) (pc := 0) (l := mergeStmt.compile 0)
      (s := mergeRefuteState 0) mergeProg_at mergeProg_noBranch mergeProg_halt rfl
  rw [hk, mergeProg_length] at hrun
  rw [hrun, mergeSkeleton_runBlock E hW]

/-- **`SmergeRuns` is semantically false for the published skeleton** — at every time bound, not
only at `T = 0`.  On `A = B = [5]` the skeleton copies `5` instead of skipping it, so its output
list has value set `{5}` while the required symmetric difference is `∅`. -/
theorem mergeSkeleton_false (E : RAMEnv) (T : ℝ) (hW : 3 ≤ E.W) :
    ¬ SmergeRuns (mergeStmt.compile 0 ++ [iHalt]) E 0 1 1 2 1 T := by
  intro h
  obtain ⟨k, s', hk, hstep, hpc, hnd, hset⟩ := h (mergeRefuteState 0) rfl
  have hstep' : (step mergeProg E)^[k] (mergeRefuteState 0) = s' := hstep
  have hge : 14 ≤ k := by
    by_contra hlt
    have hk14 : k < 14 := by omega
    have hno : NoBranch ((mergeStmt.compile 0).take k) :=
      noBranch_take _ k mergeProg_noBranch
    have hkAt : At mergeProg 0 ((mergeStmt.compile 0).take k) := At.take' mergeProg_at k
    have hlen : ((mergeStmt.compile 0).take k).length = k := by
      rw [List.length_take, mergeProg_length]
      omega
    have hprefix : (step mergeProg E)^[k] (mergeRefuteState 0)
        = runBlock ((mergeStmt.compile 0).take k) E (mergeRefuteState 0) := by
      have hh := iterate_runBlock_of_at mergeProg E ((mergeStmt.compile 0).take k)
        (mergeRefuteState 0) hkAt hno
      rwa [hlen] at hh
    have hpck : ((step mergeProg E)^[k] (mergeRefuteState 0)).pc = k := by
      rw [hprefix, runBlock_pc _ _ _ hno, List.length_take, mergeProg_length,
        Nat.min_eq_left (by omega)]
      simp [mergeRefuteState]
    rw [hstep'] at hpck
    rw [hpc, mergeStmt_len] at hpck
    omega
  have hhalt : mergeProg[mergeSkelFinal.pc]? = some iHalt := by
    rw [mergeSkelFinal_pc]
    exact mergeProg_halt
  have hconv : (step mergeProg E)^[k] (mergeRefuteState 0) = mergeSkelFinal := by
    rw [show k = (k - 14) + 14 from by omega, Function.iterate_add_apply,
      mergeSkeleton_trace_run E hW]
    exact step_iterate_halted hhalt (k - 14)
  rw [hconv] at hstep'
  have hout : outList s' = [5] := by rw [← hstep']; exact mergeSkelFinal_out
  rw [hout] at hset
  simp [mergeRefuteState, listAt] at hset

/-! ## 3. The repack loop: the `List.take` partial-sum invariant

The loop head with cursor `k` has accumulated, in each row-slot word `i`, the sum of
`2 ^ (v % W)` over the first `k` values `v` with `v / W = i`, reduced modulo `2 ^ W` (which the
machine does at every write).  That is `repackLoopMem`, and at `k = len` it is exactly the sum
`RDec.repackMem` computes, so `RDec.rowOut_repackMem` closes the goal.  No carry analysis is
needed: `packMem` is that same sum. -/

/-- The support condition of an explicit list: duplicate-free, and enumerating `x`'s support.
This is `OutputsSupport` with the address of the list made explicit — the machine reads the list
from `listBase`, not from the output-list registers. -/
def ListSupports {R : ℕ} (l : List ℕ) (x : Fin R → ZMod 2) : Prop :=
  l.Nodup ∧ ∀ v : ℕ, v ∈ l ↔ ∃ i : Fin R, i.val = v ∧ x i = 1

/-- Reading a `writeArray` block at an arbitrary address. -/
theorem writeArray_apply (B n : ℕ) (m f : ℕ → ℕ) (a : ℕ) :
    writeArray B m f n a = if B ≤ a ∧ a < B + n then f (a - B) else m a := by
  induction n generalizing a with
  | zero => simp [writeArray]
  | succ n ih =>
      show Function.update (writeArray B m f n) (B + n) (f n) a = _
      by_cases ha : a = B + n
      · subst ha
        rw [Function.update_self, if_pos (by omega), Nat.add_sub_cancel_left]
      · rw [Function.update_of_ne ha, ih]
        by_cases h : B ≤ a ∧ a < B + n
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]

/-- One write **inside** the slot of a `writeArray` block, with the machine's modular
accumulation: only the target word changes, and the accumulated word is reduced. -/
theorem update_writeArray_mod (W B n : ℕ) (m F : ℕ → ℕ) (i0 b : ℕ) (hi0 : i0 < n)
    (hF : ∀ i, i < n → F i < 2 ^ W) :
    Function.update (writeArray B m F n) (B + i0) ((F i0 + b) % 2 ^ W)
      = writeArray B m (fun i => (F i + (if i = i0 then b else 0)) % 2 ^ W) n := by
  funext a
  by_cases ha : a = B + i0
  · subst ha
    rw [Function.update_self]
    have hR : writeArray B m (fun i => (F i + (if i = i0 then b else 0)) % 2 ^ W) n (B + i0)
        = (F i0 + b) % 2 ^ W := by
      rw [writeArray_apply, if_pos (by omega), Nat.add_sub_cancel_left]
      simp
    rw [hR]
  · rw [Function.update_of_ne ha]
    have hL : writeArray B m F n a = if B ≤ a ∧ a < B + n then F (a - B) else m a :=
      writeArray_apply B n m F a
    have hR : writeArray B m (fun i => (F i + (if i = i0 then b else 0)) % 2 ^ W) n a
        = if B ≤ a ∧ a < B + n then (F (a - B) + (if a - B = i0 then b else 0)) % 2 ^ W
          else m a :=
      writeArray_apply B n m _ a
    rw [hL, hR]
    by_cases hin : B ≤ a ∧ a < B + n
    · have hlt : a - B < n := by omega
      have hne : a - B ≠ i0 := by omega
      rw [if_pos hin, if_pos hin, if_neg hne, Nat.add_zero,
        Nat.mod_eq_of_lt (hF (a - B) hlt)]
    · rw [if_neg hin, if_neg hin]

/-- The repack loop's memory after `k` values: the row slot holds the word-reduced partial sums,
and every other address is the input memory's. -/
def repackLoopMem (E : RAMEnv) (R j : ℕ) (m : ℕ → ℕ) (l : List ℕ) (k : ℕ) : ℕ → ℕ :=
  writeArray (rowSlot E R j) m
    (fun i => (∑ p ∈ range k,
      (if l.getD p 0 / E.W = i then 2 ^ (l.getD p 0 % E.W) else 0)) % 2 ^ E.W)
    (wordsOf E.W R)

/-- The zero-step invariant is the entry memory, provided the row slot starts zeroed. -/
theorem repackLoopMem_zero (E : RAMEnv) (R j : ℕ) (m : ℕ → ℕ) (l : List ℕ)
    (hz : ∀ i, i < wordsOf E.W R → m (rowSlot E R j + i) = 0) :
    repackLoopMem E R j m l 0 = m := by
  funext a
  rw [repackLoopMem, writeArray_apply]
  by_cases hin : rowSlot E R j ≤ a ∧ a < rowSlot E R j + wordsOf E.W R
  · rw [if_pos hin]
    simp only [Finset.sum_range_zero, Nat.zero_mod]
    have hsum : rowSlot E R j + (a - rowSlot E R j) = a := by omega
    rw [← hsum]
    exact (hz (a - rowSlot E R j) (by omega)).symm
  · rw [if_neg hin]

/-- The repack loop head after `k` values.  Registers the body never writes are inherited from
the previous head, so the family is closed under the body. -/
def repackHead (E : RAMEnv) (R j len listBase : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (l : List ℕ) (k pc : ℕ) : RAMState where
  pc := pc
  mem := repackLoopMem E R j m l k
  regs := fun d =>
    if d = r0 then k else if d = r7 then listBase else if d = r8 then len else
      if d = r11 then E.W else if d = r6 then wordsOf E.W R else if d = r5 then rowSlot E R j else
        if d = r4 then 1 else if d = r9 then 0 else if d = r12 then 0 else if d = r13 then 0 else
          if d = r14 then 0 else if d = r15 then 0 else r d

theorem repackHead_zero_regs (E : RAMEnv) (R j len listBase : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (l : List ℕ) (k pc : ℕ) :
    (repackHead E R j len listBase m r l k pc).regs r0 = k ∧
    (repackHead E R j len listBase m r l k pc).regs r7 = listBase ∧
    (repackHead E R j len listBase m r l k pc).regs r8 = len ∧
    (repackHead E R j len listBase m r l k pc).regs r11 = E.W ∧
    (repackHead E R j len listBase m r l k pc).regs r6 = wordsOf E.W R ∧
    (repackHead E R j len listBase m r l k pc).regs r5 = rowSlot E R j := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The loop-head family: the entry state, then the canonical heads. -/
def repackFam (E : RAMEnv) (R j len listBase : ℕ) (m : ℕ → ℕ) (s : RAMState)
    (l : List ℕ) (base : ℕ) : ℕ → RAMState
  | 0 => s
  | (k + 1) =>
      repackHead E R j len listBase m s.regs l (k + 1) base

theorem repackFam_pc (E : RAMEnv) (R j len listBase : ℕ) (m : ℕ → ℕ) (s : RAMState)
    (l : List ℕ) (base : ℕ) (hs : s.pc = base) :
    ∀ k, (repackFam E R j len listBase m s l base k).pc = base
  | 0 => hs
  | _ + 1 => rfl

theorem repackFam_mem (E : RAMEnv) (R j len listBase : ℕ) (m : ℕ → ℕ) (s : RAMState)
    (l : List ℕ) (base : ℕ) (hs : s.mem = m)
    (hz : ∀ i, i < wordsOf E.W R → m (rowSlot E R j + i) = 0) :
    ∀ k, (repackFam E R j len listBase m s l base k).mem = repackLoopMem E R j m l k
  | 0 => by
      simp only [repackFam, hs]
      exact (repackLoopMem_zero E R j m l hz).symm
  | _ + 1 => rfl

theorem repackFam_regs (E : RAMEnv) (R j len listBase : ℕ) (m : ℕ → ℕ) (s : RAMState)
    (l : List ℕ) (base : ℕ) (h0 : s.regs r0 = 0) (h7 : s.regs r7 = listBase)
    (h8 : s.regs r8 = len) (h11 : s.regs r11 = E.W) (h6 : s.regs r6 = wordsOf E.W R)
    (h5 : s.regs r5 = rowSlot E R j) :
    ∀ k, (repackFam E R j len listBase m s l base k).regs r0 = k ∧
      (repackFam E R j len listBase m s l base k).regs r7 = listBase ∧
      (repackFam E R j len listBase m s l base k).regs r8 = len ∧
      (repackFam E R j len listBase m s l base k).regs r11 = E.W ∧
      (repackFam E R j len listBase m s l base k).regs r6 = wordsOf E.W R ∧
      (repackFam E R j len listBase m s l base k).regs r5 = rowSlot E R j
  | 0 => ⟨h0, h7, h8, h11, h6, h5⟩
  | _ + 1 =>
      repackHead_zero_regs E R j len listBase m _ l _ base

theorem sum_range_two_pow (W : ℕ) : (∑ r ∈ range W, 2 ^ r : ℕ) = 2 ^ W - 1 := by
  induction W with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ, Nat.mul_two]
      have : 0 < 2 ^ n := Nat.two_pow_pos n
      omega

/-- **A word's accumulated bits fit in a word.**  The values contributing to one word are
distinct positions of `l`, hence have distinct residues modulo `W`. -/
theorem sum_bits_list_lt {l : List ℕ} (hl : l.Nodup) {W : ℕ} (hW : 0 < W) {k i : ℕ}
    (hk : k ≤ l.length) :
    (∑ p ∈ range k,
      (if l.getD p 0 / W = i then 2 ^ (l.getD p 0 % W) else 0)) < 2 ^ W := by
  rw [← Finset.sum_filter]
  set S := (range k).filter (fun p => l.getD p 0 / W = i) with hS
  have hinj : Set.InjOn (fun p => l.getD p 0 % W) ↑S := by
    intro p hp q hq hpq
    rw [hS] at hp hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hp hq
    obtain ⟨hpk, hpw⟩ := hp
    obtain ⟨hqk, hqw⟩ := hq
    have hplt : p < l.length := by omega
    have hqlt : q < l.length := by omega
    have hpq' : l.getD p 0 % W = l.getD q 0 % W := hpq
    rw [List.getD_eq_getElem l 0 hplt] at hpw hpq'
    rw [List.getD_eq_getElem l 0 hqlt] at hqw hpq'
    have heq : l[p] = l[q] := by
      have hqw' : l[q] / W = l[p] / W := by rw [hqw, hpw]
      calc l[p] = W * (l[p] / W) + l[p] % W := (Nat.div_add_mod l[p] W).symm
        _ = W * (l[q] / W) + l[q] % W := by rw [hqw', hpq']
        _ = l[q] := Nat.div_add_mod l[q] W
    exact hl.getElem_inj_iff.mp heq
  rw [← Finset.sum_image hinj]
  have hsub : S.image (fun p => l.getD p 0 % W) ⊆ range W := by
    intro r hr
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.mpr (Nat.mod_lt _ hW)
  have hle : (∑ r ∈ S.image (fun p => l.getD p 0 % W), 2 ^ r) ≤ ∑ r ∈ range W, 2 ^ r :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have hpos : 0 < 2 ^ W := Nat.two_pow_pos W
  rw [sum_range_two_pow] at hle
  omega

/-- The list stored by `listAt` is `getD`-consistent. -/
theorem getD_listAt (s : RAMState) (b len k : ℕ) (hk : k < len) :
    (listAt s b len).getD k 0 = s.mem (b + k) := by
  unfold listAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem mem_listAt (s : RAMState) (b len k : ℕ) (hk : k < len) :
    s.mem (b + k) ∈ listAt s b len := by
  unfold listAt
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

/-! ### 3.1 The body, from one loop head to the next -/

/-- Running the loop test: `k < len` so the test register becomes `1`. -/
theorem repackTest {E : RAMEnv} {z : RAMState} {base k len : ℕ}
    (hzpc : z.pc = base) (hz0 : z.regs r0 = k) (hz8 : z.regs r8 = len) (hk : k < len)
    (hW : 1 < 2 ^ E.W) :
    { runBlock (Cond.lt r15 r0 r8).code E z with pc := base + 2 }
      = { z with pc := base + 2, regs := Function.update z.regs r15 1 } := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  simp only [Cond.code, runBlock_cons, runBlock_nil, execInstr_lt, hz0, hz8, if_pos hk, h1, hzpc]

/-- **One iteration of the repack loop**: from the body entry of the head `z`, the 17-instruction
body reaches the next head, accumulating `2 ^ (v % W)` in word `v / W`. -/
theorem repackBody_spec (E : RAMEnv) (R j len listBase : ℕ) (m : ℕ → ℕ) (l : List ℕ)
    (z : RAMState) (k base : ℕ)
    (hW : 1 < 2 ^ E.W) (hlen : len < 2 ^ E.W) (hadr : listBase + len ≤ 2 ^ E.W)
    (hadr2 : rowSlot E R j + wordsOf E.W R ≤ 2 ^ E.W)
    (hdisj : listBase + len ≤ rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ listBase)
    (hval : ∀ p, p < len → l.getD p 0 < 2 ^ E.W)
    (hR : ∀ p, p < len → l.getD p 0 < R)
    (hget : ∀ p, p < len → m (listBase + p) = l.getD p 0)
    (hl : l.Nodup) (hlen' : len = l.length)
    (hk : k < len)
    (hzpc : z.pc = base + 2) (hz15 : z.regs r15 = 1)
    (hz0 : z.regs r0 = k) (hz7 : z.regs r7 = listBase)
    (hz8 : z.regs r8 = len) (hz11 : z.regs r11 = E.W) (hz6 : z.regs r6 = wordsOf E.W R)
    (hz5 : z.regs r5 = rowSlot E R j) (hzmem : z.mem = repackLoopMem E R j m l k)
    (r : Fin 16 → ℕ)
    (hzr : ∀ d, d ≠ r0 → d ≠ r4 → d ≠ r9 → d ≠ r12 → d ≠ r13 → d ≠ r14 →
      d ≠ r15 → z.regs d = r d) :
    runBlock repackBody E z = repackHead E R j len listBase m r l (k + 1) (base + 19) := by
  have hWpos : 0 < E.W := by
    rcases Nat.eq_zero_or_pos E.W with h | h
    · rw [h] at hW; simp at hW
    · exact h
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hadrk : listBase + k < 2 ^ E.W := by omega
  have hk1 : k + 1 < 2 ^ E.W := by omega
  have hvR : l.getD k 0 < R := hR k hk
  have hvW : l.getD k 0 < 2 ^ E.W := hval k hk
  have hvmod : l.getD k 0 % 2 ^ E.W = l.getD k 0 := Nat.mod_eq_of_lt hvW
  have hRW : R ≤ wordsOf E.W R * E.W := by
    have h := C8R.le_mul_wordsOf E.W hWpos R
    rwa [Nat.mul_comm] at h
  have hi0 : l.getD k 0 / E.W < wordsOf E.W R :=
    (Nat.div_lt_iff_lt_mul hWpos).mpr (Nat.lt_of_lt_of_le hvR hRW)
  have hbit : 2 ^ (l.getD k 0 % E.W) < 2 ^ E.W := by
    have hlt : l.getD k 0 % E.W < E.W := Nat.mod_lt _ hWpos
    exact Nat.pow_lt_pow_right (by norm_num) hlt
  -- the list word
  have hnin : ¬(rowSlot E R j ≤ listBase + k ∧ listBase + k < rowSlot E R j + wordsOf E.W R) := by
    rintro ⟨h1, h2⟩
    rcases hdisj with h | h <;> omega
  have hread : z.mem (listBase + k) = l.getD k 0 := by
    rw [hzmem]
    unfold repackLoopMem
    rw [writeArray_apply, if_neg hnin, hget k hk]
  have hread' : repackLoopMem E R j m l k (listBase + k) = l.getD k 0 := by
    rw [hzmem] at hread
    exact hread
  -- the slot word
  have hslot : z.mem (rowSlot E R j + (l.getD k 0 / E.W)) =
      (∑ p ∈ range k,
        (if l.getD p 0 / E.W = l.getD k 0 / E.W then 2 ^ (l.getD p 0 % E.W) else 0)) % 2 ^ E.W := by
    rw [hzmem]
    unfold repackLoopMem
    rw [writeArray_apply]
    rw [if_pos ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi0 _⟩, Nat.add_sub_cancel_left]
  have hslot' : repackLoopMem E R j m l k (rowSlot E R j + l.getD k 0 / E.W) =
      (∑ p ∈ range k,
        (if l.getD p 0 / E.W = l.getD k 0 / E.W then 2 ^ (l.getD p 0 % E.W) else 0)) % 2 ^ E.W := by
    rw [hzmem] at hslot
    exact hslot
  have haddr : (rowSlot E R j + l.getD k 0 / E.W) % 2 ^ E.W = rowSlot E R j + l.getD k 0 / E.W :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.add_lt_add_left hi0 _) hadr2)
  apply ramState_eq_of
  · rw [runBlock_pc _ _ _ (by simp [repackBody]), hzpc, repackBody_length]
    rfl
  · -- the memory effect: exactly one modular write at `rowSlot + v / W`
    have hmodk : (listBase + k) % 2 ^ E.W = listBase + k := Nat.mod_eq_of_lt hadrk
    have hwlt : wordsOf E.W R < 2 ^ E.W := by omega
    have hi0' : l.getD k 0 / E.W < 2 ^ E.W := lt_trans hi0 hwlt
    have hi0mod : l.getD k 0 / E.W % 2 ^ E.W = l.getD k 0 / E.W := Nat.mod_eq_of_lt hi0'
    have hbitmod : 2 ^ (l.getD k 0 % E.W) % 2 ^ E.W = 2 ^ (l.getD k 0 % E.W) :=
      Nat.mod_eq_of_lt hbit
    have hexp : l.getD k 0 % E.W % 2 ^ E.W = l.getD k 0 % E.W :=
      Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ hWpos) (Nat.lt_two_pow_self))
    change (runBlock repackBody E z).mem = repackLoopMem E R j m l (k + 1)
    unfold repackLoopMem
    simp only [repackBody, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
      Function.update_self, Function.update_of_ne, Fin.reduceEq, ne_eq, not_false_eq_true,
      Function.update_idem, h1, Nat.zero_mod, hzmem, hmodk, hvmod, hread', hslot', hbit, haddr,
      hi0mod, hbitmod, hexp, Nat.one_mul, Nat.mod_mod, hz0, hz5, hz6, hz7, hz8, hz11]
    unfold repackLoopMem
    rw [update_writeArray_mod E.W (rowSlot E R j) (wordsOf E.W R) m
      (fun i => (∑ p ∈ range k,
        (if l.getD p 0 / E.W = i then 2 ^ (l.getD p 0 % E.W) else 0)) % 2 ^ E.W)
      (l.getD k 0 / E.W) (2 ^ (l.getD k 0 % E.W)) hi0
      (fun i _ => Nat.mod_lt _ (Nat.two_pow_pos _))]
    congr 1
    funext i
    have hSlt : (∑ p ∈ range k,
        (if l.getD p 0 / E.W = i then 2 ^ (l.getD p 0 % E.W) else 0)) < 2 ^ E.W :=
      sum_bits_list_lt hl hWpos (by omega)
    have hSm : (∑ p ∈ range k,
        (if l.getD p 0 / E.W = i then 2 ^ (l.getD p 0 % E.W) else 0)) % 2 ^ E.W
        = ∑ p ∈ range k,
          (if l.getD p 0 / E.W = i then 2 ^ (l.getD p 0 % E.W) else 0) :=
      Nat.mod_eq_of_lt hSlt
    simp only [hSm, Finset.sum_range_succ]
    by_cases h : i = l.getD k 0 / E.W <;>
      simp [h, eq_comm, Nat.mod_eq_of_lt hbit]
  · intro d
    fin_cases d
    all_goals
      simp only [repackBody, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, Fin.reduceEq, ne_eq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, repackHead, h1, Nat.zero_mod, hz0, hz5, hz6,
        hz7, hz8, hz11, hvW, hvmod, Nat.mod_eq_of_lt hk1, ↓reduceIte, Nat.or_self, Nat.mod_mod,
        Nat.mod_self, Nat.add_zero, Nat.zero_add, eq_self_iff_true, true_or, hadrk]
    all_goals
      exact hzr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)


/-! ### 3.2 The loop -/

theorem sum_range_getD_eq_toFinset (l : List ℕ) (hl : l.Nodup) (f : ℕ → ℕ) :
    (∑ p ∈ range l.length, f (l.getD p 0)) = ∑ v ∈ l.toFinset, f v := by
  have himg : (range l.length).image (fun p => l.getD p 0) = l.toFinset := by
    ext v
    simp only [Finset.mem_image, Finset.mem_range, List.mem_toFinset, List.mem_iff_getElem]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, (List.getD_eq_getElem l 0 hp).symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, List.getD_eq_getElem l 0 hp⟩
  have hinj : Set.InjOn (fun p => l.getD p 0) ↑(range l.length) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_range] at hp hq
    have hpq' : l.getD p 0 = l.getD q 0 := hpq
    rw [List.getD_eq_getElem l 0 hp, List.getD_eq_getElem l 0 hq] at hpq'
    exact hl.getElem_inj_iff.mp hpq'
  rw [← Finset.sum_image hinj, himg]

/-- At the end of the loop the partial sums are exactly `RDec.repackMem`'s compressed memory. -/
theorem repackLoopMem_end (E : RAMEnv) (R j : ℕ) (m : ℕ → ℕ) (l : List ℕ)
    (hl : l.Nodup) (hW : 0 < E.W) :
    repackLoopMem E R j m l l.length = RDec.repackMem E R j l m := by
  funext a
  by_cases hin : ∃ i, i < wordsOf E.W R ∧ a = rowSlot E R j + i
  · obtain ⟨i, hi, rfl⟩ := hin
    have h1 : repackLoopMem E R j m l l.length (rowSlot E R j + i)
        = (∑ p ∈ range l.length,
            (if l.getD p 0 / E.W = i then 2 ^ (l.getD p 0 % E.W) else 0)) % 2 ^ E.W :=
      writeArray_get _ _ _ _ _ hi
    have h2 : RDec.repackMem E R j l m (rowSlot E R j + i)
        = ∑ v ∈ l.toFinset, (if v / E.W = i then 2 ^ (v % E.W) else 0) :=
      RDec.repackMem_slot E R j l m i hi
    rw [h1, h2, Nat.mod_eq_of_lt (sum_bits_list_lt hl hW (le_refl l.length))]
    exact sum_range_getD_eq_toFinset l hl
      (fun v => if v / E.W = i then 2 ^ (v % E.W) else 0)
  · have hout : a < rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ a := by
      rcases Nat.lt_or_ge a (rowSlot E R j) with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        by_contra hc
        exact hin ⟨a - rowSlot E R j, by omega, by omega⟩
    rw [show repackLoopMem E R j m l l.length a = m a from writeArray_frame _ _ _ _ _ hout,
      show RDec.repackMem E R j l m a = m a from RDec.repackMem_frame E R j l m a hout]

/-- The body-entry state of the repack loop at head `t`: the head with the test already run. -/
def repackTestSt (E : RAMEnv) (R j len listBase : ℕ) (m : ℕ → ℕ) (s : RAMState)
    (l : List ℕ) (base t : ℕ) : RAMState where
  pc := base + 2
  mem := (repackFam E R j len listBase m s l base t).mem
  regs := Function.update (repackFam E R j len listBase m s l base t).regs r15 1

/-- **The repack loop, simulated.**  From the loop head it reaches the exit in at most
`20 · len + 2` steps, with the accumulated row slot. -/
theorem repackLoop_sem {P : Program} {E : RAMEnv} {R j len listBase base : ℕ} {m : ℕ → ℕ}
    {l : List ℕ}
    (hAt : At P base (Stmt.compile repackStmt base)) (hW : 1 < 2 ^ E.W)
    (hlen : len < 2 ^ E.W) (hadr : listBase + len ≤ 2 ^ E.W)
    (hadr2 : rowSlot E R j + wordsOf E.W R ≤ 2 ^ E.W)
    (hdisj : listBase + len ≤ rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ listBase)
    (hval : ∀ p, p < len → l.getD p 0 < 2 ^ E.W)
    (hR : ∀ p, p < len → l.getD p 0 < R)
    (hget : ∀ p, p < len → m (listBase + p) = l.getD p 0)
    (hl : l.Nodup) (hlen' : len = l.length)
    (s : RAMState) (hspc : s.pc = base) (hs0 : s.regs r0 = 0) (hs7 : s.regs r7 = listBase)
    (hs8 : s.regs r8 = len) (hs11 : s.regs r11 = E.W) (hs6 : s.regs r6 = wordsOf E.W R)
    (hs5 : s.regs r5 = rowSlot E R j) (hsm : s.mem = m)
    (hz : ∀ i, i < wordsOf E.W R → m (rowSlot E R j + i) = 0) :
    ∃ c : ℕ, c ≤ 20 * len + 2 ∧
      (step P E)^[c] s
        = { runBlock (Cond.lt r15 r0 r8).code E
              (repackFam E R j len listBase m s l base len) with pc := base + 20 } := by
  have hpcall : ∀ t, (repackFam E R j len listBase m s l base t).pc = base :=
    repackFam_pc E R j len listBase m s l base hspc
  have hregs : ∀ t, (repackFam E R j len listBase m s l base t).regs r0 = t :=
    fun t => (repackFam_regs E R j len listBase m s l base hs0 hs7 hs8 hs11 hs6 hs5 t).1
  have h8 : ∀ t, (repackFam E R j len listBase m s l base t).regs r8 = len :=
    fun t => (repackFam_regs E R j len listBase m s l base hs0 hs7 hs8 hs11 hs6 hs5 t).2.2.1
  have hloop := Sem.loop P E base (Cond.lt r15 r0 r8) (.code repackBody) hAt hW len
    (repackFam E R j len listBase m s l base) (fun _ => 18) hpcall
    (fun t ht => by
      show (repackFam E R j len listBase m s l base t).regs r0
        < (repackFam E R j len listBase m s l base t).regs r8
      rw [hregs t, h8 t]
      exact ht)
    (fun hf => by
      change (repackFam E R j len listBase m s l base len).regs r0
        < (repackFam E R j len listBase m s l base len).regs r8 at hf
      rw [hregs len, h8 len] at hf
      omega)
    (fun t ht => by
      obtain ⟨-, -, hbodyAt, hjmp⟩ := at_loop hAt
      have hzj : { runBlock (Cond.lt r15 r0 r8).code E (repackFam E R j len listBase m s l base t)
            with pc := base + (Cond.lt r15 r0 r8).code.length + 1 }
          = repackTestSt E R j len listBase m s l base t :=
        repackTest (hpcall t) (hregs t) (h8 t) ht hW
      rw [hzj]
      have hzt_regs : ∀ d, d ≠ r15 → (repackTestSt E R j len listBase m s l base t).regs d = (repackFam E R j len listBase m s l base t).regs d := by
        intro d hd
        simp only [repackTestSt, Function.update_of_ne hd]
      have hf0 : (repackFam E R j len listBase m s l base t).regs r0 = t := hregs t
      have hf7 : (repackFam E R j len listBase m s l base t).regs r7 = listBase :=
        (repackFam_regs E R j len listBase m s l base hs0 hs7 hs8 hs11 hs6 hs5 t).2.1
      have hf8 : (repackFam E R j len listBase m s l base t).regs r8 = len := h8 t
      have hf11 : (repackFam E R j len listBase m s l base t).regs r11 = E.W :=
        (repackFam_regs E R j len listBase m s l base hs0 hs7 hs8 hs11 hs6 hs5 t).2.2.2.1
      have hf6 : (repackFam E R j len listBase m s l base t).regs r6 = wordsOf E.W R :=
        (repackFam_regs E R j len listBase m s l base hs0 hs7 hs8 hs11 hs6 hs5 t).2.2.2.2.1
      have hf5 : (repackFam E R j len listBase m s l base t).regs r5 = rowSlot E R j :=
        (repackFam_regs E R j len listBase m s l base hs0 hs7 hs8 hs11 hs6 hs5 t).2.2.2.2.2
      have hzr : ∀ d, d ≠ r0 → d ≠ r4 → d ≠ r9 → d ≠ r12 → d ≠ r13 →
          d ≠ r14 → d ≠ r15 → (repackTestSt E R j len listBase m s l base t).regs d = s.regs d := by
        intro d h0 h4 h9 h12 h13 h14 h15
        rw [hzt_regs d h15]
        cases t with
        | zero => rfl
        | succ t =>
            show (repackHead E R j len listBase m s.regs l (t + 1) base).regs d = s.regs d
            fin_cases d
            · exact absurd rfl h0
            · simp [repackHead]
            · simp [repackHead]
            · simp [repackHead]
            · exact absurd rfl h4
            · simp [repackHead, hs5]
            · simp [repackHead, hs6]
            · simp [repackHead, hs7]
            · simp [repackHead, hs8]
            · exact absurd rfl h9
            · simp [repackHead]
            · simp [repackHead, hs11]
            · exact absurd rfl h12
            · exact absurd rfl h13
            · exact absurd rfl h14
            · exact absurd rfl h15
      have hrun : Sem P E (base + 2) (base + 19) (repackTestSt E R j len listBase m s l base t)
          (fun c s' => c = 17 ∧
            s' = { repackHead E R j len listBase m s.regs l (t + 1) (base + 19) with pc := base + 19 }) := by
        refine Sem.mono (Sem.block P E (base + 2) repackBody (repackTestSt E R j len listBase m s l base t) hbodyAt
          (by simp [repackBody]) rfl) ?_
        intro c s' hs
        obtain ⟨rfl, rfl⟩ := hs
        refine ⟨rfl, repackBody_spec E R j len listBase m l (repackTestSt E R j len listBase m s l base t) t base hW hlen hadr hadr2 hdisj hval
          hR hget hl hlen' ht rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ s.regs hzr⟩
        · simp [repackTestSt]
        · rw [hzt_regs r0 (by decide)]; exact hf0
        · rw [hzt_regs r7 (by decide)]; exact hf7
        · rw [hzt_regs r8 (by decide)]; exact hf8
        · rw [hzt_regs r11 (by decide)]; exact hf11
        · rw [hzt_regs r6 (by decide)]; exact hf6
        · rw [hzt_regs r5 (by decide)]; exact hf5
        · rw [show (repackTestSt E R j len listBase m s l base t).mem = (repackFam E R j len listBase m s l base t).mem from rfl]
          exact repackFam_mem E R j len listBase m s l base hsm hz t
      refine Sem.jmp_append (hAt := hjmp) (Sem.mono hrun ?_)
      intro c s' hs
      obtain ⟨rfl, rfl⟩ := hs
      exact ⟨by omega, rfl⟩)
  obtain ⟨-, c, s', hstep, hexit, hcost, hstate⟩ := hloop
  refine ⟨c, ?_, ?_⟩
  · have hcost' : c ≤ 2 + ∑ t ∈ Finset.range len, (20 : ℕ) := hcost
    have hsum : (∑ t ∈ Finset.range len, (20 : ℕ)) = 20 * len := sum_range_const_mul len 20
    rw [hsum] at hcost'
    omega
  · have hstep' : (step P E)^[c] s = s' := hstep
    rw [hstep']
    have hpc20 : base + (Cond.lt r15 r0 r8).code.length + (Stmt.code repackBody).len + 2
        = base + 20 := rfl
    rw [hpc20] at hstate
    exact hstate

/-- **The repaired repack contract.**  `x` is a *parameter* (it determines the output, so it must
not be existentially quantified per state); the list is the one the machine reads
(`listAt s listBase len`), not `outList s`, whose `r0` is the loop cursor.  The layout hypotheses
are exactly what the loop's address arithmetic needs, and the row slot starts zeroed because
`repackBody` accumulates into it. -/
def RepackRunsS (P : Program) (E : RAMEnv) {R : ℕ} (x : Fin R → ZMod 2)
    (base j len listBase : ℕ) (T : ℝ) : Prop :=
  At P base (Stmt.compile repackStmt base) →
  ∀ s : RAMState, s.pc = base →
    s.regs r0 = 0 ∧ s.regs r7 = listBase ∧ s.regs r8 = len ∧
    s.regs r11 = E.W ∧ s.regs r6 = wordsOf E.W R ∧ s.regs r5 = rowSlot E R j →
    (∀ i, i < wordsOf E.W R → s.mem (rowSlot E R j + i) = 0) →
    (∀ v, v ∈ listAt s listBase len → v < 2 ^ E.W) →
    (∀ v, v ∈ listAt s listBase len → v < R) →
    len < 2 ^ E.W → listBase + len ≤ 2 ^ E.W → rowSlot E R j + wordsOf E.W R ≤ 2 ^ E.W →
    (listBase + len ≤ rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ listBase) →
    ListSupports (listAt s listBase len) x →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧
      s'.pc = base + repackStmt.len ∧ RowOut E R j x s'.mem

/-- **The repaired repack loop is correct.** -/
theorem repackRunsS_proved {P : Program} {E : RAMEnv} {R : ℕ} (x : Fin R → ZMod 2)
    {base j len listBase : ℕ} {T : ℝ}
    (hAt : At P base (Stmt.compile repackStmt base)) (hW : 1 < 2 ^ E.W)
    (hT : ((20 * len + 20 : ℕ) : ℝ) ≤ T) : RepackRunsS P E x base j len listBase T := by
  intro hat s hspc hregs hz hval hRv hlen hadr hadr2 hdisj hsupp
  obtain ⟨h0, h7, h8, h11, h6, h5⟩ := hregs
  clear hat
  have hWpos : 0 < E.W := by
    rcases Nat.eq_zero_or_pos E.W with h | h
    · rw [h] at hW; simp at hW
    · exact h
  have hget : ∀ p, p < len → s.mem (listBase + p) = (listAt s listBase len).getD p 0 := by
    intro p hp
    rw [getD_listAt s listBase len p hp]
  have hlen' : len = (listAt s listBase len).length := by
    simp [listAt]
  obtain ⟨c, hc, hstep⟩ := repackLoop_sem (P := P) (E := E) (R := R) (j := j) (len := len)
    (listBase := listBase) (base := base) (m := s.mem) (l := listAt s listBase len) hAt hW hlen
    hadr hadr2 hdisj
    (fun p hp => by rw [← hget p hp]; exact hval _ (mem_listAt s listBase len p hp))
    (fun p hp => by rw [← hget p hp]; exact hRv _ (mem_listAt s listBase len p hp)) hget hsupp.1 hlen'
    s hspc h0 h7 h8 h11 h6 h5 rfl hz
  -- the input state whose output list is the machine's list
  let s0 : RAMState := { s with regs := Function.update (Function.update s.regs r0 listBase) r1 len }
  have hout0 : outList s0 = listAt s listBase len := by
    show listAt s0 (s0.regs r0) (s0.regs r1) = listAt s listBase len
    have h0' : s0.regs r0 = listBase := by
      simp [s0]
    have h1' : s0.regs r1 = len := by
      simp [s0, Function.update_of_ne (by decide : r1 ≠ r0)]
    rw [h0', h1']
    rfl
  have hsupp0 : OutputsSupport s0 x := by
    refine ⟨?_, ?_⟩
    · rw [hout0]; exact hsupp.1
    · intro v; rw [hout0]; exact hsupp.2 v
  have hrow := RDec.rowOut_repackMem E R j s0 x hsupp0
  rw [hout0] at hrow
  have hs0mem : s0.mem = s.mem := rfl
  rw [hs0mem] at hrow
  refine ⟨c, _, ?_, hstep, ?_, ?_⟩
  · have hc' : (c : ℝ) ≤ ((20 * len + 2 : ℕ) : ℝ) := by exact_mod_cast hc
    have h2 : ((20 * len + 2 : ℕ) : ℝ) ≤ ((20 * len + 20 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 20 * len + 2 ≤ 20 * len + 20)
    exact le_trans (le_trans hc' h2) hT
  · rfl
  · show RowOut E R j x
      ({ runBlock (Cond.lt r15 r0 r8).code E (repackFam E R j len listBase s.mem s
        (listAt s listBase len) base len) with pc := base + 20 } : RAMState).mem
    have hmem : (runBlock (Cond.lt r15 r0 r8).code E
        (repackFam E R j len listBase s.mem s (listAt s listBase len) base len)).mem
        = repackLoopMem E R j s.mem (listAt s listBase len) (listAt s listBase len).length := by
      rw [← hlen']
      exact repackFam_mem E R j len listBase s.mem s (listAt s listBase len) base rfl hz len
    rw [hmem, repackLoopMem_end E R j s.mem (listAt s listBase len) hsupp.1 hWpos]
    exact hrow


/-! ## 4. What is false, and the non-degenerate inhabitant -/

/-- The refutation state of `RDG.RepackRunsC`: `s.regs r0 = 0` (the loop's cursor, as the contract
demands), `s.regs r1 = 2`, and the two output words `0, 1` both hold `5`, so
`outList s = [5, 5]`. -/
def dupRefute (base : ℕ) : RAMState where
  pc := base
  regs := fun d =>
    if d = r0 then 0 else if d = r1 then 2 else if d = r5 then 5 else if d = r6 then 1 else
      if d = r7 then 16 else if d = r8 then 2 else if d = r11 then 8 else 0
  mem := fun a => if a = 0 ∨ a = 1 then 5 else 0

theorem dupRefute_out (base : ℕ) : outList (dupRefute base) = [5, 5] := by
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  simp [outList, dupRefute, h2, List.range_succ]

/-- **`RDG.RepackRunsC` is false as stated.**  Its hypotheses pin `s.regs r0 = 0` — the loop
*cursor* — while its conclusion asks for `OutputsSupport s x` of the **input** state, whose output
list is `listAt s (s.regs 0) (s.regs 1)`, i.e. the words at address `0`, unrelated to `listBase`.
A state whose output list repeats a value refutes it for every `x`, whatever the machine does: the
quantifier still ranges over states the loop can never turn into a support list, and the parameter
that determines the output (`x`, hence the input list) has not been moved outside it. -/
theorem repackRunsC_false (P : Program) (T : ℝ) :
    ¬ RDG.RepackRunsC P (detEnv 8 (fun _ => 0)) 0 8 5 2 16 T := by
  have hwords : wordsOf (detEnv 8 (fun _ => 0)).W 8 = 1 := by
    show wordsOf 8 8 = 1
    norm_num [wordsOf]
  have hslot : rowSlot (detEnv 8 (fun _ => 0)) 8 5 = 5 := by
    show RDG.rowBase (detEnv 8 (fun _ => 0)) + 5 * wordsOf 8 8 = 5
    norm_num [RDG.rowBase, wordsOf, detEnv]
  intro h
  obtain ⟨k, s', hk, hstep, hpc, x, hx, hrow⟩ := h (dupRefute 0) rfl
    (by refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by
      intro i hi
      rw [hwords] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      rw [hslot]
      simp [dupRefute])
    (by
      intro v hv
      have hlist : listAt (dupRefute 0) 16 2 = [0, 0] := by
        simp [listAt, dupRefute, List.range_succ]
      rw [hlist] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h <;> (rw [h]; show (0 : ℕ) < 2 ^ 8; norm_num))
    (by show (2 : ℕ) < 2 ^ 8; norm_num)
    (by
      right
      rw [hslot, hwords]
      norm_num)
  have hnd := hx.1
  rw [dupRefute_out] at hnd
  exact absurd hnd (by simp)

/-- The support of the inhabitant: coordinate `5`. -/
def oneSupp : Fin 8 → ZMod 2 := fun i => if i.val = 5 then 1 else 0

theorem oneSupp_pack : packMem 8 oneSupp 0 = 32 := by
  unfold packMem oneSupp
  decide

/-- **The repaired contract is inhabited at a non-degenerate instance.**  `W = 8` and `R = 8`, so
`wordsOf 8 8 = 1`: the row slot is a genuine live word (not the `wordsOf = 0` accident).  The input
list is `[5]` at address `32`, and after the loop the slot word holds `packMem 8 oneSupp 0 = 32`,
the bit for coordinate `5`. -/
theorem repackRunsS_inhabited :
    ∃ (s s' : RAMState) (k : ℕ) (x : Fin 8 → ZMod 2),
      wordsOf 8 8 = 1 ∧
      (step (Stmt.compile repackStmt 0 ++ [iHalt]) (detEnv 8 (fun _ => 0)))^[k] s = s' ∧
      s'.pc = 20 ∧ s'.mem (rowSlot (detEnv 8 (fun _ => 0)) 8 0 + 0) = packMem 8 x 0 ∧
      packMem 8 x 0 = 32 := by
  have hwords : wordsOf (detEnv 8 (fun _ => 0)).W 8 = 1 := by
    show wordsOf 8 8 = 1
    norm_num [wordsOf]
  have hslot : rowSlot (detEnv 8 (fun _ => 0)) 8 0 = 0 := by
    show RDG.rowBase (detEnv 8 (fun _ => 0)) + 0 * wordsOf 8 8 = 0
    norm_num [RDG.rowBase, wordsOf, detEnv]
  let s : RAMState :=
    { pc := 0
      regs := fun d =>
        if d = r5 then rowSlot (detEnv 8 (fun _ => 0)) 8 0 else if d = r6 then 1 else
          if d = r7 then 32 else if d = r8 then 1 else if d = r11 then 8 else 0
      mem := fun a => if a = 32 then 5 else 0 }
  have hlist : listAt s 32 1 = [5] := by simp [listAt, s]
  have hsupp : ListSupports (listAt s 32 1) oneSupp := by
    constructor
    · rw [hlist]; simp
    · intro v
      rw [hlist]
      constructor
      · intro hv
        have hv5 : v = 5 := by simpa using hv
        subst hv5
        exact ⟨⟨5, by omega⟩, rfl, by simp [oneSupp]⟩
      · rintro ⟨i, hi, hx⟩
        have hi5 : i.val = 5 := by
          by_contra hne
          simp [oneSupp, hne] at hx
        simpa [hi5] using hi.symm
  have hAt : At (Stmt.compile repackStmt 0 ++ [iHalt]) 0 (Stmt.compile repackStmt 0) := by
    intro r hr
    rw [List.getElem?_append_left]
    · simp
    · simpa using hr
  obtain ⟨k, s', hk, hstep, hpc, hrow⟩ :=
    repackRunsS_proved (P := Stmt.compile repackStmt 0 ++ [iHalt])
      (E := detEnv 8 (fun _ => 0)) (R := 8) oneSupp
      (base := 0) (j := 0) (len := 1) (listBase := 32) (T := 40) hAt
      (by show (1 : ℕ) < 2 ^ 8; norm_num)
      (by norm_num) hAt s rfl
      ⟨by simp [s], by simp [s], by simp [s],
       by show (8 : ℕ) = (detEnv 8 (fun _ => 0)).W; rfl,
       by show (1 : ℕ) = wordsOf (detEnv 8 (fun _ => 0)).W 8; rw [hwords],
       by show (0 : ℕ) = rowSlot (detEnv 8 (fun _ => 0)) 8 0; rw [hslot]⟩
      (by
        intro i hi
        rw [hwords] at hi
        have hi0 : i = 0 := by omega
        subst hi0
        rw [hslot]
        simp [s])
      (by
        intro v hv
        rw [hlist] at hv
        simp only [List.mem_singleton] at hv
        subst hv
        show (5 : ℕ) < 2 ^ 8
        norm_num)
      (by
        intro v hv
        rw [hlist] at hv
        simp only [List.mem_singleton] at hv
        subst hv
        show (5 : ℕ) < 8
        norm_num)
      (by show (1 : ℕ) < 2 ^ 8; norm_num)
      (by show (32 + 1 : ℕ) ≤ 2 ^ 8; norm_num)
      (by
        right
        rw [hslot, hwords]
        norm_num)
      (by
        right
        rw [hslot, hwords]
        norm_num)
      hsupp
  have hi0holes : 0 < wordsOf (detEnv 8 (fun _ => 0)).W 8 := by rw [hwords]; norm_num
  refine ⟨s, s', k, oneSupp, hwords, hstep, ?_, ?_, oneSupp_pack⟩
  · rw [hpc, repackStmt_len]
  · have h := hrow 0 hi0holes
    rw [hslot, Nat.zero_add] at h
    exact h


/-! ## 5. The merge: why `SmergeRunsP` is false

`mergeStmtFull` has two defects that no iteration argument can repair:

* the "swap" `[iBor r5 r7 r7, iBor r6 r8 r8]` only *copies* `B`'s base/length into `(r5, r6)`; it
  leaves `(r7, r8)` at `B` too.  So the second pass iterates over `B` and scans `B`, finds every
  candidate, and keeps nothing — `B \ A` is never produced (`mergeSwap_not_swap` below);
* the second pass's cursor `r0` is not reset, so it does not even start at `0`;
* the contract quantifies over every input state and demands `(outList s').Nodup`, while the keep
  pass preserves *multiplicities* of `A`: at `A = [5, 5]`, `B = []` the output list is `[5, 5]`.

The published full program is also refuted at `T = 0`, exactly like the skeleton
(`mergeSkeleton_false_zero`): a 66-instruction block cannot finish in zero steps. -/

/-- **The published "swap" is not a swap.**  After `[iBor r5 r7 r7, iBor r6 r8 r8]` the candidate
pair `(r5, r6)` equals the membership pair `(r7, r8)`, so the second keep pass of `mergeStmtFull`
scans `B` for members of `B` and keeps nothing. -/
theorem mergeSwap_not_swap (E : RAMEnv) (s : RAMState) (hW : 1 < 2 ^ E.W)
    (h7 : s.regs r7 < 2 ^ E.W) (h8 : s.regs r8 < 2 ^ E.W) :
    (runBlock [iBor r5 r7 r7, iBor r6 r8 r8] E s).regs r5
        = (runBlock [iBor r5 r7 r7, iBor r6 r8 r8] E s).regs r7 ∧
      (runBlock [iBor r5 r7 r7, iBor r6 r8 r8] E s).regs r6
        = (runBlock [iBor r5 r7 r7, iBor r6 r8 r8] E s).regs r8 := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hm7 : s.regs r7 % 2 ^ E.W = s.regs r7 := Nat.mod_eq_of_lt h7
  have hm8 : s.regs r8 % 2 ^ E.W = s.regs r8 := Nat.mod_eq_of_lt h8
  simp only [runBlock_cons, runBlock_nil, execInstr, Function.update_self,
    Function.update_of_ne, Fin.reduceEq, ne_eq, not_false_eq_true, Nat.or_self, hm7, hm8, h1]
  trivial

/-- `mergeStmtFull`'s second pass is preceded by exactly those two instructions. -/
theorem mergeStmtFull_shape :
    mergeStmtFull.compile 0
      = mergeHeadCode ++ (mergePass.compile mergeHeadCode.length
          ++ ([iBor r5 r7 r7, iBor r6 r8 r8]
            ++ (mergePass.compile (mergeHeadCode.length + mergePass.len + 2)
              ++ [iBor r0 r9 r9]))) := rfl

/-- **`SmergeRunsP` is false at `T = 0`** — the same defect as the skeleton: the contract demands
`s'.pc = base + 66` but with `k = 0` the state has not moved, so `base = base + 66`. -/
theorem smergeRunsP_false_zero (P : Program) (E : RAMEnv) (base : ℕ) (hW : 1 < 2 ^ E.W) :
    ¬ SmergeRunsP P E base 0 0 0 0 0 0 := by
  have hpos : 0 < 2 ^ E.W := Nat.two_pow_pos E.W
  intro h
  obtain ⟨k, s', hk, hstep, hpc, hnod, hset⟩ := h ⟨base, fun _ => 0, fun _ => 0⟩ rfl
    ⟨rfl, rfl, rfl, rfl, rfl⟩
    (by
      intro v hv
      simp [listAt] at hv)
    (by show (0 : ℕ) < 2 ^ E.W; exact hpos)
    (by show (0 : ℕ) < 2 ^ E.W; exact hpos)
    (by show (0 : ℕ) < 2 ^ E.W; exact hpos)
    (by left; omega)
    (by left; omega)
  have hk0 : k = 0 := by
    have h2 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h3 : (k : ℝ) = 0 := by linarith
    exact_mod_cast h3
  subst hk0
  simp only [Function.iterate_zero_apply] at hstep
  rw [← hstep] at hpc
  rw [mergeStmtFull_len] at hpc
  change base = base + 66 at hpc
  omega


/-- The repack loop's full precondition, as one predicate. -/
def RepackPre (E : RAMEnv) (R j len listBase : ℕ) (x : Fin R → ZMod 2) (s : RAMState) : Prop :=
  (s.regs r0 = 0 ∧ s.regs r7 = listBase ∧ s.regs r8 = len ∧
    s.regs r11 = E.W ∧ s.regs r6 = wordsOf E.W R ∧ s.regs r5 = rowSlot E R j) ∧
  (∀ i, i < wordsOf E.W R → s.mem (rowSlot E R j + i) = 0) ∧
  (∀ v, v ∈ listAt s listBase len → v < 2 ^ E.W) ∧
  (∀ v, v ∈ listAt s listBase len → v < R) ∧
  len < 2 ^ E.W ∧ listBase + len ≤ 2 ^ E.W ∧ rowSlot E R j + wordsOf E.W R ≤ 2 ^ E.W ∧
  (listBase + len ≤ rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ listBase) ∧
  ListSupports (listAt s listBase len) x

/-- **The row stage's repack loop has a full `StageRun`.**  The premise `At` is the honest one: the
contract speaks about a program with the loop at `base`, and that is exactly what a caller of the
row body has.  Cost: `20 · len + 20`. -/
theorem repackStageRun (P : Program) (E : RAMEnv) {R : ℕ} (x : Fin R → ZMod 2)
    (base j len listBase : ℕ) (hAt : At P base (Stmt.compile repackStmt base)) (hW : 1 < 2 ^ E.W) :
    StageRun P E base (base + repackStmt.len) ((20 * len + 20 : ℕ) : ℝ)
      (RepackPre E R j len listBase x) (fun s => RowOut E R j x s.mem) := by
  intro s hpc hI
  obtain ⟨hregs, hz, hval, hRv, hlen, hadr, hadr2, hdisj, hsupp⟩ := hI
  obtain ⟨k, s', hk, hstep, hpc', hrow⟩ :=
    repackRunsS_proved (P := P) (E := E) (R := R) x (base := base) (j := j) (len := len)
      (listBase := listBase) (T := ((20 * len + 20 : ℕ) : ℝ)) hAt hW le_rfl
      hAt s hpc hregs hz hval hRv hlen hadr hadr2 hdisj hsupp
  exact ⟨k, s', hk, hstep, hpc', hrow⟩

end RDL
end LinearSetReconciliation327.Main


