-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_RowStage2Mirror20261122
-- name    : LinearSetReconciliation327_Main_RowStage2Mirror20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:11:06.838561+00:00
-- url     : https://prove2.me/theorems/c8ec2cb1-dcf3-474d-b513-0b2f37c28988
-- title:
--   Row-stage mirror: the `RowStage2` contract on the `DecoderLemmas` side
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_RowStage2Mirror20261122` of the Theorem 6.5 development.  It is a re-hosted mirror of the project's published row-stage bundle with only the recorded edits (the import of the `DecoderLemmas` side replaced by the `P21DetBndComp` chain, and — for the `Pay` mirrors — the per-row payload base re-pointed to the arithmetic progression `payTabAddr + j * stageLen`); the statements of the row chain are byte-identical.  It contains definitions and fully proved lemmas only (no `sorry`, no new axiom) and exists so that the later nodes of the chain compile inside the platform's per-definition budget.  This is a supporting node, not a statement of independent mathematical interest.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder) and Proposition 2.1 (the base-relative decoder); the project's verified row-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_RowScratch20261121
import Definitions.Def_LinearSetReconciliation327_Main_RowDecode20261121
import Definitions.Def_LinearSetReconciliation327_Main_P21BndAux20261122
import Definitions.Def_LinearSetReconciliation327_Main_Top65Dec
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_DecodeClose20261121
import Definitions.Def_LinearSetReconciliation327_Main_MergeStep20261121

/-!
# `RowStage2` — the dispatch block, the closed row-head family, and a bounded-cost loop rule

Round: repair Theorem 6.5's row stage in the shape the published `TopDecStagesZ` asks for.

* **§1** the two-instruction dispatch block `[iImm r1 0, iImm r2 ell]` between the row loop and the
  column loop: its one-shot `Sem`, its `ColIn ell` post, and the assembled variant `zProgDecOfTop`
  (the published `topDecStmt` is left untouched);
* **§2** the address plumbing of that variant;
* **§3** the corrected row-head family `zLoopHeads`, closed under `d65Inc`: the family at `j+1` is
  the family at `j` with the test register set to `1` and the counter to `j+1` — no hypothesis on
  `j`, in particular `r7 = 1` at every `j ≥ 1`;
* **§4** the strengthened entry predicate `zRowIn`, which carries the payload word bound the row
  body's clearing/staging pass consumes;
* **§5** `stageRun_counted_loop_le`, the upper-bounded loop rule (`k ≤ cost j` per iteration);
* **§6** the row loop re-closed, with post `r1 = d ∧ r2 = d`, and the row stage followed by the
  dispatch, reaching `ColIn ell` at `ell ≥ 1`;
* **§7** the column loop leaves `r1 = ell`, so the next stage (`ColOutAsZ`) is register-free and
  needs no second dispatch — but the same loop rule and the same splice apply if it ever does;
* **§8** a non-vacuous inhabitant at `d = 2`, `ell = 3` with concrete empty bodies: the machine
  really runs the `d`-fold loop, lands with `r1 = 2`, `r2 = 2`, executes the dispatch, and reaches
  `ColIn 3` at address `9`.

No `sorry`, no new axiom, nothing imported from `Solutions.*`, and no published file modified.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace RSD

open R66 RDec RMR

/-! ## 1. The dispatch block `[iImm r1 0, iImm r2 ell]` -/

/-- The block that separates the two counted loops.  Without it the column loop inherits the row
loop's `r1 = d`, `r2 = d` and can never satisfy `ColIn ell`. -/
def zDispatch (ell : ℕ) : Stmt := .code [iImm r1 0, iImm r2 ell]

theorem zDispatch_len (ell : ℕ) : (zDispatch ell).len = 2 := rfl

theorem zDispatch_compile (ell pc : ℕ) :
    (zDispatch ell).compile pc = [iImm r1 0, iImm r2 ell] := rfl

theorem zImm_noBranch (d : Fin 16) (v : ℕ) : NoBranch [iImm d v] := by
  simp [NoBranch, Instr.NoBranchI]

theorem zImm_run (E : RAMEnv) (pc : ℕ) (d : Fin 16) (v : ℕ) (r : Fin 16 → ℕ) (m : ℕ → ℕ) :
    runBlock [iImm d v] E ⟨pc, r, m⟩
      = ⟨pc + 1, Function.update r d (v % 2 ^ E.W), m⟩ := by
  simp [runBlock, execInstr]

/-- The dispatch block's register effect: `r1 := 0`, then `r2 := ell`, memory untouched. -/
theorem zDispatch_run (E : RAMEnv) (pc ell : ℕ) (r : Fin 16 → ℕ) (m : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hell : ell < 2 ^ E.W) :
    runBlock [iImm r1 0, iImm r2 ell] E ⟨pc, r, m⟩
      = ⟨pc + 2, Function.update (Function.update r r1 0) r2 ell, m⟩ := by
  rw [show ([iImm r1 0, iImm r2 ell] : List Instr) = [iImm r1 0] ++ [iImm r2 ell] from rfl,
    runBlock_append, zImm_run, zImm_run]
  simp only [Nat.zero_mod, Nat.mod_eq_of_lt hell]

/-- **The dispatch block, as one `Sem`.**  Two steps, from any state at `pc`, to `pc + 2` with
`r1 = 0`, `r2 = ell` and the memory untouched. -/
theorem zDispatch_sem {P : Program} {E : RAMEnv} {pc ell : ℕ} {s : RAMState}
    (hAt : At P pc [iImm r1 0, iImm r2 ell]) (hpc : s.pc = pc)
    (hW : 1 < 2 ^ E.W) (hell : ell < 2 ^ E.W) :
    Sem P E pc (pc + 2) s
      (fun k z => k = 2 ∧ z.pc = pc + 2 ∧ z.regs r1 = 0 ∧ z.regs r2 = ell ∧
        z.mem = s.mem) := by
  refine Sem.mono (Sem.block P E pc [iImm r1 0, iImm r2 ell] s hAt ?_ hpc) ?_
  · simp [NoBranch, Instr.NoBranchI]
  · rintro k z ⟨hk, rfl⟩
    obtain ⟨p, r, m⟩ := s
    simp only at hpc
    subst hpc
    rw [zDispatch_run E p ell r m hW hell]
    refine ⟨hk, rfl, ?_, ?_, rfl⟩
    · show (Function.update (Function.update r r1 0) r2 ell) r1 = 0
      rw [Function.update_of_ne (by decide : r1 ≠ r2), Function.update_self]
    · show (Function.update (Function.update r r1 0) r2 ell) r2 = ell
      rw [Function.update_self]

/-- **The dispatch establishes `ColIn ell`** — non-vacuously for every `ell < 2^W`, in particular
at every `ell ≥ 1`. -/
theorem zDispatch_ColIn {P : Program} {E : RAMEnv} {pc ell : ℕ} {s : RAMState}
    (hAt : At P pc [iImm r1 0, iImm r2 ell]) (hpc : s.pc = pc)
    (hW : 1 < 2 ^ E.W) (hell : ell < 2 ^ E.W) :
    Sem P E pc (pc + 2) s (fun k z => k = 2 ∧ ColIn ell z ∧ z.mem = s.mem) := by
  refine Sem.mono (zDispatch_sem hAt hpc hW hell) ?_
  rintro k z ⟨hk, -, h1, h2, hm⟩
  exact ⟨hk, ⟨h1, h2⟩, hm⟩

/-- **The decoder variant with the dispatch spliced in.**  `Sinit ; loop Srow ; dispatch ; loop
Sdec ; Sassem ; Sres ; Scr` — the published `topDecStmt` is not modified. -/
def zTopDecStmt (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) : Stmt :=
  .seq Sinit (.seq (topLoop Srow)
    (.seq (zDispatch ell) (.seq (topLoop Sdec) (.seq Sassem (.seq Sres Scr)))))

/-- The assembled decoder as a flat `Program`. -/
def zProgDecOfTop (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) : Program :=
  (zTopDecStmt Sinit Srow Sdec Sassem Sres Scr ell).compile 0 ++ [Instr.halt]

/-! ## 2. Addresses of the variant -/

/-- Address of the row loop (unchanged). -/
def zDRowBase (Sinit : Stmt) : ℕ := 0 + Sinit.len

/-- Address of the dispatch block: where the published `dColBase` puts the column loop. -/
def zDColBase (Sinit Srow : Stmt) : ℕ := zDRowBase Sinit + (topLoop Srow).len

/-- Address of the column loop: two instructions after `zDColBase`. -/
def zDColHead (Sinit Srow : Stmt) (ell : ℕ) : ℕ := zDColBase Sinit Srow + (zDispatch ell).len

/-- Address of the prefix assembly. -/
def zDAsBase (Sinit Srow Sdec : Stmt) (ell : ℕ) : ℕ :=
  zDColHead Sinit Srow ell + (topLoop Sdec).len

theorem zAt_row_seqD (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (zDRowBase Sinit)
      (Stmt.compile (Stmt.seq (topLoop Srow)
        (Stmt.seq (zDispatch ell) (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr)))))
        (zDRowBase Sinit)) := by
  have h0 : At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) 0
      ((zTopDecStmt Sinit Srow Sdec Sassem Sres Scr ell).compile 0) := At.compile_top _
  exact at_seq_right (a := Sinit)
    (b := Stmt.seq (topLoop Srow)
      (Stmt.seq (zDispatch ell) (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr))))) h0

theorem zAt_row_loopD (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (zDRowBase Sinit)
      (Stmt.compile (topLoop Srow) (zDRowBase Sinit)) :=
  at_seq_left (a := topLoop Srow)
    (b := Stmt.seq (zDispatch ell) (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr))))
    (zAt_row_seqD Sinit Srow Sdec Sassem Sres Scr ell)

theorem zAt_dispatch_seqD (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (zDColBase Sinit Srow)
      (Stmt.compile (Stmt.seq (zDispatch ell)
        (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr))))
        (zDColBase Sinit Srow)) :=
  at_seq_right (a := topLoop Srow)
    (b := Stmt.seq (zDispatch ell) (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr))))
    (zAt_row_seqD Sinit Srow Sdec Sassem Sres Scr ell)

theorem zAt_dispatchD (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (zDColBase Sinit Srow)
      (Stmt.compile (zDispatch ell) (zDColBase Sinit Srow)) :=
  at_seq_left (a := zDispatch ell)
    (b := Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr)))
    (zAt_dispatch_seqD Sinit Srow Sdec Sassem Sres Scr ell)

/-- The dispatch block's instructions at their address. -/
theorem zAt_dispatch_codeD (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (zDColBase Sinit Srow)
      [iImm r1 0, iImm r2 ell] := by
  have h := zAt_dispatchD Sinit Srow Sdec Sassem Sres Scr ell
  simpa [zDispatch, Stmt.compile] using h

theorem zAt_col_loopD (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (zDColHead Sinit Srow ell)
      (Stmt.compile (topLoop Sdec) (zDColHead Sinit Srow ell)) :=
  at_seq_left (a := topLoop Sdec) (b := Stmt.seq Sassem (Stmt.seq Sres Scr))
    (at_seq_right (a := zDispatch ell)
      (b := Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr)))
      (zAt_dispatch_seqD Sinit Srow Sdec Sassem Sres Scr ell))

/-! ## 3. The corrected row-head family -/

/-- **The loop-head family.**  At iteration `j` the counter is `j`, the bound is `d`, the test
register is `0` only at the entry (`j = 0`) and `1` afterwards — exactly what `d65Inc` leaves. -/
def zLoopHeads (a : ℕ) (d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) : RAMState :=
  ⟨a,
    (fun i => if i = r1 then j else if i = r2 then d
      else if i = r7 then (if j = 0 then 0 else 1) else 0),
    M j⟩

/-- The row loop's head family at the published row address. -/
def zRowHeads (Sinit : Stmt) (d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) : RAMState :=
  zLoopHeads (zDRowBase Sinit) d M j

theorem zLoopHeads_pc (a d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) : (zLoopHeads a d M j).pc = a := rfl

theorem zLoopHeads_regs1 (a d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) :
    (zLoopHeads a d M j).regs r1 = j := by
  show (if r1 = r1 then j else if r1 = r2 then d
    else if r1 = r7 then (if j = 0 then 0 else 1) else 0) = j
  rw [if_pos rfl]

theorem zLoopHeads_regs2 (a d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) :
    (zLoopHeads a d M j).regs r2 = d := by
  show (if r2 = r1 then j else if r2 = r2 then d
    else if r2 = r7 then (if j = 0 then 0 else 1) else 0) = d
  rw [if_neg (by decide : r2 ≠ r1), if_pos rfl]

theorem zLoopHeads_regs7 (a d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) :
    (zLoopHeads a d M j).regs r7 = (if j = 0 then 0 else 1) := by
  show (if r7 = r1 then j else if r7 = r2 then d
    else if r7 = r7 then (if j = 0 then 0 else 1) else 0) = (if j = 0 then 0 else 1)
  rw [if_neg (by decide : r7 ≠ r1), if_neg (by decide : r7 ≠ r2), if_pos rfl]

/-- **The defect repaired.**  At every `j ≥ 1` the family carries `r7 = 1`, which is what
`d65Inc` leaves; the published `rowHeads` fixed `r7 = 0` and was therefore not an iteration
family at all. -/
theorem zLoopHeads_regs7_of_pos (a d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) (hj : j ≠ 0) :
    (zLoopHeads a d M j).regs r7 = 1 := by
  rw [zLoopHeads_regs7, if_neg hj]

/-- The same, in the literal form the body leaves: `r7 = 1 % 2^W`. -/
theorem zLoopHeads_regs7_mod (E : RAMEnv) (a d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) (hj : j ≠ 0)
    (hW : 1 < 2 ^ E.W) :
    (zLoopHeads a d M j).regs r7 = 1 % 2 ^ E.W := by
  rw [zLoopHeads_regs7_of_pos a d M j hj, Nat.mod_eq_of_lt hW]

/-- **Closure of the family under the loop tail.**  The family at `j + 1` is obtained from the
family at `j` by setting the test register to `1` and the counter to `j + 1`, with no condition on
`j` at all — this is the exact sense in which the new family is closed. -/
theorem zLoopHeads_succ_regs (a d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) :
    (zLoopHeads a d M (j + 1)).regs
      = Function.update (Function.update (zLoopHeads a d M j).regs r7 1) r1 (j + 1) := by
  funext i
  fin_cases i <;>
    simp [zLoopHeads, Function.update_self, Function.update_of_ne]

theorem zLoopHeads_go (a d : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) (hj : j < d) :
    d65Cond.eval (zLoopHeads a d M j) := by
  simp only [d65Cond, Cond.eval, zLoopHeads_regs1, zLoopHeads_regs2]
  exact hj

theorem zLoopHeads_stop (a d : ℕ) (M : ℕ → ℕ → ℕ) : ¬ d65Cond.eval (zLoopHeads a d M d) := by
  simp only [d65Cond, Cond.eval, zLoopHeads_regs1, zLoopHeads_regs2]
  omega

theorem zD65Cond_code_length : d65Cond.code.length = 1 := rfl

/-- The test `r7 < r1 r2` preserves `r1` and `r2`. -/
theorem zCond_regs_pres (E : RAMEnv) (t : RAMState) :
    (runBlock d65Cond.code E t).regs 1 = t.regs 1 ∧
      (runBlock d65Cond.code E t).regs 2 = t.regs 2 := by
  constructor <;> simp [d65Cond, Cond.code, runBlock, execInstr]

theorem zCond_mem (E : RAMEnv) (t : RAMState) :
    (runBlock d65Cond.code E t).mem = t.mem := by
  simp [d65Cond, Cond.code, runBlock, execInstr]

/-- The test, taken, writes only `r7 := 1`. -/
theorem zCond_run_true (E : RAMEnv) (t : RAMState) (h : t.regs r1 < t.regs r2)
    (hW : 1 < 2 ^ E.W) :
    runBlock d65Cond.code E t
      = { t with pc := t.pc + 1, regs := Function.update t.regs r7 1 } := by
  simp [d65Cond, Cond.code, runBlock, execInstr, h, Nat.mod_eq_of_lt hW]

theorem zCond_regs_true (E : RAMEnv) (t : RAMState) (h : t.regs r1 < t.regs r2)
    (hW : 1 < 2 ^ E.W) :
    (runBlock d65Cond.code E t).regs = Function.update t.regs r7 1 := by
  rw [zCond_run_true E t h hW]

/-- Records are equal when their three fields are. -/
theorem zRamState_eq_of {s t : RAMState} (hpc : s.pc = t.pc)
    (hregs : ∀ i, s.regs i = t.regs i) (hmem : s.mem = t.mem) : s = t := by
  obtain ⟨p, r, m⟩ := s
  obtain ⟨p', r', m'⟩ := t
  simp only at hpc hregs hmem
  subst hpc
  subst hmem
  have hr : r = r' := funext hregs
  subst hr
  rfl

theorem zD65Inc_run (E : RAMEnv) (pc : ℕ) (r : Fin 16 → ℕ) (m : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (h1 : (1 : ℕ) % 2 ^ E.W = 1) :
    runBlock d65Inc E ⟨pc, r, m⟩
      = ⟨pc + 2, Function.update (Function.update r r7 1) r1 ((r r1 + 1) % 2 ^ E.W), m⟩ := by
  simp [d65Inc, runBlock, execInstr, h1]

/-- The counter increment `d65Inc` as a two-instruction `Sem`. -/
theorem zD65Inc_sem {P : Program} {E : RAMEnv} {pc : ℕ} {r : Fin 16 → ℕ} {m : ℕ → ℕ}
    (hAt : At P pc d65Inc) (hW : 1 < 2 ^ E.W) :
    Sem P E pc (pc + 2) ⟨pc, r, m⟩
      (fun k z => k = 2 ∧
        z = ⟨pc + 2, Function.update (Function.update r r7 1) r1 ((r r1 + 1) % 2 ^ E.W), m⟩) := by
  refine Sem.mono (Sem.block P E pc d65Inc ⟨pc, r, m⟩ hAt
    (by simp [d65Inc, NoBranch, Instr.NoBranchI]) rfl) ?_
  rintro k z ⟨hk, rfl⟩
  refine ⟨hk, ?_⟩
  rw [zD65Inc_run E pc r m hW (Nat.mod_eq_of_lt hW)]

/-- **One counter step of the family**: after the test has set `r7 = 1`, `d65Inc` carries
`zLoopHeads j` to `zLoopHeads (j+1)` (up to the program counter, which is the argument `pc`). -/
theorem zLoopHeads_d65Inc (E : RAMEnv) (a n : ℕ) (mm : ℕ → ℕ) (j pc : ℕ)
    (hj : j < n) (hjw : j + 1 < 2 ^ E.W) (hW : 1 < 2 ^ E.W) :
    runBlock d65Inc E ⟨pc, (runBlock d65Cond.code E (zLoopHeads a n (fun _ => mm) j)).regs, mm⟩
      = ⟨pc + 2, (zLoopHeads a n (fun _ => mm) (j + 1)).regs, mm⟩ := by
  have hlt : (zLoopHeads a n (fun _ => mm) j).regs r1 < (zLoopHeads a n (fun _ => mm) j).regs r2 := by
    rw [zLoopHeads_regs1, zLoopHeads_regs2]
    exact hj
  rw [zCond_regs_true E _ hlt hW,
    zD65Inc_run E pc _ mm hW (by rw [Nat.mod_eq_of_lt hW])]
  refine zRamState_eq_of rfl ?_ rfl
  intro i
  fin_cases i <;>
    simp [zLoopHeads, Function.update_self, Function.update_of_ne, Nat.mod_eq_of_lt hjw]

/-- The register half of `zLoopHeads_d65Inc`, in the shape `zD65Inc_sem` produces it. -/
theorem zD65Inc_regs_eq (E : RAMEnv) (a n : ℕ) (mm : ℕ → ℕ) (j pc : ℕ)
    (hj : j < n) (hjw : j + 1 < 2 ^ E.W) (hW : 1 < 2 ^ E.W) :
    Function.update (Function.update (runBlock d65Cond.code E (zLoopHeads a n (fun _ => mm) j)).regs r7 1) r1
      (((runBlock d65Cond.code E (zLoopHeads a n (fun _ => mm) j)).regs r1 + 1) % 2 ^ E.W)
      = (zLoopHeads a n (fun _ => mm) (j + 1)).regs := by
  have h2 := zLoopHeads_d65Inc E a n mm j pc hj hjw hW
  rw [zD65Inc_run E pc _ mm hW (by rw [Nat.mod_eq_of_lt hW])] at h2
  exact congrArg RAMState.regs h2

/-- **One body of the empty-body model**: `d65Inc` then the trailing `jmp`, with the loop's own
address `a`.  This is the concrete witness that the corrected family is reachable. -/
theorem zLoopBody_empty_sem {P : Program} {E : RAMEnv} {a n : ℕ} {m : ℕ → ℕ} {j : ℕ}
    (hAtLoop : At P a (Stmt.compile (Stmt.loop d65Cond (.seq (.code []) (.code d65Inc))) a))
    (hW : 1 < 2 ^ E.W) (hj : j < n) (hjw : j + 1 < 2 ^ E.W) :
    Sem P E (a + d65Cond.code.length + 1) a
      { runBlock d65Cond.code E (zLoopHeads a n (fun _ => m) j) with
        pc := a + d65Cond.code.length + 1 }
      (fun k s' => k = 3 ∧ s' = zLoopHeads a n (fun _ => m) (j + 1)) := by
  obtain ⟨-, -, hbodyAt, hjmp⟩ := at_loop hAtLoop
  have hAtInc : At P (a + d65Cond.code.length + 1) d65Inc := by
    simpa [Stmt.compile] using hbodyAt
  have hinc : Sem P E (a + d65Cond.code.length + 1)
      (a + d65Cond.code.length + 1 + 2)
      { runBlock d65Cond.code E (zLoopHeads a n (fun _ => m) j) with
        pc := a + d65Cond.code.length + 1 }
      (fun k z => k = 2 ∧ z = ⟨a + d65Cond.code.length + 1 + 2,
        (zLoopHeads a n (fun _ => m) (j + 1)).regs, m⟩) := by
    refine Sem.mono (zD65Inc_sem (P := P) (E := E) (pc := a + d65Cond.code.length + 1)
      (r := (runBlock d65Cond.code E (zLoopHeads a n (fun _ => m) j)).regs) (m := m) hAtInc hW) ?_
    rintro k z ⟨hk, rfl⟩
    exact ⟨hk, by
      rw [zD65Inc_regs_eq E a n m j (a + d65Cond.code.length + 1) hj hjw hW]⟩
  have hjmp' : P[a + d65Cond.code.length + 1 + 2]? = some (iJmp a) := by
    simpa [d65Inc, Stmt.len] using hjmp
  refine Sem.jmp_append (hAt := hjmp') ?_
  refine Sem.mono hinc ?_
  rintro k z ⟨hk, rfl⟩
  refine ⟨by omega, ?_⟩
  rfl

/-! ## 4. The strengthened entry predicate -/

/-- **`RowIn` with the memory the row body actually needs.**  Besides the register shape it fixes
the per-iteration memory sequence `M` (iteration `j` starts from `M j`, so the body is free to
write row `j`'s output into `M (j+1)`) and requires every row's staged payload block to consist of
words (`< 2^W`), which is exactly `clearReloadStage_sem`'s `hword` hypothesis.  The layout fact
`decoderAllocEnd t ≤ rowPayBase E j` is an environment side condition, just as in
`clearReloadStage_sem`'s `hKrow`. -/
def zRowIn (Sinit : Stmt) (E : RAMEnv) (d : ℕ) (M : ℕ → ℕ → ℕ) : RAMState → Prop :=
  fun s => s = zRowHeads Sinit d M 0 ∧
    ∀ j < d, ∀ i < stageLen E, M j (rowPayBase E j + i) < 2 ^ E.W

theorem zRowIn_regs1 {Sinit E d M s} (h : zRowIn Sinit E d M s) : s.regs 1 = 0 := by
  rw [h.1]
  exact zLoopHeads_regs1 (zDRowBase Sinit) d M 0

theorem zRowIn_regs2 {Sinit E d M s} (h : zRowIn Sinit E d M s) : s.regs 2 = d := by
  rw [h.1]
  exact zLoopHeads_regs2 (zDRowBase Sinit) d M 0

theorem zRowIn_mem {Sinit E d M s} (h : zRowIn Sinit E d M s) : s.mem = M 0 := by
  rw [h.1]
  rfl

/-- **`zRowIn` feeds the row body's clearing/staging pass**: this is precisely the `hword`
hypothesis of `clearReloadStage_sem` (kept, not re-derived, from the previous round). -/
theorem zRowIn_hword {Sinit E d M s} (h : zRowIn Sinit E d M s) {j : ℕ} (hj : j < d) :
    ∀ i, i < stageLen E → M j (rowPayBase E j + i) < 2 ^ E.W :=
  fun i hi => h.2 j hj i hi

/-- **`zRowIn` really strengthens the published `RowIn`**: it implies `RowIn d` (counter `0`,
bound `d`) and adds the memory the row body needs. -/
theorem zRowIn_implies_RowIn {Sinit E d M s} (h : zRowIn Sinit E d M s) : RowIn d s :=
  ⟨zRowIn_regs1 h, zRowIn_regs2 h⟩

/-- **`zRowIn` is inhabited at every `d`**, in particular at a real `d ≥ 1`: take the all-zero
memory, whose payload words are `0 < 2^W`.  (The stale `RowIn` was inhabited too; the point here
is that the *strengthened* one is.) -/
theorem zRowIn_nonvacuous (Sinit : Stmt) (E : RAMEnv) (d : ℕ) :
    zRowIn Sinit E d (fun _ _ => 0) (zRowHeads Sinit d (fun _ _ => 0) 0) := by
  refine ⟨rfl, ?_⟩
  intro j hj i hi
  exact Nat.two_pow_pos E.W

/-! ## 5. The upper-bounded loop rule -/

/-- **The loop rule with `≤` per iteration** (R3).  `Sem.loop`/`stageRun_counted_loop` want
`k = cost j`; the decode/repack/stage contracts only give `≤`, so the total is bounded by
`n · (K + len + 1) + (len + 1)`.  The exit state is the explicit
`{runBlock c.code E (s n) with pc := …}`. -/
theorem stageRun_counted_loop_le {P : Program} {E : RAMEnv} {a : ℕ} {c : Cond} {b : Stmt}
    {n : ℕ} {s : ℕ → RAMState} {cost : ℕ → ℕ} {K : ℝ}
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W)
    (hpc : ∀ j, (s j).pc = a) (hgo : ∀ j < n, c.eval (s j)) (hstop : ¬ c.eval (s n))
    (hbody : ∀ j < n, Sem P E (a + c.code.length + 1) a
      { runBlock c.code E (s j) with pc := a + c.code.length + 1 }
      (fun k s' => k ≤ cost j ∧ s' = s (j + 1)))
    (hcost : ∀ j < n, (cost j : ℝ) ≤ K) (hK : 0 ≤ K) :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (n : ℝ) * (K + ((c.code.length : ℝ) + 1)) + ((c.code.length : ℝ) + 2) ∧
      (step P E)^[k] (s 0) = s' ∧ s'.pc = a + c.code.length + b.len + 2 ∧
      s' = { runBlock c.code E (s n) with pc := a + c.code.length + b.len + 2 } := by
  obtain ⟨-, k, s', hstep, hb, hk, hst⟩ :=
    Sem.loopLe P E a c b hAt hW n s cost hpc hgo hstop hbody
  have hsum : ((∑ j ∈ Finset.range n, (c.code.length + 1 + cost j) : ℕ) : ℝ) ≤
      (n : ℝ) * (((c.code.length : ℝ) + 1) + K) := by
    rw [Nat.cast_sum]
    calc (∑ j ∈ Finset.range n, ((c.code.length + 1 + cost j : ℕ) : ℝ))
        ≤ ∑ j ∈ Finset.range n, (((c.code.length : ℝ) + 1) + K) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h1 : (cost j : ℝ) ≤ K := hcost j (Finset.mem_range.mp hj)
          have h2 : ((c.code.length + 1 + cost j : ℕ) : ℝ) =
              ((c.code.length : ℝ) + 1) + (cost j : ℝ) := by push_cast; ring
          rw [h2]; linarith
      _ = (n : ℝ) * (((c.code.length : ℝ) + 1) + K) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hkR : (k : ℝ) ≤ ((c.code.length : ℝ) + 1) +
      (n : ℝ) * (((c.code.length : ℝ) + 1) + K) := by
    have h4 : (k : ℝ) ≤ ((c.code.length + 1 : ℕ) : ℝ) +
        ((∑ j ∈ Finset.range n, (c.code.length + 1 + cost j) : ℕ) : ℝ) := by
      exact_mod_cast hk
    have h5 : ((c.code.length + 1 : ℕ) : ℝ) = (c.code.length : ℝ) + 1 := by push_cast; ring
    linarith
  refine ⟨k, s', ?_, hstep, hb, hst⟩
  rw [show K + ((c.code.length : ℝ) + 1) = ((c.code.length : ℝ) + 1) + K from by ring]
  linarith

/-! ## 6. The row loop and the row stage -/

/-- **The `d`-fold loop re-closed, with the corrected family.**  It lands on the dispatch block
with `r1 = d` and `r2 = d` — the state the loop really produces, and the one the corrected `row`
post must advertise.  Cost `d · (K + 2) + 3`. -/
theorem zTopLoopHeads_stageRun {P : Program} {E : RAMEnv} {a : ℕ} {b : Stmt}
    {n K : ℕ} {M : ℕ → ℕ → ℕ}
    (hAt : At P a (Stmt.compile (Stmt.loop d65Cond b) a)) (hW : 1 < 2 ^ E.W)
    (hbody : ∀ j < n, Sem P E (a + d65Cond.code.length + 1) a
      { runBlock d65Cond.code E (zLoopHeads a n M j) with
        pc := a + d65Cond.code.length + 1 }
      (fun k s' => k ≤ K ∧ s' = zLoopHeads a n M (j + 1))) :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (n : ℝ) * ((K : ℝ) + 2) + 3 ∧
      (step P E)^[k] (zLoopHeads a n M 0) = s' ∧
      s' = { runBlock d65Cond.code E (zLoopHeads a n M n) with
        pc := a + d65Cond.code.length + b.len + 2 } ∧
      s'.pc = a + d65Cond.code.length + b.len + 2 ∧
      s'.regs 1 = n ∧ s'.regs 2 = n ∧ s'.mem = M n := by
  obtain ⟨k, s', hk, hstep, hpc, hst⟩ :=
    stageRun_counted_loop_le (P := P) (E := E) (a := a) (c := d65Cond) (b := b)
      (n := n) (s := zLoopHeads a n M) (cost := fun _ => K) (K := (K : ℝ))
      hAt hW (fun j => zLoopHeads_pc a n M j) (fun j hj => zLoopHeads_go a n M j hj)
      (zLoopHeads_stop a n M) hbody (fun _ _ => le_refl _) (by positivity)
  refine ⟨k, s', ?_, hstep, hst, hpc, ?_, ?_, ?_⟩
  · rw [show ((d65Cond.code.length : ℝ) + 1) = 2 from by
        rw [zD65Cond_code_length]; norm_num,
      show ((d65Cond.code.length : ℝ) + 2) = 3 from by
        rw [zD65Cond_code_length]; norm_num] at hk
    simpa using hk
  · rw [hst]
    show (runBlock d65Cond.code E (zLoopHeads a n M n)).regs 1 = n
    rw [(zCond_regs_pres E (zLoopHeads a n M n)).1, zLoopHeads_regs1]
  · rw [hst]
    show (runBlock d65Cond.code E (zLoopHeads a n M n)).regs 2 = n
    rw [(zCond_regs_pres E (zLoopHeads a n M n)).2, zLoopHeads_regs2]
  · rw [hst]
    show (runBlock d65Cond.code E (zLoopHeads a n M n)).mem = M n
    rw [zCond_mem]
    rfl

/-- The row-loop instance of `zTopLoopHeads_stageRun`. -/
theorem zRowLoop_stageRun {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {d K ell : ℕ} {M : ℕ → ℕ → ℕ}
    (hW : 1 < 2 ^ E.W)
    (hbody : ∀ j < d, Sem (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (zDRowBase Sinit + d65Cond.code.length + 1) (zDRowBase Sinit)
      { runBlock d65Cond.code E (zRowHeads Sinit d M j) with
        pc := zDRowBase Sinit + d65Cond.code.length + 1 }
      (fun k s' => k ≤ K ∧ s' = zRowHeads Sinit d M (j + 1))) :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (d : ℝ) * ((K : ℝ) + 2) + 3 ∧
      (step (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E)^[k]
        (zRowHeads Sinit d M 0) = s' ∧
      s'.pc = zDColBase Sinit Srow ∧ s'.regs 1 = d ∧ s'.regs 2 = d ∧ s'.mem = M d := by
  obtain ⟨k, s', hk, hstep, -, hpc, h1, h2, hm⟩ :=
    zTopLoopHeads_stageRun (P := zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (E := E)
      (a := zDRowBase Sinit) (b := .seq Srow (.code d65Inc)) (n := d) (K := K) (M := M)
      (zAt_row_loopD Sinit Srow Sdec Sassem Sres Scr ell) hW hbody
  refine ⟨k, s', hk, hstep, ?_, h1, h2, hm⟩
  rw [hpc]
  show zDRowBase Sinit + d65Cond.code.length + (Stmt.seq Srow (.code d65Inc)).len + 2
    = zDColBase Sinit Srow
  simp only [zDColBase, topLoop, Stmt.len]
  omega

/-- **The row stage with the corrected post `r1 = d ∧ r2 = d`.**  This is what replaces the
published `fun s => RowOut s ∧ ColIn sch.ell s`, which was unsatisfiable at every `ell ≥ 1`.
`RowOut` is the published `RAMState → Prop`; only its memory dependence is used, and `hframe`
records exactly that (every concrete `RowOut` of the pipeline is a predicate on `s.mem`). -/
theorem zRowStage_rowPost {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {d K ell : ℕ} {M : ℕ → ℕ → ℕ} {RowOut : RAMState → Prop}
    (hW : 1 < 2 ^ E.W)
    (hbody : ∀ j < d, Sem (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (zDRowBase Sinit + d65Cond.code.length + 1) (zDRowBase Sinit)
      { runBlock d65Cond.code E (zRowHeads Sinit d M j) with
        pc := zDRowBase Sinit + d65Cond.code.length + 1 }
      (fun k s' => k ≤ K ∧ s' = zRowHeads Sinit d M (j + 1)))
    (hframe : ∀ s t : RAMState, s.mem = t.mem → (RowOut s ↔ RowOut t))
    (hOut : RowOut (zRowHeads Sinit d M d)) :
    ∀ s : RAMState, s.pc = zDRowBase Sinit → zRowIn Sinit E d M s →
      ∃ (k : ℕ) (s' : RAMState),
        (k : ℝ) ≤ (d : ℝ) * ((K : ℝ) + 2) + 3 ∧
        (step (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E)^[k] s = s' ∧
        s'.pc = zDColBase Sinit Srow ∧ RowOut s' ∧ s'.regs 1 = d ∧ s'.regs 2 = d := by
  intro s hpc hI
  obtain ⟨k, s', hk, hstep, hp, h1, h2, hm⟩ :=
    zRowLoop_stageRun (Sinit := Sinit) (Srow := Srow) (Sdec := Sdec) (Sassem := Sassem)
      (Sres := Sres) (Scr := Scr) (E := E) (d := d) (K := K) (ell := ell) (M := M)
      hW hbody
  rw [← hI.1] at hstep
  refine ⟨k, s', hk, hstep, hp, ?_, h1, h2⟩
  exact (hframe s' (zRowHeads Sinit d M d) (by rw [hm]; rfl)).mpr hOut

/-- **The row stage plus the dispatch: the column loop's entry `ColIn ell` is inhabited at every
`ell ≥ 1`.**  Cost `Trow + 2`. -/
theorem zRowStage_dispatch {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {d K ell : ℕ} {M : ℕ → ℕ → ℕ} {RowOut : RAMState → Prop}
    (hW : 1 < 2 ^ E.W) (hell : ell < 2 ^ E.W)
    (hbody : ∀ j < d, Sem (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (zDRowBase Sinit + d65Cond.code.length + 1) (zDRowBase Sinit)
      { runBlock d65Cond.code E (zRowHeads Sinit d M j) with
        pc := zDRowBase Sinit + d65Cond.code.length + 1 }
      (fun k s' => k ≤ K ∧ s' = zRowHeads Sinit d M (j + 1)))
    (hframe : ∀ s t : RAMState, s.mem = t.mem → (RowOut s ↔ RowOut t))
    (hOut : RowOut (zRowHeads Sinit d M d)) :
    StageRun (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (zDRowBase Sinit) (zDColHead Sinit Srow ell)
      ((d : ℝ) * ((K : ℝ) + 2) + 5) (zRowIn Sinit E d M)
      (fun s => RowOut s ∧ ColIn ell s) := by
  intro s hpc hI
  obtain ⟨k1, s1, hk1, hstep1, hp1, hOut1, h1, h2⟩ :=
    zRowStage_rowPost (Sinit := Sinit) (Srow := Srow) (Sdec := Sdec) (Sassem := Sassem)
      (Sres := Sres) (Scr := Scr) (E := E) (d := d) (K := K) (ell := ell) (M := M)
      (RowOut := RowOut) hW hbody hframe hOut s hpc hI
  obtain ⟨-, k2, s2, hstep2, hp2, hk2, hcol, hm2⟩ :=
    zDispatch_ColIn (P := zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell)
      (pc := zDColBase Sinit Srow) (ell := ell) (s := s1)
      (zAt_dispatch_codeD Sinit Srow Sdec Sassem Sres Scr ell) hp1 hW hell
  refine ⟨k1 + k2, s2, ?_, ?_, hp2, ?_⟩
  · have hk2' : (k2 : ℝ) = 2 := by exact_mod_cast hk2
    push_cast
    linarith
  · rw [Nat.add_comm, Function.iterate_add_apply, hstep1, hstep2]
  · exact ⟨(hframe s2 s1 hm2).mpr hOut1, hcol⟩

/-! ## 7. The column loop: the same defect, and why it needs no second dispatch -/

/-- **The column loop, closed by the same rule.**  It leaves `r1 = ell`, `r2 = ell` at the address
`zDAsBase`.  The successor `Sassem`'s precondition `ColOutAsZ` is a pure memory predicate (it
mentions no register), so the column stage needs **no** dispatch of its own; only a stage whose
precondition constrains `r1`/`r2` would need one, and then the same `zDispatch` applies. -/
theorem zColLoop_stageRun {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {ell Kc ell0 : ℕ} {Mc : ℕ → ℕ → ℕ}
    (hW : 1 < 2 ^ E.W)
    (hbody : ∀ j < ell, Sem (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell0) E
      (zDColHead Sinit Srow ell0 + d65Cond.code.length + 1) (zDColHead Sinit Srow ell0)
      { runBlock d65Cond.code E (zLoopHeads (zDColHead Sinit Srow ell0) ell Mc j) with
        pc := zDColHead Sinit Srow ell0 + d65Cond.code.length + 1 }
      (fun k s' => k ≤ Kc ∧ s' = zLoopHeads (zDColHead Sinit Srow ell0) ell Mc (j + 1))) :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (ell : ℝ) * ((Kc : ℝ) + 2) + 3 ∧
      (step (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell0) E)^[k]
        (zLoopHeads (zDColHead Sinit Srow ell0) ell Mc 0) = s' ∧
      s'.pc = zDAsBase Sinit Srow Sdec ell0 ∧ s'.regs 1 = ell ∧ s'.regs 2 = ell ∧
      s'.mem = Mc ell := by
  obtain ⟨k, s', hk, hstep, -, hpc, h1, h2, hm⟩ :=
    zTopLoopHeads_stageRun (P := zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell0) (E := E)
      (a := zDColHead Sinit Srow ell0) (b := .seq Sdec (.code d65Inc)) (n := ell) (K := Kc)
      (M := Mc) (zAt_col_loopD Sinit Srow Sdec Sassem Sres Scr ell0) hW hbody
  refine ⟨k, s', hk, hstep, ?_, h1, h2, hm⟩
  rw [hpc]
  show zDColHead Sinit Srow ell0 + d65Cond.code.length
      + (Stmt.seq Sdec (.code d65Inc)).len + 2 = zDAsBase Sinit Srow Sdec ell0
  simp only [zDAsBase, topLoop, Stmt.len]
  omega

/-- **`ColOutAsZ` is register-free.**  Every conjunct is a predicate on `s.mem` only, so the column
loop's exit `r1 = ell`, `r2 = ell` cannot obstruct the assembly stage: **no second dispatch is
needed** after the column loop.  (If a successor *did* constrain `r1`/`r2`, the same `zDispatch`
splice would apply — that is the general form of the defect.) -/
theorem zColOutAsZ_mem_congr {E : RAMEnv} {m M : ℕ} {Aset : Finset ℕ}
    {pref : Fin m → List (ZMod 2)} {s t : RAMState} (h : s.mem = t.mem) :
    C8R.ColOutAsZ E m M Aset s pref ↔ C8R.ColOutAsZ E m M Aset t pref := by
  simp [C8R.ColOutAsZ, C8R.CopyPre, C8R.HoldsVecPad, C8R.HoldsVec, C8R.DstZero, h]

/-! ## 8. A non-vacuous inhabitant at `d = 2`, `ell = 3`

The bodies are empty (`Srow = Sdec = Sassem = Sres = Scr = .code []`), so the *machine really
runs*: the row loop performs its `d = 2` iterations of `d65Inc`, the dispatch executes, and the
column loop is entered with `ColIn 3`.  Nothing here is a degenerate `d = ell = 0` instance: the
defect of the previous round was that **no** `ell ≥ 1` instance existed. -/

namespace Model

/-- A concrete environment: `W = 8`, and every `det` slot reads `200`. -/
def E : RAMEnv :=
  { W := 8, det := fun _ => 200, perm := fun _ _ => 0, permInv := fun _ _ => 0,
    coeff := fun _ _ => 0 }

theorem hW : 1 < 2 ^ E.W := by
  show (1 : ℕ) < 2 ^ 8
  norm_num

theorem hell : 3 < 2 ^ E.W := by
  show (3 : ℕ) < 2 ^ 8
  norm_num

/-- The prologue: `r1 := 0`, `r2 := 2` — a real two-instruction `Sinit`, not a degenerate one. -/
def Sinit : Stmt := .code [iImm r1 0, iImm r2 2]

/-- The empty body used for every stage of the model. -/
def Snil : Stmt := .code []

/-- The all-zero memory. -/
def m0 : ℕ → ℕ := fun _ => 0

/-- The constant memory sequence of the model. -/
def M0 : ℕ → ℕ → ℕ := fun _ => m0

/-- The assembled decoder. -/
def P : Program := zProgDecOfTop Sinit Snil Snil Snil Snil Snil 3

theorem dRowBase_eq : zDRowBase Sinit = 2 := rfl

theorem dColBase_eq : zDColBase Sinit Snil = 7 := by
  simp [zDColBase, zDRowBase, topLoop, Stmt.len, Sinit, Snil, d65Cond, Cond.code, d65Inc]

theorem dColHead_eq : zDColHead Sinit Snil 3 = 9 := by
  simp [zDColHead, dColBase_eq, zDispatch, Stmt.len]

/-- The row loop sits at address `2` in the assembled program. -/
theorem hAtRowLoop :
    At P 2 (Stmt.compile (Stmt.loop d65Cond (.seq (.code []) (.code d65Inc))) 2) := by
  have h := zAt_row_loopD Sinit Snil Snil Snil Snil Snil 3
  rw [dRowBase_eq] at h
  simpa [P, topLoop, Snil] using h

/-- **One iteration of the model body**, cost `3` (`d65Inc` plus the `jmp`). -/
theorem hbody : ∀ j < 2, Sem P E (2 + d65Cond.code.length + 1) 2
    { runBlock d65Cond.code E (zRowHeads Sinit 2 M0 j) with
      pc := 2 + d65Cond.code.length + 1 }
    (fun k s' => k ≤ 3 ∧ s' = zRowHeads Sinit 2 M0 (j + 1)) := by
  intro j hj
  have hjw : j + 1 < 2 ^ E.W := by
    rw [show E.W = 8 from rfl]
    omega
  have h := zLoopBody_empty_sem (P := P) (E := E) (a := 2) (n := 2) (m := m0) (j := j)
    hAtRowLoop hW hj hjw
  refine Sem.mono h ?_
  intro k s' hs
  exact ⟨le_of_eq hs.1, hs.2⟩

/-- `zRowIn` holds at the model's entry. -/
theorem hRowIn : zRowIn Sinit E 2 M0 (zRowHeads Sinit 2 M0 0) :=
  zRowIn_nonvacuous Sinit E 2

/-- **The row stage's corrected post, concretely**: the loop lands at the dispatch block with
`r1 = 2`, `r2 = 2`, in at most `2·(3+2)+3 = 13` steps. -/
theorem rowPostRun :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (2 : ℝ) * ((3 : ℝ) + 2) + 3 ∧
      (step P E)^[k] (zRowHeads Sinit 2 M0 0) = s' ∧
      s'.pc = zDColBase Sinit Snil ∧ s'.mem = m0 ∧ s'.regs 1 = 2 ∧ s'.regs 2 = 2 :=
  zRowStage_rowPost (Sinit := Sinit) (Srow := Snil) (Sdec := Snil) (Sassem := Snil)
    (Sres := Snil) (Scr := Snil) (E := E) (d := 2) (K := 3) (ell := 3) (M := M0)
    (RowOut := fun s => s.mem = m0) hW hbody
    (by intro s t h; rw [h]) rfl (zRowHeads Sinit 2 M0 0) rfl hRowIn

/-- **The row stage plus the dispatch, concretely.**  This is the round's success criterion: a real
`d = 2`, a real `ell = 3`, and the column loop's entry `ColIn 3` is reached at address `9`. -/
theorem main :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (2 : ℝ) * ((3 : ℝ) + 2) + 5 ∧
      (step P E)^[k] (zRowHeads Sinit 2 M0 0) = s' ∧
      s'.pc = 9 ∧ s'.mem = m0 ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 3 := by
  have hSR : StageRun P E 2 (zDColHead Sinit Snil 3) ((2 : ℝ) * ((3 : ℝ) + 2) + 5)
      (zRowIn Sinit E 2 M0) (fun s => s.mem = m0 ∧ ColIn 3 s) :=
    zRowStage_dispatch (Sinit := Sinit) (Srow := Snil) (Sdec := Snil) (Sassem := Snil)
      (Sres := Snil) (Scr := Snil) (E := E) (d := 2) (K := 3) (ell := 3) (M := M0)
      (RowOut := fun s => s.mem = m0) hW hell hbody
      (by intro s t h; rw [h]) rfl
  obtain ⟨k, s', hk, hstep, hp, hout, hcol⟩ := hSR (zRowHeads Sinit 2 M0 0) rfl hRowIn
  refine ⟨k, s', hk, hstep, ?_, hout, hcol.1, hcol.2⟩
  rw [hp, dColHead_eq]

/-- Non-vacuity of the parameters themselves: `d = 2 ≥ 1` and `ell = 3 ≥ 1`. -/
theorem params_nonvacuous : 1 ≤ (2 : ℕ) ∧ 1 ≤ (3 : ℕ) := ⟨by norm_num, by norm_num⟩

/-- The column loop's address in the model. -/
theorem dColHead_eq9 : zDColHead Sinit Snil 3 = 9 := dColHead_eq

/-- The assembly stage's address in the model. -/
theorem dAsBase_eq : zDAsBase Sinit Snil Snil 3 = 14 := by
  rw [zDAsBase, dColHead_eq]
  simp [topLoop, Stmt.len, Snil, d65Cond, Cond.code, d65Inc]

/-- The column loop sits at address `9`. -/
theorem hAtColLoop :
    At P 9 (Stmt.compile (Stmt.loop d65Cond (.seq (.code []) (.code d65Inc))) 9) := by
  have h := zAt_col_loopD Sinit Snil Snil Snil Snil Snil 3
  rw [dColHead_eq] at h
  simpa [P, topLoop, Snil] using h

/-- **One iteration of the column-loop model body.** -/
theorem colHbody : ∀ j < 3, Sem P E (9 + d65Cond.code.length + 1) 9
    { runBlock d65Cond.code E (zLoopHeads 9 3 M0 j) with
      pc := 9 + d65Cond.code.length + 1 }
    (fun k s' => k ≤ 3 ∧ s' = zLoopHeads 9 3 M0 (j + 1)) := by
  intro j hj
  have hjw : j + 1 < 2 ^ E.W := by
    rw [show E.W = 8 from rfl]
    omega
  have h := zLoopBody_empty_sem (P := P) (E := E) (a := 9) (n := 3) (m := m0) (j := j)
    hAtColLoop hW hj hjw
  refine Sem.mono h ?_
  intro k s' hs
  exact ⟨le_of_eq hs.1, hs.2⟩

/-- **The column loop, non-vacuously**: from `ColIn 3` it runs its `ell = 3` iterations and exits
with `r1 = 3`, `r2 = 3` at the assembly stage's address `14`.  This is why a successor that asked
for `ColIn` again would need its own dispatch — and why the published `ColOutAsZ`, which is
register-free, does not. -/
theorem colLoopRun :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (3 : ℝ) * ((3 : ℝ) + 2) + 3 ∧
      (step P E)^[k] (zLoopHeads 9 3 M0 0) = s' ∧
      s'.pc = 14 ∧ s'.regs 1 = 3 ∧ s'.regs 2 = 3 ∧ s'.mem = m0 := by
  obtain ⟨k, s', hk, hstep, hp, h1, h2, hm⟩ :=
    zColLoop_stageRun (Sinit := Sinit) (Srow := Snil) (Sdec := Snil) (Sassem := Snil)
      (Sres := Snil) (Scr := Snil) (E := E) (ell := 3) (Kc := 3) (ell0 := 3) (Mc := M0)
      hW colHbody
  refine ⟨k, s', hk, hstep, ?_, h1, h2, hm⟩
  rw [hp, dAsBase_eq]

end Model

end RSD
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.RSD.zDispatch_sem
#print axioms LinearSetReconciliation327.Main.RSD.zDispatch_ColIn
#print axioms LinearSetReconciliation327.Main.RSD.zLoopHeads_succ_regs
#print axioms LinearSetReconciliation327.Main.RSD.zRowIn_nonvacuous
#print axioms LinearSetReconciliation327.Main.RSD.stageRun_counted_loop_le
#print axioms LinearSetReconciliation327.Main.RSD.zTopLoopHeads_stageRun
#print axioms LinearSetReconciliation327.Main.RSD.zRowLoop_stageRun
#print axioms LinearSetReconciliation327.Main.RSD.zRowStage_rowPost
#print axioms LinearSetReconciliation327.Main.RSD.zRowStage_dispatch
#print axioms LinearSetReconciliation327.Main.RSD.zColLoop_stageRun
#print axioms LinearSetReconciliation327.Main.RSD.Model.main


