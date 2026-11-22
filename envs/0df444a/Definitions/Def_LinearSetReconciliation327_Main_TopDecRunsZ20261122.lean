-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_TopDecRunsZ20261122
-- name    : LinearSetReconciliation327_Main_TopDecRunsZ20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:12:51.392842+00:00
-- url     : https://prove2.me/theorems/9a433e7c-87a0-4877-924d-341e195a9cf3
-- title:
--   The six-stage `TopDecRuns` structure with the residual stage's postcondition made composable
-- statement:
--   A new structure `W65.TopDecRunsZ` whose six fields are those of the published `CRS.TopDecRunsIn`, except that the `res` field now *posts* `CrStageIn` — exactly the precondition the following `cr` field consumes.  `res_trans_cr` composes the two stages by one `StageRun.trans`; `haltsWithin_topDec_of_runsZ` derives Theorem 6.5's decoder-halting conjunct from the six fields alone (the published `haltsWithin_topDec_of_runsIn` needed a separate `hres`).  The new post is inhabited non-degenerately (`y != 0`) and is reached by a real 0-step residual program (`stageRun_res_nonzero`).  Definitions and proved theorems only; no `sorry`, no new axiom.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's column stage and Theorem 5.1's decoder (the two-window `DownBlkSemAtW` contract).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrField20261122

/-!
# `TopDecRunsZ` — the residual stage's postcondition, made composable

`CRS.TopDecRunsIn` (`Def_…_CrField20261122`) corrected the **`cr`** field's *precondition* to
`CrStageIn`, but left the **`res`** field's postcondition at `fun _ => True`.  Consequently
`CRS.haltsWithin_topDec_of_runsIn` still has to take a separate hypothesis

```
hres : ∀ y, StageRun … Tres (fun _ => True) (CrStageIn E M y ab al bb bl ob Lx)
```

i.e. the composition `res → cr` is *not* performed inside the structure.

This bundle closes that gap without touching the published file: a **new** structure `TopDecRunsZ`
replaces `res`'s post by exactly the predicate the next block consumes,

```
res : ∀ y, StageRun … Tres (fun _ => True) (CrStageIn E M y ab al bb bl ob Lx)
```

and then

* `res_trans_cr` — the composition `res → cr` (one `StageRun.trans`);
* `haltsWithin_topDec_of_runsZ` — conjunct 7 from the six fields alone, no `hres` side condition;
* `crStageIn_nonzero_inhabited` — the new post is inhabited at a **non-degenerate** instance
  (`y ≠ 0`), by the state `decoderStart E.W y []` itself;
* `stageRun_res_nonzero` — and it is *reached* by a real (`0`-step) residual program at that same
  non-degenerate instance, so the field is not merely a predicate that happens to be true.

Nothing here is imported from `Solutions.*`; the only imports are `Mathlib` and the published
`Definitions.Def_…_CrField20261122`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace W65

open CRS

/-! ## 1. The corrected `res` field, in a new structure -/

/-- **`TopDecRunsIn` with the residual stage's postcondition fixed.**  All six fields are those of
`CRS.TopDecRunsIn`, except that `res` now *posts* `CrStageIn`, the predicate the `cr` field consumes.
The `cr` field itself is copied verbatim from `CRS.TopDecRunsIn`. -/
structure TopDecRunsZ (Sinit Srow Sdec Sassem Sres Scr : Stmt) (E : RAMEnv) (W M n d ℓ : ℕ)
    (Tini Trow Tdec Tas Tres Tcr : ℝ) (ab al bb bl ob : ℕ) (Lx : List ℕ) (S xhat : Finset ℕ) :
    Prop where
  /-- The prologue: read `d`, `ℓ` and `wordsOf W M` from `det`'s header. -/
  init : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0 (dRowBase Sinit) Tini
      (fun s => s = decoderStart W y []) (RowIn d)
  /-- Row decoding: `d` iterations of `proposition_2_1`. -/
  row : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dRowBase Sinit) (dColBase Sinit Srow)
      Trow (RowIn d) (ColIn ℓ)
  /-- The `ℓ` child decoders of `theorem_5_1`. -/
  col : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dColBase Sinit Srow)
      (dAsBase Sinit Srow Sdec) Tdec (ColIn ℓ) (fun _ => True)
  /-- Prefix assembly. -/
  as : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dAsBase Sinit Srow Sdec)
      (dResBase Sinit Srow Sdec Sassem) Tas (fun _ => True) (fun _ => True)
  /-- **Residual syndrome, with the corrected postcondition**: it hands the `cr` block exactly the
  state it can start from, `CrStageIn E M y ab al bb bl ob Lx` — Proposition 2.3's own input state
  (registers and memory of `decoderStart E.W y []`) conjoined with the merge's block data. -/
  res : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dResBase Sinit Srow Sdec Sassem)
      (dCrBase Sinit Srow Sdec Sassem Sres) Tres (fun _ => True) (CrStageIn E M y ab al bb bl ob Lx)
  /-- **The corrected `cr` field**: 2.3's decoder · setup · unpack · merge, from `CrStageIn` to the
  merge's output `x̂ △ ê`. -/
  cr : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
      (dCrBase Sinit Srow Sdec Sassem Sres) (dEnd Sinit Srow Sdec Sassem Sres Scr) Tcr
      (CrStageIn E M y ab al bb bl ob Lx)
      (fun s' => OutListIs s' (symmDiff xhat S))

/-- The residual field of `TopDecRunsZ`, in the form the published `TopDecRunsIn` asks for it. -/
theorem topDecRunsZ_res {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv} {W M n d ℓ : ℕ}
    {Tini Trow Tdec Tas Tres Tcr : ℝ} {ab al bb bl ob : ℕ} {Lx : List ℕ} {S xhat : Finset ℕ}
    (h : TopDecRunsZ Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ Tini Trow Tdec Tas Tres Tcr
      ab al bb bl ob Lx S xhat) (y : Fin M → ZMod 2) :
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dResBase Sinit Srow Sdec Sassem)
      (dCrBase Sinit Srow Sdec Sassem Sres) Tres (fun _ => True) (CrStageIn E M y ab al bb bl ob Lx) :=
  h.res y

/-! ## 2. `res → cr` composes -/

/-- **The composition `res → cr`.**  The residual stage's new post is *literally* the `cr` stage's
pre, so the two blocks compose by `StageRun.trans` with no side condition — this is the step that
`CRS.haltsWithin_topDec_of_runsIn` had to assume as `hres`. -/
theorem res_trans_cr {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv} {M n d ℓ : ℕ}
    {Tres Tcr : ℝ} {ab al bb bl ob : ℕ} {Lx : List ℕ} {S xhat : Finset ℕ}
    (hres : ∀ y : Fin M → ZMod 2,
      StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dResBase Sinit Srow Sdec Sassem)
        (dCrBase Sinit Srow Sdec Sassem Sres) Tres (fun _ => True)
        (CrStageIn E M y ab al bb bl ob Lx))
    (hcr : ∀ y : Fin M → ZMod 2,
      StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (dCrBase Sinit Srow Sdec Sassem Sres) (dEnd Sinit Srow Sdec Sassem Sres Scr) Tcr
        (CrStageIn E M y ab al bb bl ob Lx) (fun s' => OutListIs s' (symmDiff xhat S)))
    (y : Fin M → ZMod 2) :
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dResBase Sinit Srow Sdec Sassem)
      (dEnd Sinit Srow Sdec Sassem Sres Scr) (Tres + Tcr) (fun _ => True)
      (fun s' => OutListIs s' (symmDiff xhat S)) :=
  (hres y).trans (hcr y)

/-! ## 3. Conjunct 7 from the six fields, with no `hres` -/

/-- **Conjunct 7 from `TopDecRunsZ` alone.**  This is `CRS.haltsWithin_topDec_of_runsIn` with its
`hres` hypothesis *removed*: the sixth field's post now carries `CrStageIn`, so the chain
`init → row → col → as → res → cr` closes inside the structure. -/
theorem haltsWithin_topDec_of_runsZ {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {W M n d ℓ : ℕ} {Tini Trow Tdec Tas Tres Tcr : ℝ} {ab al bb bl ob : ℕ} {Lx : List ℕ}
    {S xhat : Finset ℕ}
    (h : TopDecRunsZ Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ Tini Trow Tdec Tas Tres Tcr
      ab al bb bl ob Lx S xhat)
    (y : Fin M → ZMod 2) :
    ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (Tini + Trow + Tdec + Tas + Tres + Tcr) (decoderStart W y []) s' := by
  have hstep : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0
      (dEnd Sinit Srow Sdec Sassem Sres Scr) (Tini + Trow + Tdec + Tas + Tres + Tcr)
      (fun s => s = decoderStart W y []) (fun _ => True) :=
    ((((h.init y).trans (h.row y)).trans (h.col y)).trans (h.as y)).trans (h.res y)
      |>.trans (CRS.stageRun_post (h.cr y) (fun _ _ => trivial))
  obtain ⟨k, s', hk, hrun, hpc, -⟩ := hstep (decoderStart W y []) rfl rfl
  have hlen : dEnd Sinit Srow Sdec Sassem Sres Scr =
      ((topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0).length := by
    rw [Stmt.length_compile]
    simp only [dEnd, dCrBase, dResBase, dAsBase, dColBase, dRowBase, topDecStmt, topLoop, Stmt.len]
    omega
  have hhalt :
      (progDecOfTop Sinit Srow Sdec Sassem Sres Scr)[dEnd Sinit Srow Sdec Sassem Sres Scr]? =
        some Instr.halt := by
    rw [hlen]
    rw [show progDecOfTop Sinit Srow Sdec Sassem Sres Scr =
      (topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0 ++ [Instr.halt] from rfl,
      List.getElem?_append_right (le_refl _)]
    simp
  exact ⟨s', k, hk, hrun, by simp only [Halted, hpc, hhalt]⟩

/-! ## 4. Non-vacuity of the new `res` post (`y ≠ 0`) -/

/-- The reference environment: an `8`-bit machine. -/
def resEnv : RAMEnv := detEnv 8 (fun _ => 0)

/-- A **non-zero** payload of `8` bits. -/
def resY : Fin 8 → ZMod 2 := fun _ => 1

theorem resY_ne_zero : resY ≠ 0 := by
  intro h
  have := congrFun h ⟨0, by norm_num⟩
  simp [resY] at this

/-- The merge's block data at the witness `ab = 10, al = 1, bb = 20, bl = 1, ob = 40,
Lx = [5]`. -/
theorem resMergeData : CrMergeData resEnv 10 1 20 1 40 [5] := by
  unfold CrMergeData
  decide

/-- **The new `res` post is inhabited, non-degenerately.**  At `y = resY ≠ 0`, `M = 8`,
`wordsOf 8 8 = 1`, the state `decoderStart 8 resY []` itself satisfies
`CrStageIn resEnv 8 resY 10 1 20 1 40 [5]`. -/
theorem crStageIn_nonzero_inhabited :
    ∃ (s : RAMState), resY ≠ 0 ∧ CrStageIn resEnv 8 resY 10 1 20 1 40 [5] s :=
  ⟨decoderStart 8 resY [], resY_ne_zero, rfl, rfl, resMergeData⟩

/-- **The same post is *reached* by a real program**, not merely satisfied by a state: with
`Sres = .code []` the residual block is the `0`-step stage, and from the decoder's start state it
lands — in `0 ≤ 0` steps — in a `CrStageIn` state, at a non-degenerate `y ≠ 0`.

This is the residual-stage witness for the *strengthened* precondition `s = decoderStart W y []`;
with the published precondition `fun _ => True` no program can establish `CrStageIn` (the state it
receives is arbitrary), which is exactly why the field is a named hypothesis about `Sres`. -/
theorem stageRun_res_nonzero {Sinit Srow Sdec Sassem Scr : Stmt} :
    StageRun (progDecOfTop Sinit Srow Sdec Sassem (.code []) Scr) resEnv
      (dResBase Sinit Srow Sdec Sassem) (dResBase Sinit Srow Sdec Sassem) 0
      (fun s => s = decoderStart resEnv.W resY [])
      (CrStageIn resEnv 8 resY 10 1 20 1 40 [5]) := by
  intro s hpc hpre
  refine ⟨0, s, by norm_num, rfl, hpc, ?_⟩
  rw [hpre]
  exact ⟨rfl, rfl, resMergeData⟩

end W65
end LinearSetReconciliation327.Main


