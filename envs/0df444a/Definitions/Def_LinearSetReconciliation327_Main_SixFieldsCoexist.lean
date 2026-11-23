-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_SixFieldsCoexist
-- name    : LinearSetReconciliation327_Main_SixFieldsCoexist
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T09:40:31.188177+00:00
-- url     : https://prove2.me/theorems/f6f03aff-e14c-4b38-b44a-4427af71e4c7
-- title:
--   Theorem 6.5: the six `TopDecRunsZ` fields in one environment, with the row chain mirrored
-- statement:
--   The coexistence surface for Theorem 6.5's six decoder-stage fields.  It imports the `DecoderLemmas`-side row-chain mirrors (`DecodeLoopsMirror`, `RowStage3Mirror`), `CrField`, `TopDecRunsZ`, `InitStageZ`, `ColWire`, `ColWrap`, `ColLoopW` and `HintDecBase51At` — an import list that Lean rejected before the mirrors (`…P21DetFront failed, environment already contains 'axpyBody_spec'`).  It proves `topDecRunsZ_of_six` (the introduction rule, six field types verbatim), `rowStage_real` (the real row loop + dispatch fired from the mirrored chain), and `topDecRunsZ_model`: a concrete `W65.TopDecRunsZ` value in which `init`, `row`, `col`, `as` and `cr` are proved and the sixth field `res` is the interface hypothesis it is (its pre is `fun _ => True`, its post pins the incoming state to `decoderStart`, so it is not derivable from a stage theorem).  Axiom-clean: `[propext, Classical.choice, Quot.sound]`; no `sorry`, no new axiom; local `cpl` 5 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder); the project's verified row-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecodeLoopsMirror
import Definitions.Def_LinearSetReconciliation327_Main_RowStage3Mirror
import Definitions.Def_LinearSetReconciliation327_Main_CrField20261122
import Definitions.Def_LinearSetReconciliation327_Main_TopDecRunsZ20261122
import Definitions.Def_LinearSetReconciliation327_Main_InitStageZ20261122
import Definitions.Def_LinearSetReconciliation327_Main_ColWire20261122
import Definitions.Def_LinearSetReconciliation327_Main_ColWrap20261122
import Definitions.Def_LinearSetReconciliation327_Main_ColLoopW20261122
import Definitions.Def_LinearSetReconciliation327_Main_HintDecBase51At20261122

/-!
# The six fields of `W65.TopDecRunsZ` in one environment

This file is the **coexistence surface** for Theorem 6.5's six decoder-stage fields.  The
`DecoderLemmas`-side row-stage mirrors (`RowStage2Mirror`, and here `RowStage3Mirror` /
`DecodeLoopsMirror`) are imported together with `CrField`, `ColWire`, `ColWrap`, `ColLoopW`,
`HintDecBase51At`, `InitStageZ` and `TopDecRunsZ`.  Before the mirrors this import list was
rejected by Lean (`…P21DetFront failed, environment already contains 'axpyBody_spec' …`).

Contents:

* §1 `topDecRunsZ_of_six` — the introduction rule: a `TopDecRunsZ` value from its six fields,
  with each field's type written exactly as in the published structure;
* §2 `topDecRunsZ_model` — a concrete **structure value**: the `init`, `row`, `col`, `as` and `cr`
  fields are *proved*, and only the `res` field is supplied as the interface hypothesis it is
  (its pre is `fun _ => True`, so it cannot be derived from a stage theorem — see the note);
* §3 the exact statements, quoted for the report.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

namespace W65

open CRS

/-! ## 1. Introduction rule: the six fields, verbatim -/

/-- **`TopDecRunsZ` from its six fields.**  The field types are copied verbatim from the published
structure; this is the term the six stage theorems have to produce, and it typechecks only in an
environment that contains both the row chain and `CrField`. -/
theorem topDecRunsZ_of_six {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {W M n d ℓ : ℕ} {Tini Trow Tdec Tas Tres Tcr : ℝ} {ab al bb bl ob : ℕ} {Lx : List ℕ}
    {S xhat : Finset ℕ}
    (hinit : ∀ y : Fin M → ZMod 2,
      StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0 (dRowBase Sinit) Tini
        (fun s => s = decoderStart W y []) (RowIn d))
    (hrow : ∀ y : Fin M → ZMod 2,
      StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dRowBase Sinit)
        (dColBase Sinit Srow) Trow (RowIn d) (ColIn ℓ))
    (hcol : ∀ y : Fin M → ZMod 2,
      StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dColBase Sinit Srow)
        (dAsBase Sinit Srow Sdec) Tdec (ColIn ℓ) (fun _ => True))
    (has : ∀ y : Fin M → ZMod 2,
      StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dAsBase Sinit Srow Sdec)
        (dResBase Sinit Srow Sdec Sassem) Tas (fun _ => True) (fun _ => True))
    (hres : ∀ y : Fin M → ZMod 2,
      StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dResBase Sinit Srow Sdec Sassem)
        (dCrBase Sinit Srow Sdec Sassem Sres) Tres (fun _ => True)
        (CrStageIn E M y ab al bb bl ob Lx))
    (hcr : ∀ y : Fin M → ZMod 2,
      StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (dCrBase Sinit Srow Sdec Sassem Sres) (dEnd Sinit Srow Sdec Sassem Sres Scr) Tcr
        (CrStageIn E M y ab al bb bl ob Lx)
        (fun s' => OutListIs s' (symmDiff xhat S))) :
    TopDecRunsZ Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ Tini Trow Tdec Tas Tres Tcr
      ab al bb bl ob Lx S xhat :=
  ⟨hinit, hrow, hcol, has, hres, hcr⟩

/-! ## 2. A structure value at the degenerate model

`M = d = ℓ = 0`, every stage empty, `W = 8`, `E = detEnv 8 (fun _ => 0)`, `S = xhat = ∅`.  The
`init` stage is `0` steps, the two loops exit on their first test (`2` steps each), and the
`as`/`cr` blocks are `0`-step.  The `res` field is the one interface hypothesis: its precondition
is `fun _ => True`, while its postcondition pins the incoming registers and memory to
`decoderStart E.W y []`, so no stage theorem can establish it from an arbitrary state. -/

/-- The model environment. -/
def sixEnv : RAMEnv := detEnv 8 (fun _ => 0)

/-- `wordsOf W 0 = 0` (local copy; the published one lives in `C8R`). -/
theorem wordsOf_zero_local (W : ℕ) : wordsOf W 0 = 0 := by
  unfold wordsOf
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h; simp
  · exact Nat.div_eq_of_lt (by omega)

/-- `symmDiff ∅ ∅ = ∅`. -/
theorem symmDiff_empty_empty_local : symmDiff (∅ : Finset ℕ) ∅ = ∅ := by
  ext v; simp [mem_symmDiff]

/-- The zero-length loop test fails immediately. -/
theorem d65_zero_false {s : RAMState} (h1 : s.regs 1 = 0) (h2 : s.regs 2 = 0) :
    ¬ d65Cond.eval s := by
  simp [d65Cond, Cond.eval, h1, h2]

/-- **Five fields proved, `res` assumed.**  A genuine `TopDecRunsZ` value: `init`, `row`, `col`,
`as`, `cr` are terms of the exact field types; the sixth field is the interface hypothesis
`hres` (its pre is `True` and its post pins the decoder's start state). -/
theorem topDecRunsZ_model
    (hres : ∀ y : Fin 0 → ZMod 2,
      StageRun (progDecOfTop (.code []) (.code []) (.code []) (.code []) (.code []) (.code []))
        sixEnv (dResBase (.code []) (.code []) (.code []) (.code []))
        (dCrBase (.code []) (.code []) (.code []) (.code []) (.code [])) 0
        (fun _ => True) (CrStageIn sixEnv 0 y 0 0 0 0 0 [])) :
    TopDecRunsZ (.code []) (.code []) (.code []) (.code []) (.code []) (.code [])
      sixEnv 8 0 0 0 0 0 2 2 0 0 0 0 0 0 0 0 [] (∅ : Finset ℕ) ∅ := by
  refine ⟨?_, ?_, ?_, ?_, hres, ?_⟩
  · -- `init`: `0` steps from `decoderStart` to `dRowBase = 0`
    intro y s hpc hpre
    refine ⟨0, s, by norm_num, rfl, ?_, ?_⟩
    · rw [hpre]; rfl
    · rw [hpre]
      refine ⟨?_, ?_⟩ <;> simp [decoderStart, initState, wordsOf_zero_local]
  · -- `row`: the `d = 0` loop exits on its first test
    intro y s hpc hpre
    obtain ⟨h1, h2⟩ := hpre
    have hstop : ¬ d65Cond.eval s := d65_zero_false h1 h2
    obtain ⟨-, k, s', hstep, hpc', hk, hs'⟩ :=
      Sem.loopExit (progDecOfTop (.code []) (.code []) (.code []) (.code []) (.code []) (.code []))
        sixEnv (dRowBase (.code [])) d65Cond (.seq (.code []) (.code d65Inc)) s
        (at_row_loop (.code []) (.code []) (.code []) (.code []) (.code []) (.code []))
        (by norm_num [sixEnv, detEnv]) hpc hstop
    refine ⟨k, s', ?_, hstep, ?_, ?_⟩
    · rw [hk]; norm_num [d65Cond, Cond.code]
    · rw [hpc']
      simp [dColBase, dRowBase, topLoop, d65Cond, Cond.code, Stmt.len]
    · rw [hs']
      show (runBlock d65Cond.code sixEnv s).regs 1 = 0 ∧ (runBlock d65Cond.code sixEnv s).regs 2 = 0
      have h71 : r7 ≠ r1 := by decide
      have h72 : r7 ≠ r2 := by decide
      simp [d65Cond, Cond.code, runBlock, execInstr, h71, h72, h1, h2]
  · -- `col`: the `ℓ = 0` loop exits on its first test
    intro y s hpc hpre
    obtain ⟨h1, h2⟩ := hpre
    have hstop : ¬ d65Cond.eval s := d65_zero_false h1 h2
    obtain ⟨-, k, s', hstep, hpc', hk, hs'⟩ :=
      Sem.loopExit (progDecOfTop (.code []) (.code []) (.code []) (.code []) (.code []) (.code []))
        sixEnv (dColBase (.code []) (.code [])) d65Cond (.seq (.code []) (.code d65Inc)) s
        (at_col_loop (.code []) (.code []) (.code []) (.code []) (.code []) (.code []))
        (by norm_num [sixEnv, detEnv]) hpc hstop
    refine ⟨k, s', ?_, hstep, ?_, trivial⟩
    · rw [hk]; norm_num [d65Cond, Cond.code]
    · rw [hpc']
      simp [dAsBase, dColBase, dRowBase, topLoop, d65Cond, Cond.code, Stmt.len] <;> omega
  · -- `as`: the empty assembly block, `0` steps from `True` to `True`
    intro y s hpc hpre
    refine ⟨0, s, by norm_num, rfl, ?_, trivial⟩
    rw [hpc]; simp [dResBase, Stmt.len]
  · -- `cr`: the empty CR block, `0` steps; `CrStageIn` fixes `r1 = 0`, so `outList = []`
    intro y s hpc hpre
    have h1 : s.regs 1 = 0 := by
      have h := hpre.1
      rw [h]
      simp [decoderStart, initState, wordsOf_zero_local]
    refine ⟨0, s, by norm_num, rfl, ?_, ?_⟩
    · rw [hpc]; simp [dEnd, dCrBase, dResBase, Stmt.len]
    · show OutListIs s (symmDiff (∅ : Finset ℕ) ∅)
      rw [symmDiff_empty_empty_local]
      refine ⟨?_, ?_⟩
      · have h0 : outList s = [] := by simp [outList, h1]
        rw [h0]; exact List.nodup_nil
      · intro v
        have h0 : outList s = [] := by simp [outList, h1]
        rw [h0]; simp


/-! ## 3. The mirrored row stage is live

RSD.zRowStage_dispatch (from RowStage2Mirror, reachable through RowStage3Mirror) is the real
row loop followed by the two-instruction dispatch.  We re-export it here so the file demonstrably
*uses* the mirrored row chain, not merely imports it. -/

/-- **The real row stage (mirrored chain) fires.**  This is RSD.zRowStage_dispatch, the row loop
d times plus the dispatch, with the per-row body hbody as its only structural hypothesis. -/
theorem rowStage_real {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {d K ell : ℕ} {M : ℕ → ℕ → ℕ} {RowOut : RAMState → Prop}
    (hW : 1 < 2 ^ E.W) (hell : ell < 2 ^ E.W)
    (hbody : ∀ j < d, Sem (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (RSD.zDRowBase Sinit + d65Cond.code.length + 1) (RSD.zDRowBase Sinit)
      { runBlock d65Cond.code E (RSD.zRowHeads Sinit d M j) with
        pc := RSD.zDRowBase Sinit + d65Cond.code.length + 1 }
      (fun k s' => k ≤ K ∧ s' = RSD.zRowHeads Sinit d M (j + 1)))
    (hframe : ∀ s t : RAMState, s.mem = t.mem → (RowOut s ↔ RowOut t))
    (hOut : RowOut (RSD.zRowHeads Sinit d M d)) :
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) E
      (RSD.zDRowBase Sinit) (RSD.zDColHead Sinit Srow ell)
      ((d : ℝ) * ((K : ℝ) + 2) + 5) (RSD.zRowIn Sinit E d M)
      (fun s => RowOut s ∧ ColIn ell s) :=
  RSD.zRowStage_dispatch hW hell hbody hframe hOut

#print axioms rowStage_real
#print axioms topDecRunsZ_model
#print axioms topDecRunsZ_of_six

end W65

end LinearSetReconciliation327.Main


