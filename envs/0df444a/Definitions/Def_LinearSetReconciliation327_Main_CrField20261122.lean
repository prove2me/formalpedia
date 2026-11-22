-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrField20261122
-- name    : LinearSetReconciliation327_Main_CrField20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T10:00:10.786185+00:00
-- url     : https://prove2.me/theorems/f4dcbc8b-487a-4119-93a3-fefa511dfe06
-- title:
--   Theorem 6.5's `cr` field, restated: the decoder's own input conjoined with the merge's data
-- statement:
--   The published `TopDecRunsCR.cr` field asks for `CrMergeIn` at `dCrBase`, i.e. at the *start* of the `cr` block.  That is a category error: `CrMergeIn` describes the state at the *merge's* entry (`r0 = bb = decOutBase N t > 0`, the five arguments in `r10 ... r14`, the two blocks `[ab, ab+al)` and `[bb, bb+bl)`), while the block starts with Proposition 2.3's decoder, whose input is `decoderStart W y []` -- `r0 = 0`, the whole packed sketch on `[0, wordsOf W M)` and zeros beyond.  The two pins on `r0` (`0` and `decOutBase N t`) are incompatible and `CrMergeIn` says nothing about the sketch, so the field's hypothesis `hdec` is not derivable from `cr23_decoding` for the real `decStmt`.  This bundle restates the field in a new structure `TopDecRunsIn`: the precondition is `CrStageIn E M y ab al bb bl ob Lx`, i.e. Proposition 2.3's own input predicate -- registers and memory of `decoderStart E.W y []` -- conjoined with `CrMergeData`, the state-free part of `CrMergeIn` (`Lx.Nodup`, the word bounds and the block disjointness).  The five other fields are copied verbatim, and `haltsWithin_topDec_of_runsIn` shows the corrected field still composes to Theorem 6.5's conjunct 7 (one run from `decoderStart` to the trailing `halt`).
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's `cr` stage and Proposition 2.3.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrStage20261122
import Definitions.Def_LinearSetReconciliation327_Main_CrPipeline20261122

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

namespace CRS

/-! ## 1. The `cr` block's entry predicate

The published `TopDecRunsCR.cr` field asks for `CrMergeIn` at the address `dCrBase`, i.e. at the
*start* of the `cr` block.  That is a category error: `CrMergeIn` describes the state at the
*merge's* entry (`r0 = bb = decOutBase N t > 0`, the five arguments in `r10 … r14`, the two blocks
`[ab, ab+al)` and `[bb, bb+bl)`), while the block itself *starts* with Proposition 2.3's decoder,
whose input is `decoderStart W y []` — `r0 = 0`, the whole packed sketch on `[0, wordsOf W M)` and
zeros beyond.  The two pins on `r0` (`0` and `decOutBase N t`) are incompatible, so `CrMergeIn` is
not a predicate any state the decoder is ever handed satisfies, and `hdec` is not derivable.

The correction: the field's precondition is **the decoder's own input predicate, conjoined with the
merge's block data**.  The five arguments and the two lists are *written by the block itself*
(`upkSetup` loads `ab, ob, m, xbase, W`; the unpack's epilogue writes `r0, r1` and `r10 … r14`;
`crMergeInD_of_upk` is exactly the proof that `UpkOut` plus the decoder's window yields
`CrMergeIn`), so what the entry state has to supply is only the state-free part of `CrMergeIn`:
`Lx.Nodup` and the word/disjointness arithmetic. -/

/-- **The merge's block data**, i.e. the conjuncts of `CrMergeIn` that do not mention the state.
`CrMergeIn`'s remaining conjuncts (`r0 = bb`, `r1 = bl`, `r10 … r14`, `mList mem ab al = Lx`,
`outList t` = the decoded residual) are *produced* by the `cr` block, not read at its entry. -/
def CrMergeData (E : RAMEnv) (ab al bb bl ob : ℕ) (Lx : List ℕ) : Prop :=
  Lx.Nodup ∧ al < 2 ^ E.W ∧ bl < 2 ^ E.W ∧ ab + al ≤ 2 ^ E.W ∧ bb + bl ≤ 2 ^ E.W ∧
    ob + (al + bl) + 1 < 2 ^ E.W ∧
    (ab + al ≤ ob ∨ ob + (al + bl) ≤ ab) ∧ (bb + bl ≤ ob ∨ ob + (al + bl) ≤ bb)

/-- **The `cr` block's entry predicate, corrected.**  Proposition 2.3's own input predicate —
`decoderStart W y []`, i.e. `r0 = 0`, `r1 = wordsOf W M`, `r2 = 0` and the packed sketch `y` on
`[0, wordsOf W M)`, zeros beyond — conjoined with the merge's block data `CrMergeData`.  (The
predicate is `pc`-blind: `StageRun` hands it the state with the entry address already in `pc`.)

With `M = cr23R N t` and `y` the packed residual sketch this is *exactly* the state
`cr23_decoding` starts from, so the field now has the shape `stageRun_crPipeline` consumes. -/
def CrStageIn (E : RAMEnv) (M : ℕ) (y : Fin M → ZMod 2)
    (ab al bb bl ob : ℕ) (Lx : List ℕ) (t : RAMState) : Prop :=
  t.regs = (decoderStart E.W y []).regs ∧ t.mem = (decoderStart E.W y []).mem ∧
    CrMergeData E ab al bb bl ob Lx

/-- The `cr` block's entry is the decoder's start state, register-wise. -/
theorem crStageIn_regs {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageIn E M y ab al bb bl ob Lx t) :
    t.regs = (decoderStart E.W y []).regs := h.1

/-- The `cr` block's entry is the decoder's start state, memory-wise: the packed sketch on
`[0, wordsOf E.W M)` and zeros beyond. -/
theorem crStageIn_mem {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageIn E M y ab al bb bl ob Lx t) :
    t.mem = (decoderStart E.W y []).mem := h.2.1

/-- **`CrStageIn` is not vacuous as a shape**: its merge part is state-free, so any state whose
registers and memory are the decoder's start state satisfies it. -/
theorem crStageIn_of_eq {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState}
    (hregs : t.regs = (decoderStart E.W y []).regs) (hmem : t.mem = (decoderStart E.W y []).mem)
    (hdata : CrMergeData E ab al bb bl ob Lx) : CrStageIn E M y ab al bb bl ob Lx t :=
  ⟨hregs, hmem, hdata⟩

/-! ## 2. The corrected `cr` field, in a new structure

The other five fields are copied verbatim from the published `TopDecRunsCR`. -/

/-- **`TopDecRuns` with the corrected `cr` field.**  The `cr` field now starts from Proposition
2.3's own input state, conjoined with the merge's block data, so it is exactly what
`stageRun_crPipeline` proves from `cr23_decoding`.  `M` is the bit length of the packed sketch
(`M = cr23R N t` at Proposition 2.3). -/
structure TopDecRunsIn (Sinit Srow Sdec Sassem Sres Scr : Stmt) (E : RAMEnv) (W M n d ℓ : ℕ)
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
  /-- Residual syndrome. -/
  res : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dResBase Sinit Srow Sdec Sassem)
      (dCrBase Sinit Srow Sdec Sassem Sres) Tres (fun _ => True) (fun _ => True)
  /-- **The corrected `cr` field**: 2.3's decoder · setup · unpack · merge, from the decoder's own
  input state to the merge's output `x̂ △ ê`. -/
  cr : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
      (dCrBase Sinit Srow Sdec Sassem Sres) (dEnd Sinit Srow Sdec Sassem Sres Scr) Tcr
      (CrStageIn E M y ab al bb bl ob Lx)
      (fun s' => OutListIs s' (symmDiff xhat S))

/-- **The corrected field still yields conjunct 7.**  The five published fields plus the corrected
`cr` field compose into one run from `decoderStart` to the trailing `halt`, at the same budget, as
soon as the residual stage hands the decoder's start state over (which is the only state 2.3 can
decode from).  The proof is `haltsWithin_topDec_of_runsCR`'s. -/
theorem haltsWithin_topDec_of_runsIn {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {W M n d ℓ : ℕ} {Tini Trow Tdec Tas Tres Tcr : ℝ} {ab al bb bl ob : ℕ} {Lx : List ℕ}
    {S xhat : Finset ℕ}
    (h : TopDecRunsIn Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ Tini Trow Tdec Tas Tres Tcr
      ab al bb bl ob Lx S xhat)
    (hres : ∀ y : Fin M → ZMod 2,
      StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (dResBase Sinit Srow Sdec Sassem) (dCrBase Sinit Srow Sdec Sassem Sres) Tres
        (fun _ => True) (CrStageIn E M y ab al bb bl ob Lx))
    (y : Fin M → ZMod 2) :
    ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (Tini + Trow + Tdec + Tas + Tres + Tcr) (decoderStart W y []) s' := by
  have hstep : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0
      (dEnd Sinit Srow Sdec Sassem Sres Scr) (Tini + Trow + Tdec + Tas + Tres + Tcr)
      (fun s => s = decoderStart W y []) (fun _ => True) :=
    ((((h.init y).trans (h.row y)).trans (h.col y)).trans (h.as y)).trans (hres y)
      |>.trans (stageRun_post (h.cr y) (fun _ _ => trivial))
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

end CRS

end LinearSetReconciliation327.Main


