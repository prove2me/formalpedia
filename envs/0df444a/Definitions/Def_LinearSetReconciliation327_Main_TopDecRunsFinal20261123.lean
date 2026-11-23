-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_TopDecRunsFinal20261123
-- name    : LinearSetReconciliation327_Main_TopDecRunsFinal20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T10:21:48.518892+00:00
-- url     : https://prove2.me/theorems/6ee12925-c307-491e-9eec-4b552e766f22
-- title:
--   Theorem 6.5's six decoder fields, all four defects fixed, about the dispatched program
-- statement:
--   The six-stage decoder structure of Theorem 6.5 with all four recorded field repairs applied simultaneously and every field stated about `zProgDecOfTop` (the program with the `r1 := 0; r2 := ell` dispatch): `init` lands on the strengthened row entry `zRowIn`; `row` is the real row loop with post `r1 = d and r2 = d` (not `ColIn ell`); `col` is the ell child decoders from `cwInv` to `r1 = r2 = ell`; `as` takes the column exit to the pinned decoder start; `res` has its precondition pinned to `CrStageIn` (registers and memory of `decoderStart`, plus the merge data) instead of `fun _ => True`; `cr` runs 2.3's decoder, setup, unpack and merge from `CrStageIn` to `x-hat symmetric-difference S`.  The two-instruction dispatch between the row and column loops is a derived bridge (`dispatch_bridge`, from `zDispatch_ColIn`), not a seventh field, and conjunct 7 (`haltsWithin_topDec`) is re-derived from the six fields.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder); the project's verified six-stage development and the four field-repair bundles (`CrField`, `TopDecRunsZ`, `ColLoopW`, `RowStage2Mirror`).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_RowStage2Mirror20261122
import Definitions.Def_LinearSetReconciliation327_Main_CrField20261122
import Definitions.Def_LinearSetReconciliation327_Main_TopDecRunsZ20261122
import Definitions.Def_LinearSetReconciliation327_Main_InitStageZ20261122
import Definitions.Def_LinearSetReconciliation327_Main_ColLoopW20261122

/-!
# `TopDecRunsFinal` — Theorem 6.5's six decoder fields, all four defects fixed at once

Four earlier rounds each repaired one field of the published `TopDecRuns` /
`TopDecRunsIn` / `TopDecRunsZ`.  This bundle states **all four repairs in one
structure**, and states every field about the *dispatched* program
`RSD.zProgDecOfTop`:

| field | repair |
|---|---|
| `cr`    | pre is `CrStageIn` (2.3's own input), post `OutListIs (x̂ △ S)`; |
| `res`   | pre is `CrStageIn` (registers **and** memory pinned to `decoderStart`), not `fun _ => True`; |
| `row`   | post is the row loop's real exit `r1 = d ∧ r2 = d` (not `ColIn ℓ`, which asks `r1 = 0`); program is `zProgDecOfTop`, which contains the dispatch; |
| `col`   | pre is `cwInv` (`r1 = j`, `r2 = ℓ`, every child payload present), post `r1 = r2 = ℓ`. |

The row stage stops at the dispatch block (`zDColBase`), so its post is the loop's
own; the two-instruction dispatch `r1 := 0; r2 := ℓ` is a *derived bridge*
(`dispatch_bridge`, proved from `RSD.zDispatch_ColIn`), not a seventh field.

The residual `res` field's pre now pins the memory: the other pinned predicates
(`zRowIn`/`cwInv`) therefore carry the memory frame `MemInv` along the whole
chain, because no finite program can pin an arbitrary incoming infinite memory
(the reason `fun _ => True` was unsatisfiable).

No `sorry`, no new axiom, nothing from `Solutions.*`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace W65F

open RSD

/-! ## 1. Addresses of the dispatched decoder -/

/-- Address of the residual stage. -/
def zDResBase (Sinit Srow Sdec Sassem : Stmt) (ell : ℕ) : ℕ :=
  RSD.zDAsBase Sinit Srow Sdec ell + Sassem.len

/-- Address of the `CR` call. -/
def zDCrBase (Sinit Srow Sdec Sassem Sres : Stmt) (ell : ℕ) : ℕ :=
  zDResBase Sinit Srow Sdec Sassem ell + Sres.len

/-- Address just past the `CR` block, where `compile` puts the `halt`. -/
def zDEnd (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) : ℕ :=
  zDCrBase Sinit Srow Sdec Sassem Sres ell + Scr.len

theorem zDEnd_eq_compile (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    zDEnd Sinit Srow Sdec Sassem Sres Scr ell =
      ((RSD.zTopDecStmt Sinit Srow Sdec Sassem Sres Scr ell).compile 0).length := by
  simp only [zDEnd, zDCrBase, zDResBase, RSD.zDAsBase, RSD.zDColHead, RSD.zDColBase,
    RSD.zDRowBase, RSD.zTopDecStmt, RSD.zDispatch, topLoop, Stmt.len, Stmt.length_compile]
  omega

/-! ## 2. The field predicates -/

/-- The column loop's payload layout (the memory conjunct of `cwInv`). -/
def CwPay (E : RAMEnv) (ell M : ℕ) (y : Fin M → ZMod 2) (β0 ms : ℕ) (s : RAMState) : Prop :=
  ∀ r < ell, ∀ q < wordsOf E.W M, s.mem (β0 + r * ms + q) = packMem E.W y q

/-- **The row loop's corrected post**: `r1 = d`, `r2 = d` — the state the loop
really leaves, and the one the dispatch expects — together with the payload
layout that the column loop needs (the row stage is what produces it) and the
running memory frame. -/
def ZRowPost (E : RAMEnv) (d ell M : ℕ) (y : Fin M → ZMod 2) (β0 ms : ℕ)
    (MemInv : (ℕ → ℕ) → Prop) (s : RAMState) : Prop :=
  s.regs 1 = d ∧ s.regs 2 = d ∧ CwPay E ell M y β0 ms s ∧ MemInv s.mem

/-! ## 3. The corrected structure -/

/-- **Theorem 6.5's six decoder fields, all four defects fixed, about `zProgDecOfTop`.** -/
structure TopDecRunsFinal (Sinit Srow Sdec Sassem Sres Scr : Stmt) (E : RAMEnv)
    (W M n d ℓ β0 ms : ℕ) (Tini Trow Tdec Tas Tres Tcr : ℝ) (ab al bb bl ob : ℕ)
    (Lx : List ℕ) (S xhat : Finset ℕ) (Mrow : ℕ → ℕ → ℕ) (MemInv : (ℕ → ℕ) → Prop) : Prop where
  /-- The prologue: read `d`, `ℓ`, `wordsOf` from the header, clear the header registers. -/
  init : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0 (RSD.zDRowBase Sinit) Tini
      (fun s => s = decoderStart W y [])
      (fun s => RSD.zRowIn Sinit E d Mrow s ∧ MemInv s.mem)
  /-- Row decoding: `d` iterations of `proposition_2_1`, post `r1 = d ∧ r2 = d`. -/
  row : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (RSD.zDRowBase Sinit) (RSD.zDColBase Sinit Srow) Trow
      (fun s => RSD.zRowIn Sinit E d Mrow s ∧ MemInv s.mem)
      (ZRowPost E d ℓ M y β0 ms MemInv)
  /-- The `ℓ` child decoders of `theorem_5_1`, from `cwInv` to `r1 = r2 = ℓ`. -/
  col : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (RSD.zDColHead Sinit Srow ℓ) (RSD.zDAsBase Sinit Srow Sdec ℓ) Tdec
      (fun s => W65C.cwInv E ℓ M y β0 ms 0 s ∧ MemInv s.mem)
      (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ ∧ MemInv s.mem)
  /-- Prefix assembly: from the column exit to the pinned `cr` entry. -/
  as : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (RSD.zDAsBase Sinit Srow Sdec ℓ) (zDResBase Sinit Srow Sdec Sassem ℓ) Tas
      (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ ∧ MemInv s.mem)
      (CRS.CrStageIn E M y ab al bb bl ob Lx)
  /-- **The residual stage, with its pre pinned**: it starts from `CrStageIn` (the
  decoder's own input state), so the field is satisfiable — unlike the published
  `fun _ => True` pre, which no finite program can satisfy. -/
  res : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (zDResBase Sinit Srow Sdec Sassem ℓ) (zDCrBase Sinit Srow Sdec Sassem Sres ℓ) Tres
      (CRS.CrStageIn E M y ab al bb bl ob Lx) (CRS.CrStageIn E M y ab al bb bl ob Lx)
  /-- **The `cr` stage, corrected**: 2.3's decoder · setup · unpack · merge from
  `CrStageIn` to `x̂ △ S`. -/
  cr : ∀ y : Fin M → ZMod 2,
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (zDCrBase Sinit Srow Sdec Sassem Sres ℓ) (zDEnd Sinit Srow Sdec Sassem Sres Scr ℓ) Tcr
      (CRS.CrStageIn E M y ab al bb bl ob Lx)
      (fun s' => CRS.OutListIs s' (symmDiff xhat S))

/-! ## 4. The dispatch bridge -/

/-- **The dispatch establishes the column loop's entry from the row loop's exit.** -/
theorem dispatch_bridge {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {d ℓ M β0 ms : ℕ} {y : Fin M → ZMod 2} {MemInv : (ℕ → ℕ) → Prop}
    (hW : 1 < 2 ^ E.W) (hell : ℓ < 2 ^ E.W) :
    StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
      (RSD.zDColBase Sinit Srow) (RSD.zDColHead Sinit Srow ℓ) 2
      (ZRowPost E d ℓ M y β0 ms MemInv)
      (fun s => W65C.cwInv E ℓ M y β0 ms 0 s ∧ MemInv s.mem) := by
  intro s hpc hpre
  obtain ⟨-, k, z, hstep, hpcZ, hQ⟩ :=
    RSD.zDispatch_ColIn (P := RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ)
      (pc := RSD.zDColBase Sinit Srow) (ell := ℓ) (s := s)
      (RSD.zAt_dispatch_codeD Sinit Srow Sdec Sassem Sres Scr ℓ) hpc hW hell
  obtain ⟨hk, hcol, hm⟩ := hQ
  obtain ⟨h1, h2, hpay, hInv⟩ := hpre
  refine ⟨k, z, ?_, hstep, by rw [hpcZ]; rfl, ?_⟩
  · rw [hk]; norm_num
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact hcol.1
    · exact hcol.2
    · intro r hr q hq
      rw [hm]
      exact hpay r hr q hq
    · rw [hm]; exact hInv

/-! ## 5. Conjunct 7 from the corrected six fields -/

/-- **Conjunct 7 (`haltsWithin_topDec`) from the six corrected fields.** -/
theorem topDecRunsFinal_haltsWithin {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {W M n d ℓ β0 ms : ℕ} {Tini Trow Tdec Tas Tres Tcr : ℝ} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {S xhat : Finset ℕ} {Mrow : ℕ → ℕ → ℕ} {MemInv : (ℕ → ℕ) → Prop}
    (h : TopDecRunsFinal Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ β0 ms
      Tini Trow Tdec Tas Tres Tcr ab al bb bl ob Lx S xhat Mrow MemInv)
    (hW : 1 < 2 ^ E.W) (hell : ℓ < 2 ^ E.W) (y : Fin M → ZMod 2) :
    ∃ s' : RAMState,
      HaltsWithin (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (Tini + Trow + 2 + Tdec + Tas + Tres + Tcr) (decoderStart W y []) s' := by
  have hIR : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (RSD.zDColBase Sinit Srow) (Tini + Trow)
      (fun s => s = decoderStart W y []) (ZRowPost E d ℓ M y β0 ms MemInv) :=
    (h.init y).trans (h.row y)
  have hIRD : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (RSD.zDColHead Sinit Srow ℓ) (Tini + Trow + 2)
      (fun s => s = decoderStart W y []) (fun s => W65C.cwInv E ℓ M y β0 ms 0 s ∧ MemInv s.mem) :=
    hIR.trans (dispatch_bridge (Sinit := Sinit) (Srow := Srow) (Sdec := Sdec) (Sassem := Sassem)
      (Sres := Sres) (Scr := Scr) (E := E) (d := d) (ℓ := ℓ) (M := M) (β0 := β0) (ms := ms)
      (y := y) (MemInv := MemInv) hW hell)
  have hIRDC : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (RSD.zDAsBase Sinit Srow Sdec ℓ) (Tini + Trow + 2 + Tdec)
      (fun s => s = decoderStart W y []) (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ ∧ MemInv s.mem) :=
    hIRD.trans (h.col y)
  have hIRDCA : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (zDResBase Sinit Srow Sdec Sassem ℓ) (Tini + Trow + 2 + Tdec + Tas)
      (fun s => s = decoderStart W y []) (CRS.CrStageIn E M y ab al bb bl ob Lx) :=
    hIRDC.trans (h.as y)
  have hIRDCAR : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (zDCrBase Sinit Srow Sdec Sassem Sres ℓ) (Tini + Trow + 2 + Tdec + Tas + Tres)
      (fun s => s = decoderStart W y []) (CRS.CrStageIn E M y ab al bb bl ob Lx) :=
    hIRDCA.trans (h.res y)
  have hstep : StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0
      (zDEnd Sinit Srow Sdec Sassem Sres Scr ℓ)
      (Tini + Trow + 2 + Tdec + Tas + Tres + Tcr)
      (fun s => s = decoderStart W y []) (fun _ => True) :=
    hIRDCAR.trans (C8R.stageRun_post (h.cr y) (fun _ _ => trivial))
  obtain ⟨k, s', hk, hrun, hpc, -⟩ :=
    hstep (decoderStart W y []) rfl rfl
  have hlen := zDEnd_eq_compile Sinit Srow Sdec Sassem Sres Scr ℓ
  have hhalt :
      (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ)[zDEnd Sinit Srow Sdec Sassem Sres Scr ℓ]? =
        some Instr.halt := by
    rw [hlen]
    rw [show RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ =
      (RSD.zTopDecStmt Sinit Srow Sdec Sassem Sres Scr ℓ).compile 0 ++ [Instr.halt] from rfl,
      List.getElem?_append_right (le_refl _)]
    simp
  exact ⟨s', k, by simpa using hk, hrun, by simp only [Halted, hpc, hhalt]⟩

/-! ## 6. Introduction rule -/

/-- `TopDecRunsFinal` from its six fields. -/
theorem topDecRunsFinal_of_six {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {W M n d ℓ β0 ms : ℕ} {Tini Trow Tdec Tas Tres Tcr : ℝ} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {S xhat : Finset ℕ} {Mrow : ℕ → ℕ → ℕ} {MemInv : (ℕ → ℕ) → Prop}
    (hinit : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E 0 (RSD.zDRowBase Sinit) Tini
        (fun s => s = decoderStart W y [])
        (fun s => RSD.zRowIn Sinit E d Mrow s ∧ MemInv s.mem))
    (hrow : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (RSD.zDRowBase Sinit) (RSD.zDColBase Sinit Srow) Trow
        (fun s => RSD.zRowIn Sinit E d Mrow s ∧ MemInv s.mem)
        (ZRowPost E d ℓ M y β0 ms MemInv))
    (hcol : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (RSD.zDColHead Sinit Srow ℓ) (RSD.zDAsBase Sinit Srow Sdec ℓ) Tdec
        (fun s => W65C.cwInv E ℓ M y β0 ms 0 s ∧ MemInv s.mem)
        (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ ∧ MemInv s.mem))
    (has : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (RSD.zDAsBase Sinit Srow Sdec ℓ) (zDResBase Sinit Srow Sdec Sassem ℓ) Tas
        (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ ∧ MemInv s.mem)
        (CRS.CrStageIn E M y ab al bb bl ob Lx))
    (hres : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (zDResBase Sinit Srow Sdec Sassem ℓ) (zDCrBase Sinit Srow Sdec Sassem Sres ℓ) Tres
        (CRS.CrStageIn E M y ab al bb bl ob Lx) (CRS.CrStageIn E M y ab al bb bl ob Lx))
    (hcr : ∀ y : Fin M → ZMod 2,
      StageRun (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ℓ) E
        (zDCrBase Sinit Srow Sdec Sassem Sres ℓ) (zDEnd Sinit Srow Sdec Sassem Sres Scr ℓ) Tcr
        (CRS.CrStageIn E M y ab al bb bl ob Lx)
        (fun s' => CRS.OutListIs s' (symmDiff xhat S))) :
    TopDecRunsFinal Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ β0 ms
      Tini Trow Tdec Tas Tres Tcr ab al bb bl ob Lx S xhat Mrow MemInv :=
  ⟨hinit, hrow, hcol, has, hres, hcr⟩

end W65F
end LinearSetReconciliation327.Main


