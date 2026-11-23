-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_TopDecRunsFinalStages20261123
-- name    : LinearSetReconciliation327_Main_TopDecRunsFinalStages20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T10:34:23.575464+00:00
-- url     : https://prove2.me/theorems/3cdc8675-026b-4eee-8cff-1dcae89d0966
-- title:
--   Theorem 6.5: assembly of the corrected six decoder fields
-- statement:
--   The assembly rule for the corrected six-field decoder structure of Theorem 6.5: from the six repaired stage contracts (all stated about the dispatched program `zProgDecOfTop`) it produces `TopDecRunsFinal`.  The accompanying report records which contracts are already published in this shape.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5; the project's verified six-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_TopDecRunsFinal20261123

/-!
# `topDecRunsFinal_of_stages` — assembling the corrected six fields

This is the assembly rule: the six arguments are the exact repaired stage
statements of `TopDecRunsFinal`, and the result is the structure.  The publication
report records, field by field, which of the six are already published theorems in
this shape and which are not transportable to `zProgDecOfTop` in a single Lean
environment:

* `init` — `W65C.stageRun_initZ_rowIn` (published) gives the `zRowIn` part; the
  `MemInv` conjunct is a frame, not a new mathematical hypothesis;
* `row`  — the real proof `RSD6.zRowStage_rowPost`/`zBody_hbody` lives on the
  `P21DetBndComp` side (`RowStage6`), which cannot be imported together with
  `ColLoopW`/`CrField` (duplicate `axpyBody_spec` and 168 other names);
* `col`  — `W65C.zColStageRun_wrap` (published) is stated for `zProgDecOfTop` and
  matches the field except for the added `MemInv` conjunct;
* `as`, `res`, `cr` — `C8R.stageRun_asP`, `C8R.stageRun_resP` and
  `CRS.stageRun_crMerge_top` are stated for `progDecOfTop`, two instructions
  earlier; `StageRun`-level relocation is not available, so they need a
  re-proof or a `StageRun`-transport (see report).

No `sorry`, no new axiom.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 40000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace W65F

open RSD

/-- **`TopDecRunsFinal` from its six corrected stage statements.** -/
theorem topDecRunsFinal_of_stages {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
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


