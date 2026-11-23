-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrAtZ20261123
-- name    : LinearSetReconciliation327_Main_CrAtZ20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T12:16:41.21459+00:00
-- url     : https://prove2.me/theorems/8a284084-9886-43e4-afc8-957280caa8c2
-- title:
--   The At facts at the z addresses (+2) for the cr block
-- statement:
--   Theorem 6.5's fields are stated about the dispatched program `zProgDecOfTop`, whose `cr` block starts at `zDCrBase = dCrBase + 2` (the dispatch `r1 := 0; r2 := ell` is spliced in at `dColBase`). `StageRun` records only the endpoint, so a run cannot be relocated by two instructions; the `At` facts have to be supplied directly. This bundle proves them: the `seq` of assembly/residual/`cr` at `zDAsBase` (`zAt_as_seqD`) and each block's `At` (`zAt_asD`, `zAt_resD`, `zAt_crD`), the four sub-blocks of the `cr` block at `zDCrBase`, `zDCrBase + decStmt.len`, `+ 5`, `+ 5 + 31` (`zAt_crStage4_dec/setup/upk/mrg`, with the `decStmt.len = 282` instances), and the address arithmetic `zDEnd_crStage4`: `zDEnd = zDCrBase + Sdec.len + 122`.
-- source:
--   arXiv:2611.11409 (Linear Set Reconciliation with O(d) Additive Redundancy), Theorem 6.5 / Proposition 2.3

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrSlot20261123
import Definitions.Def_LinearSetReconciliation327_Main_TopDecRunsFinal20261123

/-!
# The `cr` merge half at the `z` addresses (`+2`)

Theorem 6.5's `cr` field is stated about the dispatched program
`RSD.zProgDecOfTop … Scr ell`, whose `cr` block starts at `W65F.zDCrBase`, i.e. **two instructions
after** the published `dCrBase` (the dispatch `r1 := 0; r2 := ℓ` is spliced in at `dColBase`).  The
published composition `CRS.stageRun_crPipeline` is stated about `progDecOfTop` at `dCrBase`, and
`StageRun` records only the endpoint, so it cannot be relocated.  This bundle re-proves it at the
shifted addresses.

Contents:

* the `At` facts of the blocks *after* the column loop — `zAt_as_seqD`, `zAt_asD`, `zAt_resD`,
  `zAt_crD` (the plumbing item 3 of the residual list);
* the `At` facts of the `cr` block's four sub-blocks at `zDCrBase`,
  `zDCrBase + decStmt.len`, `… + 5`, `… + 5 + 31` (`zAt_crStage4_dec/setup/upk/mrg`);
* `zDEnd_crStage4` — the address arithmetic;
* `stageRun_crPipelineZ` — decoder · setup · unpack · merge at the `z` addresses, i.e. the
  `CrMergeIn` half of `hdec`, whose merge step is `CRS.crMergeInD_of_upk`.

Axiom-clean: only `Mathlib` and published `Definitions.Def_*` bundles are imported.
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

/-! ## 1. The `At` facts at the `z` addresses -/

/-- The assembly, the residual stage and the `cr` call, as one `seq`, at `zDAsBase`. -/
theorem zAt_as_seqD (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (RSD.zDAsBase Sinit Srow Sdec ell)
      (Stmt.compile (Stmt.seq Sassem (Stmt.seq Sres Scr)) (RSD.zDAsBase Sinit Srow Sdec ell)) := by
  have h1 : At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell)
      (RSD.zDColBase Sinit Srow + (RSD.zDispatch ell).len)
      (Stmt.compile (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr)))
        (RSD.zDColBase Sinit Srow + (RSD.zDispatch ell).len)) :=
    at_seq_right (a := RSD.zDispatch ell)
      (b := Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr)))
      (RSD.zAt_dispatch_seqD Sinit Srow Sdec Sassem Sres Scr ell)
  have h2 : At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell)
      (RSD.zDColBase Sinit Srow + (RSD.zDispatch ell).len + (topLoop Sdec).len)
      (Stmt.compile (Stmt.seq Sassem (Stmt.seq Sres Scr))
        (RSD.zDColBase Sinit Srow + (RSD.zDispatch ell).len + (topLoop Sdec).len)) :=
    at_seq_right (a := topLoop Sdec) (b := Stmt.seq Sassem (Stmt.seq Sres Scr)) h1
  have e : RSD.zDColBase Sinit Srow + (RSD.zDispatch ell).len + (topLoop Sdec).len
      = RSD.zDAsBase Sinit Srow Sdec ell := rfl
  rw [e] at h2
  exact h2

/-- **The assembly `Sassem` at `zDAsBase`.** -/
theorem zAt_asD (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (RSD.zDAsBase Sinit Srow Sdec ell)
      (Stmt.compile Sassem (RSD.zDAsBase Sinit Srow Sdec ell)) :=
  at_seq_left (a := Sassem) (b := Stmt.seq Sres Scr)
    (zAt_as_seqD Sinit Srow Sdec Sassem Sres Scr ell)

/-- **The residual stage `Sres` at `zDResBase` = `zDAsBase + Sassem.len`.** -/
theorem zAt_resD (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell)
      (RSD.zDAsBase Sinit Srow Sdec ell + Sassem.len)
      (Stmt.compile Sres (RSD.zDAsBase Sinit Srow Sdec ell + Sassem.len)) :=
  at_seq_left (a := Sres) (b := Scr)
    (at_seq_right (a := Sassem) (b := Stmt.seq Sres Scr)
      (zAt_as_seqD Sinit Srow Sdec Sassem Sres Scr ell))

/-- **The `cr` block `Scr` at `zDCrBase` = `zDResBase + Sres.len`.** -/
theorem zAt_crD (Sinit Srow Sdec Sassem Sres Scr : Stmt) (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell)
      (RSD.zDAsBase Sinit Srow Sdec ell + Sassem.len + Sres.len)
      (Stmt.compile Scr (RSD.zDAsBase Sinit Srow Sdec ell + Sassem.len + Sres.len)) :=
  at_seq_right (a := Sres) (b := Scr)
    (at_seq_right (a := Sassem) (b := Stmt.seq Sres Scr)
      (zAt_as_seqD Sinit Srow Sdec Sassem Sres Scr ell))

/-! ## 2. The four sub-blocks of the `cr` block at the `z` addresses -/

/-- The composite `CrStage4` at `zDCrBase`. -/
theorem zAt_crStage4 (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ) (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 Sdec23 W xbase m ab ob) ell)
      (zDCrBase Sinit Srow Sdec Sassem Sres ell)
      (Stmt.compile (CRS.CrStage4 Sdec23 W xbase m ab ob) (zDCrBase Sinit Srow Sdec Sassem Sres ell)) := by
  have h := zAt_crD Sinit Srow Sdec Sassem Sres (CRS.CrStage4 Sdec23 W xbase m ab ob) ell
  have e : RSD.zDAsBase Sinit Srow Sdec ell + Sassem.len + Sres.len
      = zDCrBase Sinit Srow Sdec Sassem Sres ell := rfl
  rw [e] at h
  exact h

/-- 2.3's decoder at `zDCrBase`. -/
theorem zAt_crStage4_dec (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ) (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 Sdec23 W xbase m ab ob) ell)
      (zDCrBase Sinit Srow Sdec Sassem Sres ell)
      (Sdec23.compile (zDCrBase Sinit Srow Sdec Sassem Sres ell)) :=
  CRS.At.peelL (A := Sdec23) (B := CRS.upkSetupStmt W xbase m ab ob)
    (CRS.At.peelL (A := Stmt.seq Sdec23 (CRS.upkSetupStmt W xbase m ab ob))
      (B := Stmt.seq CRS.upkStmt RMR.mrgStmtFull)
      (zAt_crStage4 Sinit Srow Sdec Sassem Sres Sdec23 W xbase m ab ob ell))

/-- **The setup at `zDCrBase + Sdec23.len`.** -/
theorem zAt_crStage4_setup (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ)
    (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 Sdec23 W xbase m ab ob) ell)
      (zDCrBase Sinit Srow Sdec Sassem Sres ell + Sdec23.len)
      (CRS.upkSetup W xbase m ab ob) :=
  CRS.At.peelR (A := Sdec23) (B := CRS.upkSetupStmt W xbase m ab ob)
    (CRS.At.peelL (A := Stmt.seq Sdec23 (CRS.upkSetupStmt W xbase m ab ob))
      (B := Stmt.seq CRS.upkStmt RMR.mrgStmtFull)
      (zAt_crStage4 Sinit Srow Sdec Sassem Sres Sdec23 W xbase m ab ob ell))

/-- The unpack at `zDCrBase + Sdec23.len + 5`. -/
theorem zAt_crStage4_upk (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ)
    (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 Sdec23 W xbase m ab ob) ell)
      (zDCrBase Sinit Srow Sdec Sassem Sres ell + Sdec23.len + 5)
      (CRS.upkStmt.compile (zDCrBase Sinit Srow Sdec Sassem Sres ell + Sdec23.len + 5)) :=
  CRS.At.addr (CRS.At.peelL (A := CRS.upkStmt) (B := RMR.mrgStmtFull)
    (CRS.At.peelR (A := Stmt.seq Sdec23 (CRS.upkSetupStmt W xbase m ab ob))
      (B := Stmt.seq CRS.upkStmt RMR.mrgStmtFull)
      (zAt_crStage4 Sinit Srow Sdec Sassem Sres Sdec23 W xbase m ab ob ell)))
    (by simp [Stmt.len, CRS.upkSetupStmt_len, CRS.upkStmt_len])

/-- **The merge at `zDCrBase + Sdec23.len + 5 + 31`.** -/
theorem zAt_crStage4_mrg (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ)
    (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 Sdec23 W xbase m ab ob) ell)
      (zDCrBase Sinit Srow Sdec Sassem Sres ell + Sdec23.len + 5 + 31)
      (RMR.mrgStmtFull.compile (zDCrBase Sinit Srow Sdec Sassem Sres ell + Sdec23.len + 5 + 31)) :=
  CRS.At.addr (CRS.At.peelR (A := CRS.upkStmt) (B := RMR.mrgStmtFull)
    (CRS.At.peelR (A := Stmt.seq Sdec23 (CRS.upkSetupStmt W xbase m ab ob))
      (B := Stmt.seq CRS.upkStmt RMR.mrgStmtFull)
      (zAt_crStage4 Sinit Srow Sdec Sassem Sres Sdec23 W xbase m ab ob ell)))
    (by simp [Stmt.len, CRS.upkSetupStmt_len, CRS.upkStmt_len])

/-- The merge at `zDCrBase + 318`, at 2.3's own decoder. -/
theorem zAt_crStage4_decStmt_mrg (Sinit Srow Sdec Sassem Sres : Stmt) (W xbase m ab ob : ℕ)
    (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 decStmt W xbase m ab ob) ell)
      (zDCrBase Sinit Srow Sdec Sassem Sres ell + 318)
      (RMR.mrgStmtFull.compile (zDCrBase Sinit Srow Sdec Sassem Sres ell + 318)) :=
  CRS.At.addr (zAt_crStage4_mrg Sinit Srow Sdec Sassem Sres decStmt W xbase m ab ob ell)
    (by rw [CRS.decStmt_len])

/-- The setup at `zDCrBase + 282`, at 2.3's own decoder. -/
theorem zAt_crStage4_decStmt_setup (Sinit Srow Sdec Sassem Sres : Stmt) (W xbase m ab ob : ℕ)
    (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 decStmt W xbase m ab ob) ell)
      (zDCrBase Sinit Srow Sdec Sassem Sres ell + 282)
      (CRS.upkSetup W xbase m ab ob) :=
  CRS.At.addr (zAt_crStage4_setup Sinit Srow Sdec Sassem Sres decStmt W xbase m ab ob ell)
    (by rw [CRS.decStmt_len])

/-- The unpack at `zDCrBase + 287`, at 2.3's own decoder. -/
theorem zAt_crStage4_decStmt_upk (Sinit Srow Sdec Sassem Sres : Stmt) (W xbase m ab ob : ℕ)
    (ell : ℕ) :
    At (RSD.zProgDecOfTop Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 decStmt W xbase m ab ob) ell)
      (zDCrBase Sinit Srow Sdec Sassem Sres ell + 287)
      (CRS.upkStmt.compile (zDCrBase Sinit Srow Sdec Sassem Sres ell + 287)) :=
  CRS.At.addr (zAt_crStage4_upk Sinit Srow Sdec Sassem Sres decStmt W xbase m ab ob ell)
    (by rw [CRS.decStmt_len])

/-- **`zDEnd` is `zDCrBase` plus the four blocks' lengths.** -/
theorem zDEnd_crStage4 (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) (W xbase m ab ob : ℕ) (ell : ℕ) :
    zDEnd Sinit Srow Sdec Sassem Sres (CRS.CrStage4 Sdec23 W xbase m ab ob) ell
      = zDCrBase Sinit Srow Sdec Sassem Sres ell + Sdec23.len + 122 := by
  simp only [zDEnd, CRS.CrStage4_len]
  omega

end W65F
end LinearSetReconciliation327.Main


