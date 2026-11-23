-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_AsResidue20261123
-- name    : LinearSetReconciliation327_Main_AsResidue20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T12:00:14.64658+00:00
-- url     : https://prove2.me/theorems/eee56071-b953-43e2-befe-a57c979bddd7
-- title:
--   Theorem 6.5: the `as` field's post is the residue layout, and `as -> res` composes freely
-- statement:
--   The prefix-assembly stage of Theorem 6.5 does **not** produce a decoder payload at base `0`: the published contract ends with the residue layout, i.e. the assembled residue `setVec M Aset` packed at `resSrc` together with the padded `m`-word row-prefix block at `asmDst`. This node restates the field's post as exactly that layout (`ResiduePost`), proves it follows from the published assembly post by projection, identifies it with two of the three conjuncts of the residual stage's published precondition (at `xhatBase = asmDst` and `estVec = asmVec`), and proves that the assembly and the residual stage glue by `StageRun.trans` with no side condition and additive budgets. It also records the one conjunct that the residue layout does not supply -- the destination scrub `writeArray (resDst) mem 0 (wordsOf) = mem` with `resDst = 0` -- as the exact residual of the `res` field.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5; the project's published `DecodeClose20261121` (`stageRun_asP`, `stageRun_resP`, `HoldsVec`, `HoldsVecPad`, `CopyPre`, `CopyPost`) and `Top65Dec` (`StageRun.trans`).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecodeClose20261121

/-!
# Item B: the `as` field's post is the **residue layout**, not a payload at base `0`

## The defect

`TopDecRunsFinalW`'s `as` field is

```lean
  as : ∀ y, StageRun (zProgDecOfTop …) E (zDAsBase …) (zDResBase …) Tas
        (fun s => s.regs 1 = ℓ ∧ s.regs 2 = ℓ)
        (CRS.CrStageInW E M y ab al bb bl ob Lx)
```

i.e. it claims the prefix-assembly block *produces a decoder payload at base `0`*.  It does not.
The published `C8R.stageRun_asP` post is the **residue layout**

```lean
    (fun s => HoldsVecPad E.W m (asmDst E) s (asmVec E.W m pref) ∧
      CopyPost E (asmDst E) (asmSrc E) (asmLen E) s ∧
      HoldsVec E.W M (resSrc E) s (setVec M Aset))
```

— the assembled row transcripts at `asmDst E` plus the residue vector still at `resSrc E`.  Base
`0` is where the **residual** stage writes (`resDst E = 0`), so the payload at base `0` belongs to
`res`'s *post*, not to `as`'s.  The `as` field as published is therefore an interface statement
that no published theorem establishes.

## The repair

`ResiduePost` below is exactly the part of `stageRun_resP`'s pre that `as` can supply.  Two facts
make the seam close with **no side condition**:

* `residuePost_of_asP_post` — the published `as` post *implies* `ResiduePost` (it is conjuncts 3
  and 1, with `CopyPost` dropped);
* `residuePost_of_resP_pre` — the published `res` pre *implies* `ResiduePost`, after identifying
  `xhatBase := asmDst E` and `estVec := asmVec E.W m pref`.

The published `res` pre has a **third** conjunct, `writeArray (resDst E) s.mem (fun _ => 0)
(wordsOf E.W M) = s.mem` (`resDst E = 0`): "the destination window is already all zeros".  That
conjunct is *not* implied by the residue layout and *not* produced by `as` (`CopyPost` only says
the destination equals the source; it says nothing about zeros).  It is recorded here as the exact
residual of the `res` field — see `resP_pre_extra_conjunct`.

Everything below is proved with no `sorry`, from published `Definitions.Def_*` only.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace C8R

/-! ## 1. The residue layout -/

/-- **The residue layout that the residual stage consumes.**

* `HoldsVec E.W M (resSrc E)`: the assembled residue (the sketch the `res` block reads) is the
  `M`-bit vector `setVec M Aset`, packed at its own base `resSrc E`;
* `HoldsVecPad E.W m (asmDst E)`: the `m`-word padded row-prefix block is at `asmDst E`.

This is the payload the assembly block really hands over; it is *not* a decoder payload at base
`0` (that is what `res` produces, i.e. the `CrStageInW` of the `cr` entry). -/
def ResiduePost (E : RAMEnv) (M m : ℕ) (Aset : Finset ℕ) (pref : Fin m → List (ZMod 2))
    (s : RAMState) : Prop :=
  HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
    HoldsVecPad E.W m (asmDst E) s (asmVec E.W m pref)

/-- `ResiduePost` unfolded, for rewriting. -/
theorem residuePost_iff {E : RAMEnv} {M m : ℕ} {Aset : Finset ℕ}
    {pref : Fin m → List (ZMod 2)} {s : RAMState} :
    ResiduePost E M m Aset pref s ↔
      HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
        HoldsVecPad E.W m (asmDst E) s (asmVec E.W m pref) :=
  Iff.rfl

/-! ## 2. The published `as` post implies the residue layout -/

/-- **The published assembly post `⟹` the residue layout.**  Conjuncts 3 and 1, with the copy
postcondition dropped (it is not needed downstream: the residual block reads `resSrc`, not
`asmDst`). -/
theorem residuePost_of_asP_post {E : RAMEnv} {m M : ℕ} {pref : Fin m → List (ZMod 2)}
    {Aset : Finset ℕ} {s : RAMState}
    (h : HoldsVecPad E.W m (asmDst E) s (asmVec E.W m pref) ∧
      CopyPost E (asmDst E) (asmSrc E) (asmLen E) s ∧
      HoldsVec E.W M (resSrc E) s (setVec M Aset)) :
    ResiduePost E M m Aset pref s :=
  ⟨h.2.2, h.1⟩

/-! ## 3. The published `res` pre implies the residue layout — but has one conjunct more -/

/-- **The published residual pre `⟹` the residue layout**, at `xhatBase := asmDst E` and
`estVec := asmVec E.W m pref`.  The third conjunct (the destination scrub) is discarded here; it
is the extra obligation recorded in `resP_pre_extra_conjunct`. -/
theorem residuePost_of_resP_pre {E : RAMEnv} {m M : ℕ} {pref : Fin m → List (ZMod 2)}
    {Aset : Finset ℕ} {s : RAMState}
    (h : HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
      HoldsVecPad E.W m (asmDst E) s (asmVec E.W m pref) ∧
      writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem) :
    ResiduePost E M m Aset pref s :=
  ⟨h.1, h.2.1⟩

/-- **The exact residual of the `res` field.**  After the window repair the only conjunct of
`stageRun_resP`'s pre that neither `as` nor the residue layout supplies is the destination scrub
`writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem` (with `resDst E = 0`).

Equivalently: `stageRun_resP`'s pre is `ResiduePost` **and that scrub**, so the `res` field can be
discharged from the published theorem as soon as the scrub is added to the seam (or supplied by
`SresP` internally). -/
theorem resP_pre_extra_conjunct {E : RAMEnv} {m M : ℕ} {pref : Fin m → List (ZMod 2)}
    {Aset : Finset ℕ} {s : RAMState}
    (h : ResiduePost E M m Aset pref s ∧
      writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem) :
    HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
      HoldsVecPad E.W m (asmDst E) s (asmVec E.W m pref) ∧
      writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem :=
  ⟨h.1.1, h.1.2, h.2⟩

/-! ## 4. The corrected `as` statement -/

/-- **The corrected `as` field: from the column exit to the residue layout.**

This is the published `C8R.stageRun_asP` with its post replaced by `ResiduePost` — a *weaker*
post, so the proof is a projection.  Verbatim, the post is

```
ResiduePost E M m Aset pref
  = HoldsVec E.W M (resSrc E) · (setVec M Aset)
  ∧ HoldsVecPad E.W m (asmDst E) · (asmVec E.W m pref)
```

and the pre is unchanged from the published theorem (`CopyPre` at `asmDst,asmSrc,asmLen`,
`HoldsVecPad` at `asmSrc`, `HoldsVec` at `resSrc`). -/
theorem stageRun_asP_residue {Sini Srow Sdec Sres Scr : Stmt} {E : RAMEnv} {m M : ℕ}
    {pref : Fin m → List (ZMod 2)} {Aset : Finset ℕ}
    (hW : 1 < 2 ^ E.W) (hbig : 11 ≤ E.W) (hWpos : 0 < E.W)
    (hLen : asmLen E = m) (hMdet : M < 2 ^ E.W) (hSep : asmDst E + m ≤ resSrc E) :
    StageRun (progDecOfTop Sini Srow Sdec SassemP Sres Scr) E
      (dAsBase Sini Srow Sdec) (dResBase Sini Srow Sdec SassemP) (12 * (m : ℝ) + 14)
      (fun s => CopyPre E (asmDst E) (asmSrc E) (asmLen E) s ∧
        HoldsVecPad E.W m (asmSrc E) s (asmVec E.W m pref) ∧
        HoldsVec E.W M (resSrc E) s (setVec M Aset))
      (ResiduePost E M m Aset pref) := by
  intro s hpc hpre
  obtain ⟨k, s', hk, hstep, hpc', hQ⟩ :=
    stageRun_asP (Sini := Sini) (Srow := Srow) (Sdec := Sdec) (Sres := Sres) (Scr := Scr)
      (m := m) (M := M) (pref := pref) (Aset := Aset) hW hbig hWpos hLen hMdet hSep s hpc hpre
  exact ⟨k, s', hk, hstep, hpc', residuePost_of_asP_post hQ⟩

/-! ## 5. `as → res` composes with no side condition -/

/-- **The seam closes with no side condition**: the corrected `as` post *is* the `res` pre, so the
two stages glue by `StageRun.trans` and nothing else is needed.  (`Tas + Tres` is the composed
budget.) -/
theorem as_res_compose {P : Program} {E : RAMEnv} {a b c : ℕ} {Tas Tres : ℝ}
    {I R : RAMState → Prop} {M m : ℕ} {Aset : Finset ℕ} {pref : Fin m → List (ZMod 2)}
    (has : StageRun P E a b Tas I (ResiduePost E M m Aset pref))
    (hres : StageRun P E b c Tres (ResiduePost E M m Aset pref) R) :
    StageRun P E a c (Tas + Tres) I R :=
  has.trans hres

/-- The same seam stated at the published addresses of `progDecOfTop`, from the corrected `as`
statement: assembling and then residual-decoding is one stage, with the budgets added and no
additional hypothesis beyond `as`'s own. -/
theorem as_res_stage {Sini Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv} {m M : ℕ}
    {pref : Fin m → List (ZMod 2)} {Aset : Finset ℕ} {Tres : ℝ}
    {R : RAMState → Prop}
    (hW : 1 < 2 ^ E.W) (hbig : 11 ≤ E.W) (hWpos : 0 < E.W)
    (hLen : asmLen E = m) (hMdet : M < 2 ^ E.W) (hSep : asmDst E + m ≤ resSrc E)
    (hres : StageRun (progDecOfTop Sini Srow Sdec SassemP Sres Scr) E
      (dResBase Sini Srow Sdec SassemP) (dCrBase Sini Srow Sdec SassemP Sres) Tres
      (ResiduePost E M m Aset pref) R) :
    StageRun (progDecOfTop Sini Srow Sdec SassemP Sres Scr) E
      (dAsBase Sini Srow Sdec) (dCrBase Sini Srow Sdec SassemP Sres)
      ((12 * (m : ℝ) + 14) + Tres)
      (fun s => CopyPre E (asmDst E) (asmSrc E) (asmLen E) s ∧
        HoldsVecPad E.W m (asmSrc E) s (asmVec E.W m pref) ∧
        HoldsVec E.W M (resSrc E) s (setVec M Aset))
      R :=
  as_res_compose
    (stageRun_asP_residue (Sini := Sini) (Srow := Srow) (Sdec := Sdec)
      (Sres := Sres) (Scr := Scr) (m := m) (M := M) (pref := pref) (Aset := Aset)
      hW hbig hWpos hLen hMdet hSep)
    (hres)

end C8R
end LinearSetReconciliation327.Main


