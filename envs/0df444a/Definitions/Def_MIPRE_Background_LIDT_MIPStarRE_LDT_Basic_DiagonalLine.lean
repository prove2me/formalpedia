-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:07.937099+00:00
-- url     : https://prove2.me/theorems/5cefeabd-b97d-4910-8ec6-39c62c0b3104
-- title:
--   Definitions of DiagonalLine: Diagonal lines for the low individual degree test Diagonal-line geometry and rebasing operations
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DiagonalLine` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Diagonal lines for the low individual degree test. Diagonal-line geometry and rebasing operations.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (9): `MIPStarRE.LDT.DiagonalLine` (A genuinely affine diagonal line in `F_q^m`.); `MIPStarRE.LDT.DiagonalLine.appendAtHeight` (Embed a diagonal line into the slice at height `x`, keeping the new coordinate fixed.); `MIPStarRE.LDT.DiagonalLine.firstNonzeroCoord?` (The least nonzero coordinate of a direction vector, when one exists.); `MIPStarRE.LDT.DiagonalLine.nonzeroDirectionSupport` (The support of the nonzero coordinates of a direction vector.); `MIPStarRE.LDT.DiagonalLine.normalizeDirection` (Normalize a direction vector so its first nonzero coordinate becomes `1`.); `MIPStarRE.LDT.DiagonalLine.pointAt` (The canonical affine parameterization `t ↦ base + t · direction`.); `MIPStarRE.LDT.DiagonalLine.rebaseAt` (Rebase a diagonal line so that the old point `ℓ.pointAt t` becomes the new base point.); `MIPStarRE.LDT.DiagonalLine.sampleParameter` (Affine parameter of the sampled point on the canonical diagonal line through `u` in direction `v`.); `MIPStarRE.LDT.DiagonalLine.throughPointDirection` (Canonical geometric diagonal line through `u` in direction `v`.).
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `rebaseAt_pointAt_zero`, `rebaseAt_zero`, `throughPointDirection_pointAt_sampleParameter`, `throughPoint_pointAt_sampleParameter`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.DiagonalLine` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/DiagonalLine.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/DiagonalLine.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/DiagonalLine.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/DiagonalLine.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine

set_option backward.isDefEq.respectTransparency false

/-!
# Diagonal lines for the low individual degree test

Diagonal-line geometry and rebasing operations.

## References

- `references/ldt-paper/test_definition.tex`
- `blueprint/src/chapter/ch02_test.tex`
-/

namespace MIPStarRE.LDT

/-- A genuinely affine diagonal line in `F_q^m`. -/
structure DiagonalLine (params : Parameters) where
  base : Point params
  direction : Point params

deriving instance DecidableEq, Inhabited for DiagonalLine

namespace DiagonalLine

/-- The canonical affine parameterization `t ↦ base + t · direction`. -/
def pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) : Fq params → Point params :=
  fun t => addPoint ℓ.base (smulPoint t ℓ.direction)

/-- The support of the nonzero coordinates of a direction vector. -/
noncomputable def nonzeroDirectionSupport {params : Parameters} [FieldModel params.q]
    (v : Point params) : Finset (Fin params.m) :=
  Finset.univ.filter fun i => v i ≠ zeroCoord

/-- The least nonzero coordinate of a direction vector, when one exists. -/
noncomputable def firstNonzeroCoord? {params : Parameters} [FieldModel params.q]
    (v : Point params) : Option (Fin params.m) :=
  open Classical in
  let s := nonzeroDirectionSupport (params := params) v
  if hs : s.Nonempty then some (s.min' hs) else none

/-- Normalize a direction vector so its first nonzero coordinate becomes `1`. -/
noncomputable def normalizeDirection {params : Parameters} [FieldModel params.q]
    (v : Point params) : Point params :=
  open Classical in
  match firstNonzeroCoord? (params := params) v with
    | none => zeroPoint
    | some i => smulPoint (invCoord (v i)) v

/-- Canonical geometric diagonal line through `u` in direction `v`.

For nonzero `v`, we normalize by the first nonzero coordinate and shift the
base point so that this pivot coordinate is `0`. The degenerate `v = 0` case is
kept as the singleton line through `u`. -/
noncomputable def throughPointDirection {params : Parameters} [FieldModel params.q]
    (u v : Point params) : DiagonalLine params :=
  open Classical in
  match firstNonzeroCoord? (params := params) v with
    | none => { base := u, direction := zeroPoint }
    | some i =>
        let w := normalizeDirection (params := params) v
        let t := u i
        { base := fun j => subCoord (u j) (mulCoord t (w j))
          direction := w }

/-- Affine parameter of the sampled point on the canonical diagonal line through
`u` in direction `v`. -/
noncomputable def sampleParameter {params : Parameters} [FieldModel params.q]
    (u v : Point params) : Fq params :=
  open Classical in
  match firstNonzeroCoord? (params := params) v with
    | none => zeroCoord
    | some i => u i

@[simp] theorem throughPoint_pointAt_sampleParameter {params : Parameters}
    [FieldModel params.q] (u : Point params) (i : Fin params.m) :
    (AxisParallelLine.throughPoint (params := params) u i).pointAt
        (AxisParallelLine.sampleParameter (params := params) u i) = u := by
  funext j
  by_cases h : j = i
  · subst h
    unfold AxisParallelLine.pointAt AxisParallelLine.throughPoint
    simp [AxisParallelLine.sampleParameter, addCoord, zeroCoord]
  · simp [AxisParallelLine.throughPoint, AxisParallelLine.pointAt, h]

@[simp] theorem throughPointDirection_pointAt_sampleParameter {params : Parameters}
    [FieldModel params.q] (u v : Point params) :
    (DiagonalLine.throughPointDirection (params := params) u v).pointAt
        (DiagonalLine.sampleParameter (params := params) u v) = u := by
  classical
  unfold DiagonalLine.throughPointDirection DiagonalLine.sampleParameter
  split
  · funext j
    simp [DiagonalLine.pointAt, addPoint, smulPoint, zeroPoint,
      zeroCoord, addCoord, mulCoord]
  · rename_i i
    funext j
    simp [DiagonalLine.pointAt, addPoint, smulPoint, subCoord, addCoord, mulCoord]

/-- Rebase a diagonal line so that the old point `ℓ.pointAt t` becomes the new base point. -/
def rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t : Fq params) : DiagonalLine params where
  base := ℓ.pointAt t
  direction := ℓ.direction

@[simp] theorem rebaseAt_pointAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t : Fq params) :
    (rebaseAt ℓ t).pointAt zeroCoord = ℓ.pointAt t := by
  ext i
  simp [rebaseAt, pointAt, addPoint, smulPoint, addCoord, mulCoord, zeroCoord]

@[simp] theorem rebaseAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) :
    rebaseAt ℓ zeroCoord = ℓ := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             ({ base := base, direction := direction } : DiagonalLine params).pointAt zeroCoord,
           direction := direction } : DiagonalLine params) =
        ({ base := base, direction := direction } : DiagonalLine params)
      congr
      funext i
      simp [pointAt, addPoint, smulPoint, addCoord, mulCoord, zeroCoord]

/-- Embed a diagonal line into the slice at height `x`, keeping the new coordinate fixed. -/
def appendAtHeight (params : Parameters) [FieldModel params.q]
    (ℓ : DiagonalLine params) (x : Fq params) : DiagonalLine params.next where
  base := appendPoint params ℓ.base x
  direction := appendPoint params ℓ.direction zeroCoord

end DiagonalLine

end MIPStarRE.LDT


