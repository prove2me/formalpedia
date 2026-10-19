-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:12:20.824135+00:00
-- url     : https://prove2.me/theorems/61cb9281-e305-4529-939c-5b0171a7c448
-- title:
--   Definitions of AxisParallelLine: Axis-parallel lines for the low individual degree test Axis-parallel line geometry on top of the core parameter…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.AxisParallelLine` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Axis-parallel lines for the low individual degree test. Axis-parallel line geometry on top of the core parameter infrastructure: `AxisParallelLine` records a base point and a coordinate direction, with canonical parameterization, rebasing, and slice-embedding operations.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (6): `MIPStarRE.LDT.AxisParallelLine` (A genuinely axis-parallel affine line in `F_q^m`.); `MIPStarRE.LDT.AxisParallelLine.appendAtHeight` (Embed an axis-parallel line into the slice at height `x`.); `MIPStarRE.LDT.AxisParallelLine.pointAt` (The canonical affine parameterization `t ↦ base + t e_i`.); `MIPStarRE.LDT.AxisParallelLine.rebaseAt` (Rebase an axis-parallel line so that the old point `ℓ.pointAt t` becomes the new base point.); `MIPStarRE.LDT.AxisParallelLine.sampleParameter` (Affine parameter of the sampled point on the canonical axis-parallel line through `u` in direction `i`.); `MIPStarRE.LDT.AxisParallelLine.throughPoint` (Canonical geometric axis-parallel line through `u` in direction `i`.).
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `rebaseAt_direction`, `rebaseAt_pointAt_zero`, `rebaseAt_throughPoint_sampleParameter`, `rebaseAt_zero`, `throughPoint_pointAt_sampleParameter`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.AxisParallelLine` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/AxisParallelLine.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/AxisParallelLine.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/AxisParallelLine.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/AxisParallelLine.lean (definition bundle: declarations the uploaded statements rest on);
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

set_option backward.isDefEq.respectTransparency false

/-!
# Axis-parallel lines for the low individual degree test

Axis-parallel line geometry on top of the core parameter infrastructure:
`AxisParallelLine` records a base point and a coordinate direction, with
canonical parameterization, rebasing, and slice-embedding operations.

## References

- `references/ldt-paper/test_definition.tex`
- `blueprint/src/chapter/ch02_test.tex`
-/

namespace MIPStarRE.LDT

/-- A genuinely axis-parallel affine line in `F_q^m`. -/
structure AxisParallelLine (params : Parameters) where
  base : Point params
  direction : Fin params.m

deriving instance DecidableEq, Inhabited for AxisParallelLine

namespace AxisParallelLine

/-- The canonical affine parameterization `t ↦ base + t e_i`. -/
def pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) : Fq params → Point params :=
  fun t i =>
    if i = ℓ.direction then
      addCoord (ℓ.base i) t
    else
      ℓ.base i

/-- Canonical geometric axis-parallel line through `u` in direction `i`.

The representative stores zero in the moving coordinate, so all points on the
same geometric line map to the same `AxisParallelLine`. -/
def throughPoint {params : Parameters} [FieldModel params.q]
    (u : Point params) (i : Fin params.m) : AxisParallelLine params where
  base := fun j => if j = i then zeroCoord else u j
  direction := i

/-- Affine parameter of the sampled point on the canonical axis-parallel line
through `u` in direction `i`. -/
def sampleParameter {params : Parameters} [FieldModel params.q]
    (u : Point params) (i : Fin params.m) : Fq params :=
  u i

/-- Rebase an axis-parallel line so that the old point `ℓ.pointAt t`
becomes the new base point. -/
def rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t : Fq params) : AxisParallelLine params where
  base := ℓ.pointAt t
  direction := ℓ.direction

@[simp] theorem rebaseAt_pointAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t : Fq params) :
    (rebaseAt ℓ t).pointAt zeroCoord = ℓ.pointAt t := by
  ext i
  simp [rebaseAt, pointAt, addCoord, zeroCoord]

@[simp] theorem rebaseAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) :
    rebaseAt ℓ zeroCoord = ℓ := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             ({ base := base, direction := direction } : AxisParallelLine params).pointAt zeroCoord,
           direction := direction } : AxisParallelLine params) =
        ({ base := base, direction := direction } : AxisParallelLine params)
      congr
      funext i
      simp [pointAt, addCoord, zeroCoord]

@[simp] theorem rebaseAt_direction {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t : Fq params) :
    (rebaseAt ℓ t).direction = ℓ.direction :=
  rfl

/-- The canonical affine parameterization of `throughPoint u i` at parameter
`sampleParameter u i = u i` returns the original point `u`. -/
@[simp] theorem throughPoint_pointAt_sampleParameter {params : Parameters}
    [FieldModel params.q] (u : Point params) (i : Fin params.m) :
    (throughPoint (params := params) u i).pointAt
        (sampleParameter (params := params) u i) = u := by
  ext j
  by_cases h : j = i
  · subst h
    simp [throughPoint, pointAt, sampleParameter, addCoord, zeroCoord]
  · simp [throughPoint, pointAt, h]

/-- Rebasing the canonical line `throughPoint u i` at its sample parameter yields
the axis-parallel line with base `u` and direction `i`. -/
@[simp] theorem rebaseAt_throughPoint_sampleParameter {params : Parameters}
    [FieldModel params.q] (u : Point params) (i : Fin params.m) :
    rebaseAt (throughPoint (params := params) u i)
        (sampleParameter (params := params) u i) =
      { base := u, direction := i } := by
  change
    ({ base :=
        (throughPoint (params := params) u i).pointAt
          (sampleParameter (params := params) u i)
       direction := i } : AxisParallelLine params) =
      { base := u, direction := i }
  congr
  exact throughPoint_pointAt_sampleParameter u i

/-- Embed an axis-parallel line into the slice at height `x`. -/
def appendAtHeight (params : Parameters)
    (ℓ : AxisParallelLine params) (x : Fq params) : AxisParallelLine params.next where
  base := appendPoint params ℓ.base x
  direction := embedCoord params ℓ.direction

end AxisParallelLine

end MIPStarRE.LDT


