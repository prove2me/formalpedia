-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:13:57.558981+00:00
-- url     : https://prove2.me/theorems/98931586-129a-4f6e-a62f-a673f404e096
-- title:
--   Definitions of LinePolynomials: One-variable line polynomials for the low individual degree test Polynomial answer types attached to axis-parallel and…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LinePolynomials` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). One-variable line polynomials for the low individual degree test. Polynomial answer types attached to axis-parallel and diagonal lines.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (21): `MIPStarRE.LDT.AxisLinePolynomial` (Axis-parallel line answers are genuine univariate degree-`d` polynomials.); `MIPStarRE.LDT.AxisLinePolynomial.appendAtHeight` (Extend an axis-line answer to the slice at height `x`.); `MIPStarRE.LDT.AxisLinePolynomial.instCoeFunForallFq`; `MIPStarRE.LDT.AxisLinePolynomial.reparamAt` (Reparametrize an axis-line answer by translating the line parameter.); `MIPStarRE.LDT.AxisLinePolynomial.reparamAtEquiv` (Reparametrization by translation is an equivalence on axis-line answers.); `MIPStarRE.LDT.AxisLinePolynomial.restrictAtHeight` (Restrict an axis-line answer in `m + 1` variables to the slice at height `x`.); `MIPStarRE.LDT.AxisLinePolynomial.toFun` (Evaluation of an axis-line answer on the line parameter.); `MIPStarRE.LDT.DiagonalLineAnswer` (Paper-level diagonal-line answers as functions on the line parameter.); `MIPStarRE.LDT.DiagonalLineAnswer.appendAtHeight` (Extend a paper-level diagonal-line answer to the slice at height `x`.); `MIPStarRE.LDT.DiagonalLineAnswer.reparamAt` (Reparametrize a paper-level diagonal-line answer by translating the line parameter.); `MIPStarRE.LDT.DiagonalLineAnswer.reparamAtEquiv` (Reparametrization by translation is an equivalence on paper-level line answers.); `MIPStarRE.LDT.DiagonalLineAnswer.restrictAtHeight` (Restrict a paper-level ambient diagonal-line answer to the slice at height `x`.); `MIPStarRE.LDT.DiagonalLinePolynomial` (Diagonal-line answers are genuine univariate degree-`md` polynomials.); and 1 more.
--
--   **Embedded lemmas** (28): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `appendAtHeight_apply`, `appendAtHeight_reparamAt`, `ext`, `reparamAtEquiv_symm_appendAtHeight`, `reparamAt_apply`, `reparamAt_apply_zero`, `reparamAt_default`, `reparamAt_reparamAt`, `reparamAt_zero`, `appendAtHeight_apply`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LinePolynomials` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LinePolynomials.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 3 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LinePolynomials.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/LinePolynomials.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LinePolynomials.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine

set_option backward.isDefEq.respectTransparency false

/-!
# One-variable line polynomials for the low individual degree test

Polynomial answer types attached to axis-parallel and diagonal lines.

## References

- `references/ldt-paper/test_definition.tex`
- `blueprint/src/chapter/ch02_test.tex`
-/

namespace MIPStarRE.LDT

/-- Composing with the degree-one translation `C a + X` preserves `natDegree`
bounds.  Shared degree bookkeeping for the `reparamAt` reparametrizations
below. -/
theorem natDegree_comp_C_add_X_le {params : Parameters} [FieldModel params.q]
    (p : LinePolynomialModel params) (a : Scalar params) {n : ℕ}
    (hp : p.natDegree ≤ n) :
    (p.comp (_root_.Polynomial.C a + _root_.Polynomial.X)).natDegree ≤ n :=
  le_trans (_root_.Polynomial.natDegree_comp_le)
    (by rw [add_comm, _root_.Polynomial.natDegree_X_add_C, Nat.mul_one]; exact hp)

/-- Axis-parallel line answers are genuine univariate degree-`d` polynomials. -/
structure AxisLinePolynomial (params : Parameters) [FieldModel params.q] where
  poly : LinePolynomialModel params
  degreeBounded : poly.natDegree ≤ params.d

noncomputable instance {params : Parameters} [FieldModel params.q] :
    Inhabited (AxisLinePolynomial params) :=
  ⟨{ poly := 0
     degreeBounded := _root_.Polynomial.natDegree_zero.trans_le (Nat.zero_le _) }⟩

namespace AxisLinePolynomial

/-- Evaluation of an axis-line answer on the line parameter. -/
noncomputable def toFun {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) : Fq params → Fq params :=
  evalLinePolynomialModel params f.poly

noncomputable instance {params : Parameters} [FieldModel params.q] :
    CoeFun (AxisLinePolynomial params) (fun _ => Fq params → Fq params) :=
  ⟨AxisLinePolynomial.toFun⟩

@[ext] theorem ext {params : Parameters} [FieldModel params.q]
    {f g : AxisLinePolynomial params} (hpoly : f.poly = g.poly) : f = g := by
  cases f with
  | mk polyf hpolyf =>
      cases g with
      | mk polyg hpolyg =>
          cases hpoly
          congr

/-- Reparametrize an axis-line answer by translating the line parameter. -/
noncomputable def reparamAt {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t : Fq params) : AxisLinePolynomial params where
  poly := f.poly.comp (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X)
  degreeBounded := natDegree_comp_C_add_X_le f.poly (decodeScalar t) f.degreeBounded

@[simp] theorem reparamAt_apply {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t s : Fq params) :
    reparamAt f t s = f (addCoord t s) := by
  simp [reparamAt, AxisLinePolynomial.toFun, evalLinePolynomialModel, addCoord]

@[simp] theorem reparamAt_apply_zero {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t : Fq params) :
    reparamAt f t zeroCoord = f t := by
  simp [reparamAt_apply, addCoord, zeroCoord]

@[simp] theorem reparamAt_zero {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) :
    reparamAt f zeroCoord = f := by
  refine AxisLinePolynomial.ext ?_
  simp [reparamAt, zeroCoord]

@[simp] theorem reparamAt_default {params : Parameters} [FieldModel params.q]
    (t : Fq params) :
    reparamAt (default : AxisLinePolynomial params) t = default := by
  simpa [default, instInhabitedAxisLinePolynomial] using
    (show
      reparamAt ({ poly := 0, degreeBounded := by simp } : AxisLinePolynomial params) t =
        ({ poly := 0, degreeBounded := by simp } : AxisLinePolynomial params) by
        refine AxisLinePolynomial.ext ?_
        simp [reparamAt])

theorem reparamAt_reparamAt {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t s : Fq params) :
    reparamAt (reparamAt f t) s = reparamAt f (addCoord t s) := by
  refine AxisLinePolynomial.ext ?_
  change
    (f.poly.comp (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X)).comp
        (_root_.Polynomial.C (decodeScalar s) + _root_.Polynomial.X) =
      f.poly.comp (_root_.Polynomial.C (decodeScalar (addCoord t s)) + _root_.Polynomial.X)
  rw [_root_.Polynomial.comp_assoc]
  simp [addCoord, add_left_comm, add_comm]

/-- Reparametrization by translation is an equivalence on axis-line answers. -/
noncomputable def reparamAtEquiv {params : Parameters} [FieldModel params.q]
    (t : Fq params) : AxisLinePolynomial params ≃ AxisLinePolynomial params where
  toFun := fun f => reparamAt f t
  invFun := fun f => reparamAt f (subCoord zeroCoord t)
  left_inv := fun f => (reparamAt_reparamAt f t (subCoord zeroCoord t)).trans
    ((congrArg (reparamAt f) (addCoord_subCoord_right zeroCoord t)).trans (reparamAt_zero f))
  right_inv := fun f => (reparamAt_reparamAt f (subCoord zeroCoord t) t).trans
    ((congrArg (reparamAt f) (addCoord_subCoord_left zeroCoord t)).trans (reparamAt_zero f))

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- Extend an axis-line answer to the slice at height `x`. -/
def appendAtHeight (params : Parameters) [FieldModel params.q]
    (f : AxisLinePolynomial params) (_x : Fq params) : AxisLinePolynomial params.next where
  poly := f.poly
  degreeBounded := f.degreeBounded

@[simp] theorem appendAtHeight_apply {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (x t : Fq params) :
    appendAtHeight params f x t = f t :=
  rfl

/-- Slice extension commutes with translating the line parameter on axis-line answers. -/
@[simp] theorem appendAtHeight_reparamAt {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t x : Fq params) :
    appendAtHeight params (reparamAt f t) x =
      reparamAt (appendAtHeight params f x) t := by
  apply AxisLinePolynomial.ext
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The inverse reparametrization equivalence commutes with slice extension on
axis-line answers. -/
@[simp] theorem reparamAtEquiv_symm_appendAtHeight
    {params : Parameters} [FieldModel params.q]
    (f : AxisLinePolynomial params) (t x : Fq params) :
    ((reparamAtEquiv (params := params.next) t).symm
        (appendAtHeight params f x)) =
      appendAtHeight params (((reparamAtEquiv (params := params) t).symm) f) x := by
  apply AxisLinePolynomial.ext
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- Restrict an axis-line answer in `m + 1` variables to the slice at height `x`. -/
def restrictAtHeight (params : Parameters) [FieldModel params.q]
    (f : AxisLinePolynomial params.next) (_x : Fq params) : AxisLinePolynomial params where
  poly := f.poly
  degreeBounded := f.degreeBounded

end AxisLinePolynomial

/-- Diagonal-line answers are genuine univariate degree-`md` polynomials. -/
structure DiagonalLinePolynomial (params : Parameters) [FieldModel params.q] where
  poly : LinePolynomialModel params
  degreeBounded : poly.natDegree ≤ params.m * params.d

noncomputable instance {params : Parameters} [FieldModel params.q] :
    Inhabited (DiagonalLinePolynomial params) :=
  ⟨{ poly := 0
     degreeBounded := _root_.Polynomial.natDegree_zero.trans_le (Nat.zero_le _) }⟩

namespace DiagonalLinePolynomial

/-- Evaluation of a diagonal-line answer on the line parameter. -/
noncomputable def toFun {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) : Fq params → Fq params :=
  evalLinePolynomialModel params f.poly

noncomputable instance {params : Parameters} [FieldModel params.q] :
    CoeFun (DiagonalLinePolynomial params) (fun _ => Fq params → Fq params) :=
  ⟨DiagonalLinePolynomial.toFun⟩

@[ext] theorem ext {params : Parameters} [FieldModel params.q]
    {f g : DiagonalLinePolynomial params} (hpoly : f.poly = g.poly) : f = g := by
  cases f with
  | mk polyf hpolyf =>
      cases g with
      | mk polyg hpolyg =>
          cases hpoly
          congr

/-- Reparametrize a diagonal-line answer by translating the line parameter.

Concretely, the underlying univariate polynomial `f.poly` (over `Scalar params` in
the chosen field model) is precomposed with `X + C (decodeScalar t)`, i.e. the
coefficients are shifted using genuine *field* addition on `Scalar params` — not
the `Fin q` arithmetic on `Fq params`. Transporting back through `encodeScalar`
gives the answer-level identity `reparamAt f t s = f (addCoord t s)` (see
`reparamAt_apply`), where `addCoord` is field addition lifted through the coding
`FieldModel.equiv`. Composition with a degree-one polynomial preserves the
`natDegree ≤ params.m * params.d` bound.

This is the answer-level geometric fact behind rebasing a diagonal line at
parameter `t`: the old parameter `addCoord t s` becomes the new parameter `s`. -/
noncomputable def reparamAt {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t : Fq params) : DiagonalLinePolynomial params where
  poly := f.poly.comp (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X)
  degreeBounded := natDegree_comp_C_add_X_le f.poly (decodeScalar t) f.degreeBounded

@[simp] theorem reparamAt_apply {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t s : Fq params) :
    reparamAt f t s = f (addCoord t s) := by
  simp [reparamAt, DiagonalLinePolynomial.toFun, evalLinePolynomialModel, addCoord]

@[simp] theorem reparamAt_apply_zero {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t : Fq params) :
    reparamAt f t zeroCoord = f t := by
  simp [reparamAt_apply, addCoord, zeroCoord]

@[simp] theorem reparamAt_zero {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) :
    reparamAt f zeroCoord = f := by
  refine DiagonalLinePolynomial.ext ?_
  simp [reparamAt, zeroCoord]

@[simp] theorem reparamAt_default {params : Parameters} [FieldModel params.q]
    (t : Fq params) :
    reparamAt (default : DiagonalLinePolynomial params) t = default := by
  simpa [default, instInhabitedDiagonalLinePolynomial] using
    (show
      reparamAt ({ poly := 0, degreeBounded := by simp } : DiagonalLinePolynomial params) t =
        ({ poly := 0, degreeBounded := by simp } : DiagonalLinePolynomial params) by
        refine DiagonalLinePolynomial.ext ?_
        simp [reparamAt])

theorem reparamAt_reparamAt {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t s : Fq params) :
    reparamAt (reparamAt f t) s = reparamAt f (addCoord t s) := by
  refine DiagonalLinePolynomial.ext ?_
  change
    (f.poly.comp (_root_.Polynomial.C (decodeScalar t) + _root_.Polynomial.X)).comp
        (_root_.Polynomial.C (decodeScalar s) + _root_.Polynomial.X) =
      f.poly.comp (_root_.Polynomial.C (decodeScalar (addCoord t s)) + _root_.Polynomial.X)
  rw [_root_.Polynomial.comp_assoc]
  simp [addCoord, add_left_comm, add_comm]

/-- Reparametrization by translation is an equivalence on diagonal-line answers. -/
noncomputable def reparamAtEquiv {params : Parameters} [FieldModel params.q]
    (t : Fq params) : DiagonalLinePolynomial params ≃ DiagonalLinePolynomial params where
  toFun := fun f => reparamAt f t
  invFun := fun f => reparamAt f (subCoord zeroCoord t)
  left_inv := fun f => (reparamAt_reparamAt f t (subCoord zeroCoord t)).trans
    ((congrArg (reparamAt f) (addCoord_subCoord_right zeroCoord t)).trans (reparamAt_zero f))
  right_inv := fun f => (reparamAt_reparamAt f (subCoord zeroCoord t) t).trans
    ((congrArg (reparamAt f) (addCoord_subCoord_left zeroCoord t)).trans (reparamAt_zero f))

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- Extend a diagonal-line answer to the slice at height `x`. -/
def appendAtHeight (params : Parameters) [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (_x : Fq params) : DiagonalLinePolynomial params.next where
  poly := f.poly
  degreeBounded := le_trans f.degreeBounded (Nat.mul_le_mul_right _ (Nat.le_succ _))

/-- Slice extension commutes with translating the line parameter on diagonal-line answers. -/
@[simp] theorem appendAtHeight_reparamAt {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t x : Fq params) :
    appendAtHeight params (reparamAt f t) x =
      reparamAt (appendAtHeight params f x) t := by
  apply DiagonalLinePolynomial.ext
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The inverse reparametrization equivalence commutes with slice extension on
diagonal-line answers. -/
@[simp] theorem reparamAtEquiv_symm_appendAtHeight
    {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t x : Fq params) :
    ((reparamAtEquiv (params := params.next) t).symm
        (appendAtHeight params f x)) =
      appendAtHeight params (((reparamAtEquiv (params := params) t).symm) f) x := by
  apply DiagonalLinePolynomial.ext
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

end DiagonalLinePolynomial

/-! ## Paper-level diagonal-line answers -/

/-- Paper-level diagonal-line answers as functions on the line parameter.

The existing `DiagonalLinePolynomial` alphabet records a degree bound on the
univariate line polynomial.  For the slice restriction in
`inductive_step.tex`, lines 436--455, the paper uses the underlying line
function: restricting a slice-preserving ambient line is total at the function
level, while it is not total on the current degree-bounded polynomial subtype. -/
abbrev DiagonalLineAnswer (params : Parameters) := Fq params → Fq params

namespace DiagonalLineAnswer

/-- Reparametrize a paper-level diagonal-line answer by translating the line parameter. -/
def reparamAt {params : Parameters} [FieldModel params.q]
    (f : DiagonalLineAnswer params) (t : Fq params) : DiagonalLineAnswer params :=
  fun s => f (addCoord t s)

@[simp] theorem reparamAt_apply {params : Parameters} [FieldModel params.q]
    (f : DiagonalLineAnswer params) (t s : Fq params) :
    reparamAt f t s = f (addCoord t s) :=
  rfl

@[simp] theorem reparamAt_zero {params : Parameters} [FieldModel params.q]
    (f : DiagonalLineAnswer params) :
    reparamAt f zeroCoord = f := by
  funext s
  simp [reparamAt, addCoord, zeroCoord]

theorem reparamAt_reparamAt {params : Parameters} [FieldModel params.q]
    (f : DiagonalLineAnswer params) (t s : Fq params) :
    reparamAt (reparamAt f t) s = reparamAt f (addCoord t s) := by
  funext r
  simp [reparamAt, addCoord, add_left_comm, add_comm]

/-- Reparametrization by translation is an equivalence on paper-level line answers. -/
def reparamAtEquiv {params : Parameters} [FieldModel params.q]
    (t : Fq params) : DiagonalLineAnswer params ≃ DiagonalLineAnswer params where
  toFun := fun f => reparamAt f t
  invFun := fun f => reparamAt f (subCoord zeroCoord t)
  left_inv := fun f => (reparamAt_reparamAt f t (subCoord zeroCoord t)).trans
    ((congrArg (reparamAt f) (addCoord_subCoord_right zeroCoord t)).trans (reparamAt_zero f))
  right_inv := fun f => (reparamAt_reparamAt f (subCoord zeroCoord t) t).trans
    ((congrArg (reparamAt f) (addCoord_subCoord_left zeroCoord t)).trans (reparamAt_zero f))

/-- Extend a paper-level diagonal-line answer to the slice at height `x`. -/
def appendAtHeight (params : Parameters) (f : DiagonalLineAnswer params)
    (_x : Fq params) : DiagonalLineAnswer params.next :=
  fun t => f t

/-- Restrict a paper-level ambient diagonal-line answer to the slice at height `x`. -/
def restrictAtHeight (params : Parameters) (f : DiagonalLineAnswer params.next)
    (_x : Fq params) : DiagonalLineAnswer params :=
  fun t => f t

@[simp] theorem appendAtHeight_apply (params : Parameters)
    (f : DiagonalLineAnswer params) (x : Fq params) (t : Fq params.next) :
    appendAtHeight params f x t = f t :=
  rfl

@[simp] theorem restrictAtHeight_apply (params : Parameters)
    (f : DiagonalLineAnswer params.next) (x : Fq params) (t : Fq params) :
    restrictAtHeight params f x t = f t :=
  rfl

@[simp] theorem appendAtHeight_reparamAt {params : Parameters} [FieldModel params.q]
    (f : DiagonalLineAnswer params) (t x : Fq params) :
    appendAtHeight params (reparamAt f t) x =
      reparamAt (appendAtHeight params f x) t := by
  funext s
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

@[simp] theorem reparamAtEquiv_symm_appendAtHeight
    {params : Parameters} [FieldModel params.q]
    (f : DiagonalLineAnswer params) (t x : Fq params) :
    ((reparamAtEquiv (params := params.next) t).symm
        (appendAtHeight params f x)) =
      appendAtHeight params (((reparamAtEquiv (params := params) t).symm) f) x := by
  funext s
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

end DiagonalLineAnswer

namespace DiagonalLinePolynomial

/-- Forget the degree witness and view a diagonal-line polynomial as its paper-level
line answer function. -/
noncomputable def toAnswer {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) : DiagonalLineAnswer params :=
  fun t => f t

@[simp] theorem toAnswer_apply {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t : Fq params) :
    f.toAnswer t = f t :=
  rfl

@[simp] theorem toAnswer_reparamAt {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (t : Fq params) :
    (reparamAt f t).toAnswer = DiagonalLineAnswer.reparamAt f.toAnswer t := by
  funext s
  simp [toAnswer, DiagonalLineAnswer.reparamAt]

@[simp] theorem toAnswer_appendAtHeight {params : Parameters} [FieldModel params.q]
    (f : DiagonalLinePolynomial params) (x : Fq params) :
    (appendAtHeight params f x).toAnswer =
      DiagonalLineAnswer.appendAtHeight params f.toAnswer x := by
  funext t
  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

end DiagonalLinePolynomial

end MIPStarRE.LDT


