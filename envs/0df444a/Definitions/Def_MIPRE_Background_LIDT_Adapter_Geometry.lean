-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
-- name    : MIPRE_Background_LIDT_Adapter_Geometry
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:14.931113+00:00
-- url     : https://prove2.me/theorems/f4a89c81-3fe8-44c7-8b78-562f4801f788
-- title:
--   Definitions of Geometry: The seeded-CL adapter, part 1: the two games describe the same lines The seeded CL test `MIPRE.LIDT.CL.clGame` and the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Adapter.Geometry` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 1: the two games describe the same lines. The seeded CL test `MIPRE.LIDT.CL.clGame` and the canonical-line test `MIPRE.LIDT.lidtGame` present a line differently, and the adapter of `planning/lidt-cl-adapter.md` has to know that the two presentations agree where they should. This file settles the axis-parallel case, which is the one that needs the canonical representative of `def:cl-canonical` to be *computed* rather than used abstractly. The seeded test's base point for direction `w` is `rep w u = canonLin (span {w}) u`, the canonical linear map with kernel `span…
--
--   **Definitions** (2): `MIPRE.LIDT.Adapter.rescale` (Rescaling the variable of a polynomial: `rescale c f` is `t ↦ f (c t)`, on coefficients.); `MIPRE.LIDT.Adapter.revPoint` (Coordinate reversal of `F^n`, an involution.).
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_rescale`, `revPoint_add`, `revPoint_apply`, `revPoint_revPoint`, `revPoint_smul`, `revPoint_sub`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Adapter.Geometry` (`MIPRE/Background/LIDT/Adapter/Geometry.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 6 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Geometry.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Geometry.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame

/-!
# The seeded-CL adapter, part 1: the two games describe the same lines

The seeded CL test `MIPRE.LIDT.CL.clGame` and the canonical-line test
`MIPRE.LIDT.lidtGame` present a line differently, and the adapter of
`planning/lidt-cl-adapter.md` has to know that the two presentations agree where they should.
This file settles the axis-parallel case, which is the one that needs the canonical
representative of `def:cl-canonical` to be *computed* rather than used abstractly.

The seeded test's base point for direction `w` is `rep w u = canonLin (span {w}) u`, the
canonical linear map with kernel `span {w}` applied to `u`. The canonical-line test's is the
first component of `Line.through u w`, which for a normalized direction moves `u` so that the
coordinate of the direction's first nonzero entry vanishes. For `w = eᵢ` both are
`u - uᵢ • eᵢ` (`rep_single`, `through_single`, and `rep_single_eq_through` for the conjunction),
so on axis-parallel lines the two games agree on the base point exactly, with no choice
involved. The seed is the only thing the seeded question carries beyond the line.

Getting `rep` to compute means computing the pivot set: `pivots (span {eᵢ}) = {i}`
(`pivots_line`), from the dimension sequence `dim (span {eᵢ} ⊓ tail n k)`, which is `1` for
`k ≤ i` (`inf_tail_of_le`) and `0` above (`inf_tail_of_gt`), so the sequence drops exactly at
`i`. `card_pivots` then pins the set, since a line has rank one.

`projection_eq_of` is the uniqueness of a complementary decomposition, stated as a rewriting
rule because that is how `canonLin` is pinned down: `canonLin S u` is *the* element of the
canonical complement congruent to `u` modulo `S`.

Two further discrepancies are settled here, both of them differences of presentation rather
than of content.

**The diagonal convention.** The seeded test's diagonal directions have their *first* `i`
coordinates zero (`CL.zeroBelow`), the canonical-line test's have their coordinates *past* `j`
zero (`Sample.extend`). Coordinate reversal exchanges them (`revPoint_zeroBelow`), and is the
`ρ` of the paper's own reduction, there for the same reason against the tensor code test.

**The direction scale.** A `DLine` question of the seeded test carries the direction itself,
scale included, while the canonical-line test normalizes it. So the seeded questions
`(u₀, s, c • w)`, `c ≠ 0`, all describe one canonical line, and an answer in the parameter of
`u₀ + t (c • w)` has to be reparametrized. The parameter scales inversely
(`lineParam_smul`) and the polynomial follows by `rescale`, which is a bijection of the
coefficient vectors preserving the degree bound (`rescaleEquiv`) --- so no answer alphabet
changes and no degree is lost.

What is *not* here is the reconciliation of `CL.lineParam` with `Line.param`, the last of the
geometric discrepancies, nor anything about strategies or values.
-/

namespace MIPRE.LIDT.Adapter

open Finset Submodule Module MIPRE.CL

variable {F : Type*} [Field F] {n : ℕ}

/-! ## The pivot set of a coordinate line -/

/-! ## The two base points -/

/-! ## Coordinate reversal, and the two diagonal conventions

The seeded test's diagonal directions have their *first* `i` coordinates zero
(`CL.zeroBelow`); the canonical-line test's have their coordinates *past* `j` zero
(`Sample.extend`). Coordinate reversal exchanges the two, and is the `ρ` of the paper's own
reduction (there it exchanges the seeded test's convention with the tensor code test's, for the
same reason). -/

/-- Coordinate reversal of `F^n`, an involution. -/
def revPoint : (Fin n → F) ≃ (Fin n → F) where
  toFun x := fun j => x (Fin.rev j)
  invFun x := fun j => x (Fin.rev j)
  left_inv x := by funext j; simp [Fin.rev_rev]
  right_inv x := by funext j; simp [Fin.rev_rev]

omit [Field F] in
@[simp] theorem revPoint_apply (x : Fin n → F) (j : Fin n) :
    revPoint x j = x (Fin.rev j) := rfl

omit [Field F] in
@[simp] theorem revPoint_revPoint (x : Fin n → F) : revPoint (revPoint x) = x :=
  revPoint.left_inv x

@[simp] theorem revPoint_add (x y : Fin n → F) :
    revPoint (x + y) = revPoint x + revPoint y := rfl

@[simp] theorem revPoint_smul (c : F) (x : Fin n → F) :
    revPoint (c • x) = c • revPoint x := rfl

@[simp] theorem revPoint_sub (x y : Fin n → F) :
    revPoint (x - y) = revPoint x - revPoint y := rfl

/-! ## The direction scale

A `DLine` question of the seeded test carries the direction `v'` itself, scale included, while
the canonical-line test normalizes the direction. So one canonical diagonal line is described
by the seeded questions `(u₀, s, c • w)` for every `c ≠ 0`, and an answer given in the
parameter of `u₀ + t (c • w)` has to be reparametrized into that of `u₀ + t w`. Both halves are
here: `lineParam_smul` for the parameter and `rescale` for the polynomial. -/

/-- Rescaling the variable of a polynomial: `rescale c f` is `t ↦ f (c t)`, on coefficients. -/
def rescale (c : F) {k : ℕ} (f : LinePoly F k) : LinePoly F k :=
  fun i => f i * c ^ (i : ℕ)

@[simp] theorem eval_rescale (c : F) {k : ℕ} (f : LinePoly F k) (t : F) :
    (rescale c f).eval t = f.eval (c * t) := by
  simp only [LinePoly.eval, rescale, mul_pow]
  exact Finset.sum_congr rfl fun i _ => by ring

section Scale

variable [DecidableEq F]

/-! ## The two parameter conventions

`CL.lineParam u₀ w x` divides by the direction's first nonzero coordinate; `Line.param ℓ x`
reads off that coordinate of `x`, which is correct only because the canonical-line test's
directions are normalized and its base points vanish there. Both compute *the* parameter `t` of
a point `u₀ + t w` on the line, and that is the form in which they can be compared. -/

/-! ## The seeded test's canonical representative, in general

`rep w x` zeroes the coordinate of `x` at the *first nonzero coordinate of `w`*. Under
reversal, the first nonzero coordinate of `ρ dir` is the reversal of the **last** nonzero
coordinate of `dir`, whereas `Line.through` zeroes the coordinate at the **first** nonzero
coordinate of `dir`. So on a diagonal line the two tests pick *different* base points, and the
reparametrization between their answer polynomials is affine rather than linear --- this is the
"canonicalization and rebasing" of `rem:lidt-cl-adapter`. On an axis-parallel line the first and
last nonzero coordinates coincide and the shift vanishes, which is why `rep_single_eq_through`
came out clean. -/

/-! ## When two lines through a point coincide

The diagonal weight count needs this: the canonical-line test's diagonal samples `(j, v)` that
produce a given line are exactly those whose direction is *proportional* to it, which is why
several of them contribute and the weight is a sum rather than a single term. -/

end Scale

end MIPRE.LIDT.Adapter


