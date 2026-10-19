-- Prove2me | Definitions.Def_MIPRE_Foundations_OpBound
-- name    : MIPRE_Foundations_OpBound
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:29.709241+00:00
-- url     : https://prove2.me/theorems/08115632-fdb7-4b75-bb8f-8c2c82d89469
-- title:
--   Definitions of OpBound: Operator bounds on matrices, by hand The rigidity arguments of the Pauli basis test's appendix are chains of estimates…
-- statement:
--   The definitions of the module `MIPRE.Foundations.OpBound` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Operator bounds on matrices, by hand. The rigidity arguments of the Pauli basis test's appendix are chains of estimates `‖M |ψ⟩‖ ≤ …`, and the only thing they need about the operators in front is a bound `‖M v‖ ≤ K ‖v‖`. `Bnd M K` is that bound, with the four closure properties the chains use --- sums, products, scalars, and the two sources: a self-adjoint contraction has `Bnd M 1`, and an isometry has `‖M v‖ = ‖v‖` on the nose. This is the `ℓ²` operator norm, spelled as a relation instead of a number. That is deliberate. Mathlib has the norm, through `Matrix.toEuclideanCLM` and the…
--
--   **Definitions** (5): `MIPRE.aOp` (A matrix on the first factor, acting on the product space.); `MIPRE.bOp` (A matrix on the second factor, acting on the product space.); `MIPRE.evec` (A vector of `N → ℂ`, as a vector of `EuclideanSpace ℂ N`.); `MIPRE.qform` (`⟨v| M |v⟩`, as a real.); `MIPRE.snorm` (`‖M v‖`, for a fixed state `v`.).
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `aOp_one`, `bOp_one`, `evec_add`, `evec_smul`, `evec_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.OpBound` (`MIPRE/Foundations/OpBound.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OpBound.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OpBound.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

/-!
# Operator bounds on matrices, by hand

The rigidity arguments of the Pauli basis test's appendix are chains of estimates
`‖M |ψ⟩‖ ≤ …`, and the only thing they need about the operators in front is a bound
`‖M v‖ ≤ K ‖v‖`. `Bnd M K` is that bound, with the four closure properties the chains use ---
sums, products, scalars, and the two sources: a self-adjoint contraction has `Bnd M 1`, and an
isometry has `‖M v‖ = ‖v‖` on the nose.

This is the `ℓ²` operator norm, spelled as a relation instead of a number. That is deliberate.
Mathlib has the norm, through `Matrix.toEuclideanCLM` and the C*-algebra structure on
continuous linear maps, but the Loewner order on `EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n`
costs enough instance search to time out the elaborator on a statement as small as
`T * T ≤ 1 → ‖T‖ ≤ 1`. The order the arguments actually need is the one on *matrices*
(`Matrix.nonneg_iff_posSemidef`, which is cheap), so the bridge here goes from a matrix
inequality straight to a vector-norm inequality and never mentions an operator norm.
-/

noncomputable section

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder

variable {N : Type*} [Fintype N]

/-- A vector of `N → ℂ`, as a vector of `EuclideanSpace ℂ N`. -/
def evec (v : N → ℂ) : EuclideanSpace ℂ N := WithLp.toLp 2 v

omit [Fintype N] in
@[simp] theorem evec_add (v w : N → ℂ) : evec (v + w) = evec v + evec w := rfl

omit [Fintype N] in
@[simp] theorem evec_smul (c : ℂ) (v : N → ℂ) : evec (c • v) = c • evec v := rfl

omit [Fintype N] in
@[simp] theorem evec_zero : evec (0 : N → ℂ) = 0 := rfl

/-! ## The bound -/

/-! ## The norm on a fixed state

`snorm v M = ‖M v‖`. Every estimate in a rigidity argument is a statement about this, and the
four rules below --- the triangle inequality, scalars, a bound in front, an isometry in front ---
are all of them. -/

section SNorm

variable (v : N → ℂ)

/-- `‖M v‖`, for a fixed state `v`. -/
def snorm (M : Matrix N N ℂ) : ℝ := ‖evec (M *ᵥ v)‖

end SNorm

/-! ## The quadratic form -/

section QForm

variable (v : N → ℂ)

/-- `⟨v| M |v⟩`, as a real. -/
def qform (M : Matrix N N ℂ) : ℝ := (star v ⬝ᵥ (M *ᵥ v)).re

end QForm

variable [DecidableEq N]

/-! ## The bipartite structure

A soundness argument on a bipartite state works with two commuting copies of a matrix algebra
inside the one on the product space: `aOp X = X ⊗ Id` for the first factor and `bOp Y = Id ⊗ Y`
for the second. Both are ring homomorphisms, they commute with each other, and both carry a
matrix contraction to a `Bnd _ 1`, which is all the estimates need. -/

section Bipartite

-- Every lemma below mentions both factors, and matrix multiplication on the product space
-- needs all four instances; the linter's suggestion would be twenty `omit` lines that no
-- consumer benefits from, since a consumer of this section has all four.
set_option linter.unusedSectionVars false

variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

open Kronecker

/-- A matrix on the first factor, acting on the product space. -/
def aOp (X : Matrix HA HA ℂ) : Matrix (HA × HB) (HA × HB) ℂ := X ⊗ₖ (1 : Matrix HB HB ℂ)

/-- A matrix on the second factor, acting on the product space. -/
def bOp (Y : Matrix HB HB ℂ) : Matrix (HA × HB) (HA × HB) ℂ := (1 : Matrix HA HA ℂ) ⊗ₖ Y

@[simp] theorem aOp_one : aOp (1 : Matrix HA HA ℂ) = (1 : Matrix (HA × HB) (HA × HB) ℂ) :=
  Matrix.one_kronecker_one

@[simp] theorem bOp_one : bOp (1 : Matrix HB HB ℂ) = (1 : Matrix (HA × HB) (HA × HB) ℂ) :=
  Matrix.one_kronecker_one

end Bipartite

end MIPRE

end


