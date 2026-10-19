-- Prove2me | Definitions.Def_MIPRE_Foundations_OpBound_B
-- name    : MIPRE_Foundations_OpBound_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:43.544121+00:00
-- url     : https://prove2.me/theorems/5aa09a09-166f-4ab1-9287-e19464ba0727
-- title:
--   Definitions of OpBound (addendum): Operator bounds on matrices, by hand The rigidity arguments of the Pauli basis test's appendix are chains of estimates…
-- statement:
--   The definitions of the module `MIPRE.Foundations.OpBound` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Operator bounds on matrices, by hand. The rigidity arguments of the Pauli basis test's appendix are chains of estimates `‖M |ψ⟩‖ ≤ …`, and the only thing they need about the operators in front is a bound `‖M v‖ ≤ K ‖v‖`. `Bnd M K` is that bound, with the four closure properties the chains use --- sums, products, scalars, and the two sources: a self-adjoint contraction has `Bnd M 1`, and an isometry has `‖M v‖ = ‖v‖` on the nose. This is the `ℓ²` operator norm, spelled as a relation instead of a number. That is deliberate. Mathlib has the norm, through `Matrix.toEuclideanCLM` and the…
--
--   This bundle **adds** the declarations below to the already published bundle `MIPRE_Foundations_OpBound` of the same module, which the new statements of this upload need and the earlier bundle left out.
--
--   **Definitions** (1): `MIPRE.Bnd` (`‖M v‖ ≤ K ‖v‖` for every `v`: the `ℓ²` operator norm of `M` is at most `K`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.OpBound` (`MIPRE/Foundations/OpBound.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OpBound.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OpBound.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_OpBound does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_OpBound
import Theorems.Thm_MIPRE_aOp_conjTranspose

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

/-! ## The bound -/

/-- `‖M v‖ ≤ K ‖v‖` for every `v`: the `ℓ²` operator norm of `M` is at most `K`. -/
def Bnd (M : Matrix N N ℂ) (K : ℝ) : Prop := ∀ v : N → ℂ, ‖evec (M *ᵥ v)‖ ≤ K * ‖evec v‖

/-! ## The norm on a fixed state

`snorm v M = ‖M v‖`. Every estimate in a rigidity argument is a statement about this, and the
four rules below --- the triangle inequality, scalars, a bound in front, an isometry in front ---
are all of them. -/

section SNorm

variable (v : N → ℂ)

end SNorm

/-! ## The quadratic form -/

section QForm

variable (v : N → ℂ)

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

end Bipartite

end MIPRE

end


