-- Prove2me | Definitions.Def_MIPRE_Background_QLD_ExactPauli
-- name    : MIPRE_Background_QLD_ExactPauli
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:44.937205+00:00
-- url     : https://prove2.me/theorems/46b2c05b-5274-4e7c-835e-bffad72e9afb
-- title:
--   Definitions of ExactPauli: Exact Pauli observables from a simultaneous pair measurement Blueprint `lem:qld-exact-paulis`, the part of it that is…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.ExactPauli` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Exact Pauli observables from a simultaneous pair measurement. Blueprint `lem:qld-exact-paulis`, the part of it that is **exact**: given a projective measurement `S` whose outcomes are *pairs* `(g_X, g_Z)` and a map `cd` sending an outcome to a vector of `F_q^n`, the appendix builds binary observables on the enlarged space `dA (x) (C^q)^{(x) n}` which satisfy the generalized Pauli relations with no error term at all. This file is that construction and those relations. Nothing here is approximate, and nothing here mentions the game: every statement is an identity between matrices, with `IsPVM…
--
--   **Definitions** (4): `MIPRE.QLD.cdPhase` (**The phase the first tensor factor carries**, `tr(e (cd(pi p) .); `MIPRE.QLD.mTilde` (**The appendix's `eq:tilde_M`.** `M~^{W,u}_a = sum_g S^W_g (x) tau^W_{cd(g) .); `MIPRE.QLD.sCoarse` (**A coarse-graining of a measurement along a map on its outcomes.** The two marginals of the simultaneous pair measurement are this at…); `MIPRE.QLD.wTilde` (**The appendix's `eq:def-tildewj`.** The binary observable obtained from `mTilde` by the character of the field element `e`.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.ExactPauli` (`MIPRE/Background/QLD/ExactPauli.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 7 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/ExactPauli.lean; blueprint lem:qld-exact-paulis

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/ExactPauli.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl

/-!
# Exact Pauli observables from a simultaneous pair measurement

Blueprint `lem:qld-exact-paulis`, the part of it that is **exact**: given a projective measurement
`S` whose outcomes are *pairs* `(g_X, g_Z)` and a map `cd` sending an outcome to a vector of
`F_q^n`, the appendix builds binary observables on the enlarged space `dA (x) (C^q)^{(x) n}` which
satisfy the generalized Pauli relations with no error term at all. This file is that construction
and those relations.

Nothing here is approximate, and nothing here mentions the game: every statement is an identity
between matrices, with `IsPVM S` and `IsWeylFamily w` the only hypotheses. That is the point ---
the blueprint's proof paragraph says exactness comes "from projectivity of the simultaneous
measurement together with the group law of the Pauli basis", and this file is the
formalization of exactly that sentence. `thm:linearity` is not used.

## The construction

Write `pi` for one of the two projections `(g_X, g_Z) |→ g_W`. Then

* `sCoarse S pi g` is the `W`-marginal `S^W_g`, a projective measurement by `IsPVM.coarse`;
* `mTilde` is the appendix's `eq:tilde_M`,
  `M~^{W,u}_a = sum_g S^W_g (x) tau^W_{cd(g) . u + a}(u)`,
  where `tau^W_c(u)` is the syndrome projector `MIPRE.Weyl.syn w u c` --- the level set of the
  pairing with `u` --- so that `mTilde` is a projective measurement with outcomes in `F_q`;
* `wTilde` is `eq:def-tildewj`, the binary observable
  `W~^e(u) = sum_a (-1)^{tr(e a)} M~^{W,u}_a`, at a field element `e` (the appendix takes `e` in a
  self-dual basis of `F_q` over `F_2`, which this file does not need).

## The one identity everything follows from

`wTilde_eq`: the observable **factorizes**,

`W~^e(u) = pvmObs S (p |→ (-1)^{tr(e (cd (pi p) . u))})  (x)  w (e . u)`,

a signed sum of the *pair* measurement tensor a genuine Weyl operator. The `F_q`-valued syndrome
label is what makes this work: summing the syndrome projectors against the character of `a`
reassembles the Weyl operator on the line `r |→ r . u` (`MIPRE.Weyl.eq_sum_proj`), and the
`cd(g) . u` shift becomes the sign the first factor carries.

Self-adjointness (`wTilde_conjTranspose`) and involutivity (`wTilde_mul_self`) are then the
`pvmObs` calculus of `MIPRE/Foundations/PVM.lean` on the left factor and the group law on the
right. The twisted commutation (`wTilde_mul_wTilde`) is the same: the two left factors are
weightings of *one* projective measurement, so they commute exactly (`pvmObs_comm`), and the whole
phase comes from the right factors' `MIPRE.Weyl.wX_mul_wZ`.

## A repair carried over from the paper

The pinned paper's display for the commutation relation used to split into `e != e'` (claiming
exact commutation) and `e = e'` (a phase). That is false: self-duality gives `tr(e_j e_{j'}) =
delta_{j j'}`, but `tr(e_j e_{j'} c)` need not vanish for `c` outside `F_2`, and the quantity in
the exponent is `e_j e_{j'} (u . v)` with `u . v` an arbitrary field element. The paper now states
the general phase, and `wTilde_mul_wTilde` below is that general phase --- with no case split, and
with no reference to a basis, since the relation holds for every pair of field elements.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

set_option linter.unusedSectionVars false

/-! ## Two small bilinearity facts

`trDot_smul` of `MIPRE/Foundations/Weyl.lean` pulls a scalar out of the *left* argument of the
form. Both of the following pull one out of the right, which is what the two observables'
arguments need. -/

/-! ## Bilinearity of the Kronecker product over finite sums

Mathlib has `Matrix.add_kronecker` and `Matrix.kronecker_add` but not the finite-sum forms, and
every displayed calculation below moves a sum across the tensor sign. -/

/-! ## The marginals of a pair measurement -/

/-- **A coarse-graining of a measurement along a map on its outcomes.** The two marginals of the
simultaneous pair measurement are this at `Prod.fst` and `Prod.snd`; `IsPVM.coarse` is what makes
each of them projective. -/
def sCoarse (S : G × G → Matrix dA dA ℂ) (pi : G × G → G) (g : G) : Matrix dA dA ℂ :=
  ∑ p ∈ univ.filter fun p => pi p = g, S p

/-! ## The measurement and the observable -/

variable (S : G × G → Matrix dA dA ℂ) (pi : G × G → G) (cd : G → (n → F))
  (w : (n → F) → Matrix (n → F) (n → F) ℂ)

/-- **The appendix's `eq:tilde_M`.** `M~^{W,u}_a = sum_g S^W_g (x) tau^W_{cd(g) . u - a}(u)`; in
characteristic two the subtraction is the addition. -/
def mTilde (u : n → F) (a : F) : Matrix (dA × (n → F)) (dA × (n → F)) ℂ :=
  ∑ g, sCoarse S pi g ⊗ₖ syn w u (dotF (cd g) u + a)

/-- **The phase the first tensor factor carries**, `tr(e (cd(pi p) . u))`. -/
def cdPhase (e : F) (u : n → F) : G × G → ZMod 2 :=
  fun p => Algebra.trace (ZMod 2) F (e * dotF (cd (pi p)) u)

/-- **The appendix's `eq:def-tildewj`.** The binary observable obtained from `mTilde` by the
character of the field element `e`. -/
def wTilde (e : F) (u : n → F) : Matrix (dA × (n → F)) (dA × (n → F)) ℂ :=
  ∑ a : F, sgn (Algebra.trace (ZMod 2) F (e * a)) • mTilde S pi cd w u a

/-! ## The factorization

The whole content of the exactness claim. -/

/-! ## The Pauli relations, exactly -/

variable {S pi cd w}

end MIPRE.QLD

end


