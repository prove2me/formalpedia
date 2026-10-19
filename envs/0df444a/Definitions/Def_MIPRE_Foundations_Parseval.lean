-- Prove2me | Definitions.Def_MIPRE_Foundations_Parseval
-- name    : MIPRE_Foundations_Parseval
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:30.276683+00:00
-- url     : https://prove2.me/theorems/209afc16-ed80-490a-bc9a-204ce44bca02
-- title:
--   Definitions of Parseval: Parseval for the character transform The combining stage of the Pauli appendix moves between two descriptions of the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Parseval` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Parseval for the character transform. The combining stage of the Pauli appendix moves between two descriptions of the same data: an `F_q`-valued measurement `{P_a}` and its **binary observables** `O^r = sum_a (-1)^{tr(ar)} P_a`, one for each `r in F_q`. The two are Fourier transforms of each other, and what the estimates need is that the transform is an **isometry**: a bound on the observables, averaged over `r`, is a bound on the measurement elements, summed over `a`, and conversely. This file is that dictionary, for vectors and for families of matrices applied to a state: * `fourierVec` is…
--
--   **Definitions** (6): `MIPRE.fourierVec` (**The character transform** of a family of vectors indexed by `V = F_q^n`.); `MIPRE.fourierVecRaw` (The unnormalized transform: the same sum without the `1/|V|`.); `MIPRE.pairVec` (The pair `(r, s)` as a vector of `F_q^2`.); `MIPRE.trFourier` (The transform back: the `a`-th element recovered from the observables.); `MIPRE.trObs` (The binary observable of an `F_q`-indexed family of operators at the probe `r`.); `MIPRE.trVecRaw` (The unnormalized character transform of a family of vectors indexed by `F_q` itself.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `pairVec_one`, `pairVec_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Parseval` (`MIPRE/Foundations/Parseval.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 12 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Parseval.lean; blueprint lem:qld-combined-points, lem:qld-padded-points

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Parseval.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl

/-!
# Parseval for the character transform

The combining stage of the Pauli appendix moves between two descriptions of the same data: an
`F_q`-valued measurement `{P_a}` and its **binary observables**
`O^r = sum_a (-1)^{tr(ar)} P_a`, one for each `r in F_q`. The two are Fourier transforms of each
other, and what the estimates need is that the transform is an **isometry**: a bound on the
observables, averaged over `r`, is a bound on the measurement elements, summed over `a`, and
conversely.

This file is that dictionary, for vectors and for families of matrices applied to a state:

* `fourierVec` is the transform of a family of vectors indexed by `V = F_q^n`, against the
  characters of the trace form, and `sum_norm_fourierVec_sq` is Parseval --- an identity, not an
  estimate;
* `trObs` is the observable of an `F_q`-indexed family at a parameter `r`, `trObs_fourier` inverts
  it, and `sum_stateSqNorm_eq_avg_trObs` is Parseval in the form the appendix uses: the sum over
  outcomes of the squared state-norms of the elements is the average over `r` of the squared
  state-norms of the observables.

The one-field character orthogonality it all rests on is `MIPRE.Weyl.sum_sgn_trMul`.
-/

noncomputable section

namespace MIPRE

open Finset Matrix MIPRE.Weyl
open scoped Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {N : Type*} [Fintype N] [DecidableEq N]

set_option linter.unusedSectionVars false

/-! ## The transform of a family of vectors -/

/-- **The character transform** of a family of vectors indexed by `V = F_q^n`. -/
def fourierVec (T : (n → F) → (N → ℂ)) (e : n → F) : N → ℂ :=
  (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • T a

/-- The unnormalized transform: the same sum without the `1/|V|`. -/
def fourierVecRaw (T : (n → F) → (N → ℂ)) (e : n → F) : N → ℂ :=
  ∑ a : n → F, sgn (trDot a e) • T a

/-! ## The one-field transform, and its inverse

The appendix's other direction: an `F_q`-valued family `P` has binary observables
`O^r = sum_a (-1)^{tr(ar)} P_a`, and `P` is recovered from `O` by the same transform, averaged.
-/

/-- The binary observable of an `F_q`-indexed family of operators at the probe `r`. -/
def trObs (P : F → Matrix N N ℂ) (r : F) : Matrix N N ℂ :=
  ∑ a : F, sgn (Algebra.trace (ZMod 2) F (a * r)) • P a

/-- The transform back: the `a`-th element recovered from the observables. -/
def trFourier (A : F → Matrix N N ℂ) (a : F) : Matrix N N ℂ :=
  (Fintype.card F : ℂ)⁻¹ • ∑ r : F, sgn (Algebra.trace (ZMod 2) F (a * r)) • A r

/-! ## Coarse-grainings and the transform

A measurement is usually presented as a POVM whose outcomes are then *read* by a function; the
transform has to see through that reading. Both lemmas below are the same regrouping of a sum
along the fibres of the reading. -/

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

/-! ## The two-field transform of a product

The combined measurement is indexed by a *pair* `(a, b)`, and the family it transforms is a
product of one operator depending on `r` and one depending on `s`. The transform factorizes,
which is why the combined measurement is the product of the two marginals whenever the two
commute. -/

/-- The pair `(r, s)` as a vector of `F_q^2`. -/
def pairVec (r s : F) : Fin 2 → F := fun i => if i = 0 then r else s

@[simp] theorem pairVec_zero (r s : F) : pairVec r s 0 = r := if_pos rfl

@[simp] theorem pairVec_one (r s : F) : pairVec r s 1 = s := by
  rw [pairVec, if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-! ## Parseval over one copy of the field, and over two

The combining stage coarse-grains an `F_q x F_q`-valued measurement by the linear form
`(a, b) |-> alpha a + beta b`, and the fibres have `q` elements -- so a per-fibre triangle
inequality would cost a factor `q`. Parseval is what avoids that, and it is needed in three
shapes: over `F_q` (to turn the sum over fibres into an average over one probe), over
`F_q x F_q` (to turn that average back into a sum over outcome pairs), and the cancellation of
the zero probe.
-/

/-- The unnormalized character transform of a family of vectors indexed by `F_q` itself. -/
def trVecRaw (T : F → (N → ℂ)) (r : F) : N → ℂ :=
  ∑ c : F, sgn (Algebra.trace (ZMod 2) F (c * r)) • T c

/-! ## Coarse-graining by a linear form -/

end MIPRE

end


