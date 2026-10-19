-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
-- name    : MIPRE_Foundations_LowDegree_LineRestrict
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:12.349195+00:00
-- url     : https://prove2.me/theorems/489ae978-b72e-44a2-8e72-162801afa78f
-- title:
--   Definitions of LineRestrict: Restricting a polynomial to a line The expansion stage's line measurements are indexed by the *restriction to a line*…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.LineRestrict` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Restricting a polynomial to a line. The expansion stage's line measurements are indexed by the *restriction to a line* of the low-degree encoding of the ancilla's measurement outcome. This file is that operation: substitute the affine parametrization `t -> u0 + t . w` into a multivariate polynomial and read off the univariate coefficients. Two facts are all the consumers need: * `eval_lineRestrict` --- evaluating the restriction at `t` is evaluating the polynomial at the point `u0 + t . w`, so the restriction carries the same information along the line; * `natDegree_lineRestrict_le` --- the…
--
--   **Definitions** (1): `MIPRE.LowDegree.lineRestrict` (**The restriction of a multivariate polynomial to the line** `t ↦ u₀ + t • w`, as a univariate polynomial.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `lineRestrict_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.LineRestrict` (`MIPRE/Foundations/LowDegree/LineRestrict.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 1 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/LineRestrict.lean; blueprint def:line-restriction

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/LineRestrict.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding

/-!
# Restricting a polynomial to a line

The expansion stage's line measurements are indexed by the *restriction to a line* of the
low-degree encoding of the ancilla's measurement outcome. This file is that operation: substitute
the affine parametrization `t -> u0 + t . w` into a multivariate polynomial and read off the
univariate coefficients.

Two facts are all the consumers need:

* `eval_lineRestrict` --- evaluating the restriction at `t` is evaluating the polynomial at the
  point `u0 + t . w`, so the restriction carries the same information along the line;
* `natDegree_lineRestrict_le` --- the restriction has degree at most the total degree, so a
  multilinear polynomial in `m` variables restricts to degree at most `m` and the coefficient
  vector fits in a `LinePoly F m`.

`lineCoeffs` packages the coefficients as the `LinePoly` the games use, and `eval_lineCoeffs`
is the composite of the two.
-/

noncomputable section

namespace MIPRE.LowDegree

open Finset

variable {F : Type*} [Field F] {m : ℕ}

/-- **The restriction of a multivariate polynomial to the line** `t ↦ u₀ + t • w`, as a
univariate polynomial. -/
def lineRestrict (u₀ w : Fin m → F) (p : MvPolynomial (Fin m) F) : Polynomial F :=
  MvPolynomial.aeval (fun i => Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (w i)) p

@[simp] theorem lineRestrict_zero (u₀ w : Fin m → F) :
    lineRestrict u₀ w (0 : MvPolynomial (Fin m) F) = 0 := by
  rw [lineRestrict, map_zero]

end MIPRE.LowDegree

end


