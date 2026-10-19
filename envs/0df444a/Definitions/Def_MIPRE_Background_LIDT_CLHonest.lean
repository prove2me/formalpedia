-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_CLHonest
-- name    : MIPRE_Background_LIDT_CLHonest
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:43.014376+00:00
-- url     : https://prove2.me/theorems/928ecce5-01c0-4267-8a44-340ef76a4df2
-- title:
--   Definitions of CLHonest: Honest answers in the seeded CL low-degree test Piece AR-4 of `planning/answer-reduction.md` needs the completeness of…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.CLHonest` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Honest answers in the seeded CL low-degree test. Piece AR-4 of `planning/answer-reduction.md` needs the completeness of the seeded CL test (`def:lidt-cl`, `MIPRE.LIDT.CL.accepts`): a tuple of polynomials of individual degree at most `d`, answered honestly — its values at a point, its restrictions to a line — passes the test on any two questions of one sample. * `honest` — the honest answer of a tuple `G` of `ldc` polynomials to a question: the values at a point, the coefficients of the restrictions (`MIPRE.LowDegree.lineRestrict`) to an axis-parallel or diagonal line. * `accepts_honest` — the…
--
--   **Definitions** (3): `MIPRE.LIDT.CL.honest` (**The honest answer** of the tuple `G` to a question: its values at a point, its restrictions to a line.); `MIPRE.LIDT.CL.lineCo` (The coefficients of the restriction of `p` to the line `u₀ + t w`, as a `LinePoly` of degree `n`.); `MIPRE.LIDT.CL.recanon` (The decider's re-derivation of a question from the sample it reads: the base point made canonical, the diagonal direction zeroed below the…).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.CLHonest` (`MIPRE/Background/LIDT/CLHonest.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 10 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/CLHonest.lean; blueprint lem:ar-completeness

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/CLHonest.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict

/-!
# Honest answers in the seeded CL low-degree test

Piece AR-4 of `planning/answer-reduction.md` needs the completeness of the seeded CL test
(`def:lidt-cl`, `MIPRE.LIDT.CL.accepts`): a tuple of polynomials of individual degree at most `d`,
answered honestly — its values at a point, its restrictions to a line — passes the test on any
two questions of one sample.

* `honest` — the honest answer of a tuple `G` of `ldc` polynomials to a question: the values at
  a point, the coefficients of the restrictions (`MIPRE.LowDegree.lineRestrict`) to an axis-parallel
  or diagonal line.
* `accepts_honest` — the test accepts the honest answers to the two questions of a sample.
* `Regs.sampleOf_eval_question` — reading a sample back off the presentation's output gives the
  question the presentation computes: the base points it outputs are already canonical, so the
  decider's re-derivation of the base point (`rep`) changes nothing. This is what lets a decider
  that reads the sample off a question vector be fed the presentation's questions.
-/

noncomputable section

namespace MIPRE.LIDT.CL

open Finset MIPRE.CL MIPRE.LowDegree

variable {F : Type*} [Field F] {m : ℕ}

/-! ## The canonical base point -/

/-! ## Line polynomials -/

/-- The coefficients of the restriction of `p` to the line `u₀ + t w`, as a `LinePoly` of
degree `n`. -/
def lineCo (n : ℕ) (u₀ w : Point F m) (p : MvPolynomial (Fin m) F) : LinePoly F n :=
  fun i => (lineRestrict u₀ w p).coeff i

/-! ## Honest answers -/

variable [Fintype F] [DecidableEq F] [NeZero m] (hm : m ∣ Fintype.card F) {d ldc : ℕ}

/-- **The honest answer** of the tuple `G` to a question: its values at a point, its
restrictions to a line. -/
def honest (G : Fin ldc → MvPolynomial (Fin m) F) : Question F m → Answer F m d ldc
  | .point u => .values fun j => MvPolynomial.eval u (G j)
  | .aline u₀ s => .apolys fun j => lineCo d u₀ (Pi.single (chi hm s) 1) (G j)
  | .dline u₀ _ v => .dpolys fun j => lineCo (m * d) u₀ v (G j)

variable {hm}

/-! ## Reading the sample back -/

/-- The decider's re-derivation of a question from the sample it reads: the base point made
canonical, the diagonal direction zeroed below the seed's block. -/
def recanon (q : Question F m) : Question F m :=
  match q with
  | .point u => .point u
  | .aline u₀ s => .aline (rep (Pi.single (chi hm s) 1) u₀) s
  | .dline u₀ s v =>
      .dline (rep (zeroBelow (chi hm s) v) u₀) s (zeroBelow (chi hm s) v)

namespace Regs

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : Regs ι m) (S : Sel F m hm)

end Regs

end MIPRE.LIDT.CL

end


