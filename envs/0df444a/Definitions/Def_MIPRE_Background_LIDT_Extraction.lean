-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Extraction
-- name    : MIPRE_Background_LIDT_Extraction
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:56:44.695538+00:00
-- url     : https://prove2.me/theorems/5e5e4cd8-00af-4b20-abd1-1d599e1c835f
-- title:
--   Definitions of Extraction: Extracting exactly linear combined codewords Blueprint `lem:lidt-ldc-extraction`, the paper's Step 4 of the proof of…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Extraction` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Extracting exactly linear combined codewords. Blueprint `lem:lidt-ldc-extraction`, the paper's Step 4 of the proof of `lem:ld-soundness` for general `ldc` (`ldt.tex`, Claims 4 and 5 and the measurements `H`, `G`). The simultaneous test with `r` codewords is reduced to the single-codeword test in `K + m` variables by *combining*: a point `(x, y) ∈ F^K × F^m` is answered by `∑_{j < r} x_j b_j`, where `b ∈ F^r` is the original point answer at `y`. The single-codeword theorem then returns a measurement `R` of polynomials `g` in the `K + m` variables, consistent with the combined point answers.…
--
--   **Definitions** (16): `MIPRE.LIDT.Simul.IsXLin` (**Exactly `x`-linear**: every monomial with a nonzero coefficient has an `x`-part equal to a single variable to the first power.); `MIPRE.LIDT.Simul.agreeX` (The agreement, at a uniform `x`, of the combined answer with the outcome `g` evaluated at `(x, y)`, as a fraction.); `MIPRE.LIDT.Simul.badInd` (The indicator that `g` is not exactly `x`-linear and its forbidden coefficient vanishes at `y`.); `MIPRE.LIDT.Simul.badQ` (The forbidden coefficient of a polynomial that is not exactly `x`-linear (`0` for one that is).); `MIPRE.LIDT.Simul.combPOVM` (The combined point measurement: at the padded point `(x, y)`, measure the original point measurement at `y` and answer `∑_{j < r} x_j b_j`.); `MIPRE.LIDT.Simul.evalTuplePOVM` (A measurement of `r`-tuples of polynomials, evaluated at `y`.); `MIPRE.LIDT.Simul.extEval` (The extracted tuple, evaluated at `y`.); `MIPRE.LIDT.Simul.extract` (**The extraction**: the first `r` coefficients of an exactly `x`-linear polynomial, and the zero tuple otherwise.); `MIPRE.LIDT.Simul.extractPM` (**The extracted measurement**: `R` coarse-grained by `extract`, still projective.); `MIPRE.LIDT.Simul.linPoly` (**The linear form `x ↦ ∑_i c_i x_i`**, as a coefficient vector.); `MIPRE.LIDT.Simul.padB` (The answer `b ∈ F^r`, padded with zeros to the `K` combining coordinates.); `MIPRE.LIDT.Simul.pevY` (**The partial evaluation at `y`**: the coefficient vector, in the `K` combining variables, of `x ↦ g(x, y)`.); and -22 more.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `exists_badCoef`, `isPVM_pm`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Extraction` (`MIPRE/Background/LIDT/Extraction.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 16 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Extraction.lean; blueprint lem:lidt-ldc-extraction

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Extraction.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Theorems.Thm_MIPRE_IsPVM_coarse

/-!
# Extracting exactly linear combined codewords

Blueprint `lem:lidt-ldc-extraction`, the paper's Step 4 of the proof of `lem:ld-soundness` for
general `ldc` (`ldt.tex`, Claims 4 and 5 and the measurements `H`, `G`). The simultaneous test with
`r` codewords is reduced to the single-codeword test in `K + m` variables by *combining*: a point
`(x, y) ∈ F^K × F^m` is answered by `∑_{j < r} x_j b_j`, where `b ∈ F^r` is the original point
answer at `y`. The single-codeword theorem then returns a measurement `R` of polynomials `g` in the
`K + m` variables, consistent with the combined point answers. This file turns `R` back into a
measurement of `r`-tuples of polynomials in the `m` original variables.

## The extraction

A polynomial `g(x, y)` is **exactly `x`-linear** (`IsXLin`) if it is `∑_i x_i g_i(y)`: every
monomial has exactly one `x`-variable, to the first power. `extract` reads off `(g_1, …, g_r)` from
such a `g` and returns `0` otherwise; it is a deterministic relabelling of outcomes, so applied to a
projective measurement it gives a projective measurement.

## The estimate

`inconsistency_extract_right_le` (and `_left_le`, the extracted measurement on the other
party): the extracted tuple, evaluated at a uniform `y`, disagrees with
the original point answer at most `(K + m) d / q` more often than `g(x, y)` disagrees with the
combined answer at a uniform `(x, y)`. Fix `y`, the original answer `b` and the outcome `g`, and
average over `x` alone --- the Born probabilities do not see `x`, since the original point
measurement is asked `y` only and `R` is asked nothing:

* if `g` is exactly `x`-linear and its extracted tuple is `b` at `y`, there is nothing to prove;
* if `g` is exactly `x`-linear and the tuple differs from `b`, then `x ↦ g(x, y)` and the combined
  answer are two different linear forms, so they agree at a uniform `x` with probability at most
  `K d / q` (`pevY_eq_linPoly`, then Schwartz--Zippel in `K` variables, `card_agree_le`);
* if `g` is not exactly `x`-linear, a monomial with a forbidden `x`-part has a nonzero coefficient
  `Q_g`, a polynomial in `y` alone. Where `Q_g(y) ≠ 0` the same Schwartz--Zippel step applies; and
  `Q_g(y) = 0` has probability at most `m d / q` over `y`, which is paid once per outcome `g`,
  weighted by `g`'s total Born weight, because summing the Born probabilities over `b` removes `y`
  (`sum_agreeX_le`, `sum_uniform_badInd_le`).

The paper splits the last case the same way (its Claims 4 and 5). The linear-forms case costs
`K d / q` here rather than the paper's `1 / q`: the same Schwartz--Zippel lemma serves all three
cases, and the difference is absorbed by the final constants.

## The partial evaluation

`pevY g y` is the coefficient vector, in the `K` combining variables, of `x ↦ g(x, y)`
(`eval_pevY`). It is what lets Schwartz--Zippel in `K` variables be applied with `y` fixed.
-/

noncomputable section

namespace MIPRE.LIDT.Simul

open Finset MIPRE MIPRE.LIDT
open scoped Kronecker

/-! ## Polynomials in the combining and original variables -/

section Poly

variable {F : Type*} [Field F] {K m d r : ℕ}

/-- **The partial evaluation at `y`**: the coefficient vector, in the `K` combining variables, of
`x ↦ g(x, y)`. -/
def pevY (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (y : Point F m) :
    LowIndDegPoly (F := F) (m := K) (d := d) :=
  fun ex => ∑ ey : Fin m → Fin (d + 1), g (Fin.append ex ey) * ∏ j, y j ^ (ey j : ℕ)

/-- The exponent vector of the variable `x_i`. -/
def unitExp (hd : 1 ≤ d) (i : Fin K) : Fin K → Fin (d + 1) :=
  Pi.single i ⟨1, Nat.lt_succ_of_le hd⟩

/-- **The linear form `x ↦ ∑_i c_i x_i`**, as a coefficient vector. -/
def linPoly (hd : 1 ≤ d) (c : Point F K) : LowIndDegPoly (F := F) (m := K) (d := d) :=
  fun ex => ∑ i, if ex = unitExp hd i then c i else 0

/-- **Exactly `x`-linear**: every monomial with a nonzero coefficient has an `x`-part equal to a
single variable to the first power. -/
def IsXLin (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) : Prop :=
  ∀ (ex : Fin K → Fin (d + 1)) (ey : Fin m → Fin (d + 1)),
    (∀ i, ex ≠ unitExp hd i) → g (Fin.append ex ey) = 0

/-- The coefficient of `x_i`, a polynomial in `y`. -/
def xCoef (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (i : Fin K) :
    LowIndDegPoly (F := F) (m := m) (d := d) :=
  fun ey => g (Fin.append (unitExp hd i) ey)

/-- **A forbidden coefficient.** A polynomial that is not exactly `x`-linear has a monomial with a
forbidden `x`-part and a nonzero coefficient; that coefficient, as a polynomial in `y`, is
nonzero, and where it does not vanish the partial evaluation is no linear form. -/
theorem exists_badCoef {hd : 1 ≤ d} {g : LowIndDegPoly (F := F) (m := K + m) (d := d)}
    (hg : ¬ IsXLin hd g) :
    ∃ ex : Fin K → Fin (d + 1), (∀ i, ex ≠ unitExp hd i) ∧
      (fun ey => g (Fin.append ex ey) : LowIndDegPoly (F := F) (m := m) (d := d)) ≠ 0 := by
  unfold IsXLin at hg
  push Not at hg
  obtain ⟨ex, ey, hex, hne⟩ := hg
  exact ⟨ex, hex, fun h => hne (congrFun h ey)⟩

/-- The answer `b ∈ F^r`, padded with zeros to the `K` combining coordinates. -/
def padB (b : Fin r → F) : Point F K :=
  fun i => if h : (i : ℕ) < r then b ⟨i, h⟩ else 0

/-- **The extraction**: the first `r` coefficients of an exactly `x`-linear polynomial, and the
zero tuple otherwise. -/
def extract (hd : 1 ≤ d) (hr : r ≤ K) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) :
    Fin r → LowIndDegPoly (F := F) (m := m) (d := d) := by
  classical
  exact if IsXLin hd g then fun j => xCoef hd g (Fin.castLE hr j) else 0

/-- The extracted tuple, evaluated at `y`. -/
def extEval (hd : 1 ≤ d) (hr : r ≤ K) (g : LowIndDegPoly (F := F) (m := K + m) (d := d))
    (y : Point F m) : Fin r → F :=
  fun j => (extract hd hr g j).eval y

/-- The forbidden coefficient of a polynomial that is not exactly `x`-linear (`0` for one that
is). -/
def badQ (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) :
    LowIndDegPoly (F := F) (m := m) (d := d) := by
  classical
  exact if h : IsXLin hd g then 0 else fun ey => g (Fin.append (exists_badCoef h).choose ey)

end Poly

/-! ## Schwartz--Zippel at a fixed `y` -/

section Agree

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}

/-- The agreement, at a uniform `x`, of the combined answer with the outcome `g` evaluated at
`(x, y)`, as a fraction. -/
def agreeX (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d))
    (y : Point F m) (b : Fin r → F) : ℝ :=
  ((univ.filter fun x : Point F K =>
      (linPoly hd (padB b)).eval x = g.eval (Fin.append x y)).card : ℝ)
    / (Fintype.card F : ℝ) ^ K

/-- The indicator that `g` is not exactly `x`-linear and its forbidden coefficient vanishes at
`y`. -/
def badInd (hd : 1 ≤ d) (g : LowIndDegPoly (F := F) (m := K + m) (d := d)) (y : Point F m) : ℝ := by
  classical
  exact if IsXLin hd g then 0 else if (badQ hd g).eval y = 0 then 1 else 0

end Agree

/-! ## The operator form -/

section Operators

open Matrix

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- The combining coordinates of a padded point. -/
def xOf (u : Point F (K + m)) : Point F K := fun i => u (Fin.castAdd m i)

/-- The original coordinates of a padded point. -/
def yOf (u : Point F (K + m)) : Point F m := fun j => u (Fin.natAdd K j)

end Operators

/-! ## The extracted measurements, and the three conclusions -/

section Assembly

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- A projective measurement's matrices form a projective family. -/
theorem isPVM_pm {X A : Type*} [Fintype A] {n : Type*} [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) : IsPVM (P.M x) where
  isSelfAdjoint a := by rw [← Matrix.star_eq_conjTranspose]; exact P.selfAdjoint x a
  idem a := P.projective x a
  sum_eq_one := P.normalized x

/-- **The extracted measurement**: `R` coarse-grained by `extract`, still projective. -/
def extractPM (hd : 1 ≤ d) (hr : r ≤ K) {n : Type*} [Fintype n] [DecidableEq n]
    (R : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := K + m) (d := d))
      (Matrix n n ℂ)) :
    ProjectiveMeasurement Unit (Fin r → LowIndDegPoly (F := F) (m := m) (d := d))
      (Matrix n n ℂ) := by
  classical
  exact ProjectiveMeasurement.ofIsPVM (fun _ => (R.toPOVM ()).map (extract hd hr)) fun _ => by
    have h := (isPVM_pm R ()).coarse (extract hd hr)
    convert h using 1
    funext c
    rw [POVM.map_mats]
    rfl

/-- A measurement of `r`-tuples of polynomials, evaluated at `y`. -/
def evalTuplePOVM {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjectiveMeasurement Unit (Fin r → LowIndDegPoly (F := F) (m := m) (d := d))
      (Matrix n n ℂ)) (y : Point F m) : POVM (Fin r → F) n :=
  (G.toPOVM ()).map fun g j => (g j).eval y

/-- The combined point measurement: at the padded point `(x, y)`, measure the original point
measurement at `y` and answer `∑_{j < r} x_j b_j`. -/
def combPOVM {n : Type*} [Fintype n] [DecidableEq n] (hd : 1 ≤ d)
    (A : Point F m → POVM (Fin r → F) n) (u : Point F (K + m)) : POVM F n :=
  (A (yOf u)).map fun b => (linPoly hd (padB b)).eval (xOf u)

end Assembly

end MIPRE.LIDT.Simul

end


