-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Coefficients
-- name    : MIPRE_Background_LIDT_Coefficients
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:28.175478+00:00
-- url     : https://prove2.me/theorems/ac235a54-2f7c-4fd9-84c1-50217aa691be
-- title:
--   Definitions of Coefficients: Coefficient vectors of low-individual-degree polynomials `LowIndDegPoly F n d` is a coefficient vector indexed by…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Coefficients` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Coefficient vectors of low-individual-degree polynomials. `LowIndDegPoly F n d` is a coefficient vector indexed by exponent vectors with entries at most `d`. This file is the algebra of those vectors that more than one analysis needs, moved here from the Pauli basis test's `Dummy.lean` and `Linear.lean` (where it was first written) so that the simultaneous low-degree test, which sits below the Pauli test in the import graph, can use it. The names are unchanged. * **Schwartz--Zippel for any finite variable type** (`prob_agreeOn_le_individualDegree`), and the bridge `LowIndDegPoly.toMv` to…
--
--   **Definitions** (3): `MIPRE.LIDT.LowIndDegPoly.toMv` (**The polynomial a coefficient vector denotes.**); `MIPRE.LIDT.expFinsupp` (An exponent vector with entries at most `d`, as a finitely supported function.); `MIPRE.LowDegree.agreeOn` (The points of `F^σ` at which two polynomials agree.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `expFinsupp_apply`, `mem_agreeOn`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Coefficients` (`MIPRE/Background/LIDT/Coefficients.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 4 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Coefficients.lean; blueprint lem:lidt-ldc-extraction, lem:qld-global-dummy

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Coefficients.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel

/-!
# Coefficient vectors of low-individual-degree polynomials

`LowIndDegPoly F n d` is a coefficient vector indexed by exponent vectors with entries at most `d`.
This file is the algebra of those vectors that more than one analysis needs, moved here from the
Pauli basis test's `Dummy.lean` and `Linear.lean` (where it was first written) so that the
simultaneous low-degree test, which sits below the Pauli test in the import graph, can use it.
The names are unchanged.

* **Schwartz--Zippel for any finite variable type** (`prob_agreeOn_le_individualDegree`), and the
  bridge `LowIndDegPoly.toMv` to `MvPolynomial` with its evaluation, coefficient and
  individual-degree facts; `card_eval_eq_zero_le` is the form a nonzero coefficient vector needs.
* **Coefficients of a monomial pattern.** `LowIndDegPoly.coef g T t` is the coefficient vector, in
  the variables outside `T`, of the monomial `∏_{k ∈ T} u_k^{t k}`, and `eval_eq_sum_coef` is the
  decomposition `g(u) = ∑_t u^t_T · (coef g T t)(u)`.
-/

noncomputable section

/-! ## Schwartz--Zippel for any finite variable type -/

namespace MIPRE.LowDegree

open Finset MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The points of `F^σ` at which two polynomials agree. -/
def agreeOn (f g : MvPolynomial σ F) : Finset (σ → F) := {x ∈ univ | eval x f = eval x g}

@[simp] theorem mem_agreeOn {f g : MvPolynomial σ F} {x : σ → F} :
    x ∈ agreeOn f g ↔ eval x f = eval x g := by
  simp [agreeOn]

end MIPRE.LowDegree

/-! ## Coefficient vectors as polynomials -/

namespace MIPRE.LIDT

open Finset MvPolynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ}

/-- An exponent vector with entries at most `d`, as a finitely supported function. -/
def expFinsupp (e : Fin n → Fin (d + 1)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)

@[simp] theorem expFinsupp_apply (e : Fin n → Fin (d + 1)) (i : Fin n) :
    expFinsupp e i = (e i : ℕ) := rfl

/-- **The polynomial a coefficient vector denotes.** -/
def LowIndDegPoly.toMv (g : LowIndDegPoly (F := F) (m := n) (d := d)) : MvPolynomial (Fin n) F :=
  ∑ e, monomial (expFinsupp e) (g e)

end MIPRE.LIDT

/-! ## Coefficients of a monomial pattern -/

namespace MIPRE.LIDT

open Finset

variable {F : Type*} [Field F] {n d : ℕ}

end MIPRE.LIDT

end


