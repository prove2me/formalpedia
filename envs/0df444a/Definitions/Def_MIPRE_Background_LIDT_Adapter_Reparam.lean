-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
-- name    : MIPRE_Background_LIDT_Adapter_Reparam
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:11:26.497657+00:00
-- url     : https://prove2.me/theorems/eb56b286-c112-490f-a4e3-865732dd0535
-- title:
--   Definitions of Reparam: The seeded-CL adapter, part 2: affine reparametrization of a line answer Both tests answer a line question with a…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Adapter.Reparam` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 2: affine reparametrization of a line answer. Both tests answer a line question with a univariate polynomial in *the parameter of the line*, and they parametrize the same line differently: the base points differ by a multiple of the direction and the directions differ by a scalar (see `MIPRE.Background.LIDT.Adapter.Geometry`, and the correction in `planning/lidt-cl-adapter.md`). So converting an answer means substituting an affine map `t ↦ a t + b` into the polynomial — the "canonicalization and rebasing" of `rem:lidt-cl-adapter`. Answers are coefficient vectors…
--
--   **Definitions** (4): `MIPRE.LIDT.Adapter.affineMap` (The affine map to substitute.); `MIPRE.LIDT.Adapter.ofPoly` (A polynomial's coefficients, truncated to degree `k`.); `MIPRE.LIDT.Adapter.reparam` (**Affine reparametrization of an answer**: `reparam a b f` is the coefficient vector of `t ↦ f (a t + b)`, of the same degree bound.); `MIPRE.LIDT.Adapter.toPoly` (A coefficient vector, as a polynomial.).
--
--   **Embedded lemmas** (11): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `coeff_toPoly`, `eval_affineMap`, `eval_ofPoly`, `eval_reparam`, `eval_toPoly`, `natDegree_affineMap_le`, `natDegree_comp_affineMap_le`, `natDegree_toPoly_le`, `ofPoly_apply`, `ofPoly_toPoly`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Adapter.Reparam` (`MIPRE/Background/LIDT/Adapter/Reparam.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 3 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Reparam.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Reparam.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game

/-!
# The seeded-CL adapter, part 2: affine reparametrization of a line answer

Both tests answer a line question with a univariate polynomial in *the parameter of the line*,
and they parametrize the same line differently: the base points differ by a multiple of the
direction and the directions differ by a scalar (see
`MIPRE.Background.LIDT.Adapter.Geometry`, and the correction in
`planning/lidt-cl-adapter.md`). So converting an answer means substituting an affine map
`t ↦ a t + b` into the polynomial — the "canonicalization and rebasing" of
`rem:lidt-cl-adapter`.

Answers are coefficient vectors (`LinePoly F k = Fin (k+1) → F`), and the substitution has to
preserve the degree bound exactly, since the bound *is* the answer alphabet: an adapter that
raised the degree would not be producing an answer of the canonical-line test at all.

Doing this directly on coefficient vectors means a Taylor shift, hence the binomial theorem by
hand. Going through `Polynomial F` avoids that entirely: `toPoly` and `ofPoly` are mutually
inverse between coefficient vectors and polynomials of degree at most `k`
(`ofPoly_toPoly`, `toPoly_ofPoly`), `natDegree_comp_le` gives the degree bound for free, and
the inverse substitution is the composition with the inverse affine map, so `reparamEquiv` is a
bijection with no computation on coefficients at all.
-/

namespace MIPRE.LIDT.Adapter

open Finset Polynomial

variable {F : Type*} [Field F] {k : ℕ}

/-! ## Coefficient vectors and polynomials -/

/-- A coefficient vector, as a polynomial. -/
noncomputable def toPoly (f : LinePoly F k) : F[X] :=
  ∑ i, Polynomial.C (f i) * Polynomial.X ^ (i : ℕ)

/-- A polynomial's coefficients, truncated to degree `k`. -/
def ofPoly (p : F[X]) : LinePoly F k := fun i => p.coeff (i : ℕ)

@[simp] theorem ofPoly_apply (p : F[X]) (i : Fin (k + 1)) :
    (ofPoly p : LinePoly F k) i = p.coeff (i : ℕ) := rfl

theorem natDegree_toPoly_le (f : LinePoly F k) : (toPoly f).natDegree ≤ k := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  calc (Polynomial.C (f i) * Polynomial.X ^ (i : ℕ)).natDegree
      ≤ (i : ℕ) := by
        simpa using natDegree_C_mul_le (f i) (Polynomial.X ^ (i : ℕ))
    _ ≤ k := Nat.lt_succ_iff.mp i.isLt

@[simp] theorem coeff_toPoly (f : LinePoly F k) (i : Fin (k + 1)) :
    (toPoly f).coeff (i : ℕ) = f i := by
  rw [toPoly, finsetSum_coeff]
  rw [Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)]
  · simp
  · rw [coeff_C_mul, coeff_X_pow, if_neg (fun hc => hj (Fin.ext hc.symm)), mul_zero]

@[simp] theorem ofPoly_toPoly (f : LinePoly F k) : (ofPoly (toPoly f) : LinePoly F k) = f := by
  funext i
  exact coeff_toPoly f i

/-- Evaluation agrees with `Polynomial.eval`. -/
theorem eval_toPoly (f : LinePoly F k) (t : F) : (toPoly f).eval t = f.eval t := by
  rw [toPoly, eval_finsetSum, LinePoly.eval]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- On polynomials of degree at most `k`, truncation loses nothing. -/
theorem toPoly_ofPoly {p : F[X]} (hp : p.natDegree ≤ k) :
    toPoly (ofPoly p : LinePoly F k) = p := by
  ext j
  by_cases hj : j ≤ k
  · have h := coeff_toPoly (ofPoly p : LinePoly F k) ⟨j, Nat.lt_succ_of_le hj⟩
    simpa using h
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega)),
      coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_toPoly_le (ofPoly p : LinePoly F k)) (by omega))]

/-- Evaluating the truncation of a polynomial of degree at most `k`. -/
theorem eval_ofPoly {p : F[X]} (hp : p.natDegree ≤ k) (t : F) :
    (ofPoly p : LinePoly F k).eval t = p.eval t := by
  rw [← eval_toPoly, toPoly_ofPoly hp]

/-! ## The affine substitution -/

/-- The affine map to substitute. -/
noncomputable def affineMap (a b : F) : F[X] := Polynomial.C a * Polynomial.X + Polynomial.C b

theorem natDegree_affineMap_le (a b : F) : (affineMap a b).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simpa using natDegree_C_mul_le a Polynomial.X
  · simp

@[simp] theorem eval_affineMap (a b t : F) : (affineMap a b).eval t = a * t + b := by
  simp [affineMap]

/-- **Affine reparametrization of an answer**: `reparam a b f` is the coefficient vector of
`t ↦ f (a t + b)`, of the same degree bound. -/
noncomputable def reparam (a b : F) (f : LinePoly F k) : LinePoly F k :=
  ofPoly ((toPoly f).comp (affineMap a b))

theorem natDegree_comp_affineMap_le (a b : F) (f : LinePoly F k) :
    ((toPoly f).comp (affineMap a b)).natDegree ≤ k :=
  (natDegree_comp_le).trans (by
    calc (toPoly f).natDegree * (affineMap a b).natDegree
        ≤ (toPoly f).natDegree * 1 :=
          Nat.mul_le_mul_left _ (natDegree_affineMap_le a b)
      _ ≤ k := by rw [mul_one]; exact natDegree_toPoly_le f)

@[simp] theorem eval_reparam (a b : F) (f : LinePoly F k) (t : F) :
    (reparam a b f).eval t = f.eval (a * t + b) := by
  rw [reparam, eval_ofPoly (natDegree_comp_affineMap_le a b f), eval_comp, eval_affineMap,
    eval_toPoly]

end MIPRE.LIDT.Adapter


