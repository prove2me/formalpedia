-- Prove2me | Definitions.Def_GeneralPieces_Series_Rings
-- name    : GeneralPieces_Series_Rings
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:15.21071+00:00
-- url     : https://prove2.me/theorems/0149c16e-51b0-4b52-8873-4b4d4eb1f275
-- title:
--   Rings
-- statement:
--   Definitions and structural lemmas for Rings, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Rings.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
set_option autoImplicit false
section
section
namespace GeneralPieces.Series
open LaurentPolynomial
abbrev L : Type := AddMonoidAlgebra ℚ (ℤ × ℤ)
abbrev S : Type := HahnSeries ℤ (LaurentPolynomial ℚ)
abbrev Lp : Type := S
abbrev Lm : Type := S
noncomputable def mo (x y : ℤ) : S := HahnSeries.single y (T x)
noncomputable def cf (f : S) (x y : ℤ) : ℚ := (f.coeff y).coeff x
theorem mo_zero : mo 0 0 = 1 := rfl
theorem mo_mul_mo (a b c d : ℤ) : mo a b * mo c d = mo (a + c) (b + d) := by
  unfold mo
  rw [HahnSeries.single_mul_single, T_add]
theorem diag_bddBelow (d : ℤ) (c : ℤ → ℚ) (j₀ : ℤ) :
    BddBelow (Function.support fun j : ℤ => if j₀ ≤ j then (C (c j) * T (d - j) : LaurentPolynomial ℚ) else 0) :=
  ⟨j₀, fun j hj => by
    by_contra h
    exact hj (if_neg h)⟩
noncomputable def diag (d : ℤ) (c : ℤ → ℚ) (j₀ : ℤ) : S :=
  HahnSeries.ofSuppBddBelow (fun j => if j₀ ≤ j then C (c j) * T (d - j) else 0) (diag_bddBelow d c j₀)
noncomputable def moHom : Multiplicative (ℤ × ℤ) →* S where
  toFun p := mo p.toAdd.1 p.toAdd.2
  map_one' := mo_zero
  map_mul' _ _ := (mo_mul_mo _ _ _ _).symm
noncomputable def moHom' : Multiplicative (ℤ × ℤ) →* S where
  toFun p := mo p.toAdd.2 p.toAdd.1
  map_one' := mo_zero
  map_mul' _ _ := (mo_mul_mo _ _ _ _).symm
noncomputable def toP : L →ₐ[ℚ] Lp := AddMonoidAlgebra.lift ℚ S (ℤ × ℤ) moHom
noncomputable def toM : L →ₐ[ℚ] Lm := AddMonoidAlgebra.lift ℚ S (ℤ × ℤ) moHom'
noncomputable def cfP (f : Lp) (x y : ℤ) : ℚ := cf f x y
noncomputable def cfM (f : Lm) (x y : ℤ) : ℚ := cf f y x
noncomputable def W (x y : ℤ) : L := AddMonoidAlgebra.single (x, y) 1
noncomputable def eps : S := diag (-1) (fun _ => 1) 0
noncomputable def dW : L := W 1 0 - W 0 1
noncomputable def epsP : Lp := eps
noncomputable def epsM : Lm := -eps
end GeneralPieces.Series


