-- Prove2me | Definitions.Def_MazurTransfer_Order18CoefficientFields
-- name    : MazurTransfer_Order18CoefficientFields
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T17:45:24.41864+00:00
-- url     : https://prove2.me/theorems/f17555ca-dfcf-411c-b1ca-df1ddb8dec61
-- title:
--   Order-18 number-field data: coefficient-fields
-- statement:
--   Let $p(T)=T^3-3T-1$ and $q(S)=S^3-3S-10$ be the separately certified irreducible cubics. These data construct
--   \[K=\mathbb Q[T]/(p),\qquad F=\mathbb Q[S]/(q),\]
--   with their original distinguished roots and Weierstrass quotient models. The field constructors use exactly the separately proved irreducibility witnesses. No class-number, unit-rank, Selmer or torsion assertion is included. The named downstream consumers prove relative irreducibility and complete the order-18 descent.
-- source:
--   Exact whole pure-data commands from user MazurTheorem WIP, commit 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Original types, values and docstrings retained. Apache-2.0 attribution retained. Constructor validity, where needed, comes only from separately proved public irreducibility statements; no class-number, unit-rank, Selmer or torsion assertion is included.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Definitions.Def_MazurTransfer_Order18RationalCubics
import Theorems.Thm_MazurTransfer_order18_rational_cubics_irreducible

noncomputable section
open Polynomial

namespace MazurTorsion.XOneEighteenRealCubicQuotient

instance cubicPolynomial_irreducibleFact : Fact (Irreducible cubicPolynomial) :=
  ⟨MazurTransfer.order18_rational_cubics_irreducible.1⟩

/-- The real cubic coefficient field of the elliptic quotient. -/
abbrev K := AdjoinRoot cubicPolynomial

/-- The distinguished generator of the real cubic field. -/
def tau : K :=
  AdjoinRoot.root cubicPolynomial

/-- The elliptic quotient over the real cubic field. -/
def quotientCurve : WeierstrassCurve K :=
  ⟨1, tau ^ 2 + tau - 3, tau ^ 2 + tau - 1,
    -tau ^ 2 + 4, -tau - 2⟩

/-- The rational-coefficient model `[1,-1,1,25,1]`, base-changed to `K`. -/
def rationalModel : WeierstrassCurve K :=
  ⟨1, -1, 1, 25, 1⟩

end MazurTorsion.XOneEighteenRealCubicQuotient

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

instance twoDivisionPolynomial_irreducibleFact : Fact (Irreducible twoDivisionPolynomial) :=
  ⟨MazurTransfer.order18_rational_cubics_irreducible.2⟩

/-- The rational cubic two-division field. -/
abbrev F := AdjoinRoot twoDivisionPolynomial

/-- Its distinguished generator. -/
def sigma : F :=
  AdjoinRoot.root twoDivisionPolynomial

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


