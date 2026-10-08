-- Prove2me | Definitions.Def_MazurTransfer_Order18RealCubicQuotientData
-- name    : MazurTransfer_Order18RealCubicQuotientData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T14:04:49.439973+00:00
-- url     : https://prove2.me/theorems/3295f5d5-6af4-4a94-a9e2-dd244ab544e1
-- title:
--   Order18: the original real cubic field and elliptic quotient
-- statement:
--   The quotient K=ℚ[T]/(T³−3T−1), its distinguished generator τ, and the exact original Weierstrass curve with coefficients (1,τ²+τ−3,τ²+τ−1,−τ²+4,−τ−2). The field structure uses the separately Proved irreducibility theorem. Ellipticity, point finiteness and point classification remain separate theorem obligations.
-- source:
--   User MazurTheorem WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0 original headers and attribution retained. Exact original data declarations selected by typed kernel dependencies and whole original Lean AST ranges. All nontrivial supporting proofs are separately registered theorem obligations. Named downstream consumers: the complete cubic-quotient point-finiteness theorem and original full rational genus-two order18 exclusion. No rank, finiteness, image-triviality, point-classification or torsion conclusion is assumed in this package.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order18RealCubicPolynomialData
import Theorems.Thm_MazurTransfer_order18_real_cubic_polynomial_irreducible
open Polynomial WeierstrassCurve
namespace MazurTorsion.XOneEighteenRealCubicQuotient
noncomputable section
instance cubicPolynomial_irreducibleFact : Fact (Irreducible cubicPolynomial) :=
  ⟨MazurTransfer.order18_real_cubic_polynomial_irreducible⟩
/-- The real cubic coefficient field of the elliptic quotient. -/
abbrev K := AdjoinRoot cubicPolynomial

/-- The distinguished generator of the real cubic field. -/
def tau : K :=
  AdjoinRoot.root cubicPolynomial

/-- The elliptic quotient over the real cubic field. -/
def quotientCurve : WeierstrassCurve K :=
  ⟨1, tau ^ 2 + tau - 3, tau ^ 2 + tau - 1,
    -tau ^ 2 + 4, -tau - 2⟩
end
end MazurTorsion.XOneEighteenRealCubicQuotient


