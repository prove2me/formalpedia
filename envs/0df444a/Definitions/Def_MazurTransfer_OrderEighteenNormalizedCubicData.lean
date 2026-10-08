-- Prove2me | Definitions.Def_MazurTransfer_OrderEighteenNormalizedCubicData
-- name    : MazurTransfer_OrderEighteenNormalizedCubicData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T14:16:47.724021+00:00
-- url     : https://prove2.me/theorems/190844e8-cbb4-475f-ab2a-e1020c77e43c
-- title:
--   Literal vector polynomial for the order-18 normalized dyadic cubic
-- statement:
--   In the coefficient ring $C=(\mathbb Z/16\mathbb Z)^3$ with multiplication reduced using $\tau^3=3\tau+1$, this module defines the identity vector, $\gamma=(7,10,1)$, and the vector polynomial $F(z)=z^3+(\tau^2-3)z^2+(-2\tau^2+\tau+4)z-1$. It contains no root or nonsquare assertion. The named downstream consumer proves the unique finite root and transports that result into the integral dyadic completion.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: XOneEighteenDyadicGeneratorCertificate.lean and XOneEighteenDyadicGeneratorRingCertificate.lean. Four complete pure data commands selected by Lean AST ranges; original signatures and values retained.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import Mathlib
import Definitions.Def_MazurTransfer_OrderEighteenDyadicCandidateData

open MazurTorsion.XOneEighteenDyadicCubicCertificate

namespace MazurTorsion.XOneEighteenDyadicGeneratorCertificate

/-- The multiplicative identity in the cubic coefficient model. -/
def one : CubicResidue := ![1, 0, 0]

/-- Reduction modulo `16` of the normalized generator at `s ≡ 74`. -/
def normalizedGenerator : CubicResidue := ![7, 10, 1]

end MazurTorsion.XOneEighteenDyadicGeneratorCertificate

namespace MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate

/-- The coefficient ring used throughout this finite certificate. -/
abbrev R := ZMod 16

/-- Evaluation of the normalized relative cubic on coefficient vectors.
The two coefficient vectors are respectively `τ² - 3` and
`-2τ² + τ + 4`. -/
def normalizedRelativeCubicValue (z : Fin 3 → R) : Fin 3 → R :=
  XOneEighteenDyadicCubicCertificate.mul
      (XOneEighteenDyadicCubicCertificate.mul z z) z +
    XOneEighteenDyadicCubicCertificate.mul ![-3, 0, 1]
      (XOneEighteenDyadicCubicCertificate.mul z z) +
    XOneEighteenDyadicCubicCertificate.mul ![4, 1, -2] z -
    XOneEighteenDyadicGeneratorCertificate.one

end MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate


