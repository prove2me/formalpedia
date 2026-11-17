-- Prove2me | Definitions.Def_TateOriginDivision
-- name    : TateOriginDivision
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:20.574105+00:00
-- url     : https://prove2.me/theorems/aa058894-9982-415b-8f31-80a82e655744
-- title:
--   The marked Tate origin and its odd-order division setup
-- statement:
--   The file abbreviates the rational Tate normal-form curve $W(b,c)$ and defines its marked affine point $P=(0,0)$. These carriers support the generic translation between odd additive order and vanishing or nonvanishing of the corresponding division-polynomial evaluation at the origin. This is the reusable interface from a rational odd-order point to raw Tate division conditions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_TateZ2xZ10Reduction
/-!
# Generic odd-order division condition at the Tate origin

This file factors out the kernel-checked division-polynomial argument shared by
the order-11 and order-18 developments.  If the marked origin on a Tate normal
form has odd additive order `n`, then `preΨ'_n(0) = 0`.  Conversely, a proper
odd multiple below the exact order has nonzero evaluation.

The final theorem combines this with `TateNormalFormBridge`: every rational
point of odd order greater than three produces nonsingular Tate parameters
with a nonzero `b` parameter and the corresponding raw division condition.
No explicit factorization of `preΨ'_n(0)` is asserted here.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOriginDivision

open Scratch.TateZ2xZ10Reduction

noncomputable section

abbrev W (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

theorem tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W, tateNormalFormCurve]

/-- The marked point `(0,0)` on a Tate normal form. -/
def tateOrigin (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

end

end MazurProof.TateOriginDivision


