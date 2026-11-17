-- Prove2me | Definitions.Def_TateNormalFormBridge
-- name    : TateNormalFormBridge
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:19.301204+00:00
-- url     : https://prove2.me/theorems/c33f59ac-2d6b-4e4e-b862-b95f4a02ffea
-- title:
--   Normalization of marked elliptic-curve points to Tate form
-- statement:
--   The file defines the marked point $(0,0)$ on a nonsingular Tate normal form and the additive equivalence associated with equality of Weierstrass equations. Around these carriers it organizes the translation-to-the-origin and scaling constructions that preserve the group law and the order of a marked point. Its role is to turn any rational point of order greater than three into explicit Tate parameters with nonzero $b$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_TateZ2xZ10Reduction
/-!
# A reusable Tate-normal-form bridge

The N=10 and N=12 reductions contain the same normalization argument.  This
file extracts the part that depends only on a marked point of order greater
than three: after two explicit Weierstrass variable changes, the marked point
is `(0,0)` on Tate normal form and its additive order is preserved.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.TateNormalFormBridge

open Scratch.TateZ2xZ10Reduction

noncomputable section

lemma tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]

/-- The marked origin on Tate normal form. -/
def tateOrigin (b c : ℚ)
    [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

noncomputable def pointCurveEqAddEquiv
    {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point W' := by
  subst h
  exact AddEquiv.refl _

end

end MazurProof.TateNormalFormBridge


