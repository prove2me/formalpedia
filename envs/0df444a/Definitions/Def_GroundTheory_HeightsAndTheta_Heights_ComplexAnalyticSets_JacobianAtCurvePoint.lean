-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_JacobianAtCurvePoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_JacobianAtCurvePoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:16.642337+00:00
-- url     : https://prove2.me/theorems/13bf2e9a-b7ba-4cad-8b02-c02847580a89
-- title:
--   Jacobian At Curve Point
-- statement:
--   Definitions and structural lemmas for Jacobian At Curve Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/JacobianAtCurvePoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial IsLocalRing GradientAtPoint
noncomputable section
namespace JacobianAtCurvePoint
variable {σ : Type}
abbrev ptMax (w : σ → ℂ) : Ideal (MvPolynomial σ ℂ) := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
abbrev ptLoc (w : σ → ℂ) : Type := Localization.AtPrime (ptMax w)
abbrev ptIdeal (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : Ideal (ptLoc w) :=
  I.map (algebraMap (MvPolynomial σ ℂ) (ptLoc w))
abbrev ptQuot (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) : Type := ptLoc w ⧸ ptIdeal I w
variable [Fintype σ]
end JacobianAtCurvePoint
end
end GroundTheory.Heights₂.Heights


