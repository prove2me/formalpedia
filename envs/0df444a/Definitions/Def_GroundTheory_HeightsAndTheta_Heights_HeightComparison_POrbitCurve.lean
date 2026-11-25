-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:53:51.579939+00:00
-- url     : https://prove2.me/theorems/466eaf7c-086c-434f-9ea5-edece5678a47
-- title:
--   POrbit Curve
-- statement:
--   Definitions and structural lemmas for POrbit Curve, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCurve.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
namespace OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
def tDeg (ι : Type) [DecidableEq ι] : ι → ι → ℕ := fun k ↦ Pi.single k 1
def coneMapQ (x : Cone n (AlgebraicClosure ℚ)) :
    MvPolynomial (Coord n) ℚ →ₐ[ℚ] MvPolynomial ι (AlgebraicClosure ℚ) :=
  aeval fun p ↦ C (flatCone x p) * X p.1
end OrbitCurve
end
end GroundTheory.Heights₂.Heights


