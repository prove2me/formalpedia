-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:05:44.429805+00:00
-- url     : https://prove2.me/theorems/b1b1d097-d75a-4808-961a-3aec5fbf362a
-- title:
--   PCoord Curve Algebraic
-- statement:
--   Definitions and structural lemmas for PCoord Curve Algebraic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/PCoordCurveAlgebraic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CoordCurveDegree
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
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 Algebra
namespace CoordCurveDegree
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
def coneMapQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p ↦ C (y p) * X p.1
end CoordCurveDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet


