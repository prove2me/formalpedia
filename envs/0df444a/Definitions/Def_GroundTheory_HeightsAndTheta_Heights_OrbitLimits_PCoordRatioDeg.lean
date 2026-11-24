-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCoordRatioDeg
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCoordRatioDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:39:02.899813+00:00
-- url     : https://prove2.me/theorems/55979b7c-e8dd-441d-b9ca-b8d656207ad3
-- title:
--   PCoord Ratio Deg
-- statement:
--   Definitions and structural lemmas for PCoord Ratio Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCoordRatioDeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordRatioDeg
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
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace CoordRatioDeg
def ratioField {S M : Type*} [Field M] [CharZero M] (R : S → S → Prop) (z : S → M) : IntermediateField ℚ M :=
  IntermediateField.adjoin ℚ {t | ∃ p q, R p q ∧ t = z p / z q}
end CoordRatioDeg
end GroundTheory.Heights₂.Heights.Targets


