-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:53.568479+00:00
-- url     : https://prove2.me/theorems/b6725437-3184-4f44-8a52-81462f2d9709
-- title:
--   Statements Curve Ring Finite
-- statement:
--   Definitions and structural lemmas for Statements Curve Ring Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsCurveRingFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def CurveRingFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 → Module.Finite ℤ (curveRing y)
end GroundTheory.Heights₂.Heights.Targets


