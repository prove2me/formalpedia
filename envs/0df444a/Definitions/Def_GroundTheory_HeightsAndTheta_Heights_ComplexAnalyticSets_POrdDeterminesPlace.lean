-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POrdDeterminesPlace
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POrdDeterminesPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:10.269399+00:00
-- url     : https://prove2.me/theorems/0524356e-c021-499a-ba25-16f3844191a4
-- title:
--   POrd Determines Place
-- statement:
--   Definitions and structural lemmas for POrd Determines Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/POrdDeterminesPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdDeterminesPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
instance isIntegral_curveNormalisation (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
  inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
    ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
end
end GroundTheory.Heights₂.Heights


