-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PReducedNormalisationPlace
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PReducedNormalisationPlace
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T07:27:39.317498+00:00
-- url     : https://prove2.me/theorems/7df9c8a1-4ff1-483f-8735-14b5d2aba533
-- title:
--   PReduced Normalisation Place
-- statement:
--   Definitions and structural lemmas for PReduced Normalisation Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PReducedNormalisationPlace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StReducedNormalisationPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMinimalPrimePlace
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
open MvPolynomial ComplexSets MinimalPrimePlace
noncomputable section
namespace ReducedNormalisationPlace
variable {A B : Type*} [CommRing A] [CommRing B]
end ReducedNormalisationPlace
end
end GroundTheory.Heights₂.Heights


