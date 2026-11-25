-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionIndependence
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionIndependence
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:01:19.425793+00:00
-- url     : https://prove2.me/theorems/54643cb5-4002-4c81-9958-b186d672bcd3
-- title:
--   PPair Number Expansion Independence
-- statement:
--   Definitions and structural lemmas for PPair Number Expansion Independence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionIndependence.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
section ClassNumPairDiff
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end ClassNumPairDiff
end
end GroundTheory.Heights₂.Heights.NumbersDVR


