-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_StrictNormalCrossingsEraseMember
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_StrictNormalCrossingsEraseMember
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:07:06.187941+00:00
-- url     : https://prove2.me/theorems/a62a77f3-6d89-460a-9017-89d57ddcf8d8
-- title:
--   Strict Normal Crossings Erase Member
-- statement:
--   Definitions and structural lemmas for Strict Normal Crossings Erase Member, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/StrictNormalCrossingsEraseMember.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def natSuccAbove (j i : ℕ) : ℕ := if i < j then i else i + 1
def complOrderEmbPreimage (m : ℕ) (S : Finset (Fin m)) (s : Fin m) : Option (Fin (m - S.card)) :=
  if hs : s ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S hs))
def transportSuccAboveToCompl {m : ℕ} (S : Finset (Fin m)) (j : ℕ) (a : ℕ → Option (Fin m))
    (i : ℕ) : Option (Fin (m - S.card)) :=
  (a (natSuccAbove j i)).bind (complOrderEmbPreimage m S)
end FunctorialResolution.EmbeddedResolution
end


