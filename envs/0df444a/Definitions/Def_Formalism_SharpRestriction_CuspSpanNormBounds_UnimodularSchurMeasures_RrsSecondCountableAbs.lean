-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrsSecondCountableAbs
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrsSecondCountableAbs
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:23:31.103572+00:00
-- url     : https://prove2.me/theorems/9dbb872d-cd27-4ed5-b92c-c348d870153a
-- title:
--   Rrs Second Countable Abs
-- statement:
--   Definitions and structural lemmas for Rrs Second Countable Abs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrsSecondCountableAbs.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set Topology
open scoped Pointwise
section Abs
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
end Abs
open Formalism.MainNotions.S
end Formalism.MainNotions.LeviCoordinates
end


