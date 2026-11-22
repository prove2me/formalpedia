-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrRightOfFinite
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrRightOfFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:31.849123+00:00
-- url     : https://prove2.me/theorems/83b6535a-bc3d-40d2-ac72-43792a5415f8
-- title:
--   Rr Right Of Finite
-- statement:
--   Definitions and structural lemmas for Rr Right Of Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnimodularSchurMeasures/RrRightOfFinite.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
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
open MeasureTheory Set
open scoped ENNReal Pointwise
section Abs3
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
end Abs3
end Formalism.MainNotions.LeviCoordinates
end


