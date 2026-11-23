-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_IndepPts
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_IndepPts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:12.316822+00:00
-- url     : https://prove2.me/theorems/c021d35a-120b-43c8-8d1d-263f678eea84
-- title:
--   Indep Pts
-- statement:
--   Definitions and structural lemmas for Indep Pts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/IndepPts.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JInjCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DetAlg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB
variable {K : Type} [Field K]
  (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
  (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
    (S →ₐ[K] T) → pts S → pts T → Prop)
end ReciprocityTheory.ChartRestriction.G.PullbackSections


