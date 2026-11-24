-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteOfLocallyFinite
-- name    : Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteOfLocallyFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:13.955575+00:00
-- url     : https://prove2.me/theorems/972b210f-e3f2-44e2-a46f-c6c907f55dd6
-- title:
--   Finite Of Locally Finite
-- statement:
--   Definitions and structural lemmas for Finite Of Locally Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FiniteOfLocallyFinite.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ProperlyDiscontinuousFlags
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.PropDiscCompare
open NumberField Topology ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end GlobalTheory.PropDiscCompare


