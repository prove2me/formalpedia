-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_SecondOrderMonomial
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_SecondOrderMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:08.186986+00:00
-- url     : https://prove2.me/theorems/d681ae93-164e-46ac-8866-bb96e165550e
-- title:
--   Second Order Monomial
-- statement:
--   Definitions and structural lemmas for Second Order Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/SecondOrderMonomial.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.HalfIdentity
variable {k : Type} [CommRing k] {d : ℕ}
section
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)
variable [Fintype ι]
end
end GlobalTheory.HalfIdentity


