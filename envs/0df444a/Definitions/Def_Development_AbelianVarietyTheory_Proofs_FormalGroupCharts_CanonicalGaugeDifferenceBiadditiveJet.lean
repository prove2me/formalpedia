-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonicalGaugeDifferenceBiadditiveJet
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:18:33.009501+00:00
-- url     : https://prove2.me/theorems/f07c07e1-f7ff-4c24-9885-54650f613edb
-- title:
--   Canonical Gauge Difference Biadditive Jet
-- statement:
--   Definitions and structural lemmas for Canonical Gauge Difference Biadditive Jet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonicalGaugeDifferenceBiadditiveJet.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqFormalExpIffAndExistsLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open MvPowerSeries
namespace GlobalTheory.ChartCmp.GaugeDiff
section Map
variable {R k : Type} [CommRing R] [CommRing k] {d : ℕ} (β : R →+* k)
def mapPt {n : ℕ} (a : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map β (a i)
end Map
section Ring
variable {k : Type} [CommRing k] {d : ℕ}
variable [Algebra ℚ k]
end Ring
end GlobalTheory.ChartCmp.GaugeDiff


