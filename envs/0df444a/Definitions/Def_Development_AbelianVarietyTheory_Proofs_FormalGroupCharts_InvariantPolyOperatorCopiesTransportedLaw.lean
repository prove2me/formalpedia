-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantPolyOperatorCopiesTransportedLaw
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantPolyOperatorCopiesTransportedLaw
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:50:55.047572+00:00
-- url     : https://prove2.me/theorems/f0665ba8-f783-480a-a96f-3e77f4bb5ef3
-- title:
--   Invariant Poly Operator Copies Transported Law
-- statement:
--   Definitions and structural lemmas for Invariant Poly Operator Copies Transported Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/InvariantPolyOperatorCopiesTransportedLaw.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
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
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.ChartTrans GlobalTheory.NabCol
namespace GlobalTheory.ChartTransN
variable {k : Type} [CommRing k] {d n : ℕ}
end GlobalTheory.ChartTransN


