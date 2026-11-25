-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralGermNabValCongr
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralGermNabValCongr
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:44:34.955435+00:00
-- url     : https://prove2.me/theorems/42dfddcd-26b3-4c9a-8e9a-b9c0fb5573c1
-- title:
--   Exists Integral Germ Nab Val Congr
-- statement:
--   Definitions and structural lemmas for Exists Integral Germ Nab Val Congr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralGermNabValCongr.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.IntegralColumnGerm
end GlobalTheory.IntegralColumnGerm
namespace GlobalTheory
open IntegralColumnGerm
end GlobalTheory


