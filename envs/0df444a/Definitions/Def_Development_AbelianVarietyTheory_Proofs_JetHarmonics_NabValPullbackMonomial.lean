-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:17:46.518828+00:00
-- url     : https://prove2.me/theorems/7ceb2c3c-e5c3-49e2-9042-ecb622e641dd
-- title:
--   Nab Val Pullback Monomial
-- statement:
--   Definitions and structural lemmas for Nab Val Pullback Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NabValPullbackMonomial.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
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
namespace GlobalTheory.PullbackColumn
variable {k : Type} [CommRing k] {d : ℕ}
end GlobalTheory.PullbackColumn
namespace GlobalTheory
open PullbackColumn
end GlobalTheory


