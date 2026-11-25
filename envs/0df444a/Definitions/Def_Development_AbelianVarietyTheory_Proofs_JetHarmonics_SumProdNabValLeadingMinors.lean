-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdNabValLeadingMinors
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdNabValLeadingMinors
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:00.266667+00:00
-- url     : https://prove2.me/theorems/16b7701e-e6b4-4462-a0d0-e1753bd9c1fd
-- title:
--   Sum Prod Nab Val Leading Minors
-- statement:
--   Definitions and structural lemmas for Sum Prod Nab Val Leading Minors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SumProdNabValLeadingMinors.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.CrudeValue
variable {k : Type} [CommRing k] {d : ℕ}
variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] [Algebra ℚ k] [Algebra R k]
end GlobalTheory.CrudeValue
namespace GlobalTheory
end GlobalTheory


