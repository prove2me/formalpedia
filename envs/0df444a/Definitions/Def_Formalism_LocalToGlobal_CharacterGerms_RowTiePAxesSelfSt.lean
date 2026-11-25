-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:29.726083+00:00
-- url     : https://prove2.me/theorems/e44fe77f-d19b-4f95-a4cb-f5bef4a88172
-- title:
--   Row Tie PAxes Self St
-- statement:
--   Definitions and structural lemmas for Row Tie PAxes Self St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePAxesSelfSt.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
end Formalism.L2.FormalSeriesBounds


