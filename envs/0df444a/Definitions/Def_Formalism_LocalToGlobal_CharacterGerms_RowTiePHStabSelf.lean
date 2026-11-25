-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStabSelf
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePHStabSelf
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:53:09.866965+00:00
-- url     : https://prove2.me/theorems/e76e72be-b50e-4537-b9c6-c24120e52231
-- title:
--   Row Tie PHStab Self
-- statement:
--   Definitions and structural lemmas for Row Tie PHStab Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStabSelf.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
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
section Rename₂
variable {dd : ℕ}
end Rename₂
section Self
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I0 : Type} [Fintype I0]
end Self
end Formalism.L2.FormalSeriesBounds


