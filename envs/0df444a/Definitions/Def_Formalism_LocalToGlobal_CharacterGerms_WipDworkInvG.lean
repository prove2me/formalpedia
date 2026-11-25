-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_WipDworkInvG
-- name    : Formalism_LocalToGlobal_CharacterGerms_WipDworkInvG
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:27.332667+00:00
-- url     : https://prove2.me/theorems/8af3d9b1-7a26-441e-b8c3-d0d637cb00b4
-- title:
--   Wip Dwork Inv G
-- statement:
--   Definitions and structural lemmas for Wip Dwork Inv G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/WipDworkInvG.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
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
open MvPowerSeries
namespace Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] {v : AddValuation C (WithTop ℝ)}
end Formalism.L2.FormalSeriesBounds.AltInv


