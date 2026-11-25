-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieP_TCoord
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieP_TCoord
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:09.454772+00:00
-- url     : https://prove2.me/theorems/c33db46f-99a5-4891-8dc8-01dd275f4fb6
-- title:
--   Row Tie P TCoord
-- statement:
--   Definitions and structural lemmas for Row Tie P TCoord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieP_TCoord.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
namespace TCoord
open Formalism.IncomingBounds FormalGermZero GeneralGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]
end TCoord
def TCoordSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.TCoordSt Hc
end Formalism.L2.FormalSeriesBounds


