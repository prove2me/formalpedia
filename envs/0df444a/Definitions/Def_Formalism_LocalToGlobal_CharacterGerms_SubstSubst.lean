-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
-- name    : Formalism_LocalToGlobal_CharacterGerms_SubstSubst
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:23.152626+00:00
-- url     : https://prove2.me/theorems/87b2076c-948d-4d93-95b0-610f67ba2c39
-- title:
--   Subst Subst
-- statement:
--   Definitions and structural lemmas for Subst Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/SubstSubst.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet
import Definitions.Def_Formalism_DropLevelBounds_ConstantCoeffVanishing_UbintConstantCoeffEqZero
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace VP
section Gen
variable {C : Type} [Field C] {σ τ ρ : Type}
end Gen
section Exp
variable {C : Type} [Field C] [CharZero C] {n dd : ℕ}
end Exp
end VP
end Formalism.L2.FormalSeriesBounds


