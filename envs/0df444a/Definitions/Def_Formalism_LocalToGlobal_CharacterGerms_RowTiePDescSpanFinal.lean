-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanFinal
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanFinal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:53:15.576324+00:00
-- url     : https://prove2.me/theorems/ca5bfcb3-e949-4aab-826a-13332a035777
-- title:
--   Row Tie PDesc Span Final
-- statement:
--   Definitions and structural lemmas for Row Tie PDesc Span Final, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescSpanFinal.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaLeaves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
end Formalism.L2.FormalSeriesBounds


