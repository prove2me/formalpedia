-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLinearCombination
-- name    : Formalism_LocalToGlobal_CharacterGerms_UncurryLinearCombination
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-27T05:58:25.999998+00:00
-- url     : https://prove2.me/theorems/6a607cbe-993a-5c0e-b210-508e8efc0c29
-- title:
--   Uncurry Linear Combination
-- statement:
--   Definitions and structural lemmas for Uncurry Linear Combination, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UncurryLinearCombination.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstVanishingAt
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
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
end Formalism.L2.FormalSeriesBounds


