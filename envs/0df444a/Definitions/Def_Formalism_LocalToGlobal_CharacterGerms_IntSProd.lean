-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd
-- name    : Formalism_LocalToGlobal_CharacterGerms_IntSProd
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:42:24.218978+00:00
-- url     : https://prove2.me/theorems/12608b7e-0a31-4e9d-82d5-5cb78c9a261b
-- title:
--   Int SProd
-- statement:
--   Definitions and structural lemmas for Int SProd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IntSProd.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
namespace VP
section Inv
variable {C : Type} [Field C] {V : VF C} {σ : Type}
end Inv
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
end VP
end Formalism.L2.FormalSeriesBounds


