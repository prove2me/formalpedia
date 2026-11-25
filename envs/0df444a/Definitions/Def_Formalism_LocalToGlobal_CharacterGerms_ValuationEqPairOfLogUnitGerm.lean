-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
-- name    : Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:08.831014+00:00
-- url     : https://prove2.me/theorems/4e57b0ca-d2eb-4605-bc2c-c6d442c12056
-- title:
--   Valuation Eq Pair Of Log Unit Germ
-- statement:
--   Definitions and structural lemmas for Valuation Eq Pair Of Log Unit Germ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfLogUnitGerm.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
end VP
end Formalism.L2.FormalSeriesBounds


