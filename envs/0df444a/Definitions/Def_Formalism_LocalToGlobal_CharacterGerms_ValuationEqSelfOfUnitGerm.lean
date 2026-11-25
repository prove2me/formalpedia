-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
-- name    : Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:07.856259+00:00
-- url     : https://prove2.me/theorems/1ae2b528-c456-55c1-ad29-7b18970d8ff2
-- title:
--   Valuation Eq Self Of Unit Germ
-- statement:
--   Definitions and structural lemmas for Valuation Eq Self Of Unit Germ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqSelfOfUnitGerm.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
namespace VP
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))
end VP
end Formalism.L2.FormalSeriesBounds


