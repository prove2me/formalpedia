-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
-- name    : Formalism_LocalToGlobal_CharacterGerms_ValNonnegLeadingCoeffOfMemTySet
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T11:19:55.451508+00:00
-- url     : https://prove2.me/theorems/7a4a316e-b407-4800-9e33-f78daeec14be
-- title:
--   Val Nonneg Leading Coeff Of Mem Ty Set
-- statement:
--   Definitions and structural lemmas for Val Nonneg Leading Coeff Of Mem Ty Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValNonnegLeadingCoeffOfMemTySet.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
end RawChart
end Formalism.L2.FormalSeriesBounds


