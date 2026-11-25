-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
-- name    : Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:50.802213+00:00
-- url     : https://prove2.me/theorems/8cb58b1f-abaf-4774-a0ea-4f371e8a9c5f
-- title:
--   Coeff Along Cv Congr
-- statement:
--   Definitions and structural lemmas for Coeff Along Cv Congr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffAlongCvCongr.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
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


