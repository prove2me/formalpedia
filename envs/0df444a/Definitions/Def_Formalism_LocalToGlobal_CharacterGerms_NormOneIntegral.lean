-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
-- name    : Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:25.045882+00:00
-- url     : https://prove2.me/theorems/581192cb-3624-4756-baa8-4da4a5e8a0f6
-- title:
--   Norm One Integral
-- statement:
--   Definitions and structural lemmas for Norm One Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
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
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
section Gen
variable {C : Type} [Field C]
def ZP (C : Type) [Field C] (σ : Type) : Subring (MvPolynomial σ C) := (MvPolynomial.map (Int.castRingHom C)).range
end Gen
end Formalism.L2.FormalSeriesBounds.RF


