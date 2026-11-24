-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SphericalInductionTransitivityOfLeviExists
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SphericalInductionTransitivityOfLeviExists
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:28:34.259965+00:00
-- url     : https://prove2.me/theorems/f595b97e-16e4-4a61-8a59-a4a021861584
-- title:
--   Spherical Induction Transitivity Of Levi Exists
-- statement:
--   Definitions and structural lemmas for Spherical Induction Transitivity Of Levi Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SphericalInductionTransitivityOfLeviExists.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.SatakeWeyl
namespace GlobalTheory.InertZeta
section
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
end
end GlobalTheory.InertZeta
end


