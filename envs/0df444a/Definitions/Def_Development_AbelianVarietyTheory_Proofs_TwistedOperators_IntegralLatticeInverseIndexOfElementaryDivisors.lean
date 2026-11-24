-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralLatticeInverseIndexOfElementaryDivisors
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralLatticeInverseIndexOfElementaryDivisors
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:38:11.044192+00:00
-- url     : https://prove2.me/theorems/3d41e288-d65d-47cc-8b98-5587807f3b67
-- title:
--   Integral Lattice Inverse Index Of Elementary Divisors
-- statement:
--   Definitions and structural lemmas for Integral Lattice Inverse Index Of Elementary Divisors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralLatticeInverseIndexOfElementaryDivisors.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardIntegersModUniformizerEqQSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
namespace GlobalTheory.InertZeta
section
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
def scaledInt (c : L) : AddSubgroup L := (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft c)
end
section
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
end
end GlobalTheory.InertZeta


