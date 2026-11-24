-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjoint
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjoint
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:03.62738+00:00
-- url     : https://prove2.me/theorems/d26a2a78-47ef-434b-8954-881c6e12c602
-- title:
--   Fock Pairing Linear Substitution Adjoint
-- statement:
--   Definitions and structural lemmas for Fock Pairing Linear Substitution Adjoint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockPairingLinearSubstitutionAdjoint.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Formalism.L2.DIV
namespace GlobalTheory.MinorFrame
variable {σ σ' : Type} [Fintype σ] [Fintype σ']
end GlobalTheory.MinorFrame
end


