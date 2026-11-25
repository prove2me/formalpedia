-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
-- name    : Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:04.619426+00:00
-- url     : https://prove2.me/theorems/2e3a7281-d05d-4f62-bd0d-49487053ac21
-- title:
--   Nat Cast Mul Tmul
-- statement:
--   Definitions and structural lemmas for Nat Cast Mul Tmul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NatCastMulTmul.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
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
open TensorProduct IsLocalRing
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
section T
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
variable {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
def chi (τ : OE →+* R) : (ℤ_[l] ⊗[ℤ] OE) →+* ResidueField R := (residue R).comp (tauX τ).toRingHom
variable {d : ℕ} [NeZero d] (em : ZMod d → OE →+* R)
end T
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl


