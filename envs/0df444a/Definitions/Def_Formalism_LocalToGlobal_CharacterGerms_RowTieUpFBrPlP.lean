-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:21.950989+00:00
-- url     : https://prove2.me/theorems/e29e42e4-76d9-49b8-945c-e45813be2c51
-- title:
--   Row Tie Up FBr Pl P
-- statement:
--   Definitions and structural lemmas for Row Tie Up FBr Pl P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieUpFBrPlP.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
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
open TensorProduct IsLocalRing Polynomial
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
section Main
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ_[l] R] {d : ℕ} [NeZero d]
  (em : ZMod d → OE →+* R)
end Main
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl


