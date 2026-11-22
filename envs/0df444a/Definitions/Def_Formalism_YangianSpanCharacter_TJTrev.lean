-- Prove2me | Definitions.Def_Formalism_YangianSpanCharacter_TJTrev
-- name    : Formalism_YangianSpanCharacter_TJTrev
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:05:22.442697+00:00
-- url     : https://prove2.me/theorems/89e5f07b-fa76-4eca-83f4-8059c43fdf1e
-- title:
--   TJTrev
-- statement:
--   Definitions and structural lemmas for TJTrev, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/YangianSpanCharacter/TJTrev.lean

import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.YangianSpanCharacter.T
open Matrix
def TJTrev : Prop :=
  ∀ (R A : Type) [CommRing R] [Ring A] [Algebra R A] (q d di : A) (Y : R),
    d * di = 1 → di * d = 1 → d * q = q * d + d →
      Tm (Y + 1) q d di * J A * (Tm Y q d di)ᵀ = J A
end Formalism.YangianSpanCharacter.T


