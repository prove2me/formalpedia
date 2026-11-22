-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_SArith
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_SArith
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:34.169647+00:00
-- url     : https://prove2.me/theorems/c42e22f8-26f5-44b5-b64a-776b532929c7
-- title:
--   SArith
-- statement:
--   Definitions and structural lemmas for SArith, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/SArith.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.S
open NumberField
def SplitsCompl (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : 𝓞 E) ∈ P) → Ideal.absNorm P = p ∧ (p : 𝓞 E) ∉ P ^ 2
end Formalism.MainNotions.S


