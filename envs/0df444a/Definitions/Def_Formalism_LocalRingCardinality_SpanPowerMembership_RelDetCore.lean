-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:35:58.119133+00:00
-- url     : https://prove2.me/theorems/9357fbc3-d70c-4260-a512-e9eccd1dbe8d
-- title:
--   Rel Det Core
-- statement:
--   Definitions and structural lemmas for Rel Det Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/RelDetCore.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace Formalism.BasicNotions.Examples₂
section Core
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}
def detIdeal (L : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x | ∃ v : Fin N → Fin N → E, (∀ j, v j ∈ L) ∧ x = (Matrix.of v).det}
end Core
end Formalism.BasicNotions.Examples₂


