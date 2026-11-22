-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_AdCpctDen
-- name    : Formalism_PeriodIntegrals_AdCpctDen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:11.301926+00:00
-- url     : https://prove2.me/theorems/0c276ae4-e00b-4509-9216-dcf253d195f7
-- title:
--   Ad Cpct Den
-- statement:
--   Definitions and structural lemmas for Ad Cpct Den, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/AdCpctDen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
open NumberField IsDedekindDomain
def AdCpctDen : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (C : Set (FiniteAdeleRing (𝓞 F) F)), IsCompact C →
    ∃ N : ℕ, 0 < N ∧ ∀ f : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ C → IsIntegral ℤ ((N : F) * f)
end PI


