-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LocalEnd
-- name    : Formalism_PeriodIntegrals_LocalEnd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:09.316272+00:00
-- url     : https://prove2.me/theorems/89042ea6-6f59-4eae-ae1c-9c5b3d7944c8
-- title:
--   Local End
-- statement:
--   Definitions and structural lemmas for Local End, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LocalEnd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace PI
def LocalEndHomeo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F),
    Continuous τ ∧ ∃ τ' : v.adicCompletion F →+* v.adicCompletion F, Continuous τ' ∧ ∀ a, τ (τ' a) = a
end PI


