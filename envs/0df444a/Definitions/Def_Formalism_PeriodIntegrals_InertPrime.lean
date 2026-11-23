-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_InertPrime
-- name    : Formalism_PeriodIntegrals_InertPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:08.027913+00:00
-- url     : https://prove2.me/theorems/29899b88-5674-4b30-bb11-a92dcbdfb54a
-- title:
--   Inert Prime
-- statement:
--   Definitions and structural lemmas for Inert Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/InertPrime.lean

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
namespace PI
def InertPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (b : K) (d p : ℕ), b ^ 2 = -(d : K) → p.Prime →
    jacobiSym (-(d : ℤ)) p = -1 → (Ideal.span {(p : 𝓞 K)}).IsPrime
end PI


