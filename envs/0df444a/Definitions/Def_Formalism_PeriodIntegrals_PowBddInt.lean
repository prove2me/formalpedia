-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_PowBddInt
-- name    : Formalism_PeriodIntegrals_PowBddInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:26.924398+00:00
-- url     : https://prove2.me/theorems/28e5ca48-6ab1-4caf-95b5-e956cef7d74e
-- title:
--   Pow Bdd Int
-- statement:
--   Definitions and structural lemmas for Pow Bdd Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/PowBddInt.lean

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
open Matrix
def PowBddInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (γ : Matrix (Fin k) (Fin k) E) (N : ℕ), 0 < N →
    (∀ (n : ℕ) (i j : Fin k), IsIntegral ℤ ((N : E) * (γ ^ n) i j)) →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i)
end PI


