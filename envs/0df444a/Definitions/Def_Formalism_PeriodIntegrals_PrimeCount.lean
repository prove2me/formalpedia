-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_PrimeCount
-- name    : Formalism_PeriodIntegrals_PrimeCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:49:00.68798+00:00
-- url     : https://prove2.me/theorems/da691a28-60f8-4474-b88c-6d9ea2cca5d6
-- title:
--   Prime Count
-- statement:
--   Definitions and structural lemmas for Prime Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/PrimeCount.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI
def pr (y : ℝ) : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime
def PrimeCountBound : Prop := ∀ y : ℝ, 1 < y → ((pr y).card : ℝ) < 1.26 * y / Real.log y
end PI


