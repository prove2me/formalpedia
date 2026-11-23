-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_Chebyshev
-- name    : Formalism_PeriodIntegrals_Chebyshev
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:57.728232+00:00
-- url     : https://prove2.me/theorems/2ab572e6-d575-478f-b1af-9f2c9c0f9def
-- title:
--   Chebyshev
-- statement:
--   Definitions and structural lemmas for Chebyshev, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/Chebyshev.lean

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
def PsiLeTwo : Prop := ∀ y : ℝ, 0 ≤ y → Chebyshev.psi y ≤ 2 * y
def PsiLower : Prop := ∀ u : ℝ, 2 ≤ u → 1 / 5 * u ≤ Chebyshev.psi u
def PrimeTailLogFour : Prop :=
  ∀ X : ℝ, 0 < X → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2 * Real.log 4 / X
end PI


