-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_PrimeSums
-- name    : Formalism_PeriodIntegrals_PrimeSums
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:03.711147+00:00
-- url     : https://prove2.me/theorems/e5c72acc-c1e1-4eda-bd3c-ced4b15503c5
-- title:
--   Prime Sums
-- statement:
--   Definitions and structural lemmas for Prime Sums, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/PrimeSums.lean

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
def PrimeLogOverP : Prop :=
  ∀ Y : ℝ, 1 < Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y
def ThetaBound : Prop :=
  ∀ Y : ℝ, 1 < Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ Q, Real.log (p : ℝ) ≤ 1.02 * Y
def PrimeLogOverPSqTail : Prop :=
  ∀ X : ℝ, 0 < X → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X
end PI


