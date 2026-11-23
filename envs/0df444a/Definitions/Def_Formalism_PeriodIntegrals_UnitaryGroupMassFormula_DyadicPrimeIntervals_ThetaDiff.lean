-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DyadicPrimeIntervals_ThetaDiff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:10.512145+00:00
-- url     : https://prove2.me/theorems/427605b4-b275-4315-a4e4-078dc0f40281
-- title:
--   Theta Diff
-- statement:
--   Definitions and structural lemmas for Theta Diff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DyadicPrimeIntervals/ThetaDiff.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.PrimesDyadicRS.W
def At (y : ℝ) : Prop :=
  3 * y / (5 * Real.log y) < (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)
def SmallNat : Prop := ∀ h : ℕ, 41 ≤ h → h < 131072 →
  3 * ((h : ℝ) + 1) <
    10 * ((Nat.primeCounting h : ℝ) - (Nat.primeCounting (h / 2) : ℝ)) * Real.log ((h : ℝ) / 2)
def ThetaDiff : Prop := ∀ y : ℝ, 1 ≤ y →
  Chebyshev.theta (2 * y) - Chebyshev.theta y ≤
    ((Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)) * Real.log (2 * y)
def PsiTheta : Prop := ∀ x : ℝ, 1 ≤ x →
  Chebyshev.psi x - Chebyshev.theta x ≤ 3 * Chebyshev.psi (Real.sqrt x)
def RealIneq : Prop := ∀ y : ℝ, 65536 ≤ y →
  3 * y / (5 * Real.log y) * Real.log (2 * y) <
    (0.92129 * (2 * y) - 5 / 2 * Real.log (2 * y))
      - 3 * (1.1056 * Real.sqrt (2 * y) + 0.7 * Real.log (Real.sqrt (2 * y)) ^ 2)
      - (1.1056 * y + 0.7 * Real.log y ^ 2)
end PI.PrimesDyadicRS.W


