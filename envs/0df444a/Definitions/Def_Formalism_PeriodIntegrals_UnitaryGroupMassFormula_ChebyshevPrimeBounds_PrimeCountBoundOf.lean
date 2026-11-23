-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:27.371244+00:00
-- url     : https://prove2.me/theorems/f14619cb-bf93-4b26-a979-ffed3ad28997
-- title:
--   Prime Count Bound Of
-- statement:
--   Definitions and structural lemmas for Prime Count Bound Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/PrimeCountBoundOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimeCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.PC
open Real
def chA : ℝ := log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30
def lf (x : ℝ) : ℝ := log ((Nat.factorial ⌊x⌋₊ : ℕ) : ℝ)
def chD (x : ℝ) : ℝ := lf x - lf (x / 2) - lf (x / 3) - lf (x / 5) + lf (x / 30)
def LfUpper : Prop := ∀ y : ℝ, 1 ≤ y → lf y ≤ y * log y - y + log y / 2 + 1
def LfLower : Prop := ∀ y : ℝ, 1 ≤ y → y * log y - y - log y / 2 + 9 / 10 ≤ lf y
def ANum : Prop := 0.92129 ≤ chA ∧ chA ≤ 0.9213
def DUpper : Prop := ∀ x : ℝ, 30 ≤ x → chD x ≤ chA * x + 5 / 2 * log x - 4
def DLower : Prop := ∀ x : ℝ, 30 ≤ x → chA * x - 5 / 2 * log x + 2 ≤ chD x
def Sandwich : Prop := ∀ x : ℝ, 0 ≤ x →
  Chebyshev.psi x - Chebyshev.psi (x / 6) ≤ chD x ∧ chD x ≤ Chebyshev.psi x
def CHUpper : Prop := ∀ x : ℝ, 1 ≤ x → Chebyshev.psi x ≤ 1.1056 * x + 0.7 * (log x) ^ 2
def CHLower : Prop := ∀ x : ℝ, 30 ≤ x → 0.92129 * x - 5 / 2 * log x ≤ Chebyshev.psi x
def PCLarge (x₀ : ℝ) : Prop := ∀ y : ℝ, x₀ ≤ y → ((pr y).card : ℝ) < 1.26 * y / log y
def PCSmall (x₀ : ℝ) : Prop := ∀ y : ℝ, 1 < y → y < x₀ → ((pr y).card : ℝ) < 1.26 * y / log y
end PI.PC


