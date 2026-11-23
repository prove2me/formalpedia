-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegrallyClosedPowerSeries
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegrallyClosedPowerSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:44.967822+00:00
-- url     : https://prove2.me/theorems/1864727a-8934-4cfe-8b70-4a0f1b0af419
-- title:
--   Is Integrally Closed Power Series
-- statement:
--   Definitions and structural lemmas for Is Integrally Closed Power Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegrallyClosedPowerSeries.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace GlobalTheory.PowerSeriesNormal
open PowerSeries
variable {R : Type} [CommRing R] [IsDomain R]
def almostMultiples (g : R⟦X⟧) : Ideal R⟦X⟧ where
  carrier := {f | ∃ h, h ≠ 0 ∧ ∀ n : ℕ, g ^ n ∣ h * f ^ n}
  zero_mem' := ⟨1, one_ne_zero, fun n => by
    rw [one_mul]; exact pow_dvd_pow_of_dvd (dvd_zero g) n⟩
  add_mem' := by
    rintro a b ⟨h, hh, H⟩ ⟨k, hk, K⟩
    refine ⟨h * k, mul_ne_zero hh hk, fun n => ?_⟩
    rw [add_pow, Finset.mul_sum]
    refine Finset.dvd_sum fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have e : g ^ n = g ^ i * g ^ (n - i) := by rw [← pow_add, Nat.add_sub_cancel' hi']
    have e2 : h * k * (a ^ i * b ^ (n - i) * (n.choose i : R⟦X⟧))
        = (h * a ^ i) * (k * b ^ (n - i)) * (n.choose i : R⟦X⟧) := by ring
    rw [e, e2]
    exact (mul_dvd_mul (H i) (K _)).mul_right _
  smul_mem' := by
    rintro c a ⟨h, hh, H⟩
    refine ⟨h, hh, fun n => ?_⟩
    rw [smul_eq_mul, mul_pow, mul_left_comm]
    exact (H n).mul_left _
end GlobalTheory.PowerSeriesNormal


