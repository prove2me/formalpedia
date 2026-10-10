-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffExpectedLoss_eq_openingReserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T09:48:34.38721+00:00
-- url     : https://prove2.me/submissions/99a1276f-03b1-4fae-baab-01587b3e9d67

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_finiteHattendorffExpectedLoss
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk
import Theorems.Thm_ActuarialValuation_finiteHattendorffLoss_pathwise
import Theorems.Thm_ActuarialValuation_finiteHattendorffShock_expected_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (K : Ω → ℕ) (n : ℕ) (v : ℝ)
    (premium benefit reserve : ℕ → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hsum : (∑ ω : Ω, w ω) = 1)
    (hS : ∀ t ∈ Finset.range n, 0 < finiteMortalitySurvivalMass w K t)
    (hR : ∀ t ∈ Finset.range n,
      finiteReserveAnnualBalance v reserve premium benefit
        (finiteMortalitySurvivalRate w K) (finiteMortalityDeathRate w K) t) :
    finiteHattendorffExpectedLoss w K n v premium benefit reserve =
      reserve 0 := by
  classical
  let rho := finiteHattendorffNetAtRisk v benefit reserve
  let shock := finiteMortalityDiscountedShock w K rho n
  have hpath :
      finiteHattendorffLoss K n v premium benefit reserve =
        (fun ω : Ω => reserve 0 + shock ω) := by
    funext ω
    exact finiteHattendorffLoss_pathwise
      w K n v premium benefit reserve hw hsum hS hR ω
  have hshock :
      (∑ ω : Ω, w ω * shock ω) = 0 :=
    finiteHattendorffShock_expected_zero w K n rho hS
  change (∑ ω : Ω, w ω * finiteHattendorffLoss K n v premium benefit reserve ω) =
    reserve 0
  rw [hpath]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  rw [hsum, hshock]
  ring
