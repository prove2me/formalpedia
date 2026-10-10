-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffReserveLoss_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T09:51:52.254658+00:00
-- url     : https://prove2.me/submissions/4b47abb8-6d2f-427e-8c9b-8292dacbc8bc

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_finiteHattendorffExpectedLoss
import Definitions.Def_actuarial_finiteHattendorffLossVariance
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Theorems.Thm_ActuarialValuation_finiteHattendorffLoss_pathwise
import Theorems.Thm_ActuarialValuation_finiteHattendorffShock_expected_zero
import Theorems.Thm_ActuarialValuation_finiteHattendorffLossVariance_eq_shock
import Theorems.Thm_ActuarialValuation_finiteHattendorffShock_variance

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
    (finiteHattendorffExpectedLoss w K n v premium benefit reserve = reserve 0) ∧
      (finiteHattendorffLossVariance w K n v premium benefit reserve =
        ∑ t ∈ Finset.range n,
          (finiteHattendorffNetAtRisk v benefit reserve t) ^ 2 *
            finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t) := by
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
  constructor
  · change (∑ ω : Ω, w ω * finiteHattendorffLoss K n v premium benefit reserve ω) =
      reserve 0
    rw [hpath]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul]
    rw [hsum, hshock]
    ring
  · calc
      finiteHattendorffLossVariance w K n v premium benefit reserve =
          finiteMortalityVariance w shock :=
            finiteHattendorffLossVariance_eq_shock
              w K n v premium benefit reserve hw hsum hS hR
      _ = ∑ t ∈ Finset.range n, (rho t) ^ 2 *
            finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t :=
              finiteHattendorffShock_variance w K n rho hw hS
