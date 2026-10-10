-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffLoss_variance_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T09:33:40.291801+00:00
-- url     : https://prove2.me/submissions/1c13ccc1-e260-48c3-b128-7ddac6dd731b

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteHattendorffLossVariance
import Definitions.Def_actuarial_finiteHattendorffNetAtRisk
import Definitions.Def_actuarial_finiteMortalityDiscountedShock
import Theorems.Thm_ActuarialValuation_finiteHattendorffLoss_pathwise
import Theorems.Thm_ActuarialValuation_finiteHattendorffVariance_shift
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
    finiteHattendorffLossVariance w K n v premium benefit reserve =
      ∑ t ∈ Finset.range n,
        (finiteHattendorffNetAtRisk v benefit reserve t) ^ 2 *
          finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t := by
  let rho := finiteHattendorffNetAtRisk v benefit reserve
  let shock := finiteMortalityDiscountedShock w K rho n
  have hpath :
      finiteHattendorffLoss K n v premium benefit reserve =
        (fun ω : Ω => reserve 0 + shock ω) := by
    funext ω
    exact finiteHattendorffLoss_pathwise
      w K n v premium benefit reserve hw hsum hS hR ω
  calc
    finiteHattendorffLossVariance w K n v premium benefit reserve =
        finiteMortalityVariance w (fun ω : Ω => reserve 0 + shock ω) := by
          change finiteMortalityVariance w
            (finiteHattendorffLoss K n v premium benefit reserve) =
            finiteMortalityVariance w (fun ω : Ω => reserve 0 + shock ω)
          rw [hpath]
    _ = finiteMortalityVariance w shock :=
      finiteHattendorffVariance_shift w shock (reserve 0) hsum
    _ = ∑ t ∈ Finset.range n, (rho t) ^ 2 *
          finiteMortalityDeathMass w K t * finiteMortalitySurvivalRate w K t :=
      finiteHattendorffShock_variance w K n rho hw hS
