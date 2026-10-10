-- Prove2me | solution 1 for ActuarialValuation.hattendorff_annual_allocation_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:08:52.482096+00:00
-- url     : https://prove2.me/submissions/3ab8f99d-0292-427e-80b9-30b336ffee7c

import Mathlib.Data.Finset.Range
import Definitions.Def_actuarial_annualReserveGain
import Definitions.Def_actuarial_discountedAnnualGainSum
import Definitions.Def_actuarial_finiteScenarioCovariance
import Definitions.Def_actuarial_finiteScenarioExpectation
import Definitions.Def_actuarial_finiteScenarioVariance
import Theorems.Thm_ActuarialValuation_annualReserveGain_expected_zero
import Theorems.Thm_ActuarialValuation_annualReserveGain_discounted_telescope
import Theorems.Thm_ActuarialValuation_discountedAnnualGain_variance_orthogonal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (C : ℕ → Ω → ℝ) (R : ℕ → ℝ)
    (v : ℝ) (n : ℕ) (ω : Ω)
    (hw : (∑ a : Ω, w a) = 1)
    (hR : ∀ k ∈ Finset.range n,
      finiteScenarioExpectation w (C k) + v * R (k + 1) = R k)
    (horth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i ≠ j → finiteScenarioCovariance w (annualReserveGain C R v i)
        (annualReserveGain C R v j) = 0) :
    (∀ k ∈ Finset.range n,
      finiteScenarioExpectation w (annualReserveGain C R v k) = 0)
    ∧ (finiteScenarioVariance w
      (discountedAnnualGainSum (annualReserveGain C R v) v n) =
      ∑ k ∈ Finset.range n, v ^ (2 * k) *
        finiteScenarioVariance w (annualReserveGain C R v k))
    ∧ (discountedAnnualGainSum (annualReserveGain C R v) v n ω =
       discountedAnnualGainSum C v n ω + v ^ n * R n - R 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    exact annualReserveGain_expected_zero w C R v k hw (hR k hk)
  · exact discountedAnnualGain_variance_orthogonal w
      (annualReserveGain C R v) v n horth
  · exact annualReserveGain_discounted_telescope C R v n ω
